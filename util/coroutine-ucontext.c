/*
 * ucontext coroutine initialization code
 *
 * Copyright (C) 2006  Anthony Liguori <anthony@codemonkey.ws>
 * Copyright (C) 2011  Kevin Wolf <kwolf@redhat.com>
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.0 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, see <http://www.gnu.org/licenses/>.
 */

/* XXX Is there a nicer way to disable glibc's stack check for longjmp? */
#ifdef _FORTIFY_SOURCE
#undef _FORTIFY_SOURCE
#endif
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <dlfcn.h>
#include <fcntl.h>
#include <stdlib.h>
#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <pthread.h>
#include <signal.h>
#include "qemu/osdep.h"
#include <ucontext.h>
#include "qemu-common.h"
#include "qemu/coroutine_int.h"

#ifdef CONFIG_VALGRIND_H
#include <valgrind/valgrind.h>
#endif

#define INITIAL_STACK_SIZE (1 << 12)
#define MAX_STACK_SIZE (1 << 20)

typedef struct {
    Coroutine base;
    void *stack;
    sigjmp_buf env;

#ifdef CONFIG_VALGRIND_H
    unsigned int valgrind_stack_id;
#endif

    size_t allocated_stack_size;
} CoroutineUContext;

/**
 * Per-thread coroutine bookkeeping
 */
typedef struct {
    /** Currently executing coroutine */
    Coroutine *current;

    /** The default coroutine */
    CoroutineUContext leader;

    stack_t signal_stack;
} CoroutineThreadState;

static pthread_key_t thread_state_key;

/**
 * Global coroutine bookkeeping
 */
typedef int TItype __attribute__ ((mode (TI)));

typedef struct {
    /** Actual stack size that we need to grow. */
    size_t size;
    char  *pc;
} max_stack_t;

typedef union {
    max_stack_t stack;
    TItype      m_128;
} max_stack_ut;

typedef struct {
    max_stack_ut max_stack;
    int segfault_count;
    int zero_fd;
    struct sigaction old_sigsegv_act;
} CoroutineGlobalState;

static CoroutineGlobalState global;

/*
 * va_args to makecontext() must be type 'int', so passing
 * the pointer we need may require several int args. This
 * union is a quick hack to let us do that
 */
union cc_arg {
    void *p;
    int i[2];
};

/*
 * Pointers to libc functions are resolved in the coroutine_init constructor.
 * However, coroutine_init is not the first constructor that is invoked, and
 * other constructors may call malloc() which then calls call sigprocmask().
 * To workaround this, we initialize these pointers to a nop function until
 * the libc function pointers are resolved.
 */
static int nop_sigmask(int how, const sigset_t *set, sigset_t *oldset)
{
    return 0;
}

#define SIGMASK_WRAPPER(func) \
static int (*libc_##func)(int, const sigset_t *, sigset_t *) =          \
    &nop_sigmask;                                                       \
int func(int how, const sigset_t *set, sigset_t *oldset)                \
{                                                                       \
    sigset_t fixed_set;                                                 \
                                                                        \
    if (set && sigismember(set, SIGSEGV)) {                             \
      fixed_set = *set;                                                 \
      sigdelset(&fixed_set, SIGSEGV);                                   \
      set = &fixed_set;                                                 \
    }                                                                   \
                                                                        \
    return libc_##func(how, set, oldset);                               \
}

SIGMASK_WRAPPER(sigprocmask)
SIGMASK_WRAPPER(pthread_sigmask)
#undef SIGMASK_WRAPPER

static void try_update_max_stack(size_t size, void *uctx)
{
    ucontext_t *u = (ucontext_t *)uctx;
#if defined(__x86_64__)
    char *pc = (char *)u->uc_mcontext.gregs[REG_RIP];
#else
    char *pc = NULL;
#endif

    max_stack_ut newval;
    max_stack_ut oldval = global.max_stack;

    newval.stack.size = size;
    newval.stack.pc = pc;

    while (oldval.stack.size < newval.stack.size) {
        oldval.m_128 = __sync_val_compare_and_swap(&global.max_stack.m_128,
                                                   oldval.m_128, newval.m_128);
    }
}

static void sigsegv_action(int signum, siginfo_t *si, void *uctx)
{
    CoroutineThreadState *s = pthread_getspecific(thread_state_key);
    CoroutineUContext *current;
    void *p;

#define CHECK(exp) if (!(exp)) abort()

    /* Check that the sigsegv is actually a stack error that we can fix.
     * Otherwise, abort() the process */

    /* This a thread that runs coroutines */
    CHECK(s);

    /* This is a memory access (protection) error; the page exists */
    CHECK(si->si_signo == SIGSEGV);
    CHECK(si->si_code == SEGV_ACCERR);

    current = DO_UPCAST(CoroutineUContext, base, s->current);

    /* Check that this is not the default coroutine of the thread,
       which runs on the thread's stack allocated by pthread */
    CHECK(current != &s->leader);

    /* Now check siginfo to make sure that the fault address is within the
       address rance allocated for the current coroutine. */
    CHECK(si->si_addr >= current->stack);
    p = current->stack + MAX_STACK_SIZE - current->allocated_stack_size;
    CHECK(si->si_addr < p);

    /* Double the stack from the end */
    p -= current->allocated_stack_size;
    CHECK(p >= current->stack);
    p = mmap(p, current->allocated_stack_size, PROT_READ | PROT_WRITE,
             MAP_ANONYMOUS | MAP_PRIVATE | MAP_FIXED, -1, 0);
    CHECK(p != MAP_FAILED);

#undef CHECK

    /* Success! */
    current->allocated_stack_size *= 2;

    /* Update global max stack */
    try_update_max_stack(current->stack + MAX_STACK_SIZE - si->si_addr, uctx);
    __sync_fetch_and_add(&global.segfault_count, 1);
}

static void coroutine_init_global_state(CoroutineGlobalState *s)
{
    struct sigaction sa;

    /* Open /dev/zero for mmap for the purpose of reserving virtual
       address space for each coroutine stack */
    s->zero_fd = open("/dev/zero", O_RDONLY);
    if (s->zero_fd == -1) {
        abort();
    }

    /* Arm SIGSEGV handler */
    sa.sa_sigaction = sigsegv_action;
    sa.sa_flags = SA_ONSTACK | SA_SIGINFO;
    sigfillset(&sa.sa_mask);

    if (sigaction(SIGSEGV, &sa, &s->old_sigsegv_act) == -1) {
        abort();
    }

    s->max_stack.stack.size = INITIAL_STACK_SIZE;
}

static void coroutine_cleanup_global_state(CoroutineGlobalState *s)
{
    if (sigaction(SIGSEGV, &s->old_sigsegv_act, NULL) == -1) {
        abort();
    }

    if (s->segfault_count > 0) {
        fprintf(stderr, "Max coroutine stack size: %ld bytes Segfault PC %p "
                "Segfault count %d\n", s->max_stack.stack.size,
                s->max_stack.stack.pc, s->segfault_count);
    }
    close(s->zero_fd);
}

static CoroutineThreadState *coroutine_get_thread_state(void)
{
    CoroutineThreadState *s = pthread_getspecific(thread_state_key);

    if (!s) {
        s = g_malloc0(sizeof(*s));
        s->current = &s->leader.base;

        /* Allocate an alternate stack for handling SIGSEGV, if necessary. */
        if (sigaltstack(NULL, &s->signal_stack) == -1) {
            abort();
        }
        if (s->signal_stack.ss_flags == SS_DISABLE) {
            s->signal_stack.ss_sp = mmap(NULL, SIGSTKSZ, PROT_READ | PROT_WRITE,
                                         MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
            if (s->signal_stack.ss_sp == MAP_FAILED) {
                abort();
            }
            s->signal_stack.ss_flags = 0;
            s->signal_stack.ss_size = SIGSTKSZ;

            if (sigaltstack(&s->signal_stack, NULL) == -1) {
                abort();
            }
        } else {
            s->signal_stack.ss_sp = NULL;
        }

        pthread_setspecific(thread_state_key, s);
    }
    return s;
}

static void qemu_coroutine_thread_cleanup(void *opaque)
{
    CoroutineThreadState *s = opaque;

    if (s->signal_stack.ss_sp) {
        s->signal_stack.ss_flags = SS_DISABLE;
        if (sigaltstack(&s->signal_stack, NULL) == -1) {
            abort();
        }
        munmap(s->signal_stack.ss_sp, s->signal_stack.ss_size);
    }

    g_free(s);

}

static void __attribute__((constructor)) coroutine_init(void)
{
    int ret;

    ret = pthread_key_create(&thread_state_key, qemu_coroutine_thread_cleanup);
    if (ret != 0) {
        fprintf(stderr, "unable to create leader key: %s\n", strerror(errno));
        abort();
    }

    coroutine_init_global_state(&global);

#define RESOLVE_LIBC_FUNC(func)                                 \
    if (!(libc_##func = dlsym(RTLD_NEXT, #func))) abort()

    RESOLVE_LIBC_FUNC(sigprocmask);
    RESOLVE_LIBC_FUNC(pthread_sigmask);
#undef RESOLVE_LIBC_FUNC
}

static void __attribute__((destructor)) coroutine_cleanup(void)
{
    coroutine_cleanup_global_state(&global);
}

static void coroutine_trampoline(int i0, int i1)
{
    union cc_arg arg;
    CoroutineUContext *self;
    Coroutine *co;

    arg.i[0] = i0;
    arg.i[1] = i1;
    self = arg.p;
    co = &self->base;

    /* Initialize longjmp environment and switch back the caller */
    if (!sigsetjmp(self->env, 0)) {
        siglongjmp(*(sigjmp_buf *)co->entry_arg, 1);
    }
    coroutine_get_thread_state()->current = co;

    while (true) {
        co->entry(co->entry_arg);
        /* Deallocate excess stack when coroutine terminates. */
        if (self->allocated_stack_size > INITIAL_STACK_SIZE) {
            self->allocated_stack_size = INITIAL_STACK_SIZE;
            self->stack = mmap(self->stack, MAX_STACK_SIZE - INITIAL_STACK_SIZE,
                               PROT_READ, MAP_SHARED | MAP_FIXED,
                               global.zero_fd, 0);
            if (self->stack == MAP_FAILED) {
                abort();
            }
        }
        qemu_coroutine_switch(co, co->caller, COROUTINE_TERMINATE);
    }
}

Coroutine *qemu_coroutine_new(void)
{
    const size_t stack_size = MAX_STACK_SIZE;
    CoroutineUContext *co;
    ucontext_t old_uc, uc;
    sigjmp_buf old_env;
    union cc_arg arg = {0};
    void *p;

    /* Ensures that the thread state has been initialized */
    coroutine_get_thread_state();

    /* The ucontext functions preserve signal masks which incurs a
     * system call overhead.  sigsetjmp(buf, 0)/siglongjmp() does not
     * preserve signal masks but only works on the current stack.
     * Since we need a way to create and switch to a new stack, use
     * the ucontext functions for that but sigsetjmp()/siglongjmp() for
     * everything else.
     */

    if (getcontext(&uc) == -1) {
        abort();
    }

    co = g_malloc0(sizeof(*co));

    /* mmap in stack in 2 steps: map in /dev/zero for the max stack size
     * to reserve the virtual address space, then map in actual memory
     * for only the initial stack allocation
     */
    co->stack = mmap(NULL, stack_size, PROT_READ, MAP_SHARED,
                     global.zero_fd, 0);
    if (co->stack == MAP_FAILED) {
        abort();
    }
    co->allocated_stack_size = INITIAL_STACK_SIZE;
    p = co->stack + stack_size - co->allocated_stack_size;
    p = mmap(p, co->allocated_stack_size, PROT_READ | PROT_WRITE,
             MAP_ANONYMOUS | MAP_PRIVATE | MAP_FIXED, -1, 0);
    if (p == MAP_FAILED) {
        abort();
    }

    co->base.entry_arg = &old_env; /* stash away our jmp_buf */

    uc.uc_link = &old_uc;
    uc.uc_stack.ss_sp = co->stack;
    uc.uc_stack.ss_size = stack_size;
    uc.uc_stack.ss_flags = 0;

#ifdef CONFIG_VALGRIND_H
    co->valgrind_stack_id =
        VALGRIND_STACK_REGISTER(co->stack, co->stack + stack_size);
#endif

    arg.p = co;

    makecontext(&uc, (void (*)(void))coroutine_trampoline,
                2, arg.i[0], arg.i[1]);

    /* swapcontext() in, siglongjmp() back out */
    if (!sigsetjmp(old_env, 0)) {
        swapcontext(&old_uc, &uc);
    }
    return &co->base;
}

#ifdef CONFIG_VALGRIND_H
#ifdef CONFIG_PRAGMA_DIAGNOSTIC_AVAILABLE
/* Work around an unused variable in the valgrind.h macro... */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
static inline void valgrind_stack_deregister(CoroutineUContext *co)
{
    VALGRIND_STACK_DEREGISTER(co->valgrind_stack_id);
}
#ifdef CONFIG_PRAGMA_DIAGNOSTIC_AVAILABLE
#pragma GCC diagnostic pop
#endif
#endif

void qemu_coroutine_delete(Coroutine *co_)
{
    CoroutineUContext *co = DO_UPCAST(CoroutineUContext, base, co_);

#ifdef CONFIG_VALGRIND_H
    valgrind_stack_deregister(co);
#endif

    munmap(co->stack, MAX_STACK_SIZE);
    g_free(co);
}

CoroutineAction qemu_coroutine_switch(Coroutine *from_, Coroutine *to_,
                                      CoroutineAction action)
{
    CoroutineUContext *from = DO_UPCAST(CoroutineUContext, base, from_);
    CoroutineUContext *to = DO_UPCAST(CoroutineUContext, base, to_);
    int ret;

    ret = sigsetjmp(from->env, 0);
    if (ret == 0) {
        siglongjmp(to->env, action);
    }
    coroutine_get_thread_state()->current = from_;

    return ret;
}

Coroutine *qemu_coroutine_self(void)
{
    CoroutineThreadState *s = coroutine_get_thread_state();

    return s->current;
}

bool qemu_in_coroutine(void)
{
    CoroutineThreadState *s = pthread_getspecific(thread_state_key);

    return s && s->current->caller;
}
