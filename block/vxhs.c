/*
 * QEMU Block driver for Veritas HyperScale (VxHS)
 *
 * Copyright (c) 2017 Veritas Technologies LLC.
 *
 * This work is licensed under the terms of the GNU GPL, version 2 or later.
 * See the COPYING file in the top-level directory.
 *
 */

#include "qemu/osdep.h"
#include "block/vxhs_shim.h"
#include <gmodule.h>
#include <sys/param.h>
#include "block/block_int.h"
#include "qapi/qmp/qerror.h"
#include "qapi/qmp/qdict.h"
#include "qapi/qmp/qstring.h"
#include "trace.h"
#include "qemu/uri.h"
#include "qapi/error.h"
#include "qemu/uuid.h"
#include "crypto/tlscredsx509.h"

#define VXHS_OPT_FILENAME           "filename"
#define VXHS_OPT_VDISK_ID           "vdisk-id"
#define VXHS_OPT_SERVER             "server"
#define VXHS_OPT_HOST               "host"
#define VXHS_OPT_PORT               "port"

/* Only accessed under QEMU global mutex */
static uint32_t vxhs_ref;

typedef enum {
    VDISK_AIO_READ,
    VDISK_AIO_WRITE,
} VDISKAIOCmd;

/*
 * HyperScale AIO callbacks structure
 */
typedef struct VXHSAIOCB {
    BlockAIOCB common;
    int err;
} VXHSAIOCB;

typedef struct VXHSvDiskHostsInfo {
    void *dev_handle; /* Device handle */
    char *host; /* Host name or IP */
    int port; /* Host's port number */
} VXHSvDiskHostsInfo;

/*
 * Structure per vDisk maintained for state
 */
typedef struct BDRVVXHSState {
    VXHSvDiskHostsInfo vdisk_hostinfo; /* Per host info */
    char *vdisk_guid;
    char *tlscredsid; /* tlscredsid */
} BDRVVXHSState;

#define LIBVXHS_FULL_PATHNAME "/usr/lib64/qemu/libvxhs.so.1"
static bool libvxhs_loaded;
static GModule *libvxhs_handle;

static LibVXHSFuncs libvxhs;

typedef struct LibVXHSSymbols {
    const char *name;
    gpointer *addr;
} LibVXHSSymbols;

static LibVXHSSymbols libvxhs_symbols[] = {
    {"iio_init",        (gpointer *) &libvxhs.iio_init},
    {"iio_fini",        (gpointer *) &libvxhs.iio_fini},
    {"iio_min_version", (gpointer *) &libvxhs.iio_min_version},
    {"iio_max_version", (gpointer *) &libvxhs.iio_max_version},
    {"iio_open",        (gpointer *) &libvxhs.iio_open},
    {"iio_close",       (gpointer *) &libvxhs.iio_close},
    {"iio_writev",      (gpointer *) &libvxhs.iio_writev},
    {"iio_readv",       (gpointer *) &libvxhs.iio_readv},
    {"iio_ioctl",       (gpointer *) &libvxhs.iio_ioctl},
    {NULL}
};

static void bdrv_vxhs_set_funcs(GModule *handle, Error **errp)
{
    int i = 0;
    while (libvxhs_symbols[i].name) {
        const char *name = libvxhs_symbols[i].name;
        if (!g_module_symbol(handle, name, libvxhs_symbols[i].addr)) {
            error_setg(errp, "%s could not be loaded from libvxhs: %s",
                       name, g_module_error());
            return;
        }
        ++i;
    }
}

static void bdrv_vxhs_load_libs(Error **errp)
{
    Error *local_err = NULL;
    int32_t ver;

    if (libvxhs_loaded) {
        return;
    }

    if (!g_module_supported()) {
        error_setg(errp, "modules are not supported on this platform: %s",
                     g_module_error());
        return;
    }

    libvxhs_handle = g_module_open(LIBVXHS_FULL_PATHNAME,
                                   G_MODULE_BIND_LAZY | G_MODULE_BIND_LOCAL);
    if (!libvxhs_handle) {
        error_setg(errp, "error loading libvxhs: %s", g_module_error());
        return;
    }

    g_module_make_resident(libvxhs_handle);

    bdrv_vxhs_set_funcs(libvxhs_handle, &local_err);
    if (local_err) {
        error_propagate(errp, local_err);
        return;
    }

    /* Now check to see if the libvxhs we are using here is supported
     * by the loaded version */

    ver = (*libvxhs.iio_min_version)();
    if (ver > QNIO_VERSION) {
        error_setg(errp, "Trying to use libvxhs version %"PRId32" API, but "
                         "only %"PRId32" or newer is supported by %s",
                          QNIO_VERSION, ver, LIBVXHS_FULL_PATHNAME);
        return;
    }

    ver = (*libvxhs.iio_max_version)();
    if (ver < QNIO_VERSION) {
        error_setg(errp, "Trying to use libvxhs version %"PRId32" API, but "
                         "only %"PRId32" or earlier is supported by %s",
                          QNIO_VERSION, ver, LIBVXHS_FULL_PATHNAME);
        return;
    }

    libvxhs_loaded = true;
}

static void vxhs_complete_aio_bh(void *opaque)
{
    VXHSAIOCB *acb = opaque;
    BlockCompletionFunc *cb = acb->common.cb;
    void *cb_opaque = acb->common.opaque;
    int ret = 0;

    if (acb->err != 0) {
        trace_vxhs_complete_aio(acb, acb->err);
        ret = (-EIO);
    }

    qemu_aio_unref(acb);
    cb(cb_opaque, ret);
}

/*
 * Called from a libqnio thread
 */
static void vxhs_iio_callback(void *ctx, uint32_t opcode, uint32_t error)
{
    VXHSAIOCB *acb = NULL;

    switch (opcode) {
    case IRP_READ_REQUEST:
    case IRP_WRITE_REQUEST:

        /*
         * ctx is VXHSAIOCB*
         * ctx is NULL if error is QNIOERROR_CHANNEL_HUP
         */
        if (ctx) {
            acb = ctx;
        } else {
            trace_vxhs_iio_callback(error);
            goto out;
        }

        if (error) {
            if (!acb->err) {
                acb->err = error;
            }
            trace_vxhs_iio_callback(error);
        }

        aio_bh_schedule_oneshot(bdrv_get_aio_context(acb->common.bs),
                                vxhs_complete_aio_bh, acb);
        break;

    default:
        if (error == QNIOERROR_HUP) {
            /*
             * Channel failed, spontaneous notification,
             * not in response to I/O
             */
            trace_vxhs_iio_callback_chnfail(error, errno);
        } else {
            trace_vxhs_iio_callback_unknwn(opcode, error);
        }
        break;
    }
out:
    return;
}

static QemuOptsList runtime_opts = {
    .name = "vxhs",
    .head = QTAILQ_HEAD_INITIALIZER(runtime_opts.head),
    .desc = {
        {
            .name = VXHS_OPT_FILENAME,
            .type = QEMU_OPT_STRING,
            .help = "URI to the Veritas HyperScale image",
        },
        {
            .name = VXHS_OPT_VDISK_ID,
            .type = QEMU_OPT_STRING,
            .help = "UUID of the VxHS vdisk",
        },
        {
            .name = "tls-creds",
            .type = QEMU_OPT_STRING,
            .help = "ID of the TLS/SSL credentials to use",
        },
        { /* end of list */ }
    },
};

static QemuOptsList runtime_tcp_opts = {
    .name = "vxhs_tcp",
    .head = QTAILQ_HEAD_INITIALIZER(runtime_tcp_opts.head),
    .desc = {
        {
            .name = VXHS_OPT_HOST,
            .type = QEMU_OPT_STRING,
            .help = "host address (ipv4 addresses)",
        },
        {
            .name = VXHS_OPT_PORT,
            .type = QEMU_OPT_NUMBER,
            .help = "port number on which VxHSD is listening (default 9999)",
            .def_value_str = "9999"
        },
        { /* end of list */ }
    },
};

/*
 * Parse incoming URI and populate *options with the host
 * and device information
 */
static int vxhs_parse_uri(const char *filename, QDict *options)
{
    URI *uri = NULL;
    char *port;
    int ret = 0;

    trace_vxhs_parse_uri_filename(filename);
    uri = uri_parse(filename);
    if (!uri || !uri->server || !uri->path) {
        uri_free(uri);
        return -EINVAL;
    }

    qdict_put_str(options, VXHS_OPT_SERVER ".host", uri->server);

    if (uri->port) {
        port = g_strdup_printf("%d", uri->port);
        qdict_put_str(options, VXHS_OPT_SERVER ".port", port);
        g_free(port);
    }

    qdict_put_str(options, "vdisk-id", uri->path);

    trace_vxhs_parse_uri_hostinfo(uri->server, uri->port);
    uri_free(uri);

    return ret;
}

static void vxhs_parse_filename(const char *filename, QDict *options,
                                Error **errp)
{
    if (qdict_haskey(options, "vdisk-id") || qdict_haskey(options, "server")) {
        error_setg(errp, "vdisk-id/server and a file name may not be specified "
                         "at the same time");
        return;
    }

    if (strstr(filename, "://")) {
        int ret = vxhs_parse_uri(filename, options);
        if (ret < 0) {
            error_setg(errp, "Invalid URI. URI should be of the form "
                       "  vxhs://<host_ip>:<port>/<vdisk-id>");
        }
    }
}

static int vxhs_init_and_ref(void)
{
    if (vxhs_ref++ == 0) {
        if ((*libvxhs.iio_init)(QNIO_VERSION, vxhs_iio_callback)) {
            return -ENODEV;
        }
    }
    return 0;
}

static void vxhs_unref(void)
{
    if (--vxhs_ref == 0) {
        (*libvxhs.iio_fini)();
    }
}

static void vxhs_get_tls_creds(const char *id, char **cacert,
                               char **key, char **cert, Error **errp)
{
    Object *obj;
    QCryptoTLSCreds *creds;
    QCryptoTLSCredsX509 *creds_x509;

    obj = object_resolve_path_component(
        object_get_objects_root(), id);

    if (!obj) {
        error_setg(errp, "No TLS credentials with id '%s'",
                   id);
        return;
    }

    creds_x509 = (QCryptoTLSCredsX509 *)
        object_dynamic_cast(obj, TYPE_QCRYPTO_TLS_CREDS_X509);

    if (!creds_x509) {
        error_setg(errp, "Object with id '%s' is not TLS credentials",
                   id);
        return;
    }

    creds = &creds_x509->parent_obj;

    if (creds->endpoint != QCRYPTO_TLS_CREDS_ENDPOINT_CLIENT) {
        error_setg(errp,
                   "Expecting TLS credentials with a client endpoint");
        return;
    }

    /*
     * Get the cacert, client_cert and client_key file names.
     */
    if (!creds->dir) {
        error_setg(errp, "TLS object missing 'dir' property value");
        return;
    }

    *cacert = g_strdup_printf("%s/%s", creds->dir,
                              QCRYPTO_TLS_CREDS_X509_CA_CERT);
    *cert = g_strdup_printf("%s/%s", creds->dir,
                            QCRYPTO_TLS_CREDS_X509_CLIENT_CERT);
    *key = g_strdup_printf("%s/%s", creds->dir,
                           QCRYPTO_TLS_CREDS_X509_CLIENT_KEY);
}

static int vxhs_open(BlockDriverState *bs, QDict *options,
                     int bdrv_flags, Error **errp)
{
    BDRVVXHSState *s = bs->opaque;
    void *dev_handlep;
    QDict *backing_options = NULL;
    QemuOpts *opts = NULL;
    QemuOpts *tcp_opts = NULL;
    char *of_vsa_addr = NULL;
    Error *local_err = NULL;
    const char *vdisk_id_opt;
    const char *server_host_opt;
    int ret = 0;
    char *cacert = NULL;
    char *client_key = NULL;
    char *client_cert = NULL;

    bdrv_vxhs_load_libs(&local_err);
    if (local_err) {
        error_propagate(errp, local_err);
        /* on error, cannot cleanup because the iio_fini() function
         * is not loaded */
        return -EINVAL;
    }

    ret = vxhs_init_and_ref();
    if (ret < 0) {
        error_setg(&local_err, "libvxhs iio_init() failed");
        ret = -EINVAL;
        goto out;
    }

    /* Create opts info from runtime_opts and runtime_tcp_opts list */
    opts = qemu_opts_create(&runtime_opts, NULL, 0, &error_abort);
    tcp_opts = qemu_opts_create(&runtime_tcp_opts, NULL, 0, &error_abort);

    qemu_opts_absorb_qdict(opts, options, &local_err);
    if (local_err) {
        ret = -EINVAL;
        goto out;
    }

    /* vdisk-id is the disk UUID */
    vdisk_id_opt = qemu_opt_get(opts, VXHS_OPT_VDISK_ID);
    if (!vdisk_id_opt) {
        error_setg(&local_err, QERR_MISSING_PARAMETER, VXHS_OPT_VDISK_ID);
        ret = -EINVAL;
        goto out;
    }

    /* vdisk-id may contain a leading '/' */
    if (strlen(vdisk_id_opt) > UUID_FMT_LEN + 1) {
        error_setg(&local_err, "vdisk-id cannot be more than %d characters",
                   UUID_FMT_LEN);
        ret = -EINVAL;
        goto out;
    }

    s->vdisk_guid = g_strdup(vdisk_id_opt);
    trace_vxhs_open_vdiskid(vdisk_id_opt);

    /* get the 'server.' arguments */
    qdict_extract_subqdict(options, &backing_options, VXHS_OPT_SERVER".");

    qemu_opts_absorb_qdict(tcp_opts, backing_options, &local_err);
    if (local_err != NULL) {
        ret = -EINVAL;
        goto out;
    }

    server_host_opt = qemu_opt_get(tcp_opts, VXHS_OPT_HOST);
    if (!server_host_opt) {
        error_setg(&local_err, QERR_MISSING_PARAMETER,
                   VXHS_OPT_SERVER"."VXHS_OPT_HOST);
        ret = -EINVAL;
        goto out;
    }

    if (strlen(server_host_opt) > MAXHOSTNAMELEN) {
        error_setg(&local_err, "server.host cannot be more than %d characters",
                   MAXHOSTNAMELEN);
        ret = -EINVAL;
        goto out;
    }

    /* check if we got tls-creds via the --object argument */
    s->tlscredsid = g_strdup(qemu_opt_get(opts, "tls-creds"));
    if (s->tlscredsid) {
        vxhs_get_tls_creds(s->tlscredsid, &cacert, &client_key,
                           &client_cert, &local_err);
        if (local_err != NULL) {
            ret = -EINVAL;
            goto out;
        }
        trace_vxhs_get_creds(cacert, client_key, client_cert);
    }

    s->vdisk_hostinfo.host = g_strdup(server_host_opt);
    s->vdisk_hostinfo.port = g_ascii_strtoll(qemu_opt_get(tcp_opts,
                                                          VXHS_OPT_PORT),
                                                          NULL, 0);

    trace_vxhs_open_hostinfo(s->vdisk_hostinfo.host,
                             s->vdisk_hostinfo.port);

    of_vsa_addr = g_strdup_printf("of://%s:%d",
                                  s->vdisk_hostinfo.host,
                                  s->vdisk_hostinfo.port);

    /*
     * Open qnio channel to storage agent if not opened before
     */
    dev_handlep = (*libvxhs.iio_open)(of_vsa_addr, s->vdisk_guid, 0,
                                      cacert, client_key, client_cert);
    if (dev_handlep == NULL) {
        trace_vxhs_open_iio_open(of_vsa_addr);
        ret = -ENODEV;
        goto out;
    }
    s->vdisk_hostinfo.dev_handle = dev_handlep;

out:
    g_free(of_vsa_addr);
    QDECREF(backing_options);
    qemu_opts_del(tcp_opts);
    qemu_opts_del(opts);
    g_free(cacert);
    g_free(client_key);
    g_free(client_cert);

    if (ret < 0) {
        vxhs_unref();
        error_propagate(errp, local_err);
        g_free(s->vdisk_hostinfo.host);
        g_free(s->vdisk_guid);
        g_free(s->tlscredsid);
        s->vdisk_guid = NULL;
    }

    return ret;
}

static const AIOCBInfo vxhs_aiocb_info = {
    .aiocb_size = sizeof(VXHSAIOCB)
};

/*
 * This allocates QEMU-VXHS callback for each IO
 * and is passed to QNIO. When QNIO completes the work,
 * it will be passed back through the callback.
 */
static BlockAIOCB *vxhs_aio_rw(BlockDriverState *bs, int64_t sector_num,
                               QEMUIOVector *qiov, int nb_sectors,
                               BlockCompletionFunc *cb, void *opaque,
                               VDISKAIOCmd iodir)
{
    VXHSAIOCB *acb = NULL;
    BDRVVXHSState *s = bs->opaque;
    size_t size;
    uint64_t offset;
    int iio_flags = 0;
    int ret = 0;
    void *dev_handle = s->vdisk_hostinfo.dev_handle;

    offset = sector_num * BDRV_SECTOR_SIZE;
    size = nb_sectors * BDRV_SECTOR_SIZE;
    acb = qemu_aio_get(&vxhs_aiocb_info, bs, cb, opaque);

    /*
     * Initialize VXHSAIOCB.
     */
    acb->err = 0;

    iio_flags = IIO_FLAG_ASYNC;

    switch (iodir) {
    case VDISK_AIO_WRITE:
            ret = (*libvxhs.iio_writev)(dev_handle, acb, qiov->iov, qiov->niov,
                                        offset, (uint64_t)size, iio_flags);
            break;
    case VDISK_AIO_READ:
            ret = (*libvxhs.iio_readv)(dev_handle, acb, qiov->iov, qiov->niov,
                                       offset, (uint64_t)size, iio_flags);
            break;
    default:
            trace_vxhs_aio_rw_invalid(iodir);
            goto errout;
    }

    if (ret != 0) {
        trace_vxhs_aio_rw_ioerr(s->vdisk_guid, iodir, size, offset,
                                acb, ret, errno);
        goto errout;
    }
    return &acb->common;

errout:
    qemu_aio_unref(acb);
    return NULL;
}

static BlockAIOCB *vxhs_aio_readv(BlockDriverState *bs,
                                   int64_t sector_num, QEMUIOVector *qiov,
                                   int nb_sectors,
                                   BlockCompletionFunc *cb, void *opaque)
{
    return vxhs_aio_rw(bs, sector_num, qiov, nb_sectors, cb,
                       opaque, VDISK_AIO_READ);
}

static BlockAIOCB *vxhs_aio_writev(BlockDriverState *bs,
                                   int64_t sector_num, QEMUIOVector *qiov,
                                   int nb_sectors,
                                   BlockCompletionFunc *cb, void *opaque)
{
    return vxhs_aio_rw(bs, sector_num, qiov, nb_sectors,
                       cb, opaque, VDISK_AIO_WRITE);
}

static void vxhs_close(BlockDriverState *bs)
{
    BDRVVXHSState *s = bs->opaque;

    trace_vxhs_close(s->vdisk_guid);

    g_free(s->vdisk_guid);
    s->vdisk_guid = NULL;

    /*
     * Close vDisk device
     */
    if (s->vdisk_hostinfo.dev_handle) {
        (*libvxhs.iio_close)(s->vdisk_hostinfo.dev_handle);
        s->vdisk_hostinfo.dev_handle = NULL;
    }

    vxhs_unref();

    /*
     * Free the dynamically allocated host string etc
     */
    g_free(s->vdisk_hostinfo.host);
    g_free(s->tlscredsid);
    s->tlscredsid = NULL;
    s->vdisk_hostinfo.host = NULL;
    s->vdisk_hostinfo.port = 0;
}

static int64_t vxhs_get_vdisk_stat(BDRVVXHSState *s)
{
    int64_t vdisk_size = -1;
    int ret = 0;
    void *dev_handle = s->vdisk_hostinfo.dev_handle;

    ret = (*libvxhs.iio_ioctl)(dev_handle, IOR_VDISK_STAT, &vdisk_size, 0);
    if (ret < 0) {
        trace_vxhs_get_vdisk_stat_err(s->vdisk_guid, ret, errno);
        return -EIO;
    }

    trace_vxhs_get_vdisk_stat(s->vdisk_guid, vdisk_size);
    return vdisk_size;
}

/*
 * Returns the size of vDisk in bytes. This is required
 * by QEMU block upper block layer so that it is visible
 * to guest.
 */
static int64_t vxhs_getlength(BlockDriverState *bs)
{
    BDRVVXHSState *s = bs->opaque;
    int64_t vdisk_size;

    vdisk_size = vxhs_get_vdisk_stat(s);
    if (vdisk_size < 0) {
        return -EIO;
    }

    return vdisk_size;
}

static BlockDriver bdrv_vxhs = {
    .format_name                  = "vxhs",
    .protocol_name                = "vxhs",
    .instance_size                = sizeof(BDRVVXHSState),
    .bdrv_file_open               = vxhs_open,
    .bdrv_parse_filename          = vxhs_parse_filename,
    .bdrv_close                   = vxhs_close,
    .bdrv_getlength               = vxhs_getlength,
    .bdrv_aio_readv               = vxhs_aio_readv,
    .bdrv_aio_writev              = vxhs_aio_writev,
};

static void bdrv_vxhs_init(void)
{
    bdrv_register(&bdrv_vxhs);
}

block_init(bdrv_vxhs_init);
