/*
 ****************************************************************************
 * (C) 2006 - Cambridge University
 ****************************************************************************
 *
 *        File: xenbus.c
 *      Author: Steven Smith (sos22@cam.ac.uk)
 *     Changes: Grzegorz Milos (gm281@cam.ac.uk)
 *     Changes: John D. Ramsdell
 *
 *        Date: Jun 2006, chages Aug 2005
 *
 * Environment: Xen FreeRTOS
 * Description: Minimal implementation of xenbus
 *
 ****************************************************************************
 **/
#include <inttypes.h>
#include <os.h>
#include <lib.h>
#include <xenbus.h>
#include <events.h>
#include <xen/io/xs_wire.h>
#include <xen/hvm/params.h>
#include <spinlock.h>
#include <xmalloc.h>
#include <semaphore.h>
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"
#include <export.h>

#define min(x,y) ({                       \
    typeof(x) tmpx = (x);                 \
    typeof(y) tmpy = (y);                 \
    tmpx < tmpy ? tmpx : tmpy;            \
    })

#ifdef XENBUS_DEBUG
#define DEBUG(_f, _a...) \
    printk("XEN_FREERTOS(file=xenbus.c, line=%d) " _f , __LINE__, ## _a)
#else
#define DEBUG(_f, _a...)    ((void)0)
#endif

QueueHandle_t xb_WaitQueue;
QueueHandle_t xb_WatchQueue;
struct xenstore_domain_interface *xenstore_buf;
EXPORT_SYMBOL(xenstore_buf);
static __DECLARE_SEMAPHORE_GENERIC(xb_write_sem, 1);

xenbus_event_queue xenbus_events;
static struct watch {
    char *token;
    char *path;
    xenbus_event_queue *events;
    struct watch *next;
} *watches;

struct xenbus_req_info
{
    int in_use:1;
    QueueHandle_t waitq;
    void *reply;
};

#define NR_REQS 32
static struct xenbus_req_info req_info[NR_REQS];

static char *errmsg(struct xsd_sockmsg *rep);

uint32_t xenbus_evtchn;
EXPORT_SYMBOL(xenbus_evtchn);

/* FIXME: Taken from sched.c. */
#define RUNNABLE_FLAG   0x00000001
#define set_runnable(_thread)   (_thread->flags |= RUNNABLE_FLAG)

void wake(struct thread *thread)
{
    thread->wakeup_time = 0LL;
    set_runnable(thread);
}

void schedule(void)
{
}

// Small changes in get_xenbus.
#ifdef CONFIG_PARAVIRT
void get_xenbus(void *p)
{
    start_info_t *si = p;

    xenbus_evtchn = si->store_evtchn;
    //xenstore_buf = mfn_to_virt(si->store_mfn);
    xenstore_buf = (struct xenstore_domain_interface *)((uint32_t)(si->store_mfn) << 12);
}
#else
void get_xenbus(void *p)
{
    uint64_t v;

    if ( hvm_get_parameter(HVM_PARAM_STORE_EVTCHN, &v) )
        BUG();
    xenbus_evtchn = v;

    if( hvm_get_parameter(HVM_PARAM_STORE_PFN, &v) )
        BUG();
    //xenstore_buf = (struct xenstore_domain_interface *)map_frame_virt(v);
    xenstore_buf = (struct xenstore_domain_interface *)(v<<12);
}
#endif

static void memcpy_from_ring(const void *Ring, void *Dest, int off, int len)
{
    int c1, c2;
    const char *ring = Ring;
    char *dest = Dest;

    c1 = min(len, XENSTORE_RING_SIZE - off);
    c2 = len - c1;
    memcpy(dest, ring + off, c1);
    memcpy(dest + c1, ring, c2);
}

char **xenbus_wait_for_watch_return(xenbus_event_queue *queue)
{
    struct xenbus_event *event;
    if ( !queue )
        queue = &xenbus_events;
    while ( !(event = *queue) )
    {
        uint32_t ulReceivedValue;
        xQueueReceive( xb_WatchQueue, &ulReceivedValue, portMAX_DELAY );
    }
    *queue = event->next;

    return &event->path;

}
EXPORT_SYMBOL(xenbus_wait_for_watch_return);

void xenbus_wait_for_watch(xenbus_event_queue *queue)
{
    char **ret;

    if ( !queue )
        queue = &xenbus_events;
    ret = xenbus_wait_for_watch_return(queue);
    if ( ret )
        free(ret);
#if 0
    else
        printk("unexpected path returned by watch\n");
#endif
}
EXPORT_SYMBOL(xenbus_wait_for_watch);

void xenbus_release_wait_for_watch(xenbus_event_queue *queue)
{
}
EXPORT_SYMBOL(xenbus_release_wait_for_watch);

char *xenbus_wait_for_value(const char *path, const char *value,
                            xenbus_event_queue *queue)
{
    if ( !queue )
        queue = &xenbus_events;

    for( ;; )
    {
        char *res, *msg;
        int r;

        msg = xenbus_read(XBT_NIL, path, &res);
        if ( msg )
            return msg;

        r = strcmp(value,res);
        free(res);

        if ( r==0 )
            return NULL;

        xenbus_wait_for_watch(queue);
    }
}
EXPORT_SYMBOL(xenbus_wait_for_value);

char *xenbus_switch_state(xenbus_transaction_t xbt, const char *path,
                          XenbusState state)
{
    char *current_state;
    char *msg = NULL;
    char *msg2 = NULL;
    char value[2];
    XenbusState rs;
    int xbt_flag = 0;
    int retry = 0;

    do {
        if ( xbt == XBT_NIL )
        {
            msg = xenbus_transaction_start(&xbt);
            if ( msg )
                goto exit;
            xbt_flag = 1;
        }

        msg = xenbus_read(xbt, path, &current_state);
        if ( msg )
            goto exit;

        rs = (XenbusState) (current_state[0] - '0');
        free(current_state);
        if ( rs == state )
        {
            msg = NULL;
            goto exit;
        }

        snprintf(value, 2, "%d", state);
        msg = xenbus_write(xbt, path, value);

exit:
        if ( xbt_flag )
        {
            msg2 = xenbus_transaction_end(xbt, 0, &retry);
            xbt = XBT_NIL;
        }
        if ( msg == NULL && msg2 != NULL )
            msg = msg2;
        else
            free(msg2);
    } while ( retry );

    return msg;
}
EXPORT_SYMBOL(xenbus_switch_state);

char *xenbus_wait_for_state_change(const char *path, XenbusState *state,
                                   xenbus_event_queue *queue)
{
    if ( !queue )
        queue = &xenbus_events;

    for( ;; )
    {
        char *res, *msg;
        XenbusState rs;

        msg = xenbus_read(XBT_NIL, path, &res);
        if ( msg )
            return msg;

        rs = (XenbusState)(res[0] - 48);
        free(res);

        if ( rs == *state )
            xenbus_wait_for_watch(queue);
        else
        {
            *state = rs;
            break;
        }
    }
    return NULL;
}
EXPORT_SYMBOL(xenbus_wait_for_state_change);

static void xenbus_read_data(char *buf, unsigned int len)
{
    unsigned int off = 0;
    unsigned int prod, cons;
    unsigned int size;
    uint32_t ulReceivedValue;

    while ( off != len )
    {
        if (xenstore_buf->rsp_prod == xenstore_buf->rsp_cons) {
            xQueueReceive( xb_WaitQueue, &ulReceivedValue, portMAX_DELAY );
        }
        prod = xenstore_buf->rsp_prod;
        cons = xenstore_buf->rsp_cons;
        size = min(len - off, prod - cons);
        rmb();   /* Make sure data read from ring is ordered with rsp_prod. */
        memcpy_from_ring(xenstore_buf->rsp, buf + off,
                         MASK_XENSTORE_IDX(cons), size);
        off += size;
        mb();    /* memcpy() and rsp_cons update must not be reordered. */
        xenstore_buf->rsp_cons += size;
        mb();    /* rsp_cons must be visible before we look at rsp_prod. */
    }
}

static void xenbus_evtchn_handler(evtchn_port_t port, struct pt_regs *regs,
                                  void *ign)
{
    const uint32_t ulValueToSend = 0;
    xQueueSend( xb_WaitQueue, &ulValueToSend, 0U);
}

static int nr_live_reqs;
static DEFINE_SPINLOCK(req_lock);
static DECLARE_WAIT_QUEUE_HEAD(req_wq);

/* Release a xenbus identifier */
static void release_xenbus_id(int id)
{
    BUG_ON(!req_info[id].in_use);

    spin_lock(&req_lock);

    req_info[id].in_use = 0;
    nr_live_reqs--;
    req_info[id].in_use = 0;
    if ( nr_live_reqs == 0 || nr_live_reqs == NR_REQS - 1 )
        wake_up(&req_wq);

    spin_unlock(&req_lock);
}

/* Allocate an identifier for a xenbus request.  Blocks if none are
   available. */
static int allocate_xenbus_id(void)
{
    static int probe;
    int o_probe;

    while ( 1 )
    {
        spin_lock(&req_lock);
        if ( nr_live_reqs < NR_REQS )
            break;
        spin_unlock(&req_lock);
        wait_event(req_wq, nr_live_reqs < NR_REQS);
    }

    o_probe = probe;
    while ( req_info[o_probe].in_use )
    {
        o_probe = (o_probe + 1) % NR_REQS;
        BUG_ON(o_probe == probe);
    }
    nr_live_reqs++;
    req_info[o_probe].in_use = 1;
    probe = (o_probe + 1) % NR_REQS;

    spin_unlock(&req_lock);

    req_info[o_probe].waitq = xQueueCreate( 5, sizeof( uint32_t ) );

    return o_probe;
}

/* Initialise xenbus. */
void init_xenbus(void)
{
    int err;
    err = bind_evtchn(xenbus_evtchn, xenbus_evtchn_handler, NULL);
    unmask_evtchn(xenbus_evtchn);
    xb_WaitQueue = xQueueCreate( 5, sizeof( uint32_t ) );
    xb_WatchQueue = xQueueCreate( 5, sizeof( uint32_t ) );
}

void fini_xenbus(void)
{
}

void suspend_xenbus(void)
{
    /* Check for live requests and wait until they finish */
    while ( 1 )
    {
        spin_lock(&req_lock);
        if ( nr_live_reqs == 0 )
            break;
        spin_unlock(&req_lock);
        wait_event(req_wq, nr_live_reqs == 0);
    }

    mask_evtchn(xenbus_evtchn);
    xenstore_buf = NULL;
    spin_unlock(&req_lock);
}

#if 0

void resume_xenbus(int canceled)
{
    char *msg;
    struct watch *watch;
    struct write_req req[2];
    struct xsd_sockmsg *rep;

#ifdef CONFIG_PARAVIRT
    get_xenbus(&start_info);
#else
    get_xenbus(0);
#endif
    unmask_evtchn(xenbus_evtchn);

    if ( !canceled )
    {
        for ( watch = watches; watch; watch = watch->next )
        {
            req[0].data = watch->path;
            req[0].len = strlen(watch->path) + 1;
            req[1].data = watch->token;
            req[1].len = strlen(watch->token) + 1;

            rep = xenbus_msg_reply(XS_WATCH, XBT_NIL, req, ARRAY_SIZE(req));
            msg = errmsg(rep);
            if ( msg )
            {
                xprintk("error on XS_WATCH: %s\n", msg);
                free(msg);
            }
            else
                free(rep);
        }
    }

    notify_remote_via_evtchn(xenbus_evtchn);
}

#endif

/*
 * Send data to xenbus.  This can block.  All of the requests are seen
 * by xenbus as if sent atomically.  The header is added
 * automatically, using type %type, req_id %req_id, and trans_id
 * %trans_id.
 */
static void xb_write(int type, int req_id, xenbus_transaction_t trans_id,
                     const struct write_req *req, int nr_reqs)
{
    XENSTORE_RING_IDX prod;
    int r;
    int len = 0;
    const struct write_req *cur_req;
    int req_off;
    int total_off;
    int this_chunk;
    struct xsd_sockmsg m = {.type = type, .req_id = req_id, .tx_id = trans_id };
    struct write_req header_req = { &m, sizeof(m) };

    for ( r = 0; r < nr_reqs; r++ )
        len += req[r].len;

    m.len = len;
    len += sizeof(m);

    cur_req = &header_req;

    BUG_ON(len > XENSTORE_PAYLOAD_MAX);

    /* Make sure we are the only thread trying to write. */
    down(&xb_write_sem);

    /* Send the message in chunks using free ring space when available. */
    total_off = 0;
    req_off = 0;
    while ( total_off < len )
    {
        prod = xenstore_buf->req_prod;
        if ( prod - xenstore_buf->req_cons >= XENSTORE_RING_SIZE )
        {
            /* Send evtchn to notify remote */
            notify_remote_via_evtchn(xenbus_evtchn);

            /* Wait for there to be space on the ring */
            DEBUG("prod %d, len %d, cons %d, size %d; waiting.\n", prod,
                  len - total_off, xenstore_buf->req_cons, XENSTORE_RING_SIZE);
            if (prod - xenstore_buf->req_cons >= XENSTORE_RING_SIZE) {
                uint32_t ulReceivedValue;
                xQueueReceive( xb_WaitQueue, &ulReceivedValue, portMAX_DELAY );
            }
            DEBUG("Back from wait.\n");
        }

        this_chunk = min(cur_req->len - req_off,
                         XENSTORE_RING_SIZE - MASK_XENSTORE_IDX(prod));
        this_chunk = min(this_chunk,
                         xenstore_buf->req_cons + XENSTORE_RING_SIZE - prod);
        memcpy((char *)xenstore_buf->req + MASK_XENSTORE_IDX(prod),
               (char *)cur_req->data + req_off, this_chunk);
        prod += this_chunk;
        req_off += this_chunk;
        total_off += this_chunk;
        if ( req_off == cur_req->len )
        {
            req_off = 0;
            if ( cur_req == &header_req )
                cur_req = req;
            else
                cur_req++;
        }

        /* Remote must see entire message before updating indexes */
        wmb();
        xenstore_buf->req_prod = prod;
    }

    /* Send evtchn to notify remote */
    notify_remote_via_evtchn(xenbus_evtchn);

    DEBUG("Complete main loop of xb_write.\n");
    BUG_ON(req_off != 0);
    BUG_ON(total_off != len);

    up(&xb_write_sem);
}

/*
 * Send a mesasge to xenbus, in the same fashion as xb_write, and
 * block waiting for a reply.  The reply is malloced and should be
 * freed by the caller.
 */
struct xsd_sockmsg *xenbus_msg_reply(int type, xenbus_transaction_t trans,
                                     struct write_req *io, int nr_reqs)
{
    int id;
    DEFINE_WAIT(w);
    struct xsd_sockmsg *rep;
    uint32_t ulReceivedValue=0;

    id = allocate_xenbus_id();
    xb_write(type, id, trans, io, nr_reqs);
    xQueueReceive( req_info[id].waitq, &ulReceivedValue, portMAX_DELAY );
    rep = req_info[id].reply;
    BUG_ON(rep->req_id != id);
    release_xenbus_id(id);

    return rep;
}
EXPORT_SYMBOL(xenbus_msg_reply);

static char *errmsg(struct xsd_sockmsg *rep)
{
    char *res;

    if ( !rep )
    {
        char msg[] = "No reply";
        size_t len = strlen(msg) + 1;
        return memcpy(malloc(len), msg, len);
    }
    if ( rep->type != XS_ERROR )
        return NULL;

    res = malloc(rep->len + 1);
    memcpy(res, rep + 1, rep->len);
    res[rep->len] = 0;
    free(rep);

    return res;
}

/*
 * List the contents of a directory.  Returns a malloc()ed array of
 * pointers to malloc()ed strings.  The array is NULL terminated.  May
 * block.
 */
char *xenbus_ls(xenbus_transaction_t xbt, const char *pre, char ***contents)
{
    struct xsd_sockmsg *reply, *repmsg;
    struct write_req req[] = { { pre, strlen(pre)+1 } };
    int nr_elems, x, i;
    char **res, *msg;

    repmsg = xenbus_msg_reply(XS_DIRECTORY, xbt, req, ARRAY_SIZE(req));
    msg = errmsg(repmsg);
    if ( msg )
    {
        *contents = NULL;
        return msg;
    }

    reply = repmsg + 1;
    for ( x = nr_elems = 0; x < repmsg->len; x++ )
        nr_elems += (((char *)reply)[x] == 0);

    res = malloc(sizeof(res[0]) * (nr_elems + 1));
    for ( x = i = 0; i < nr_elems; i++ )
    {
        int l = strlen((char *)reply + x);

        res[i] = malloc(l + 1);
        memcpy(res[i], (char *)reply + x, l + 1);
        x += l + 1;
    }

    res[i] = NULL;
    free(repmsg);
    *contents = res;

    return NULL;
}
EXPORT_SYMBOL(xenbus_ls);

char *xenbus_read(xenbus_transaction_t xbt, const char *path, char **value)
{
    struct write_req req[] = { {path, strlen(path) + 1} };
    struct xsd_sockmsg *rep;
    char *res, *msg;
    rep = xenbus_msg_reply(XS_READ, xbt, req, ARRAY_SIZE(req));
    msg = errmsg(rep);
    if ( msg )
    {
        *value = NULL;
        return msg;
    }

    res = malloc(rep->len + 1);
    memcpy(res, rep + 1, rep->len);
    res[rep->len] = 0;
    free(rep);
    *value = res;

    return NULL;
}
EXPORT_SYMBOL(xenbus_read);

char *xenbus_write(xenbus_transaction_t xbt, const char *path,
                   const char *value)
{
    struct write_req req[] = {
        {path, strlen(path) + 1},
        {value, strlen(value)},
    };
    struct xsd_sockmsg *rep;
    char *msg;

    rep = xenbus_msg_reply(XS_WRITE, xbt, req, ARRAY_SIZE(req));
    msg = errmsg(rep);
    if ( msg )
        return msg;

    free(rep);

    return NULL;
}
EXPORT_SYMBOL(xenbus_write);

char* xenbus_watch_path_token(xenbus_transaction_t xbt, const char *path,
                              const char *token, xenbus_event_queue *events)
{
    struct xsd_sockmsg *rep;
    struct write_req req[] = {
        {path, strlen(path) + 1},
        {token, strlen(token) + 1},
    };
    struct watch *watch = malloc(sizeof(*watch));
    char *msg;

    if ( !events )
        events = &xenbus_events;

    watch->token = strdup(token);
    watch->path = strdup(path);
    watch->events = events;
    watch->next = watches;
    watches = watch;

    rep = xenbus_msg_reply(XS_WATCH, xbt, req, ARRAY_SIZE(req));

    msg = errmsg(rep);
    if ( msg )
        return msg;

    free(rep);

    return NULL;
}
EXPORT_SYMBOL(xenbus_watch_path_token);

char* xenbus_unwatch_path_token(xenbus_transaction_t xbt, const char *path,
                                const char *token)
{
    struct xsd_sockmsg *rep;
    struct write_req req[] = {
        {path, strlen(path) + 1},
        {token, strlen(token) + 1},
    };
    struct watch *watch, **prev;
    char *msg;

    rep = xenbus_msg_reply(XS_UNWATCH, xbt, req, ARRAY_SIZE(req));

    msg = errmsg(rep);
    if ( msg )
        return msg;

    free(rep);

    for ( prev = &watches, watch = *prev; watch;
          prev = &watch->next, watch = *prev)
        if ( !strcmp(watch->token, token) )
        {
            free(watch->token);
            free(watch->path);
            *prev = watch->next;
            free(watch);
            break;
        }

    return NULL;
}
EXPORT_SYMBOL(xenbus_unwatch_path_token);

char *xenbus_rm(xenbus_transaction_t xbt, const char *path)
{
    struct write_req req[] = { {path, strlen(path) + 1} };
    struct xsd_sockmsg *rep;
    char *msg;

    rep = xenbus_msg_reply(XS_RM, xbt, req, ARRAY_SIZE(req));
    msg = errmsg(rep);
    if ( msg )
        return msg;

    free(rep);

    return NULL;
}
EXPORT_SYMBOL(xenbus_rm);

char *xenbus_get_perms(xenbus_transaction_t xbt, const char *path, char **value)
{
    struct write_req req[] = { {path, strlen(path) + 1} };
    struct xsd_sockmsg *rep;
    char *res, *msg;

    rep = xenbus_msg_reply(XS_GET_PERMS, xbt, req, ARRAY_SIZE(req));
    msg = errmsg(rep);
    if ( msg )
    {
        *value = NULL;
        return msg;
    }

    res = malloc(rep->len + 1);
    memcpy(res, rep + 1, rep->len);
    res[rep->len] = 0;
    free(rep);
    *value = res;

    return NULL;
}
EXPORT_SYMBOL(xenbus_get_perms);

#define PERM_MAX_SIZE 32
char *xenbus_set_perms(xenbus_transaction_t xbt, const char *path, domid_t dom,
                       char perm)
{
    char value[PERM_MAX_SIZE];
    struct write_req req[] = {
        {path, strlen(path) + 1},
        {value, 0},
    };
    struct xsd_sockmsg *rep;
    char *msg;

    snprintf(value, PERM_MAX_SIZE, "%c%hu", perm, dom);
    req[1].len = strlen(value) + 1;
    rep = xenbus_msg_reply(XS_SET_PERMS, xbt, req, ARRAY_SIZE(req));
    msg = errmsg(rep);
    if ( msg )
        return msg;

    free(rep);

    return NULL;
}
EXPORT_SYMBOL(xenbus_set_perms);

char *xenbus_transaction_start(xenbus_transaction_t *xbt)
{
    /*
     * xenstored becomes angry if you send a length 0 message, so just
     * shove a nul terminator on the end
     */
    struct write_req req = { "", 1};
    struct xsd_sockmsg *rep;
    char *err;

    rep = xenbus_msg_reply(XS_TRANSACTION_START, 0, &req, 1);
    err = errmsg(rep);
    if ( err )
        return err;

    sscanf((char *)(rep + 1), "%lu", xbt);
    free(rep);

    return NULL;
}
EXPORT_SYMBOL(xenbus_transaction_start);

char *xenbus_transaction_end(xenbus_transaction_t t, int abort, int *retry)
{
    struct xsd_sockmsg *rep;
    struct write_req req;
    char *err;

    *retry = 0;

    req.data = abort ? "F" : "T";
    req.len = 2;
    rep = xenbus_msg_reply(XS_TRANSACTION_END, t, &req, 1);
    err = errmsg(rep);
    if ( err )
    {
        if ( !strcmp(err, "EAGAIN") )
        {
            *retry = 1;
            free(err);
            return NULL;
        }
        else
            return err;
    }
    free(rep);

    return NULL;
}
EXPORT_SYMBOL(xenbus_transaction_end);

int xenbus_read_integer(const char *path)
{
    char *res, *buf;
    int t;

    res = xenbus_read(XBT_NIL, path, &buf);
    if ( res )
    {
        printk("Failed to read %s.\n", path);
        free(res);
        return -1;
    }

    sscanf(buf, "%d", &t);
    free(buf);

    return t;
}
EXPORT_SYMBOL(xenbus_read_integer);

int xenbus_read_uuid(const char *path, unsigned char uuid[16])
{
    char *res, *buf;

    res = xenbus_read(XBT_NIL, path, &buf);
    if ( res )
    {
       printk("Failed to read %s.\n", path);
       free(res);
       return 0;
    }

    if ( strlen(buf) != ((2 * 16) + 4) /* 16 hex bytes and 4 hyphens */ ||
         sscanf(buf, "%2hhx%2hhx%2hhx%2hhx-"
                     "%2hhx%2hhx-"
                     "%2hhx%2hhx-"
                     "%2hhx%2hhx-"
                     "%2hhx%2hhx%2hhx%2hhx%2hhx%2hhx",
                uuid, uuid + 1, uuid + 2, uuid + 3,
                uuid + 4, uuid + 5, uuid + 6, uuid + 7,
                uuid + 8, uuid + 9, uuid + 10, uuid + 11,
                uuid + 12, uuid + 13, uuid + 14, uuid + 15) != 16)
    {
        printk("Xenbus path %s value %s is not a uuid!\n", path, buf);
        free(buf);
        return 0;
    }

    free(buf);

    return 1;
}
EXPORT_SYMBOL(xenbus_read_uuid);

#define BUFFER_SIZE 256
static void xenbus_build_path(const char *dir, const char *node, char *res)
{
    BUG_ON(strlen(dir) + strlen(node) + 1 >= BUFFER_SIZE);
    sprintf(res,"%s/%s", dir, node);
}

char *xenbus_printf(xenbus_transaction_t xbt, const char* node,
                    const char* path, const char* fmt, ...)
{
    char fullpath[BUFFER_SIZE];
    char val[BUFFER_SIZE];
    va_list args;

    xenbus_build_path(node, path, fullpath);
    va_start(args, fmt);
    vsprintf(val, fmt, args);
    va_end(args);

    return xenbus_write(xbt,fullpath,val);
}
EXPORT_SYMBOL(xenbus_printf);

domid_t xenbus_get_self_id(void)
{
    char *dom_id;
    domid_t ret;

    BUG_ON(xenbus_read(XBT_NIL, "domid", &dom_id));
    sscanf(dom_id, "%"SCNd16, &ret);

    return ret;
}
EXPORT_SYMBOL(xenbus_get_self_id);

char *xenbus_read_string(xenbus_transaction_t xbt, const char *dir,
                         const char *node, char **value)
{
    char path[BUFFER_SIZE];

    xenbus_build_path(dir, node, path);

    return xenbus_read(xbt, path, value);
}
EXPORT_SYMBOL(xenbus_read_string);

char *xenbus_read_unsigned(xenbus_transaction_t xbt, const char *dir,
                           const char *node, unsigned int *value)
{
    char path[BUFFER_SIZE];
    char *msg;
    char *str;

    xenbus_build_path(dir, node, path);
    msg = xenbus_read(xbt, path, &str);
    if ( msg )
        return msg;

    if ( sscanf(str, "%u", value) != 1 )
        msg = strdup("EINVAL");
    free(str);

    return msg;
}
EXPORT_SYMBOL(xenbus_read_unsigned);

void xenBusTask( void * pvParameters )
{
    struct xsd_sockmsg msg;
    char *data;
    const uint32_t ulValueToSend = 0;
    for( ; ; )
    {
        xenbus_read_data((char *)&msg, sizeof(msg));
        data = malloc(sizeof(msg) + msg.len);
        memcpy(data, &msg, sizeof(msg));
        xenbus_read_data(data + sizeof(msg), msg.len);
#if 0
        if ( msg.req_id >= NR_REQS || !req_info[msg.req_id].in_use )
        {
            printk("Xenstore: illegal request id %d %d len:%d size:%d\n", msg.req_id, msg.type,msg.len,sizeof(msg));
            free(data);
            continue;
        }
#endif
        if ( msg.type == XS_WATCH_EVENT )
        {
            int counter=0;
            char *c;
            struct xenbus_event *event = malloc(sizeof(*event) + msg.len);
            xenbus_event_queue *events = NULL;
            struct watch *watch;
            int zeroes = 0;

            //data = (char *)event + sizeof(*event);
            //xenbus_read_data(data, msg.len);

            counter=0;
            for ( c = data + sizeof(msg); c < data + sizeof(msg) + msg.len; c++ ) {
                if ( !*c )
                    zeroes++;
            }
            printk("\n");

            if ( zeroes != 2 )
            {
                printk("Xenstore: illegal watch event data\n");
                free(event);
                continue;
            }

            event->path = data + sizeof(msg);
            event->token = event->path + strlen(event->path) + 1;

            for ( watch = watches; watch; watch = watch->next ) {
                if ( !strcmp(watch->token, event->token) )
                {
                    events = watch->events;
                    break;
                }
            }

            if ( events )
            {
                event->next = *events;
                *events = event;
                xQueueSend( xb_WatchQueue, &ulValueToSend, 0U);
            }
            else
            {
                printk("Xenstore: unexpected watch token %s\n", event->token);
                free(event);
            }

            continue;
        }

        //printk("Message is good.\n");
        req_info[msg.req_id].reply = data;
        xQueueSend( req_info[msg.req_id].waitq, &ulValueToSend, 0U);


    }
}

/*
 * Local variables:
 * mode: C
 * c-basic-offset: 4
 * End:
 */
