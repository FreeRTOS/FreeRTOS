/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 1995 Danny Gasparovski
 */

/*
 * mbuf's in SLiRP are much simpler than the real mbufs in
 * FreeBSD.  They are fixed size, determined by the MTU,
 * so that one whole packet can fit.  Mbuf's cannot be
 * chained together.  If there's more data than the mbuf
 * could hold, an external g_malloced buffer is pointed to
 * by m_ext (and the data pointers) and M_EXT is set in
 * the flags
 */

#include "slirp.h"

#define MBUF_THRESH 30

/*
 * Find a nice value for msize
 */
#define SLIRP_MSIZE(mtu) \
    (offsetof(struct mbuf, m_dat) + IF_MAXLINKHDR + TCPIPHDR_DELTA + (mtu))

void m_init(Slirp *slirp)
{
    slirp->m_freelist.qh_link = slirp->m_freelist.qh_rlink = &slirp->m_freelist;
    slirp->m_usedlist.qh_link = slirp->m_usedlist.qh_rlink = &slirp->m_usedlist;
}

static void m_cleanup_list(struct slirp_quehead *list_head)
{
    struct mbuf *m, *next;

    m = (struct mbuf *)list_head->qh_link;
    while ((struct slirp_quehead *)m != list_head) {
        next = m->m_next;
        if (m->m_flags & M_EXT) {
            g_free(m->m_ext);
        }
        g_free(m);
        m = next;
    }
    list_head->qh_link = list_head;
    list_head->qh_rlink = list_head;
}

void m_cleanup(Slirp *slirp)
{
    m_cleanup_list(&slirp->m_usedlist);
    m_cleanup_list(&slirp->m_freelist);
    m_cleanup_list(&slirp->if_batchq);
    m_cleanup_list(&slirp->if_fastq);
}

/*
 * Get an mbuf from the free list, if there are none
 * allocate one
 *
 * Because fragmentation can occur if we alloc new mbufs and
 * free old mbufs, we mark all mbufs above mbuf_thresh as M_DOFREE,
 * which tells m_free to actually g_free() it
 */
struct mbuf *m_get(Slirp *slirp)
{
    register struct mbuf *m;
    int flags = 0;

    DEBUG_CALL("m_get");

    if (MBUF_DEBUG || slirp->m_freelist.qh_link == &slirp->m_freelist) {
        m = g_malloc(SLIRP_MSIZE(slirp->if_mtu));
        slirp->mbuf_alloced++;
        if (MBUF_DEBUG || slirp->mbuf_alloced > MBUF_THRESH)
            flags = M_DOFREE;
        m->slirp = slirp;
    } else {
        m = (struct mbuf *)slirp->m_freelist.qh_link;
        slirp_remque(m);
    }

    /* Insert it in the used list */
    slirp_insque(m, &slirp->m_usedlist);
    m->m_flags = (flags | M_USEDLIST);

    /* Initialise it */
    m->m_size = SLIRP_MSIZE(slirp->if_mtu) - offsetof(struct mbuf, m_dat);
    m->m_data = m->m_dat;
    m->m_len = 0;
    m->m_nextpkt = NULL;
    m->m_prevpkt = NULL;
    m->resolution_requested = false;
    m->expiration_date = (uint64_t)-1;
    DEBUG_ARG("m = %p", m);
    return m;
}

void m_free(struct mbuf *m)
{
    DEBUG_CALL("m_free");
    DEBUG_ARG("m = %p", m);

    if (m) {
        /* Remove from m_usedlist */
        if (m->m_flags & M_USEDLIST)
            slirp_remque(m);

        /* If it's M_EXT, free() it */
        if (m->m_flags & M_EXT) {
            g_free(m->m_ext);
            m->m_flags &= ~M_EXT;
        }
        /*
         * Either free() it or put it on the free list
         */
        if (m->m_flags & M_DOFREE) {
            m->slirp->mbuf_alloced--;
            g_free(m);
        } else if ((m->m_flags & M_FREELIST) == 0) {
            slirp_insque(m, &m->slirp->m_freelist);
            m->m_flags = M_FREELIST; /* Clobber other flags */
        }
    } /* if(m) */
}

/*
 * Copy data from one mbuf to the end of
 * the other.. if result is too big for one mbuf, allocate
 * an M_EXT data segment
 */
void m_cat(struct mbuf *m, struct mbuf *n)
{
    /*
     * If there's no room, realloc
     */
    if (M_FREEROOM(m) < n->m_len)
        m_inc(m, m->m_len + n->m_len);

    memcpy(m->m_data + m->m_len, n->m_data, n->m_len);
    m->m_len += n->m_len;

    m_free(n);
}


/* make m 'size' bytes large from m_data */
void m_inc(struct mbuf *m, int size)
{
    int gapsize;

    /* some compilers throw up on gotos.  This one we can fake. */
    if (M_ROOM(m) > size) {
        return;
    }

    if (m->m_flags & M_EXT) {
        gapsize = m->m_data - m->m_ext;
        m->m_ext = g_realloc(m->m_ext, size + gapsize);
    } else {
        gapsize = m->m_data - m->m_dat;
        m->m_ext = g_malloc(size + gapsize);
        memcpy(m->m_ext, m->m_dat, m->m_size);
        m->m_flags |= M_EXT;
    }

    m->m_data = m->m_ext + gapsize;
    m->m_size = size + gapsize;
}


void m_adj(struct mbuf *m, int len)
{
    if (m == NULL)
        return;
    if (len >= 0) {
        /* Trim from head */
        m->m_data += len;
        m->m_len -= len;
    } else {
        /* Trim from tail */
        len = -len;
        m->m_len -= len;
    }
}


/*
 * Copy len bytes from m, starting off bytes into n
 */
int m_copy(struct mbuf *n, struct mbuf *m, int off, int len)
{
    if (len > M_FREEROOM(n))
        return -1;

    memcpy((n->m_data + n->m_len), (m->m_data + off), len);
    n->m_len += len;
    return 0;
}


/*
 * Given a pointer into an mbuf, return the mbuf
 * XXX This is a kludge, I should eliminate the need for it
 * Fortunately, it's not used often
 */
struct mbuf *dtom(Slirp *slirp, void *dat)
{
    struct mbuf *m;

    DEBUG_CALL("dtom");
    DEBUG_ARG("dat = %p", dat);

    /* bug corrected for M_EXT buffers */
    for (m = (struct mbuf *)slirp->m_usedlist.qh_link;
         (struct slirp_quehead *)m != &slirp->m_usedlist; m = m->m_next) {
        if (m->m_flags & M_EXT) {
            if ((char *)dat >= m->m_ext && (char *)dat < (m->m_ext + m->m_size))
                return m;
        } else {
            if ((char *)dat >= m->m_dat && (char *)dat < (m->m_dat + m->m_size))
                return m;
        }
    }

    DEBUG_ERROR("dtom failed");

    return (struct mbuf *)0;
}

/*
 * Duplicate the mbuf
 *
 * copy_header specifies whether the bytes before m_data should also be copied.
 * header_size specifies how many bytes are to be reserved before m_data.
 */
struct mbuf *m_dup(Slirp *slirp, struct mbuf *m,
                   bool copy_header,
                   size_t header_size)
{
    struct mbuf *n;
    int mcopy_result;

    /* The previous mbuf was supposed to have it already, we can check it along
     * the way */
    assert(M_ROOMBEFORE(m) >= header_size);

    n = m_get(slirp);
    m_inc(n, m->m_len + header_size);

    if (copy_header) {
        m->m_len += header_size;
        m->m_data -= header_size;
        mcopy_result = m_copy(n, m, 0, m->m_len + header_size);
        n->m_data += header_size;
        m->m_len -= header_size;
        m->m_data += header_size;
    } else {
        n->m_data += header_size;
        mcopy_result = m_copy(n, m, 0, m->m_len);
    }
    g_assert(mcopy_result == 0);

    return n;
}

void *mtod_check(struct mbuf *m, size_t len)
{
    if (m->m_len >= len) {
        return m->m_data;
    }

    DEBUG_ERROR("mtod failed");

    return NULL;
}

void *m_end(struct mbuf *m)
{
    return m->m_data + m->m_len;
}
