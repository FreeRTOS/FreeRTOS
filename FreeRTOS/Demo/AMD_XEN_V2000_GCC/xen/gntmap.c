/*
 * Manages grant mappings from other domains.
 *
 * Diego Ongaro <diego.ongaro@citrix.com>, July 2008
 *
 * Files of libxengnttab contain a gntmap, which is an array of
 * (host address, grant handle) pairs. Grant handles come from a hypervisor map
 * operation and are needed for the corresponding unmap.
 *
 * This is a rather naive implementation in terms of performance. If we start
 * using it frequently, there's definitely some low-hanging fruit here.
 *
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR 
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE 
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING 
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER 
 * DEALINGS IN THE SOFTWARE.
 */

#include <os.h>
#include <lib.h>
#include <e820.h>
#include <xmalloc.h>
#include <memory.h>
#include <errno.h>
#include <xen/grant_table.h>
#include <inttypes.h>
#include <gntmap.h>

//#define GNTMAP_DEBUG
#ifdef GNTMAP_DEBUG
#define DEBUG(_f, _a...) \
    printk("XEN_FREERTOS(gntmap.c:%d): %s" _f "\n", __LINE__, __func__, ## _a)
#else
#define DEBUG(_f, _a...)    ((void)0)
#endif


#define DEFAULT_MAX_GRANTS 128

struct gntmap_entry {
    unsigned long host_addr;
    grant_handle_t handle;
};

static inline int
gntmap_entry_used(struct gntmap *map, int idx)
{
    return map->entries[idx].host_addr != 0;
}

static int gntmap_find_free_entry(struct gntmap *map)
{
    int i;

    for (i = 0; i < map->nentries; i++) {
        if (!gntmap_entry_used(map, i))
            return i;
    }

    DEBUG("(map=%p): all %d entries full",
           map, map->nentries);
    return -1;
}

static int gntmap_find_entry(struct gntmap *map, unsigned long addr)
{
    int i;

    for (i = 0; i < map->nentries; i++) {
        if (map->entries[i].host_addr == addr)
            return i;
    }
    return -1;
}

int
gntmap_set_max_grants(struct gntmap *map, int count)
{
    DEBUG("(map=%p, count=%d)", map, count);

    if (map->nentries != 0)
        return -EBUSY;

    map->entries = xmalloc_array(struct gntmap_entry, count);
    if (map->entries == NULL)
        return -ENOMEM;

#if 0
#ifndef CONFIG_PARAVIRT
    map->start_pfn = e820_get_reserved_pfns(count);
#endif
#endif

    memset(map->entries, 0, sizeof(struct gntmap_entry) * count);
    map->nentries = count;
    return 0;
}

static int
_gntmap_unmap_grant_ref(struct gntmap *map, int idx)
{
    struct gntmap_entry *entry = map->entries + idx;
    struct gnttab_unmap_grant_ref op;
    int rc;

#ifdef CONFIG_PARAVIRT
    op.host_addr    = (uint64_t) entry->host_addr;
#else
    op.host_addr    = (uint64_t)(map->start_pfn + idx) << PAGE_SHIFT;
#endif
    op.dev_bus_addr = 0;
    op.handle       = entry->handle;

    rc = HYPERVISOR_grant_table_op(GNTTABOP_unmap_grant_ref, &op, 1);
    if (rc != 0 || op.status != GNTST_okay) {
        printk("GNTTABOP_unmap_grant_ref failed: "
               "returned %d, status %" PRId16 "\n",
               rc, op.status);
        return rc != 0 ? rc : op.status;
    }

    entry->host_addr = 0;
    return 0;
}

static int
_gntmap_map_grant_ref(struct gntmap *map, int idx,
                      unsigned long host_addr,
                      uint32_t domid,
                      uint32_t ref,
                      int writable)
{
    struct gntmap_entry *entry = map->entries + idx;
    struct gnttab_map_grant_ref op;
    int rc;
#ifndef CONFIG_PARAVIRT
    unsigned long pfn = map->start_pfn + idx;
#endif
    op.ref = (grant_ref_t) ref;
    op.dom = (domid_t) domid;
#ifdef CONFIG_PARAVIRT
    op.host_addr = (uint64_t) host_addr;
#else
    op.host_addr = (uint64_t)pfn << 12;
#endif
    op.flags = GNTMAP_host_map;
    if (!writable)
        op.flags |= GNTMAP_readonly;

    rc = HYPERVISOR_grant_table_op(GNTTABOP_map_grant_ref, &op, 1);
    if (rc != 0 || op.status != GNTST_okay) {
        printk("GNTTABOP_map_grant_ref failed: "
               "returned %d, status %" PRId16 "\n",
               rc, op.status);
        return rc != 0 ? rc : op.status;
    }
    printk("Grant table hypercall successfully done.\n");

/* FIXME: Include for 4 level page table. */
#if 0
#ifndef CONFIG_PARAVIRT
    rc = do_map_frames(host_addr, &pfn, 1, 0, 0, DOMID_SELF, NULL,
                       writable ? L1_PROT : L1_PROT_RO);
    if ( rc )
    {
        _gntmap_unmap_grant_ref(map, idx);
        return rc;
    }
#endif
#endif

    printk("Frames mapped in our memory.\n");
    entry->host_addr = host_addr;
    entry->handle = op.handle;
    
    return 0;
}

int
gntmap_munmap(struct gntmap *map, unsigned long start_address, int count)
{
    int i, rc;
    int idx;

    DEBUG("(map=%p, start_address=%lx, count=%d)",
           map, start_address, count);

#ifndef CONFIG_PARAVIRT
    unmap_frames(start_address, count);
#endif

    for (i = 0; i < count; i++) {
        idx = gntmap_find_entry(map, start_address + PAGE_SIZE * i);
        if (idx < 0) {
            printk("gntmap: tried to munmap unknown page\n");
            return -EINVAL;
        }

        rc = _gntmap_unmap_grant_ref(map, idx);
        if (rc != 0)
            return rc;
    }

    return 0;
}

void*
gntmap_map_grant_refs(struct gntmap *map, 
                      uint32_t count,
                      uint32_t *domids,
                      int domids_stride,
                      uint32_t *refs,
                      int writable)
{
    unsigned long addr;
    int idx;
    int i;

    DEBUG("(map=%p, count=%" PRIu32 ", "
           "domids=%p [%" PRIu32 "...], domids_stride=%d, "
           "refs=%p [%" PRIu32 "...], writable=%d)",
           map, count,
           domids, domids == NULL ? 0 : domids[0], domids_stride,
           refs, refs == NULL ? 0 : refs[0], writable);

    (void) gntmap_set_max_grants(map, DEFAULT_MAX_GRANTS);

    addr = (unsigned long)pvAlignedMalloc((size_t)(count * 4096), 4096);
    if (addr == 0)
        return NULL;

    for (i = 0; i < count; i++) {
        idx = gntmap_find_free_entry(map);
        if (idx < 0 ||
            _gntmap_map_grant_ref(map, idx,
                                  addr + 4096 * i,
                                  domids[i * domids_stride],
                                  refs[i],
                                  writable) != 0) {

            (void) gntmap_munmap(map, addr, i);
            return NULL;
        }
    }

    return (void*) addr;
}

void
gntmap_init(struct gntmap *map)
{
    DEBUG("(map=%p)", map);
    map->nentries = 0;
    map->entries = NULL;
}

void
gntmap_fini(struct gntmap *map)
{
    int i;

    DEBUG("(map=%p)", map);

    for (i = 0; i < map->nentries; i++) {
        if (gntmap_entry_used(map, i))
            (void) _gntmap_unmap_grant_ref(map, i);
    }

#if 0
#ifndef CONFIG_PARAVIRT
    e820_put_reserved_pfns(map->start_pfn, map->nentries);
    map->start_pfn = 0;
#endif
#endif

    free(map->entries);
    map->entries = NULL;
    map->nentries = 0;
}
