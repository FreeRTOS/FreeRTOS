#include <metal/scrub.h>
#include <sys/types.h>

/* brk is handled entirely within the C library.  This limits METAL programs
 * that use the C library to be disallowed from dynamically allocating memory
 * without talking to the C library, but that sounds like a sane way to go
 * about it.  Note that there is no error checking anywhere in this file, users
 * will simply get the relevant error when actually trying to use the memory
 * that's been allocated. */
extern char metal_segment_heap_target_start;
extern char metal_segment_heap_target_end;
static char *__brk = &metal_segment_heap_target_start;

#ifdef _PICOLIBC__
#define _brk brk
#define _sbrk sbrk
#endif

int _brk(void *addr) {
    __brk = addr;
    return 0;
}

char *_sbrk(ptrdiff_t incr) {
    char *old = __brk;

    /* If __heap_size == 0, we can't allocate memory on the heap */
    if (&metal_segment_heap_target_start == &metal_segment_heap_target_end) {
        return (void *)-1;
    }

    /* Don't move the break past the end of the heap */
    if ((__brk + incr) < &metal_segment_heap_target_end) {
        __brk += incr;
    } else {
        __brk = &metal_segment_heap_target_end;
        return (void *)-1;
    }
    /* Scrub out allocated memory to avoid spurious ECC errors */
    metal_mem_scrub(old, incr);

    return old;
}
