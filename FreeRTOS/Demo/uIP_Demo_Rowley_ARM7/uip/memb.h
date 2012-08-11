/**
 * \addtogroup exampleapps
 * @{
 */

/**
 * \file
 * Memory block allocation routines.
 * \author Adam Dunkels <adam@sics.se>
 *
 */

#ifndef __MEMB_H__
#define __MEMB_H__

/**
 * Declare a memory block.
 *
 * \param name The name of the memory block (later used with
 * memb_init(), memb_alloc() and memb_free()).
 *
 * \param size The size of each memory chunk, in bytes.
 *
 * \param num The total number of memory chunks in the block.
 *
 */
#define MEMB(name, size, num) \
        static char memb_mem[(size + 1) * num]; \
        static struct memb_blocks name = {size, num, memb_mem}

struct memb_blocks {
  unsigned short size;
  unsigned short num;
  char *mem;
};

void  memb_init(struct memb_blocks *m);
char *memb_alloc(struct memb_blocks *m);
char  memb_ref(struct memb_blocks *m, char *ptr);
char  memb_free(struct memb_blocks *m, char *ptr);


#endif /* __MEMB_H__ */
