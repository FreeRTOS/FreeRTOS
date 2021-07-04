/***************************************************************************
 * Project               	   : shakti devt board
 * Name of the file	           : malloc_firstfit.c
 * Brief Description of file       : Malloc using First-fit algorithm code.
 * Name of Author    	           : Abhinav Ramnath
 * Email ID                        : abhinavramnath13@gmail.com

 Copyright (C) 2019  IIT Madras. All rights reserved.

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <https://www.gnu.org/licenses/>.
 ***************************************************************************/
/**
@file malloc_firstfit.c
@brief Malloc using First-fit algorithm code.
@detail This algorithm implements the malloc function using the first-fit algorithm. It allocates and frees blocks of memory for usage.
*/ 

#include<unistd.h>
#include<sys/types.h>
#include "platform.h"
#include "defines.h"
#include "log.h"

extern char* _HEAP_SIZE[];
char* HEAP_SIZE = (char *)&_HEAP_SIZE;

//Header block denotes start of the segment
struct Header
{
	size_t size;
	int free;
	struct Header* next;
};

struct Header* global_base=NULL;

/** @fn  struct Header* allocate_block(struct Header* last, size_t size)
 * @brief it allocates a block of given size 
 * @detail it allocates a block of the given size after receiving the parameter of the last allocated block
 * @param struct Header* last -  pointer to the last allocated memory or the end of the heap
 * @param size_t size - specifes the size of the block to be allocated
 * @return returns a pointer to the newly allocated block
 *         returns null if mmemory allocated or block allocation fails
 */
struct Header* allocate_block(struct Header* last, size_t size)
{
	uintptr_t x=0;

	log_trace("\nFunction allocate_block entered");

	if(last->size > size)
	{
		struct Header* newblock;
		void *p = last;

		p += size + sizeof(struct Header);
		x = p;

		x = ((( x) + ((REGSIZE) - 1)) & ~((REGSIZE) - 1));

		p = x;

		newblock = p;

		newblock->size = last->size - size - sizeof(struct Header);

		last->size = size;
		last->free = 0;
		last->next = newblock;

		newblock->free = 1;
		newblock->next = NULL;

		return last;
	}
	else
		return NULL;
	log_trace("\nFunction allocate_block entered");
}

//We search for free blocks
/** @fn  struct Header *find_free_block(struct Header **last, size_t size)
 * @brief finds free blocks from the linked list of blocks in the memory
 * @detail  iterates through the linked list to find a block of required size that is free
 * @param  struct Header **last - pointer to the heap
 * @param  size_t size - size of the block 
 * @return returns a free block if available
 *         returns null if unavailable
 */
struct Header *find_free_block(struct Header **last, size_t size)
{
	log_trace("\nfind free entered");

	struct Header *current = global_base;

	while (current && !(current->free && current->size >= size))
	{

		log_debug("\n Inside Loop %d %d %x %x",current->size,size,current,*last);
		*last = current;
		current = current->next;
	}

	log_debug("\n After Loop %d %d %x %x",current->size,size,current,*last);

	if(current && current->size>=size)
	{
		*last=current;
		return current;
	}
	else
		return NULL;

	log_trace("\nfind free exited");
}

//Creating a new block
/** @fn struct Header* request_heap()
 * @brief  requests memory from the heap
 * @detail  this function requests memory from the heap using the brk function
 * @return returns a pointer to the allocated heap
 *         returns NULL if heap is unable to be allocated
 */
struct Header* request_heap()
{
	struct Header *block;

	block = m_sbrk(0);

	void *request = m_sbrk(HEAP_SIZE);

	if((void*)block == request); // Not thread safe.
	block=request;

	log_debug("\nInitial Heap start address =%x",block);

	if (request == (void*) -1) {
		log_error("\nNo space left to allocate memory");
		return NULL; // sbrk failed.
	}

	block->size = HEAP_SIZE;
	block->next = NULL;
	block->free = 1;

	log_debug("\nBlock Assigned");

	return block;
}

//malloc function to allocate space
/** @fn  void *malloc(size_t size)
 * @brief  this function is used to dynamically allocate memory
 * @detail  when this function is called memory is allocated in the heap during runtime
 * @param size_t size - size of the block to be allocated
 * @return  returns a pointer to the assigned block
 *          returns NULL if allocation fails
 */
void *malloc(size_t size)
{
	struct Header *block;

	if (size <= 0) {
               return NULL;
	}

	log_info("\n global_base: %x",global_base);

	if(global_base==0x00000000)
	{
		// First call. global_base is empty
		log_debug("\n Requesting block");

		block = request_heap();

		log_debug("\n block=%x",block);

		if (!block)
		{
			return NULL;
		}
		global_base = block;
	}

	struct Header *last = global_base;

	block = find_free_block(&last, size);

	if(!block)
	{
		log_error("\n No free blocks");
		return NULL;
	}

	log_debug("\nBlock = %x Block Size = %d Size = %d",block,block->size,size);

	if (block->size>size)
	{
		// Failed to find free block.
		block = allocate_block(last,size);

		if (!block)
		{
			return NULL;
		}
	}
	else if(block->size==size)
	{
		// Found free block
		log_debug("\nFound free block of same size");
		block->free = 0;
	}

  return(block+1);
}

/** @fn  struct Header *get_block_ptr(void *ptr)
 * @brief function to get block pointer
 * @detail  function returns the pointer to the block
 * @param void* ptr - pointer to the block
 * @return returns pointer to the block
 */
struct Header *get_block_ptr(void *ptr)
{
  return (struct Header*)ptr - 1;
}

//free to free the memory allocated by malloc
/** @fn  void free(void *ptr)
 * @brief frees the memory assigned by malloc
 * @detail  frees the memory assigned by malloc and when freed this memory is added back to the list to be reused
 * @param void *ptr - pointer to the memory assigned by malloc
 */
void free(void *ptr)
{
	if (!ptr)
	{
		log_error("\n Wrong value passed to free");
		return;
	}

	struct Header* block_ptr = get_block_ptr(ptr);

	log_debug("\n %x is freed",block_ptr);

	if(block_ptr->free==0)
		block_ptr->free = 1;
}
