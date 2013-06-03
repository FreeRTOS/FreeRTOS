/*
 * @brief Memory management for host mode
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
  * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#define  __INCLUDE_FROM_USB_DRIVER
#include "USBMode.h"

#ifdef USB_CAN_BE_HOST

#include "../../../Common/Common.h"
#include "USBTask.h"
#include "HAL/HAL.h"
#include "USBMemory.h"

/************************************************************************/
/* LOCAL SYMBOL DECLARATIION                                            */
/************************************************************************/
#define TEST_NEW_ALLOC	0

#if TEST_NEW_ALLOC

typedef struct MemBlockInfo_t {
	uint32_t size :15; // memory size of this block
	uint32_t type :2;  // indicate whether this memory block is free, pad or used
	uint32_t next :15; // offset (from head address) to the next block
} sMemBlockInfo, *PMemBlockInfo;

typedef enum
{
	MEM_FREE = 0,
	MEM_PAD,
	MEM_USED,
}enMemBlockType;

#else

typedef struct MemBlockInfo_t {
	uint32_t size :15; // memory size of this block
	uint32_t isFree :1; // indicate whether this memory block is free or used
	uint32_t next :16; // offset (from head address) to the next block
} sMemBlockInfo, *PMemBlockInfo;

#endif
/************************************************************************/
/* LOCAL DEFINE                                                         */
/************************************************************************/
#define ALIGN_FOUR_BYTES    (4) // FIXME only m3 is 1 byte alignment

/* FIXME the following dynamic allocation is temporarly */

#define  HEADER_SIZE                (sizeof(sMemBlockInfo))
#define  HEADER_POINTER(x)          ((uint8_t *)x - sizeof(sMemBlockInfo))
#define  NEXT_BLOCK(x)            	((PMemBlockInfo) ( ((x)->next==0) ? 0 : ((uint32_t)head +(x)->next) ))
#define  LINK_TO_THIS_BLOCK(x)      (((uint32_t)(x))-((uint32_t)head))

PRAGMA_ALIGN_4
static uint8_t USB_Mem_Buffer[USBRAM_BUFFER_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);

void USB_Memory_Init(uint32_t Memory_Pool_Size)
{
	PMemBlockInfo head = (PMemBlockInfo) USB_Mem_Buffer;

	head->next = 0;
	head->size = (Memory_Pool_Size & 0xfffffffc) - HEADER_SIZE ;// align memory size
#if TEST_NEW_ALLOC
	head->type = MEM_FREE;
#else
	head->isFree = 1;
#endif
}

uint8_t* USB_Memory_Alloc(uint32_t size, uint32_t num_aligned_bytes)
{
	PMemBlockInfo freeBlock=NULL, newBlock, blk_ptr = NULL;
	PMemBlockInfo head = (PMemBlockInfo) USB_Mem_Buffer;

#if TEST_NEW_ALLOC
	for (blk_ptr = head; blk_ptr != NULL; blk_ptr = NEXT_BLOCK(blk_ptr)) // 1st-fit technique
	{
		if (((blk_ptr->type == MEM_FREE)||(blk_ptr->type == MEM_PAD)) && (blk_ptr->size >= size))
		{
			/* Filter by requested size */
			if (blk_ptr->size <= HEADER_SIZE + size) // where (blk_size=size | blk_size=size+HEAD) then allocate whole block & do not create freeBlock
			{
				blk_ptr->next = 0;
				blk_ptr->type = MEM_USED;
			} else {
				/* Locate empty block at end of found block */
				freeBlock = (PMemBlockInfo) (((uint32_t) blk_ptr) + size + HEADER_SIZE);
				freeBlock->next = blk_ptr->next;
				freeBlock->size = blk_ptr->size - (HEADER_SIZE + size);
				freeBlock->type = blk_ptr->type;

				/* Locate new block at start of found block */
				blk_ptr->size = size;
				blk_ptr->next = LINK_TO_THIS_BLOCK(freeBlock);
				blk_ptr->type = MEM_USED;
			}
			/* Filter by requested alignment*/
			if(num_aligned_bytes > 0)
			{
				uint32_t pad_size = (((uint32_t)blk_ptr) + HEADER_SIZE) % num_aligned_bytes;
				if(pad_size == 0) break;							//block found
				else 												//not fit alignment
					if(blk_ptr->next != 0)							//break if this is the last block in chain
					{
						uint32_t padBlkSize;

						if((num_aligned_bytes - pad_size) >= HEADER_SIZE)
							padBlkSize = num_aligned_bytes - pad_size - HEADER_SIZE;
						else
							padBlkSize = 2*num_aligned_bytes - pad_size - HEADER_SIZE;

						if(padBlkSize > freeBlock->size) 			//not enough space to create new pad
						{
							blk_ptr->next = freeBlock->next;
							blk_ptr->size = freeBlock->size + HEADER_SIZE + size;
							blk_ptr->type = MEM_PAD;
						}
						else										//there is space for new pad
						{
							newBlock = (PMemBlockInfo) (((uint32_t) blk_ptr) + HEADER_SIZE + padBlkSize);
							newBlock->next = freeBlock->next;
							newBlock->type = freeBlock->type;
							newBlock->size = freeBlock->size + HEADER_SIZE + size - padBlkSize;

							blk_ptr->size = padBlkSize;
							blk_ptr->next = LINK_TO_THIS_BLOCK(newBlock);
							blk_ptr->type = MEM_PAD;
						}
					}
			}
			else if(blk_ptr->type == MEM_USED)	break;
		}
	}

	if (blk_ptr == NULL) {
		return ((uint8_t *) NULL);
	}

	return (((uint8_t *) blk_ptr) + HEADER_SIZE);		

#else
	/* Align the requested size by 4 bytes */
	if ((size % ALIGN_FOUR_BYTES) != 0) {
		size = (((size >> 2) << 2) + ALIGN_FOUR_BYTES);
	}

	for (freeBlock = head; freeBlock != NULL; freeBlock = NEXT_BLOCK(freeBlock)) // 1st-fit technique
	{
		if ((freeBlock->isFree == 1) && (freeBlock->size >= size))
		{
			blk_ptr = freeBlock;
			break;
		}
	}

	if (blk_ptr == NULL) {
		return ((uint8_t *) NULL);
	}

	if (blk_ptr->size <= HEADER_SIZE + size) // where (blk_size=size | blk_size=size+HEAD) then allocate whole block & do not create freeBlock
	{
		newBlock = blk_ptr;
		//newBlock->size    = blk_ptr->size;
		//newBlock->next    = blk_ptr->next;
		newBlock->isFree = 0;
	} else {
		/* Locate empty block at end of found block */
		freeBlock = (PMemBlockInfo) (((uint8_t *) blk_ptr) + size + HEADER_SIZE);
		freeBlock->next = blk_ptr->next;
		freeBlock->size = blk_ptr->size - (HEADER_SIZE + size);
		freeBlock->isFree = 1;

		/* Locate new block at start of found block */
		newBlock = blk_ptr;
		newBlock->size = size;
		newBlock->next = LINK_TO_THIS_BLOCK(freeBlock);
		newBlock->isFree = 0;
	}

	return (((uint8_t *) newBlock) + HEADER_SIZE);
#endif
}

void USB_Memory_Free(uint8_t *ptr)
{
	PMemBlockInfo prev;
	PMemBlockInfo head = (PMemBlockInfo) USB_Mem_Buffer;
	PMemBlockInfo blk_ptr;

	if (ptr == NULL)
	{
		return;
	}

	blk_ptr = (PMemBlockInfo) HEADER_POINTER(ptr);
	
#if TEST_NEW_ALLOC
	
	bool being_pad = false;
	if (blk_ptr->next != 0) // merge with next free block
	{
		if ((NEXT_BLOCK(blk_ptr)->type == MEM_FREE)||(NEXT_BLOCK(blk_ptr)->type == MEM_PAD))
		{
			blk_ptr->size = blk_ptr->size + NEXT_BLOCK(blk_ptr)->size + HEADER_SIZE;
			blk_ptr->next = NEXT_BLOCK(blk_ptr)->next;
			blk_ptr->type = NEXT_BLOCK(blk_ptr)->type;
		}
		else being_pad = true;
	}

	for (prev = head; prev != NULL; prev = NEXT_BLOCK(prev)) // merge with previous free block
	{
		if (NEXT_BLOCK(prev) == blk_ptr)
		{
			if ((prev->type == MEM_FREE)||(prev->type == MEM_PAD))
			{
				prev->size = prev->size + blk_ptr->size + HEADER_SIZE;
				prev->next = blk_ptr->next;
			}
			else if(being_pad == true)						 // prev&next blocks are used
				blk_ptr->type = MEM_PAD;

			break;
		}
	}	

#else
	if (blk_ptr->next != 0) // merge with next free block
	{
		if (NEXT_BLOCK(blk_ptr)->isFree == 1)
		{
			blk_ptr->size = blk_ptr->size + NEXT_BLOCK(blk_ptr)->size + HEADER_SIZE;
			blk_ptr->next = NEXT_BLOCK(blk_ptr)->next;
		}
	}

	for (prev = head; prev != NULL; prev = NEXT_BLOCK(prev)) // merge with previous free block
	{
		if (NEXT_BLOCK(prev) == blk_ptr)
		{
			if (prev->isFree == 1)
			{
				prev->size = prev->size + blk_ptr->size + HEADER_SIZE;
				prev->next = blk_ptr->next;
				blk_ptr = prev;
			}
			break;
		}
	}

	blk_ptr->isFree = 1;

#endif
	return;
}

#endif
