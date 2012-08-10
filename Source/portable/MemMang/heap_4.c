/*
    FreeRTOS V7.1.1 - Copyright (C) 2012 Real Time Engineers Ltd.


    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************


    http://www.FreeRTOS.org - Documentation, training, latest information,
    license and contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell
    the code with commercial support, indemnification, and middleware, under
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/*
 * A sample implementation of pvPortMalloc() and vPortFree() that combines 
 * (coalescences) adjacent memory blocks as they are freed, and in so doing 
 * limits memory fragmentation.
 *
 * See heap_1.c, heap_2.c and heap_3.c for alternative implementations, and the 
 * memory management pages of http://www.FreeRTOS.org for more information.
 */
#include <stdlib.h>

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
all the API functions to use the MPU wrappers.  That should only be done when
task.h is included from an application file. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

#include "FreeRTOS.h"
#include "task.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/* Block sizes must not get too small. */
#define heapMINIMUM_BLOCK_SIZE	( ( size_t ) ( heapSTRUCT_SIZE * 2 ) )

/* Allocate the memory for the heap.  The struct is used to force byte
alignment without using any non-portable code. */
static union xRTOS_HEAP
{
	#if portBYTE_ALIGNMENT == 8
		volatile portDOUBLE dDummy;
	#else
		volatile unsigned long ulDummy;
	#endif
	unsigned char ucHeap[ configTOTAL_HEAP_SIZE ];
} xHeap;

/* Define the linked list structure.  This is used to link free blocks in order
of their memory address. */
typedef struct A_BLOCK_LINK
{
	struct A_BLOCK_LINK *pxNextFreeBlock;	/*<< The next free block in the list. */
	size_t xBlockSize;						/*<< The size of the free block. */
} xBlockLink;

/*-----------------------------------------------------------*/

/*
 * Inserts a block of memory that is being freed into the correct position in 
 * the list of free memory blocks.  The block being freed will be merged with
 * the block in front it and/or the block behind it if the memory blocks are
 * adjacent to each other.
 */
static void prvInsertBlockIntoFreeList( xBlockLink *pxBlockToInsert );

/*
 * Called automatically to setup the required heap structures the first time
 * pvPortMalloc() is called.
 */
static void prvHeapInit( void );

/*-----------------------------------------------------------*/

/* The size of the structure placed at the beginning of each allocated memory
block must by correctly byte aligned. */
static const unsigned short heapSTRUCT_SIZE	= ( sizeof( xBlockLink ) + portBYTE_ALIGNMENT - ( sizeof( xBlockLink ) % portBYTE_ALIGNMENT ) );

/* Ensure the pxEnd pointer will end up on the correct byte alignment. */
static const size_t xTotalHeapSize = ( ( size_t ) configTOTAL_HEAP_SIZE ) & ( ( size_t ) ~portBYTE_ALIGNMENT_MASK );

/* Create a couple of list links to mark the start and end of the list. */
static xBlockLink xStart, *pxEnd = NULL;

/* Keeps track of the number of free bytes remaining, but says nothing about
fragmentation. */
static size_t xFreeBytesRemaining = ( ( size_t ) configTOTAL_HEAP_SIZE ) & ( ( size_t ) ~portBYTE_ALIGNMENT_MASK );

/* STATIC FUNCTIONS ARE DEFINED AS MACROS TO MINIMIZE THE FUNCTION CALL DEPTH. */

/*-----------------------------------------------------------*/

void *pvPortMalloc( size_t xWantedSize )
{
xBlockLink *pxBlock, *pxPreviousBlock, *pxNewBlockLink;
void *pvReturn = NULL;

	vTaskSuspendAll();
	{
		/* If this is the first call to malloc then the heap will require
		initialisation to setup the list of free blocks. */
		if( pxEnd == NULL )
		{
			prvHeapInit();
		}

		/* The wanted size is increased so it can contain a xBlockLink
		structure in addition to the requested amount of bytes. */
		if( xWantedSize > 0 )
		{
			xWantedSize += heapSTRUCT_SIZE;

			/* Ensure that blocks are always aligned to the required number of 
			bytes. */
			if( xWantedSize & portBYTE_ALIGNMENT_MASK )
			{
				/* Byte alignment required. */
				xWantedSize += ( portBYTE_ALIGNMENT - ( xWantedSize & portBYTE_ALIGNMENT_MASK ) );
			}
		}

		if( ( xWantedSize > 0 ) && ( xWantedSize < xTotalHeapSize ) )
		{
			/* Traverse the list from the start	(lowest address) block until one
			of adequate size is found. */
			pxPreviousBlock = &xStart;
			pxBlock = xStart.pxNextFreeBlock;
			while( ( pxBlock->xBlockSize < xWantedSize ) && ( pxBlock->pxNextFreeBlock != NULL ) )
			{
				pxPreviousBlock = pxBlock;
				pxBlock = pxBlock->pxNextFreeBlock;
			}

			/* If the end marker was reached then a block of adequate size was
			not found. */
			if( pxBlock != pxEnd )
			{
				/* Return the memory space - jumping over the xBlockLink structure
				at its start. */
				pvReturn = ( void * ) ( ( ( unsigned char * ) pxPreviousBlock->pxNextFreeBlock ) + heapSTRUCT_SIZE );

				/* This block is being returned for use so must be taken out of
				the	list of free blocks. */
				pxPreviousBlock->pxNextFreeBlock = pxBlock->pxNextFreeBlock;

				/* If the block is larger than required it can be split into two. */
				if( ( pxBlock->xBlockSize - xWantedSize ) > heapMINIMUM_BLOCK_SIZE )
				{
					/* This block is to be split into two.  Create a new block
					following the number of bytes requested. The void cast is
					used to prevent byte alignment warnings from the compiler. */
					pxNewBlockLink = ( void * ) ( ( ( unsigned char * ) pxBlock ) + xWantedSize );

					/* Calculate the sizes of two blocks split from the single
					block. */
					pxNewBlockLink->xBlockSize = pxBlock->xBlockSize - xWantedSize;
					pxBlock->xBlockSize = xWantedSize;

					/* Insert the new block into the list of free blocks. */
					prvInsertBlockIntoFreeList( ( pxNewBlockLink ) );
				}

				xFreeBytesRemaining -= pxBlock->xBlockSize;
			}
		}
	}
	xTaskResumeAll();

	#if( configUSE_MALLOC_FAILED_HOOK == 1 )
	{
		if( pvReturn == NULL )
		{
			extern void vApplicationMallocFailedHook( void );
			vApplicationMallocFailedHook();
		}
	}
	#endif

	return pvReturn;
}
/*-----------------------------------------------------------*/

void vPortFree( void *pv )
{
unsigned char *puc = ( unsigned char * ) pv;
xBlockLink *pxLink;

	if( pv != NULL )
	{
		/* The memory being freed will have an xBlockLink structure immediately
		before it. */
		puc -= heapSTRUCT_SIZE;

		/* This casting is to keep the compiler from issuing warnings. */
		pxLink = ( void * ) puc;

		vTaskSuspendAll();
		{
			/* Add this block to the list of free blocks. */
			xFreeBytesRemaining += pxLink->xBlockSize;
			prvInsertBlockIntoFreeList( ( ( xBlockLink * ) pxLink ) );			
		}
		xTaskResumeAll();
	}
}
/*-----------------------------------------------------------*/

size_t xPortGetFreeHeapSize( void )
{
	return xFreeBytesRemaining;
}
/*-----------------------------------------------------------*/

void vPortInitialiseBlocks( void )
{
	/* This just exists to keep the linker quiet. */
}
/*-----------------------------------------------------------*/

static void prvHeapInit( void )
{
xBlockLink *pxFirstFreeBlock;
unsigned char *pucHeapEnd;

	/* Ensure the start of the heap is aligned. */
	configASSERT( ( ( ( unsigned long ) xHeap.ucHeap ) & ( ( unsigned long ) portBYTE_ALIGNMENT_MASK ) ) == 0UL );

	/* xStart is used to hold a pointer to the first item in the list of free
	blocks.  The void cast is used to prevent compiler warnings. */
	xStart.pxNextFreeBlock = ( void * ) xHeap.ucHeap;
	xStart.xBlockSize = ( size_t ) 0;

	/* pxEnd is used to mark the end of the list of free blocks and is inserted
	at the end of the heap space. */
	pucHeapEnd = xHeap.ucHeap + xTotalHeapSize;
	pucHeapEnd -= heapSTRUCT_SIZE;
	pxEnd = ( void * ) pucHeapEnd;
	configASSERT( ( ( ( unsigned long ) pxEnd ) & ( ( unsigned long ) portBYTE_ALIGNMENT_MASK ) ) == 0UL );
	pxEnd->xBlockSize = 0;
	pxEnd->pxNextFreeBlock = NULL;

	/* To start with there is a single free block that is sized to take up the
	entire heap space, minus the space taken by pxEnd. */
	pxFirstFreeBlock = ( void * ) xHeap.ucHeap;
	pxFirstFreeBlock->xBlockSize = xTotalHeapSize - heapSTRUCT_SIZE;
	pxFirstFreeBlock->pxNextFreeBlock = pxEnd;

	/* The heap now contains pxEnd. */
	xFreeBytesRemaining -= heapSTRUCT_SIZE;
}
/*-----------------------------------------------------------*/

static void prvInsertBlockIntoFreeList( xBlockLink *pxBlockToInsert )
{
xBlockLink *pxIterator;
unsigned char *puc;

	/* Iterate through the list until a block is found that has a higher address
	than the block being inserted. */
	for( pxIterator = &xStart; pxIterator->pxNextFreeBlock < pxBlockToInsert; pxIterator = pxIterator->pxNextFreeBlock )
	{
		/* Nothing to do here, just iterate to the right position. */
	}

	/* Do the block being inserted, and the block it is being inserted after
	make a contiguous block of memory? */	
	puc = ( unsigned char * ) pxIterator;
	if( ( puc + pxIterator->xBlockSize ) == ( unsigned char * ) pxBlockToInsert )
	{
		pxIterator->xBlockSize += pxBlockToInsert->xBlockSize;
		pxBlockToInsert = pxIterator;
	}

	/* Do the block being inserted, and the block it is being inserted before
	make a contiguous block of memory? */
	puc = ( unsigned char * ) pxBlockToInsert;
	if( ( puc + pxBlockToInsert->xBlockSize ) == ( unsigned char * ) pxIterator->pxNextFreeBlock )
	{
		if( pxIterator->pxNextFreeBlock != pxEnd )
		{
			/* Form one big block from the two blocks. */
			pxBlockToInsert->xBlockSize += pxIterator->pxNextFreeBlock->xBlockSize;
			pxBlockToInsert->pxNextFreeBlock = pxIterator->pxNextFreeBlock->pxNextFreeBlock;
		}
		else
		{
			pxBlockToInsert->pxNextFreeBlock = pxEnd;
		}
	}
	else
	{
		pxBlockToInsert->pxNextFreeBlock = pxIterator->pxNextFreeBlock;		
	}

	/* If the block being inserted plugged a gab, so was merged with the block
	before and the block after, then it's pxNextFreeBlock pointer will have
	already been set, and should not be set here as that would make it point
	to itself. */
	if( pxIterator != pxBlockToInsert )
	{
		pxIterator->pxNextFreeBlock = pxBlockToInsert;
	}
}


#define INCLUDE_TEST_CODE 1
#if INCLUDE_TEST_CODE == 1

#define heapMAX_TEST_BLOCKS 6

void vTestHeap4( void )
{
void *pvReturned;
static void *pvUsedBlocks[ heapMAX_TEST_BLOCKS ];
unsigned long ulIndex = 0, ulSize, ulRandSample;
static const unsigned long ulCombinations[ 6 ][ 3 ] =
{
	{ 0, 1, 2 },
	{ 0, 2, 1 },
	{ 1, 0, 2 },
	{ 1, 2, 0 },
	{ 2, 0, 1 },
	{ 2, 1, 0 }
};

	/* Attempt to obtain a block of memory that equals the enture heap size.
	This should fail as the size of a block link structure will be added to the
	block in pvPortMalloc(). */
	pvReturned = pvPortMalloc( xTotalHeapSize );
	configASSERT( pvReturned == NULL );

	/* Attempt to obtain a block of memory that equals the entire heap size 
	minus the size of the block link structure that will get added to the 
	wanted size	inside pvPortMalloc().  This should also fail as the heap 
	already contains a start and end block link structure. */
	pvReturned = pvPortMalloc( xTotalHeapSize - heapSTRUCT_SIZE );
	configASSERT( pvReturned == NULL );

	/* Attempt to obtain a block of memory that equals the entire heap size 
	minus the size of the block link structure that will get added to the 
	wanted size inside pvPortMalloc(), minus the size of the block link 
	structure that marks the end of the heap. */
	pvReturned = pvPortMalloc( xTotalHeapSize - ( 2 * heapSTRUCT_SIZE ) );

	/* The returned value should point just past the first block link. */
	configASSERT( pvReturned == ( xHeap.ucHeap + heapSTRUCT_SIZE ) );

	/* There should be no heap remaining. */
	configASSERT( xFreeBytesRemaining == 0 );

	/* The start should point to the end. */
	configASSERT( xStart.pxNextFreeBlock == pxEnd );

	/* Free the memory again. */
	vPortFree( pvReturned );

	/* The heap should be back to its full size, which is the total bytes
	in the array minus the space taken up by the pxEnd structure. */
	configASSERT( xFreeBytesRemaining == ( xTotalHeapSize - heapSTRUCT_SIZE ) );

	/* The start block should now point to a block that holds the entire heap
	space, which should itself point to the end. */
	configASSERT( xStart.pxNextFreeBlock->xBlockSize == ( xTotalHeapSize - heapSTRUCT_SIZE ) );
	configASSERT( xStart.pxNextFreeBlock->pxNextFreeBlock == pxEnd );

	/* The next test plugs a gap that create a continuous block up to the pxEnd
	marker. */

	/* Remove a small block. */
	pvUsedBlocks[ ulIndex ] = pvPortMalloc( 8 );
	configASSERT( xFreeBytesRemaining == ( xTotalHeapSize - heapSTRUCT_SIZE - 8 - heapSTRUCT_SIZE ) );
	ulIndex++;

	/* Remove another block. */
	pvUsedBlocks[ ulIndex ] = pvPortMalloc( 32 );

	/* Return the frist removed block, which should join with the start block
	and leave a gap. */
	vPortFree( pvUsedBlocks[ 0 ] );
	
	/* Return the second free block, which should fill the gap. */
	vPortFree( pvUsedBlocks[ 1 ] );

	/* The heap should be back to its full size, which is the total bytes
	in the array minus the space taken up by the pxEnd structure. */
	configASSERT( xFreeBytesRemaining == ( xTotalHeapSize - heapSTRUCT_SIZE ) );

	/* The start block should now point to a block that holds the entire heap
	space, which should itself point to the end. */
	configASSERT( xStart.pxNextFreeBlock->xBlockSize == ( xTotalHeapSize - heapSTRUCT_SIZE ) );
	configASSERT( xStart.pxNextFreeBlock->pxNextFreeBlock == pxEnd );

	/* The next test plugs a gap that create a continuous block but not up to
	the end marker - it then fills the last gap too. */

	ulIndex = 0;

	/* Remove a small block. */
	pvUsedBlocks[ ulIndex ] = pvPortMalloc( 8 );
	configASSERT( xFreeBytesRemaining == ( xTotalHeapSize - heapSTRUCT_SIZE - 8 - heapSTRUCT_SIZE ) );
	ulIndex++;

	/* Remove another block. */
	pvUsedBlocks[ ulIndex ] = pvPortMalloc( 32 );
	ulIndex++;

	/* And one final block. */
	pvUsedBlocks[ ulIndex ] = pvPortMalloc( 128 );

	/* Return the frist removed block, which should join with the start block
	and leave a gap. */
	vPortFree( pvUsedBlocks[ 0 ] );

	/* Return the last block, which should join with the end. */
	vPortFree( pvUsedBlocks[ 2 ] );
	
	/* Return the middle block block, which should fill the gap. */
	vPortFree( pvUsedBlocks[ 1 ] );

	/* The heap should be back to its full size, which is the total bytes
	in the array minus the space taken up by the pxEnd structure. */
	configASSERT( xFreeBytesRemaining == ( xTotalHeapSize - heapSTRUCT_SIZE ) );

	/* The start block should now point to a block that holds the entire heap
	space, which should itself point to the end. */
	configASSERT( xStart.pxNextFreeBlock->xBlockSize == ( xTotalHeapSize - heapSTRUCT_SIZE ) );
	configASSERT( xStart.pxNextFreeBlock->pxNextFreeBlock == pxEnd );

	for( ulIndex = 0; ulIndex < 6; ulIndex++ )
	{
		pvUsedBlocks[ 0 ] = pvPortMalloc( 10 );
		pvUsedBlocks[ 1 ] = pvPortMalloc( 1 );
		pvUsedBlocks[ 2 ] = pvPortMalloc( 10000 );

		vPortFree( pvUsedBlocks[ ulCombinations[ ulIndex ][ 0 ] ] );
		vPortFree( pvUsedBlocks[ ulCombinations[ ulIndex ][ 1 ] ] );
		vPortFree( pvUsedBlocks[ ulCombinations[ ulIndex ][ 2 ] ] );

		/* The heap should be back to its full size, which is the total bytes
		in the array minus the space taken up by the pxEnd structure. */
		configASSERT( xFreeBytesRemaining == ( xTotalHeapSize - heapSTRUCT_SIZE ) );

		/* The start block should now point to a block that holds the entire heap
		space, which should itself point to the end. */
		configASSERT( xStart.pxNextFreeBlock->xBlockSize == ( xTotalHeapSize - heapSTRUCT_SIZE ) );
		configASSERT( xStart.pxNextFreeBlock->pxNextFreeBlock == pxEnd );
	}

	/* Do the same, but using the entire block of memory. */
	for( ulIndex = 0; ulIndex < 6; ulIndex++ )
	{
		/* Total heap size. */
		ulSize = xTotalHeapSize - heapSTRUCT_SIZE;

		/* Minus 4 heap structs (three allocated blocks plus pxEnd. */
		ulSize -= 4 * heapSTRUCT_SIZE;

		pvUsedBlocks[ 0 ] = pvPortMalloc( ulSize / 3 );
		pvUsedBlocks[ 1 ] = pvPortMalloc( ulSize / 3 );
		/* The last block includes any remainder. */
		pvUsedBlocks[ 2 ] = pvPortMalloc( ( ulSize / 3 ) + ( ulSize % 3 ) );
		configASSERT( pvUsedBlocks[ 2 ] );		
		configASSERT( xFreeBytesRemaining == 0 );

		vPortFree( pvUsedBlocks[ ulCombinations[ ulIndex ][ 0 ] ] );
		vPortFree( pvUsedBlocks[ ulCombinations[ ulIndex ][ 1 ] ] );
		vPortFree( pvUsedBlocks[ ulCombinations[ ulIndex ][ 2 ] ] );

		/* The heap should be back to its full size, which is the total bytes
		in the array minus the space taken up by the pxEnd structure. */
		configASSERT( xFreeBytesRemaining == ( xTotalHeapSize - heapSTRUCT_SIZE ) );

		/* The start block should now point to a block that holds the entire heap
		space, which should itself point to the end. */
		configASSERT( xStart.pxNextFreeBlock->xBlockSize == ( xTotalHeapSize - heapSTRUCT_SIZE ) );
		configASSERT( xStart.pxNextFreeBlock->pxNextFreeBlock == pxEnd );
	}

	/* Do the same, but using random block sizes. */
	for( ulRandSample = 0; ulRandSample < 0x5ffff; ulRandSample++ )
	{
		for( ulIndex = 0; ulIndex < 6; ulIndex++ )
		{
			pvUsedBlocks[ 0 ] = pvPortMalloc( rand() );
			pvUsedBlocks[ 1 ] = pvPortMalloc( rand() );
			pvUsedBlocks[ 2 ] = pvPortMalloc( rand() );

			vPortFree( pvUsedBlocks[ ulCombinations[ ulIndex ][ 0 ] ] );
			vPortFree( pvUsedBlocks[ ulCombinations[ ulIndex ][ 1 ] ] );
			vPortFree( pvUsedBlocks[ ulCombinations[ ulIndex ][ 2 ] ] );

			/* The heap should be back to its full size, which is the total bytes
			in the array minus the space taken up by the pxEnd structure. */
			configASSERT( xFreeBytesRemaining == ( xTotalHeapSize - heapSTRUCT_SIZE ) );

			/* The start block should now point to a block that holds the entire heap
			space, which should itself point to the end. */
			configASSERT( xStart.pxNextFreeBlock->xBlockSize == ( xTotalHeapSize - heapSTRUCT_SIZE ) );
			configASSERT( xStart.pxNextFreeBlock->pxNextFreeBlock == pxEnd );
		}
	}

/* Particularly test the case where the block being inserted fills a gap 
requiring both the block in front and the block behind to be merged into one. */
}

#endif INCLUDE_TEST_CODE
