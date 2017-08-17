#warning Temoporary file and a dependent on the Zynq network interface.

/*
 * uncached_memory.c
 *
 * This module will declare 1 MB of memory and switch off the caching for it.
 *
 * pucGetUncachedMemory( ulSize ) returns a trunc of this memory with a length
 * rounded up to a multiple of 4 KB
 *
 * ucIsCachedMemory( pucBuffer ) returns non-zero if a given pointer is NOT
 * within the range of the 1 MB non-cached memory.
 *
 */

/*
 * After "_end", 1 MB of uncached memory will be allocated for DMA transfers.
 * Both the DMA descriptors as well as all EMAC TX-buffers will be allocated in
 * uncached memory.
 */

#include "Zynq/x_emacpsif.h"
#include "Zynq/x_topology.h"
#include "xstatus.h"

#include "xparameters.h"
#include "xparameters_ps.h"
#include "xil_exception.h"
#include "xil_mmu.h"

#include "FreeRTOS.h"

#include "uncached_memory.h"

#include "Demo_Logging.h"

#define UNCACHED_MEMORY_SIZE	0x100000ul

#define DDR_MEMORY_END	(XPAR_PS7_DDR_0_S_AXI_HIGHADDR+1)

static void vInitialiseUncachedMemory( void );

static uint8_t *pucHeadOfMemory;
static uint32_t ulMemorySize;
static uint8_t *pucStartOfMemory = NULL;

uint8_t ucIsCachedMemory( const uint8_t *pucBuffer )
{
uint8_t ucReturn;

	if( ( pucStartOfMemory != NULL ) &&
		( pucBuffer >= pucStartOfMemory ) &&
		( pucBuffer < ( pucStartOfMemory + UNCACHED_MEMORY_SIZE ) ) )
	{
		ucReturn = pdFALSE;
	}
	else
	{
		ucReturn = pdTRUE;
	}

	return ucReturn;
}

uint8_t *pucGetUncachedMemory( uint32_t ulSize )
{
uint8_t *pucReturn;

	if( pucStartOfMemory == NULL )
	{
		vInitialiseUncachedMemory( );
	}
	if( ( pucStartOfMemory == NULL ) || ( ulSize > ulMemorySize ) )
	{
		pucReturn = NULL;
	}
	else
	{
	uint32_t ulSkipSize;

		pucReturn = pucHeadOfMemory;
		ulSkipSize = ( ulSize + 0x1000ul ) & ~0xffful;
		pucHeadOfMemory += ulSkipSize;
		ulMemorySize -= ulSkipSize;
	}

	return pucReturn;
}

extern u8 _end;

static void vInitialiseUncachedMemory( )
{
	/* At the end of program's space... */
	pucStartOfMemory = (uint8_t *) &_end;
	/*
	 * Align the start address to 1 MB boundary.
	 */
	pucStartOfMemory = (uint8_t *)( ( ( uint32_t )pucStartOfMemory + UNCACHED_MEMORY_SIZE ) & ( ~( UNCACHED_MEMORY_SIZE - 1 ) ) );

	if( ( ( u32 )pucStartOfMemory ) + UNCACHED_MEMORY_SIZE > DDR_MEMORY_END )
	{
		vLoggingPrintf("vInitialiseUncachedMemory: Can not allocate uncached memory\n" );
	}
	else
	{
		/*
		 * Some objects want to be stored in uncached memory. Hence the 1 MB
		 * address range that starts after "_end" is made uncached
		 * by setting appropriate attributes in the translation table.
		 */
		Xil_SetTlbAttributes( ( uint32_t )pucStartOfMemory, 0xc02 ); // addr, attr

		/* For experiments in the SDIO driver, make the remaining uncached memory public */
		pucHeadOfMemory = pucStartOfMemory;
		ulMemorySize = UNCACHED_MEMORY_SIZE;
		memset( pucStartOfMemory, '\0', UNCACHED_MEMORY_SIZE );
	}
}
