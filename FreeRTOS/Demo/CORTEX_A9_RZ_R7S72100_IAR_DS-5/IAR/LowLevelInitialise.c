/*************************************************************************
 *
 *   Used with ICCARM and AARM.
 *
 *    (c) Copyright IAR Systems 2013
 *
 *    File name   : main.c
 *    Description : main module
 **************************************************************************/

/*
 * Called from Cstart.s to configure the chip and board specific IO before
 * main() is called.
 */

/** include files **/
#include <Renesas/ior7s721000.h>
#include <intrinsics.h>
#include <stdint.h>
#include "armv7a_cp15_drv.h"
#include "devdrv_common.h"

/* Renesas include files. */
#include "stb_init.h"
#include "port_init.h"
#include "devdrv_intc.h"


/** external data **/
#pragma section = ".intvec"

extern void Peripheral_BasicInit( void );
void LowLevelInitialisation(void);
unsigned long __write(int fildes, const void *buf, unsigned long nbytes);

/* Called from cstartup.s before the kernel is started. */
void LowLevelInitialisation(void)
{
	/* Chip configuration functions from IAR. ********************************/
	/* Disable MMU, enable ICache */
	CP15_Mmu(FALSE);
	CP15_ICache(FALSE);
	CP15_SetVectorBase( (uint32_t )__section_begin( ".intvec" ) );

	/* Set Low vectors mode in CP15 Control Register */
	CP15_SetHighVectors(FALSE);


	/* Chip and board specific configuration functions from Renesas. *********/
	Peripheral_BasicInit();
	STB_Init();
	PORT_Init();
    R_BSC_Init( ( uint8_t ) ( BSC_AREA_CS2 | BSC_AREA_CS3 ) );
    R_INTC_Init();


	CP15_ICache(TRUE);

	/* Start with interrupts enabled. */
    __enable_irq();
    __enable_fiq();
}

/* Keep the linker happy. */
unsigned long __write(int fildes, const void *buf, unsigned long nbytes)
{
	return 0;
}
