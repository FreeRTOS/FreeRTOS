/*
 * File:	start.c
 * Purpose:	Kinetis start up routines. 
 *
 * Notes:		
 */

#include "start.h"
#include "common.h"
#include "wdog.h"
#include "sysinit.h"

/********************************************************************/
/*!
 * \brief   Kinetis Start
 * \return  None
 *
 * This function calls all of the needed starup routines and then 
 * branches to the main process.
 */
void start(void)
{
	/* Disable the watchdog timer */
	wdog_disable();

	/* Copy any vector or data sections that need to be in RAM */
	common_startup();

	/* Perform processor initialization */
	sysinit();
        
    /* Determine the flash revision */
    flash_identify();    

	/* Jump to main process */
	main();

	/* No actions to perform after this so wait forever */
	while(1);
}
/********************************************************************/
/*!
 * \brief   flash Identify
 * \return  None
 *
 * This is primarly a reporting function that displays information
 * about the specific flash parameters and flash version ID for 
 * the current device. These parameters are obtained using a special
 * flash command call "read resource." The first four bytes returned
 * are the flash parameter revision, and the second four bytes are
 * the flash version ID.
 */
void flash_identify (void)
{
    /* Get the flash parameter version */

    /* Write the flash FCCOB registers with the values for a read resource command */
    FTFL_FCCOB0 = 0x03;
    FTFL_FCCOB1 = 0x00;
    FTFL_FCCOB2 = 0x00;
    FTFL_FCCOB3 = 0x00;
    FTFL_FCCOB8 = 0x01;

    /* All required FCCOBx registers are written, so launch the command */
    FTFL_FSTAT = FTFL_FSTAT_CCIF_MASK;

    /* Wait for the command to complete */
    while(!(FTFL_FSTAT & FTFL_FSTAT_CCIF_MASK));
    
    /* Get the flash version ID */   

    /* Write the flash FCCOB registers with the values for a read resource command */
    FTFL_FCCOB0 = 0x03;
    FTFL_FCCOB1 = 0x00;
    FTFL_FCCOB2 = 0x00;
    FTFL_FCCOB3 = 0x04;
    FTFL_FCCOB8 = 0x01;

    /* All required FCCOBx registers are written, so launch the command */
    FTFL_FSTAT = FTFL_FSTAT_CCIF_MASK;

    /* Wait for the command to complete */
    while(!(FTFL_FSTAT & FTFL_FSTAT_CCIF_MASK));
}
/********************************************************************/

