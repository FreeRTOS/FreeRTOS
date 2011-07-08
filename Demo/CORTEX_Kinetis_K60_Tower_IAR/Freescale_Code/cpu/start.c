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
        
    printf("\n\n");
	
	/* Determine the last cause(s) of reset */
	if (MC_SRSH & MC_SRSH_SW_MASK)
		printf("Software Reset\n");
	if (MC_SRSH & MC_SRSH_LOCKUP_MASK)
		printf("Core Lockup Event Reset\n");
	if (MC_SRSH & MC_SRSH_JTAG_MASK)
		printf("JTAG Reset\n");
	
	if (MC_SRSL & MC_SRSL_POR_MASK)
		printf("Power-on Reset\n");
	if (MC_SRSL & MC_SRSL_PIN_MASK)
		printf("External Pin Reset\n");
	if (MC_SRSL & MC_SRSL_COP_MASK)
		printf("Watchdog(COP) Reset\n");
	if (MC_SRSL & MC_SRSL_LOC_MASK)
		printf("Loss of Clock Reset\n");
	if (MC_SRSL & MC_SRSL_LVD_MASK)
		printf("Low-voltage Detect Reset\n");
	if (MC_SRSL & MC_SRSL_WAKEUP_MASK)
		printf("LLWU Reset\n");	
	

	/* Determine specific Kinetis device and revision */
	cpu_identify();
	
	/* Jump to main process */
	main();

	/* No actions to perform after this so wait forever */
	while(1);
}
/********************************************************************/
/*!
 * \brief   Kinetis Identify
 * \return  None
 *
 * This is primarly a reporting function that displays information
 * about the specific CPU to the default terminal including:
 * - Kinetis family
 * - package
 * - die revision
 * - P-flash size
 * - Ram size
 */
void cpu_identify (void)
{
    /* Determine the Kinetis family */
    switch((SIM_SDID & SIM_SDID_FAMID(0x7))>>SIM_SDID_FAMID_SHIFT) 
    {  
    	case 0x0:
    		printf("\nK10-");
    		break;
    	case 0x1:
    		printf("\nK20-");
    		break;
    	case 0x2:
    		printf("\nK30-");
    		break;
    	case 0x3:
    		printf("\nK40-");
    		break;
    	case 0x4:
    		printf("\nK60-");
    		break;
    	case 0x5:
    		printf("\nK70-");
    		break;
    	case 0x6:
    		printf("\nK50-");
    		break;
    	case 0x7:
    		printf("\nK53-");
    		break;
	default:
		printf("\nUnrecognized Kinetis family device.\n");  
		break;  	
    }

    /* Determine the package size */
    switch((SIM_SDID & SIM_SDID_PINID(0xF))>>SIM_SDID_PINID_SHIFT) 
    {  
    	case 0x2:
    		printf("32pin       ");
    		break;
    	case 0x4:
    		printf("48pin       ");
    		break;
    	case 0x5:
    		printf("64pin       ");
    		break;
    	case 0x6:
    		printf("80pin       ");
    		break;
    	case 0x7:
    		printf("81pin       ");
    		break;
    	case 0x8:
    		printf("100pin      ");
    		break;
    	case 0x9:
    		printf("104pin      ");
    		break;
    	case 0xA:
    		printf("144pin      ");
    		break;
    	case 0xC:
    		printf("196pin      ");
    		break;
    	case 0xE:
    		printf("256pin      ");
    		break;
	default:
		printf("\nUnrecognized Kinetis package code.      ");  
		break;  	
    }                

    /* Determine the revision ID */
    printf("Silicon rev %d     \n", (SIM_SDID & SIM_SDID_REVID(0xF))>>SIM_SDID_REVID_SHIFT);
    
    
    /* Determine the flash revision */
    flash_identify();    
    
    /* Determine the P-flash size */
    switch((SIM_FCFG1 & SIM_FCFG1_FSIZE(0xFF))>>SIM_FCFG1_FSIZE_SHIFT)
    {
    	case 0x0:
    		printf("12 kBytes of P-flash	");
    		break;
    	case 0x1:
    		printf("16 kBytes of P-flash	");
    		break;
    	case 0x2:
    		printf("32 kBytes of P-flash	");
    		break;
    	case 0x3:
    		printf("48 kBytes of P-flash	");
    		break;
    	case 0x4:
    		printf("64 kBytes of P-flash	");
    		break;
    	case 0x5:
    		printf("96 kBytes of P-flash	");
    		break;
    	case 0x6:
    		printf("128 kBytes of P-flash	");
    		break;
    	case 0x7:
    		printf("192 kBytes of P-flash	");
    		break;
    	case 0x8:
    		printf("256 kBytes of P-flash	");
    		break;
    	case 0x9:
    		printf("320 kBytes of P-flash	");
    		break;
    	case 0xA:
    		printf("384 kBytes of P-flash	");
    		break;
    	case 0xB:
    		printf("448 kBytes of P-flash	");
    		break;
    	case 0xC:
    		printf("512 kBytes of P-flash	");
    		break;
    	case 0xFF:
    		printf("Full size P-flash	");
    		break;
		default:
			printf("ERR!! Undefined P-flash size\n");  
			break;  		
    }

    /* Determine the RAM size */
    switch((SIM_SOPT1 & SIM_SOPT1_RAMSIZE(0xF))>>SIM_SOPT1_RAMSIZE_SHIFT)
    {
    	case 0x5:
    		printf(" 32 kBytes of RAM\n\n");
    		break;
    	case 0x7:
    		printf(" 64 kBytes of RAM\n\n");
    		break;
    	case 0x8:
    		printf(" 96 kBytes of RAM\n\n");
    		break;
    	case 0x9:
    		printf(" 128 kBytes of RAM\n\n");
    		break;
		default:
			printf(" ERR!! Undefined RAM size\n\n");  
			break;  		
    }
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
    
    printf("Flash parameter version %d.%d.%d.%d\n",FTFL_FCCOB4,FTFL_FCCOB5,FTFL_FCCOB6,FTFL_FCCOB7);

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

    printf("Flash version ID %d.%d.%d.%d\n",FTFL_FCCOB4,FTFL_FCCOB5,FTFL_FCCOB6,FTFL_FCCOB7);  
}
/********************************************************************/

