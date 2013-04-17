/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of
* this software. By using this software, you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name	   : resetprg.c
* Device(s)    : RX111
* Description  : Defines post-reset routines that are used to configure the MCU prior to the main program starting.
*                This is were the program counter starts on power-up or reset.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.11.2012 0.01     Beta Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Defines machine level functions used in this file */
#include    <machine.h>
/* Defines MCU configuration functions used in this file */
#include    <_h_c_lib.h>
/* Defines standard variable types used in this file */
#include    <stdbool.h>
#include    <stdint.h>

/* This macro is here so that the stack will be declared here. This is used to prevent multiplication of stack size. */
#define     BSP_DECLARE_STACK
/* Define the target platform */
#include    "platform.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define PSW_init  (0x00030000)

/***********************************************************************************************************************
Pre-processor Directives
***********************************************************************************************************************/
/* Declare the contents of the function 'Change_PSW_PM_to_UserMode' as assembler to the compiler */
#pragma inline_asm Change_PSW_PM_to_UserMode

/* Set this as the entry point from a power-on reset */
#pragma entry PowerON_Reset_PC

/***********************************************************************************************************************
External function Prototypes
***********************************************************************************************************************/
/* Functions to setup I/O library */
extern void _INIT_IOLIB(void);
extern void _CLOSEALL(void);

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
/* Power-on reset function declaration */
void PowerON_Reset_PC(void);

#if RUN_IN_USER_MODE==1
    #if __RENESAS_VERSION__ < 0x01010000
    /* MCU usermode switcher function declaration */
    static void Change_PSW_PM_to_UserMode(void);
    #endif
#endif

/* Main program function delcaration */
void main(void);
static void operating_frequency_set(void);
static void clock_source_select(void);

/***********************************************************************************************************************
* Function name: PowerON_Reset_PC
* Description  : This function is the MCU's entry point from a power-on reset.
*                The following steps are taken in the startup code:
*                1. The User Stack Pointer (USP) and Interrupt Stack Pointer (ISP) are both set immediately after entry
*                   to this function. The USP and ISP stack sizes are set in the file stacksct.h.
*                   Default sizes are USP=4K and ISP=1K.
*                2. The interrupt vector base register is set to point to the beginning of the relocatable interrupt
*                   vector table.
*                3. The MCU is setup for floating point operations by setting the initial value of the Floating Point
*                   Status Word (FPSW).
*                4. The MCU operating frequency is set by configuring the Clock Generation Circuit (CGC) in
*                   operating_frequency_set.
*                5. Calls are made to functions to setup the C runtime environment which involves initializing all
*                   initialed data, zeroing all uninitialized variables, and configuring STDIO if used
*                   (calls to _INITSCT and _INIT_IOLIB).
*                6. Board-specific hardware setup, including configuring I/O pins on the MCU, in hardware_setup.
*                7. Global interrupts are enabled by setting the I bit in the Program Status Word (PSW), and the stack
*                   is switched from the ISP to the USP.  The initial Interrupt Priority Level is set to zero, enabling
*                   any interrupts with a priority greater than zero to be serviced.
*                8. The processor is optionally switched to user mode.  To run in user mode, set the macro
*                   RUN_IN_USER_MODE above to a 1.
*                9. The bus error interrupt is enabled to catch any accesses to invalid or reserved areas of memory.
*
*                Once this initialization is complete, the user's main() function is called.  It should not return.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
#pragma section ResetPRG		// output PowerON_Reset to PResetPRG section
void PowerON_Reset_PC(void)
{
    /* Stack pointers are setup prior to calling this function - see comments above */

    /* Initialise the MCU processor word */
#if __RENESAS_VERSION__ >= 0x01010000
    set_intb((void *)__sectop("C$VECT"));
#else
    set_intb((unsigned long)__sectop("C$VECT"));
#endif

#ifdef NMI_ISR_CALLBACK
    /* Enable NMI interrupt if callback is configured in r_bsp_config.h */
    ICU.NMIER.BIT.NMIEN = 1;
#endif

    /* Switch to high-speed operation */
    operating_frequency_set();

    /* Initialize C runtime environment */
    _INITSCT();

#if IO_LIB_ENABLE == 1
    /* Comment this out if not using I/O lib */
    _INIT_IOLIB();
#endif

    /* Configure the MCU and YRDK hardware */
    hardware_setup();

    /* Change the MCU's usermode from supervisor to user */
    nop();
    set_psw(PSW_init);
#if RUN_IN_USER_MODE==1
    /* Use chg_pmusr() intrinsic if possible. */
    #if __RENESAS_VERSION__ >= 0x01010000
    chg_pmusr() ;
    #else
    Change_PSW_PM_to_UserMode();
    #endif
#endif

    /* Enable the bus error interrupt to catch accesses to illegal/reserved areas of memory */
    /* The ISR for this interrupt can be found in vecttbl.c in the function "bus_error_isr" */
    /* Clear any pending interrupts */
    IR(BSC,BUSERR) = 0;
    /* Make this the highest priority interrupt (adjust as necessary for your application */
    IPR(BSC,BUSERR) = 0x0F;
    /* Enable the interrupt in the ICU*/
    IEN(BSC,BUSERR) = 1;
    /* Enable illegal address interrupt in the BSC */
    BSC.BEREN.BIT.IGAEN = 1;

    /* Call the main program function (should not return) */
    main();

#if IO_LIB_ENABLE == 1
    /* Comment this out if not using I/O lib - cleans up open files */
    _CLOSEALL();
#endif

    while(1)
    {
        /* Infinite loop. Put a breakpoint here if you want to catch an exit of main(). */
    }
}

/***********************************************************************************************************************
* Function name: operating_frequency_set
* Description  : Configures the clock settings for each of the device clocks
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void operating_frequency_set(void)
{
    /* Used for constructing value to write to SCKCR and CKOCR registers. */
    uint32_t temp_clock = 0;

    /*
    Clock Description              Frequency
    ----------------------------------------
    Input Clock Frequency............  16 MHz
    PLL frequency (x3)...............  48 MHz
    Internal Clock Frequency.........  24 MHz
    Peripheral Clock Frequency.......  24 MHz
    Clock Out Frequency..............  1  MHz */

    volatile unsigned int i;

    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA50B;

    /* Select the clock based upon user's choice. */
    clock_source_select();


    /* Figure out setting for FCK bits. */
#if   FCK_DIV == 1
    /* Do nothing since FCK bits should be 0. */
#elif FCK_DIV == 2
    temp_clock |= 0x10000000;
#elif FCK_DIV == 4
    temp_clock |= 0x20000000;
#elif FCK_DIV == 8
    temp_clock |= 0x30000000;
#elif FCK_DIV == 16
    temp_clock |= 0x40000000;
#elif FCK_DIV == 32
    temp_clock |= 0x50000000;
#elif FCK_DIV == 64
    temp_clock |= 0x60000000;
#else
    #error "Error! Invalid setting for FCK_DIV in r_bsp_config.h"
#endif

    /* Figure out setting for ICK bits. */
#if   ICK_DIV == 1
    /* Do nothing since ICK bits should be 0. */
#elif ICK_DIV == 2
    temp_clock |= 0x01000000;
#elif ICK_DIV == 4
    temp_clock |= 0x02000000;
#elif ICK_DIV == 8
    temp_clock |= 0x03000000;
#elif ICK_DIV == 16
    temp_clock |= 0x04000000;
#elif ICK_DIV == 32
    temp_clock |= 0x05000000;
#elif ICK_DIV == 64
    temp_clock |= 0x06000000;
#else
    #error "Error! Invalid setting for ICK_DIV in r_bsp_config.h"
#endif

    /* Figure out setting for PCKB bits. */
#if   PCKB_DIV == 1
    /* Do nothing since PCKB bits should be 0. */
#elif PCKB_DIV == 2
    temp_clock |= 0x00000100;
#elif PCKB_DIV == 4
    temp_clock |= 0x00000200;
#elif PCKB_DIV == 8
    temp_clock |= 0x00000300;
#elif PCKB_DIV == 16
    temp_clock |= 0x00000400;
#elif PCKB_DIV == 32
    temp_clock |= 0x00000500;
#elif PCKB_DIV == 64
    temp_clock |= 0x00000600;
#else
    #error "Error! Invalid setting for PCKB_DIV in r_bsp_config.h"
#endif

    /* Figure out setting for PCKD bits. */
#if   PCKD_DIV == 1
    /* Do nothing since PCKD bits should be 0. */
#elif PCKD_DIV == 2
    temp_clock |= 0x00000001;
#elif PCKD_DIV == 4
    temp_clock |= 0x00000002;
#elif PCKD_DIV == 8
    temp_clock |= 0x00000003;
#elif PCKD_DIV == 16
    temp_clock |= 0x00000004;
#elif PCKD_DIV == 32
    temp_clock |= 0x00000005;
#elif PCKD_DIV == 64
    temp_clock |= 0x00000006;
#else
    #error "Error! Invalid setting for PCKD_DIV in r_bsp_config.h"
#endif

    /* Set SCKCR register. */
    SYSTEM.SCKCR.LONG = temp_clock;

    /* Choose clock source. Default for r_bsp_config.h is PLL. */
    SYSTEM.SCKCR3.WORD = ((uint16_t)CLOCK_SOURCE) << 8;

    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;
}

/***********************************************************************************************************************
* Function name: clock_source_select
* Description  : Enables and disables clocks as chosen by the user. This function also implements the software delays
*                needed for the clocks to stabilize.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void clock_source_select (void)
{
    /* Declared volatile for software delay purposes. */
    volatile unsigned int i;

    /* NOTE: AS OF VERSION 0.50 OF THE RX111 HARDWARE MANUAL, ALL OF THE CLOCK
     * STABILIZATION TIMES ARE TBD. FOR NOW, WHERE EVER A WAIT COUNT REGISTER
     * IS AVAILABLE, THE DELAY IS SET TO THE MAX NUMBER OF CYCLES. WHERE EVER
     * DELAY LOOPS ARE PRESENT, THE VALUES FROM THE 63N ARE RE-USED. KEEP IN
     * MIND THAT THE 63N RUNS ON A FASTER CRYSTAL.
     */

#if (CLOCK_SOURCE == 1)
    /* HOCO is chosen. Start it operating. */
    SYSTEM.HOCOCR.BYTE = 0x00;
    /* The delay period needed is to make sure that the HOCO has stabilized.*/
    for(i = 0; i< 28; i++)			// tHOCOWT2 is TBD
    {
        nop() ;
    }
#else
    /* HOCO is not chosen. Stop the HOCO. */
    SYSTEM.HOCOCR.BYTE = 0x01;
#endif

#if (CLOCK_SOURCE == 2)
    /* Main clock oscillator is chosen. Start it operating. */
    SYSTEM.MOSCWTCR.BYTE = 0x07;	// Wait 65,536 cycles
    /* Set the main clock to operating. */
    SYSTEM.MOSCCR.BYTE = 0x00;
    /* The delay period needed is to make sure that the main clock has stabilized. */
    for(i = 0; i< 140; i++)			// tMAINOSCWT is TBD
    {
        nop() ;
    }
#endif

#if (CLOCK_SOURCE == 3)
    /* Sub-clock oscillator is chosen. Start it operating. */
    /* In section 9.8.4, there is a reference to a SOSCWTCR register, but there is no
     * description for this register in the manual nor reference for it in iodefine.h. */

    /* Set the sub-clock to operating. */
    SYSTEM.SOSCCR.BYTE = 0x00;
    /* The delay period needed is to make sure that the sub-clock has stabilized. */
    for(i = 0; i< 30233; i++)		// tSUBOSCWT0 is TBD
    {
        nop() ;
    }
#else
    /* Set the sub-clock to stopped. */
    SYSTEM.SOSCCR.BYTE = 0x01;
#endif

#if (CLOCK_SOURCE == 4)
    /* PLL is chosen. Start it operating. Must start main clock as well since PLL uses it. */
    SYSTEM.MOSCWTCR.BYTE = 0x07;	// Wait 65,536 cycles
    /* Set the main clock to operating. */
    SYSTEM.MOSCCR.BYTE = 0x00;

    /* Set PLL Input Divisor. */
    SYSTEM.PLLCR.BIT.PLIDIV = PLL_DIV >> 1;

    /* Set PLL Multiplier. */
    SYSTEM.PLLCR.BIT.STC = (PLL_MUL * 2) - 1;

    /* Set the PLL to operating. */
    SYSTEM.PLLCR2.BYTE = 0x00;
    /* The delay period needed is to make sure that the main clock and PLL have stabilized. */
    for(i = 0; i< 140; i++)			// tPLLWT2 is TBD
    {
        nop() ;
    }
#endif

    /* LOCO is saved for last since it is what is running by default out of reset. This means you do not want to turn
       it off until another clock has been enabled and is ready to use. */
#if (CLOCK_SOURCE == 0)
    /* LOCO is chosen. This is the default out of reset. */
    SYSTEM.LOCOCR.BYTE = 0x00;
#else
    /* LOCO is not chosen and another clock has already been setup. Turn off the LOCO. */
    SYSTEM.LOCOCR.BYTE = 0x01;
#endif

    /* Make sure a valid clock was chosen. */
#if (CLOCK_SOURCE > 4) || (CLOCK_SOURCE < 0)
    #error "ERROR - Valid clock source must be chosen in r_bsp_config.h using CLOCK_SOURCE macro."
#endif
}


/***********************************************************************************************************************
* Function name: Change_PSW_PM_to_UserMode
* Description  : Assembler function, used to change the MCU's usermode from supervisor to user.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
#if RUN_IN_USER_MODE==1
    #if __RENESAS_VERSION__ < 0x01010000
static void Change_PSW_PM_to_UserMode(void)
{
    MVFC   PSW,R1
    OR     #00100000h,R1
    PUSH.L R1
    MVFC   PC,R1
    ADD    #10,R1
    PUSH.L R1
    RTE
    NOP
    NOP
}
    #endif
#endif
