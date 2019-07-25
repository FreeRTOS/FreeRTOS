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
* File Name	   : hwsetup.c
* Device(s)    : RX
* H/W Platform : RSKRX210
* Description  : Defines the initialization routines used each time the MCU is restarted.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.11.2012 0.01     Beta Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* I/O Register and board definitions */
#include "platform.h"
#include "r_switches_if.h"
/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
/* MCU I/O port configuration function delcaration */
static void output_ports_configure(void);

/* Interrupt configuration function delcaration */
static void interrupts_configure(void);

/* MCU peripheral module configuration function declaration */
static void peripheral_modules_enable(void);

/* Configure MCU clocks. */
static void clock_source_select (void);
void operating_frequency_set(void);

/***********************************************************************************************************************
* Function name: hardware_setup
* Description  : Contains setup functions called at device restart
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void vHardwareSetup(void)
{
	operating_frequency_set();
    output_ports_configure();
    interrupts_configure();
    peripheral_modules_enable();
}

/***********************************************************************************************************************
* Function name: output_ports_configure
* Description  : Configures the port and pin direction settings, and sets the pin outputs to a safe level.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void output_ports_configure(void)
{
    /* Enable LEDs. */
    /* Start with LEDs off. */
    LED0 = LED_OFF;
    LED1 = LED_OFF;
    LED2 = LED_OFF;
    LED3 = LED_OFF;

    /* Set LED pins as outputs. */
    LED0_PDR = 1;
    LED1_PDR = 1;
    LED2_PDR = 1;
    LED3_PDR = 1;

    /* Enable switches. */
    /* Set pins as inputs. */
    SW1_PDR = 0;
    SW2_PDR = 0;
    SW3_PDR = 0;

    /* Set port mode registers for switches. */
    SW1_PMR = 0;
    SW2_PMR = 0;
    SW3_PMR = 0;

    /* Unlock MPC registers to enable writing to them. */
    MPC.PWPR.BIT.B0WI = 0 ;     /* Unlock protection register */
    MPC.PWPR.BIT.PFSWE = 1 ;    /* Unlock MPC registers */

    /* TXD1 is output. */
    PORT1.PDR.BIT.B6 = 1;
    PORT1.PMR.BIT.B6 = 1;
    MPC.P16PFS.BYTE  = 0x0A;
    /* RXD1 is input. */
    PORT1.PDR.BIT.B5 = 0;
    PORT1.PMR.BIT.B5 = 1;
    MPC.P15PFS.BYTE  = 0x0A;

    /* Configure the pin connected to the ADC Pot as an input */
    PORT4.PDR.BIT.B4 = 0;

    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA50B;

    /* Turn off module stop for the A2D converter. */
    SYSTEM.MSTPCRA.BIT.MSTPA17 = 0;

    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;

    /* Initialise the first button to generate an interrupt. */
    R_SWITCHES_Init();
}

/***********************************************************************************************************************
* Function name: interrupts_configure
* Description  : Configures interrupts used
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void interrupts_configure(void)
{
    /* Add code here to setup additional interrupts */
}

/***********************************************************************************************************************
* Function name: peripheral_modules_enable
* Description  : Enables and configures peripheral devices on the MCU
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void peripheral_modules_enable(void)
{
	/* Enable triggers to start an ADC conversion. */
	S12AD.ADCSR.BIT.TRGE = 1;

	/* Only channel 4 is going to be used. */
	S12AD.ADANSA.BIT.ANSA4 = 1;
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
        __asm volatile( "NOP" );
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
        __asm volatile( "NOT" );
    }
#endif

#if (CLOCK_SOURCE == 3)
    /* Sub-clock oscillator is chosen. Start it operating. */
    /* In section 9.8.4, there is a reference to a SOSCWTCR register, but there is no
     * description for this register in the manual nor reference for it in iorx111.h. */

    /* Set the sub-clock to operating. */
    SYSTEM.SOSCCR.BYTE = 0x00;
    /* The delay period needed is to make sure that the sub-clock has stabilized. */
    for(i = 0; i< 30233; i++)		// tSUBOSCWT0 is TBD
    {
        __asm volatile( "NOP" );
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
        __asm volatile( "NOP" );
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


