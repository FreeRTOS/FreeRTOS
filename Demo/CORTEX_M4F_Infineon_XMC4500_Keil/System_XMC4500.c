/**************************************************************************//**
 * @file     system_XMC4500.h
 * @brief    CMSIS Cortex-M4 Device Peripheral Access Layer Header File
 *           for the Infineon XMC4500 Device Series
 * @version  V2.1
 * @date     20. December 2011
 *
 * @note
 * Copyright (C) 2011 ARM Limited. All rights reserved.
 *
 * @par
 * ARM Limited (ARM) is supplying this software for use with Cortex-M 
 * processor based microcontrollers.  This file can be freely distributed 
 * within development tools that are supporting such ARM based processors. 
 *
 * @par
 * THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
 * OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
 * ARM SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
 * CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
 *
 ******************************************************************************/

#include "System_XMC4500.h"
#include <XMC4500.h>

/*----------------------------------------------------------------------------
  Define clocks	is located in System_XMC4500.h
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
uint32_t SystemCoreClock = CLOCK_OSC_HP;/*!< System Clock Frequency (Core Clock)*/


/*----------------------------------------------------------------------------
  static functions declarations
 *----------------------------------------------------------------------------*/
static int SystemClockSetup(void);
static void USBClockSetup(void);

/*----------------------------------------------------------------------------
  Keil pragma to prevent warnings
 *----------------------------------------------------------------------------*/
#pragma diag_suppress 177


/*
//-------- <<< Use Configuration Wizard in Context Menu >>> ------------------
*/



/*--------------------- Watchdog Configuration -------------------------------
//
// <e> Watchdog Configuration
//     <o1.0> Disable Watchdog
//
// </e>
*/
#define WDT_SETUP               1
#define WDTENB_nVal             0x00000001

/*--------------------- CLOCK Configuration -------------------------------
//
// <e> Main Clock Configuration
//     <o1.0..1> CPU clock divider
//                     <0=> fCPU = fSYS 
//                     <1=> fCPU = fSYS / 2
//     <o2.0..1>  Peripheral Bus clock divider
//                     <0=> fPB	= fCPU
//                     <1=> fPB	= fCPU / 2
//     <o3.0..1>  CCU Bus clock divider
//                     <0=> fCCU = fCPU
//                     <1=> fCCU = fCPU / 2
//
// </e>
// 
*/

#define SCU_CLOCK_SETUP               1
#define	SCU_CPUCLKCR_DIV		0x00000000
#define	SCU_PBCLKCR_DIV		    0x00000000
#define	SCU_CCUCLKCR_DIV		0x00000000



/*--------------------- USB CLOCK Configuration ---------------------------
//
// <e> USB Clock Configuration
//
// </e>
// 
*/

#define SCU_USB_CLOCK_SETUP              0


/*--------------------- CLOCKOUT Configuration -------------------------------
//
// <e> Clock OUT Configuration
//     <o1.0..1>   Clockout Source Selection
//                     <0=> System Clock
//                     <2=> USB Clock
//                     <3=> Divided value of PLL Clock
//     <o2.0..1>   Clockout Pin Selection
//                     <0=> P1.15
//                     <1=> P0.8
//                     
//
// </e>
// 
*/

#define SCU_CLOCKOUT_SETUP               0
#define	SCU_CLOCKOUT_SOURCE		0x00000000
#define	SCU_CLOCKOUT_PIN		0x00000000




/**
  * @brief  Setup the microcontroller system.
  *         Initialize the PLL and update the 
  *         SystemCoreClock variable.
  * @param  None
  * @retval None
  */
void SystemInit(void)
{
/* Setup the WDT */
  #if WDT_SETUP
  WDT->CTR &= ~WDTENB_nVal; 
  #endif

/* enable coprocessor FPU */
  #if (__FPU_PRESENT == 1) && (__FPU_USED == 1)
  SCB->CPACR |= ((3UL << 10*2) |                 /* set CP10 Full Access */
                 (3UL << 11*2)  );               /* set CP11 Full Access */
  #endif

/* Disable branch prediction - PCON.PBS = 1 */
  PREF->PCON |= (PREF_PCON_PBS_Msk << PREF_PCON_PBS_Pos);

/* Setup the clockout */
  #if SCU_CLOCKOUT_SETUP
  SCU_CLK->EXTCLKCR	|= SCU_CLOCKOUT_SOURCE;
  if (SCU_CLOCKOUT_PIN) {
	  					PORT0->IOCR8 = 0x00000088;   /*P0.8 --> ALT1 select +  HWSEL */
					    PORT0->HWSEL &= (~PORT0_HWSEL_HW8_Msk);
						}
  else PORT1->IOCR12 = 0x88000000;                    /*P1.15--> ALT1 select */
  #endif

/* Setup the System clock */ 
  #if SCU_CLOCK_SETUP
  SystemClockSetup();
  #endif

/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
  SystemCoreClock = SYSTEM_FREQUENCY;/*!< System Clock Frequency (Core Clock)*/

/* Setup the USB PL */ 
  #if SCU_USB_CLOCK_SETUP
  USBClockSetup();
  #endif

}


/**
  * @brief  Update SystemCoreClock according to Clock Register Values
  * @note   -  
  * @param  None
  * @retval None
  */
void SystemCoreClockUpdate(void)
{

/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
  SystemCoreClock = SYSTEM_FREQUENCY;/*!< System Clock Frequency (Core Clock)*/

}


/**
  * @brief  -
  * @note   -  
  * @param  None
  * @retval None
  */
static int SystemClockSetup(void)
{
/* enable PLL first */
  SCU_PLL->PLLCON0 &= ~(SCU_PLL_PLLCON0_VCOPWD_Msk | SCU_PLL_PLLCON0_PLLPWD_Msk);

/* Enable OSC_HP */
  if (SCU_PLL_CLOCK_INPUT == SCU_CLOCK_CRYSTAL)
  {

   SCU_OSC->OSCHPCTRL = (OSC_HP_MODE<<4);	 /*enable the OSC_HP*/
   /* setup OSC WDG devider */
   SCU_OSC->OSCHPCTRL |= (OSCHPWDGDIV<<16);         
   /* select external OSC as PLL input */
   SCU_PLL->PLLCON2 &= ~SCU_PLL_PLLCON2_PINSEL_Msk;
   /* restart OSC Watchdog */
   SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_OSCRES_Msk;  

   do 
   {
	   ;  /* here a timeout need to be added */
   }while(!((SCU_PLL->PLLSTAT) & (SCU_PLL_PLLSTAT_PLLHV_Msk | SCU_PLL_PLLSTAT_PLLLV_Msk |SCU_PLL_PLLSTAT_PLLSP_Msk))); 

  }

/* Setup Main PLL */
  /* select FOFI as system clock */
  if(SCU_CLK->SYSCLKCR != 0X000000)SCU_CLK->SYSCLKCR = 0x00000000; /*Select FOFI*/
  /* Go to bypass the Main PLL */
  SCU_PLL->PLLCON0 |= SCU_PLL_PLLCON0_VCOBYP_Msk;
  /* disconnect OSC_HP to PLL */
  SCU_PLL->PLLCON0 |= SCU_PLL_PLLCON0_FINDIS_Msk;
  /* Setup devider settings for main PLL */
  SCU_PLL->PLLCON1 = ((PLL_K1DIV) | (PLL_NDIV<<8) | (PLL_K2DIV_STEP_1<<16) | (PLL_PDIV<<24));
  /* we may have to set OSCDISCDIS */
  SCU_PLL->PLLCON0 |= SCU_PLL_PLLCON0_OSCDISCDIS_Msk;
  /* connect OSC_HP to PLL */
  SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_FINDIS_Msk;
  /* restart PLL Lock detection */
  SCU_PLL->PLLCON0 |= SCU_PLL_PLLCON0_RESLD_Msk;
  /* wait for PLL Lock */
  while (!(SCU_PLL->PLLSTAT & SCU_PLL_PLLSTAT_VCOLOCK_Msk));
  /* Go back to the Main PLL */
  SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_VCOBYP_Msk;

  /*********************************************************
  here we need to setup the system clock divider
  *********************************************************/

	SCU_CLK->CPUCLKCR = SCU_CPUCLKCR_DIV;
	SCU_CLK->PBCLKCR = SCU_PBCLKCR_DIV;	
	SCU_CLK->CCUCLKCR = SCU_CCUCLKCR_DIV;

  /* Switch system clock to PLL */
  SCU_CLK->SYSCLKCR |=  0x00010000; 
															  
  /*********************************************************
  here the ramp up of the system clock starts
  *********************************************************/
  /* Delay for next K2 step ~50탎 */
  /********************************/
  SysTick->LOAD  = ((1250+100) & SysTick_LOAD_RELOAD_Msk) - 1;/* set reload register */
  SysTick->VAL   = 0;                                         /* Load the SysTick Counter Value */
  SysTick->CTRL  = SysTick_CTRL_CLKSOURCE_Msk |
                   SysTick_CTRL_ENABLE_Msk;                    /* Enable SysTick IRQ and SysTick Timer */

  while (SysTick->VAL >= 100);								   /* wait for ~50탎  */
  SysTick->CTRL  &= ~SysTick_CTRL_ENABLE_Msk;                 /* Stop SysTick Timer */
  /********************************/

  /* Setup devider settings for main PLL */
  SCU_PLL->PLLCON1 = ((PLL_K1DIV) | (PLL_NDIV<<8) | (PLL_K2DIV_STEP_2<<16) | (PLL_PDIV<<24));

  /* Delay for next K2 step ~50탎 */
  /********************************/
  SysTick->LOAD  = ((3000+100) & SysTick_LOAD_RELOAD_Msk) - 1;
  SysTick->VAL   = 0;                                         /* Load the SysTick Counter Value */
  SysTick->CTRL  = SysTick_CTRL_CLKSOURCE_Msk |
                   SysTick_CTRL_ENABLE_Msk;                    /* Enable SysTick IRQ and SysTick Timer */

  while (SysTick->VAL >= 100);								   /* wait for ~50탎  */
  SysTick->CTRL  &= ~SysTick_CTRL_ENABLE_Msk;                 /* Stop SysTick Timer */
  /********************************/

  /* Setup devider settings for main PLL */
  SCU_PLL->PLLCON1 = ((PLL_K1DIV) | (PLL_NDIV<<8) | (PLL_K2DIV_STEP_3<<16) | (PLL_PDIV<<24));

  /* Delay for next K2 step ~50탎 */
  /********************************/
  SysTick->LOAD  = ((4800+100) & SysTick_LOAD_RELOAD_Msk) - 1;
  SysTick->VAL   = 0;                                         /* Load the SysTick Counter Value */
  SysTick->CTRL  = SysTick_CTRL_CLKSOURCE_Msk |
                   SysTick_CTRL_ENABLE_Msk;                    /* Enable SysTick IRQ and SysTick Timer */

  while (SysTick->VAL >= 100);								   /* wait for ~50탎  */
  SysTick->CTRL  &= ~SysTick_CTRL_ENABLE_Msk;                 /* Stop SysTick Timer */
  /********************************/

  /* Setup devider settings for main PLL */
  SCU_PLL->PLLCON1 = ((PLL_K1DIV) | (PLL_NDIV<<8) | (PLL_K2DIV<<16) | (PLL_PDIV<<24));

  SCU_TRAP->TRAPCLR = SCU_TRAP_TRAPCLR_SOSCWDGT_Msk | SCU_TRAP_TRAPCLR_SVCOLCKT_Msk;  /* clear request for System OCS Watchdog Trap and System VCO Lock Trap  */

  return(1);

}

/**
  * @brief  -
  * @note   -  
  * @param  None
  * @retval None
  */
static void USBClockSetup(void)
{
/* enable PLL first */
  SCU_PLL->USBPLLCON &= ~(SCU_PLL_USBPLLCON_VCOPWD_Msk | SCU_PLL_USBPLLCON_PLLPWD_Msk);

/* check and if not already running enable OSC_HP */
  if(!((SCU_PLL->PLLSTAT) & (SCU_PLL_PLLSTAT_PLLHV_Msk | SCU_PLL_PLLSTAT_PLLLV_Msk |SCU_PLL_PLLSTAT_PLLSP_Msk)))
  {
	  if (SCU_PLL_CLOCK_INPUT == SCU_CLOCK_CRYSTAL)
	  {
	
	   SCU_OSC->OSCHPCTRL = (OSC_HP_MODE<<4);	 /*enable the OSC_HP*/
	   /* setup OSC WDG devider */
	   SCU_OSC->OSCHPCTRL |= (OSCHPWDGDIV<<16);         
	   /* select external OSC as PLL input */
	   SCU_PLL->PLLCON2 &= ~SCU_PLL_PLLCON2_PINSEL_Msk;
	   /* restart OSC Watchdog */
	   SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_OSCRES_Msk;  
	
	   do 
	   {
		   ;  /* here a timeout need to be added */
	   }while(!((SCU_PLL->PLLSTAT) & (SCU_PLL_PLLSTAT_PLLHV_Msk | SCU_PLL_PLLSTAT_PLLLV_Msk |SCU_PLL_PLLSTAT_PLLSP_Msk))); 
	
	  }
  }


/* Setup USB PLL */
  /* Go to bypass the Main PLL */
  SCU_PLL->USBPLLCON |= SCU_PLL_USBPLLCON_VCOBYP_Msk;
  /* disconnect OSC_FI to PLL */
  SCU_PLL->USBPLLCON |= SCU_PLL_USBPLLCON_FINDIS_Msk;
  /* Setup devider settings for main PLL */
  SCU_PLL->USBPLLCON = ((USBPLL_NDIV<<8) | (USBPLL_PDIV<<24));
  /* we may have to set OSCDISCDIS */
  SCU_PLL->USBPLLCON |= SCU_PLL_USBPLLCON_OSCDISCDIS_Msk;
  /* connect OSC_FI to PLL */
  SCU_PLL->USBPLLCON &= ~SCU_PLL_USBPLLCON_FINDIS_Msk;
  /* restart PLL Lock detection */
  SCU_PLL->USBPLLCON |= SCU_PLL_USBPLLCON_RESLD_Msk;
  /* wait for PLL Lock */
  while (!(SCU_PLL->USBPLLSTAT & SCU_PLL_USBPLLSTAT_VCOLOCK_Msk));
 
}


