/**************************************************************************//**
 * @file     system_XMC4500.c
 * @brief    CMSIS Cortex-M4 Device Peripheral Access Layer Header File
 *           for the Infineon XMC4500 Device Series
 * @version  V3.0.1 Alpha
 * @date     17. September 2012
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

#include "system_XMC4500.h"
#include <XMC4500.h>

/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
/*!< System Clock Frequency (Core Clock)*/
uint32_t SystemCoreClock;

/* clock definitions, do not modify! */
#define SCU_CLOCK_CRYSTAL              	1
#define SCU_CLOCK_BACK_UP_FACTORY		   	2
#define SCU_CLOCK_BACK_UP_AUTOMATIC	   	3


#define HIB_CLOCK_FOSI					1
#define HIB_CLOCK_OSCULP				2




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
/* not avalible in config wizzard*/
/*
* mandatory clock parameters **************************************************
*
* source for clock generation
* range: SCU_CLOCK_CRYSTAL (crystal or external clock at crystal input)
*
**************************************************************************************/
// Selection of imput lock for PLL
/*************************************************************************************/
#define	SCU_PLL_CLOCK_INPUT	SCU_CLOCK_CRYSTAL
//#define	SCU_PLL_CLOCK_INPUT	SCU_CLOCK_BACK_UP_FACTORY
//#define	SCU_PLL_CLOCK_INPUT	SCU_CLOCK_BACK_UP_AUTOMATIC

/*************************************************************************************/
// Standby clock selection for Backup clock source trimming
/*************************************************************************************/
#define	SCU_STANDBY_CLOCK  HIB_CLOCK_OSCULP
//#define	SCU_STANDBY_CLOCK  HIB_CLOCK_FOSI

/*************************************************************************************/
// Global clock parameters
/*************************************************************************************/
#define CLOCK_FSYS							120000000
#define	CLOCK_CRYSTAL_FREQUENCY	12000000
#define	CLOCK_BACK_UP						24000000

/*************************************************************************************/
/* OSC_HP setup parameters */
/*************************************************************************************/
#define	SCU_OSC_HP_MODE	0xF0
#define	SCU_OSCHPWDGDIV	2

/*************************************************************************************/
/* MAIN PLL setup parameters */
/*************************************************************************************/
//Divider settings for external crystal @ 12 MHz
/*************************************************************************************/
#define 	SCU_PLL_K1DIV	1
#define 	SCU_PLL_K2DIV	3
#define 	SCU_PLL_PDIV	1
#define 	SCU_PLL_NDIV	79

/*************************************************************************************/
//Divider settings for use of backup clock source trimmed
/*************************************************************************************/
//#define 	SCU_PLL_K1DIV	1
//#define 	SCU_PLL_K2DIV	3
//#define 	SCU_PLL_PDIV	3
//#define 	SCU_PLL_NDIV	79
/*************************************************************************************/

/*--------------------- USB CLOCK Configuration ---------------------------
//
// <e> USB Clock Configuration
//
// </e>
//
*/

#define SCU_USB_CLOCK_SETUP              0
/* not avalible in config wizzard*/
#define 	SCU_USBPLL_PDIV	0
#define 	SCU_USBPLL_NDIV	31
#define 	SCU_USBDIV	3

/*--------------------- Flash Wait State Configuration -------------------------------
//
// <e> Flash Wait State Configuration
//     <o1.0..3>   Flash Wait State
//                     <0=> 3 WS
//                     <1=> 4 WS
//                     <2=> 5 WS
//										 <3=> 6 WS
// </e>
//
*/

#define PMU_FLASH             1
#define	PMU_FLASH_WS					0x00000000


/*--------------------- CLOCKOUT Configuration -------------------------------
//
// <e> Clock OUT Configuration
//     <o1.0..1>   Clockout Source Selection
//                     <0=> System Clock
//                     <2=> Divided value of USB PLL output
//                     <3=> Divided value of PLL Clock
//     <o2.0..4>   Clockout divider <1-10><#-1>
//     <o3.0..1>   Clockout Pin Selection
//                     <0=> P1.15
//                     <1=> P0.8
//
//
// </e>
//
*/

#define SCU_CLOCKOUT_SETUP               0
#define	SCU_CLOCKOUT_SOURCE		0x00000003
#define	SCU_CLOCKOUT_DIV		0x00000009
#define	SCU_CLOCKOUT_PIN		0x00000001

/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
/*!< System Clock Frequency (Core Clock)*/
#if SCU_CLOCK_SETUP
uint32_t SystemCoreClock = CLOCK_FSYS;
#else
uint32_t SystemCoreClock = CLOCK_BACK_UP;
#endif

/*----------------------------------------------------------------------------
  static functions declarations
 *----------------------------------------------------------------------------*/
#if (SCU_CLOCK_SETUP == 1)
static int SystemClockSetup(void);
#endif

#if (SCU_USB_CLOCK_SETUP == 1)
static int USBClockSetup(void);
#endif


/**
  * @brief  Setup the microcontroller system.
  *         Initialize the PLL and update the
  *         SystemCoreClock variable.
  * @param  None
  * @retval None
  */
void SystemInit(void)
{
int temp;

#if (__FPU_PRESENT == 1) && (__FPU_USED == 1)
SCB->CPACR |= ((3UL << 10*2) |                 /* set CP10 Full Access */
               (3UL << 11*2)  );               /* set CP11 Full Access */
#endif

/* Enable unaligned memory access - SCB_CCR.UNALIGN_TRP = 0 */
SCB->CCR &= ~(SCB_CCR_UNALIGN_TRP_Msk);

/* Setup the WDT */
#if WDT_SETUP

WDT->CTR &= ~WDTENB_nVal;

#endif

/* Setup the Flash Wait State */
#if PMU_FLASH
temp = FLASH0->FCON;
temp &= ~FLASH_FCON_WSPFLASH_Msk;
temp |= PMU_FLASH_WS+3;
FLASH0->FCON = temp;
#endif


/* Setup the clockout */
#if SCU_CLOCKOUT_SETUP

SCU_CLK->EXTCLKCR	|= SCU_CLOCKOUT_SOURCE;
/*set PLL div for clkout */
SCU_CLK->EXTCLKCR	|= SCU_CLOCKOUT_DIV<<16;

if (SCU_CLOCKOUT_PIN) {
						PORT0->IOCR8 = 0x00000088;   /*P0.8 --> ALT1 select +  HWSEL */
					    PORT0->HWSEL &= (~PORT0_HWSEL_HW8_Msk);
					    //PORT0->PDR1 &= (~PORT0_PDR1_PD8_Msk);  /*set to strong driver */
						}
else {
		PORT1->IOCR12 = 0x88000000;                    /*P1.15--> ALT1 select */
	    //PORT1->PDR1 &= (~PORT1_PDR1_PD15_Msk);  /*set to strong driver */
		}

#endif


/* Setup the System clock */
#if SCU_CLOCK_SETUP
SystemClockSetup();
#endif

/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
SystemCoreClockUpdate();/*!< System Clock Frequency (Core Clock)*/


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
unsigned int PDIV;
unsigned int NDIV;
unsigned int K2DIV;
unsigned int long VCO;


/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
if (SCU_CLK->SYSCLKCR ==  0x00010000)
{
	if (SCU_PLL->PLLSTAT & SCU_PLL_PLLSTAT_VCOLOCK_Msk){
		/* check if PLL is locked */
		/* read back divider settings */
		 PDIV = ((SCU_PLL->PLLCON1 & SCU_PLL_PLLCON1_PDIV_Msk)>>24)+1;
		 NDIV = ((SCU_PLL->PLLCON1 & SCU_PLL_PLLCON1_NDIV_Msk)>>8)+1;
		 K2DIV  = ((SCU_PLL->PLLCON1 & SCU_PLL_PLLCON1_K2DIV_Msk)>>16)+1;

		if(SCU_PLL->PLLCON2 & SCU_PLL_PLLCON2_PINSEL_Msk){
		/* the selected clock is the Backup clock fofi */
		VCO = (CLOCK_BACK_UP/PDIV)*NDIV;
		SystemCoreClock = VCO/K2DIV;
		/* in case the sysclock div is used */
		SystemCoreClock = SystemCoreClock/((SCU_CLK->SYSCLKCR & SCU_CLK_SYSCLKCR_SYSDIV_Msk)+1);

		}
		else
		{
		/* the selected clock is the PLL external oscillator */
		VCO = (CLOCK_CRYSTAL_FREQUENCY/PDIV)*NDIV;
		SystemCoreClock = VCO/K2DIV;
		/* in case the sysclock div is used */
		SystemCoreClock = SystemCoreClock/((SCU_CLK->SYSCLKCR & SCU_CLK_SYSCLKCR_SYSDIV_Msk)+1);
		}


	}
}
else
{
SystemCoreClock = CLOCK_BACK_UP;
}


}


/**
  * @brief  -
  * @note   -
  * @param  None
  * @retval None
  */
#if (SCU_CLOCK_SETUP == 1)
static int SystemClockSetup(void)
{
int temp;
unsigned int long VCO;
int stepping_K2DIV;

/* this weak function enables DAVE3 clock App usage */
if(AllowPLLInitByStartup()){

/* check if PLL is switched on */
if ((SCU_PLL->PLLCON0 &(SCU_PLL_PLLCON0_VCOPWD_Msk | SCU_PLL_PLLCON0_PLLPWD_Msk)) != 0){
/* enable PLL first */
  SCU_PLL->PLLCON0 &= ~(SCU_PLL_PLLCON0_VCOPWD_Msk | SCU_PLL_PLLCON0_PLLPWD_Msk);

}

/* Enable OSC_HP if not already on*/
  if (SCU_PLL_CLOCK_INPUT == SCU_CLOCK_CRYSTAL)
  {
	/********************************************************************************************************************/
	/*   Use external crystal for PLL clock input                                                                            */
	/********************************************************************************************************************/

   if (SCU_OSC->OSCHPCTRL & SCU_OSC_OSCHPCTRL_MODE_Msk){
	   SCU_OSC->OSCHPCTRL &= ~(SCU_OSC_HP_MODE);	 /*enable the OSC_HP*/
	   /* setup OSC WDG devider */
	   SCU_OSC->OSCHPCTRL |= (SCU_OSCHPWDGDIV<<16);
	   /* select external OSC as PLL input */
	   SCU_PLL->PLLCON2 &= ~SCU_PLL_PLLCON2_PINSEL_Msk;
	   /* restart OSC Watchdog */
	   SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_OSCRES_Msk;

       /* Timeout for wait loop ~150ms */
	   /********************************/
	   SysTick->LOAD  = ((5000000+100) & SysTick_LOAD_RELOAD_Msk) - 1;/* set reload register */
	   SysTick->VAL   = 0;                                         /* Load the SysTick Counter Value */
	   SysTick->CTRL  = SysTick_CTRL_CLKSOURCE_Msk |
	                   SysTick_CTRL_ENABLE_Msk;                    /* Enable SysTick IRQ and SysTick Timer */
	   do
	   {
       ;/* wait for ~150ms  */
	   }while((((SCU_PLL->PLLSTAT) & (SCU_PLL_PLLSTAT_PLLHV_Msk | SCU_PLL_PLLSTAT_PLLLV_Msk |SCU_PLL_PLLSTAT_PLLSP_Msk)) != 0x380)&&(SysTick->VAL >= 500));

	   SysTick->CTRL  &= ~SysTick_CTRL_ENABLE_Msk;                 /* Stop SysTick Timer */
	   if (((SCU_PLL->PLLSTAT) & (SCU_PLL_PLLSTAT_PLLHV_Msk | SCU_PLL_PLLSTAT_PLLLV_Msk |SCU_PLL_PLLSTAT_PLLSP_Msk)) != 0x380)
	   return(0);/* Return Error */

    }
  }
  else if (SCU_PLL_CLOCK_INPUT == SCU_CLOCK_BACK_UP_FACTORY)
	{
	/********************************************************************************************************************/
	/*   Use factory trimming Back-up clock for PLL clock input                                                                            */
	/********************************************************************************************************************/
		/* PLL Back up clock selected */
		SCU_PLL->PLLCON2 |= SCU_PLL_PLLCON2_PINSEL_Msk;

	}
  else if (SCU_PLL_CLOCK_INPUT == SCU_CLOCK_BACK_UP_AUTOMATIC)
  {
	/********************************************************************************************************************/
	/*   Use automatic trimming Back-up clock for PLL clock input                                                                            */
	/********************************************************************************************************************/
	/* check for HIB Domain enabled  */
	if((SCU_POWER->PWRSTAT & SCU_POWER_PWRSTAT_HIBEN_Msk) == 0)
		SCU_POWER->PWRSET |= SCU_POWER_PWRSET_HIB_Msk; /*enable Hibernate domain*/

   /* check for HIB Domain is not in reset state  */
	if ((SCU_RESET->RSTSTAT & SCU_RESET_RSTSTAT_HIBRS_Msk)== 1)
	    SCU_RESET->RSTCLR |= SCU_RESET_RSTCLR_HIBRS_Msk; /*de-assert hibernate reset*/

			/* PLL Back up clock selected */
		SCU_PLL->PLLCON2 |= SCU_PLL_PLLCON2_PINSEL_Msk;

		if (SCU_STANDBY_CLOCK == HIB_CLOCK_FOSI)
			{
			/****************************************************************************************************************/
			/*   Use fOSI as source of the standby clock                                                                             */
			/****************************************************************************************************************/
			SCU_HIBERNATE->HDCR &= ~SCU_HIBERNATE_HDCR_STDBYSEL_Msk;

			SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_FOTR_Msk;
			for(temp=0;temp<=0xFFFF;temp++);

			SCU_PLL->PLLCON0 |= SCU_PLL_PLLCON0_AOTREN_Msk;
			}
		else if (SCU_STANDBY_CLOCK == HIB_CLOCK_OSCULP)
			{
			/****************************************************************************************************************/
			/*   Use fULP as source of the standby clock                                                                            */
			/****************************************************************************************************************/
			/*check OSCUL if running correct*/
			if ((SCU_HIBERNATE->OSCULCTRL & SCU_HIBERNATE_OSCULCTRL_MODE_Msk)!= 0)
				{
					while (SCU_GENERAL->MIRRSTS & SCU_GENERAL_MIRRSTS_OSCULCTRL_Msk);

					SCU_HIBERNATE->OSCULCTRL &= ~SCU_HIBERNATE_OSCULCTRL_MODE_Msk; /*enable OSCUL*/
					/*now ceck if the clock is OK using OSCULP Oscillator Watchdog (ULPWDG)*/
					/* select OSCUL clock for RTC*/
					SCU_HIBERNATE->HDCR |= SCU_HIBERNATE_HDCR_RCS_Msk;
					while (SCU_GENERAL->MIRRSTS & SCU_GENERAL_MIRRSTS_HDCR_Msk);
					/*enable OSCULP WDG Alarm Enable*/
					SCU_HIBERNATE->HDCR |= SCU_HIBERNATE_HDCR_ULPWDGEN_Msk;
					while (SCU_GENERAL->MIRRSTS & SCU_GENERAL_MIRRSTS_HDCR_Msk);
					/*wait now for clock is stable */
					do
					{
					SCU_HIBERNATE->HDCLR |= SCU_HIBERNATE_HDCLR_ULPWDG_Msk;
					while (SCU_GENERAL->MIRRSTS & SCU_GENERAL_MIRRSTS_HDCLR_Msk);
					for(temp=0;temp<=0xFFFF;temp++);
					}
					while ((SCU_HIBERNATE->HDSTAT & SCU_HIBERNATE_HDSTAT_ULPWDG_Msk)==SCU_HIBERNATE_HDSTAT_ULPWDG_Msk);

					SCU_HIBERNATE->HDCLR |= SCU_HIBERNATE_HDCLR_ULPWDG_Msk;
					while (SCU_GENERAL->MIRRSTS & SCU_GENERAL_MIRRSTS_HDCLR_Msk);
				}
			// now OSCULP is running and can be used
			SCU_HIBERNATE->HDCR |= SCU_HIBERNATE_HDCR_STDBYSEL_Msk;
			while (SCU_GENERAL->MIRRSTS & SCU_GENERAL_MIRRSTS_HDCR_Msk);

			SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_FOTR_Msk;
			/*TRIAL for delay loop*/
			for(temp=0;temp<=0xFFFF;temp++);

			SCU_PLL->PLLCON0 |= SCU_PLL_PLLCON0_AOTREN_Msk;
			/*TRIAL for delay loop*/
			for(temp=0;temp<=0xFFFF;temp++);

			}
  }

	/********************************************************************************************************************/
	/*   Setup and look the main PLL                                                                                    */
	/********************************************************************************************************************/

if (!(SCU_PLL->PLLSTAT & SCU_PLL_PLLSTAT_VCOLOCK_Msk)){
	/* Systen is still running from internal clock */
		   /* select FOFI as system clock */
		   if((SCU_CLK->SYSCLKCR & SCU_CLK_SYSCLKCR_SYSSEL_Msk) != 0x0)SCU_CLK->SYSCLKCR &= ~SCU_CLK_SYSCLKCR_SYSSEL_Msk; /*Select FOFI*/


			 /*calulation for stepping*/
			 if (SCU_PLL_CLOCK_INPUT == SCU_CLOCK_CRYSTAL)VCO = (CLOCK_CRYSTAL_FREQUENCY/(SCU_PLL_PDIV+1))*(SCU_PLL_NDIV+1);
			 if ((SCU_PLL_CLOCK_INPUT == SCU_CLOCK_BACK_UP_AUTOMATIC) ||(SCU_PLL_CLOCK_INPUT == SCU_CLOCK_BACK_UP_FACTORY))
					VCO = (CLOCK_BACK_UP/(SCU_PLL_PDIV+1))*(SCU_PLL_NDIV+1);

			 stepping_K2DIV = (VCO/24000000)-1;
			 /* Go to bypass the Main PLL */
		   SCU_PLL->PLLCON0 |= SCU_PLL_PLLCON0_VCOBYP_Msk;
		   /* disconnect OSC_HP to PLL */
		   SCU_PLL->PLLCON0 |= SCU_PLL_PLLCON0_FINDIS_Msk;
		   /* Setup devider settings for main PLL */
		   SCU_PLL->PLLCON1 = ((SCU_PLL_K1DIV) | (SCU_PLL_NDIV<<8) | (stepping_K2DIV<<16) | (SCU_PLL_PDIV<<24));
		   /* we may have to set OSCDISCDIS */
		   SCU_PLL->PLLCON0 |= SCU_PLL_PLLCON0_OSCDISCDIS_Msk;
		   /* connect OSC_HP to PLL */
		   SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_FINDIS_Msk;
		   /* restart PLL Lock detection */
		   SCU_PLL->PLLCON0 |= SCU_PLL_PLLCON0_RESLD_Msk;
		   /* wait for PLL Lock */
		   /* setup time out loop */
	       /* Timeout for wait loo ~150ms */
		   /********************************/
		   SysTick->LOAD  = ((5000000+100) & SysTick_LOAD_RELOAD_Msk) - 1;/* set reload register */
		   SysTick->VAL   = 0;                                         /* Load the SysTick Counter Value */
		   SysTick->CTRL  = SysTick_CTRL_CLKSOURCE_Msk |
		                   SysTick_CTRL_ENABLE_Msk;                    /* Enable SysTick IRQ and SysTick Timer */

		   while ((!(SCU_PLL->PLLSTAT & SCU_PLL_PLLSTAT_VCOLOCK_Msk))&&(SysTick->VAL >= 500));
	       SysTick->CTRL  &= ~SysTick_CTRL_ENABLE_Msk;                 /* Stop SysTick Timer */

		   if ((SCU_PLL->PLLSTAT & SCU_PLL_PLLSTAT_VCOLOCK_Msk)==SCU_PLL_PLLSTAT_VCOLOCK_Msk)
		   		{
				/* Go back to the Main PLL */
				SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_VCOBYP_Msk;
				}
				else return(0);


	   /*********************************************************
	   here we need to setup the system clock divider
	   *********************************************************/

		SCU_CLK->CPUCLKCR = SCU_CPUCLKCR_DIV;
		SCU_CLK->PBCLKCR = SCU_PBCLKCR_DIV;
		SCU_CLK->CCUCLKCR = SCU_CCUCLKCR_DIV;


		 /* Switch system clock to PLL */
	   SCU_CLK->SYSCLKCR |=  0x00010000;

	   /* we may have to reset OSCDISCDIS */
	   SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_OSCDISCDIS_Msk;


		 /*********************************************************/
		 /* Delay for next K2 step ~50탎 */
		 /*********************************************************/
		 SysTick->LOAD  = ((1250+100) & SysTick_LOAD_RELOAD_Msk) - 1;/* set reload register */
		 SysTick->VAL   = 0;                                         /* Load the SysTick Counter Value */
		 SysTick->CTRL  = SysTick_CTRL_CLKSOURCE_Msk |
										 SysTick_CTRL_ENABLE_Msk;                    /* Enable SysTick IRQ and SysTick Timer */

		 while (SysTick->VAL >= 100);								   /* wait for ~50탎  */
		 SysTick->CTRL  &= ~SysTick_CTRL_ENABLE_Msk;                 /* Stop SysTick Timer */
		 /*********************************************************/

	   /*********************************************************
	   here the ramp up of the system clock starts FSys < 60MHz
	   *********************************************************/
		if (CLOCK_FSYS > 60000000){
			 /*calulation for stepping*/
			 if (SCU_PLL_CLOCK_INPUT == SCU_CLOCK_CRYSTAL)VCO = (CLOCK_CRYSTAL_FREQUENCY/(SCU_PLL_PDIV+1))*(SCU_PLL_NDIV+1);
			 if ((SCU_PLL_CLOCK_INPUT == SCU_CLOCK_BACK_UP_AUTOMATIC) ||(SCU_PLL_CLOCK_INPUT == SCU_CLOCK_BACK_UP_FACTORY))
					VCO = (CLOCK_BACK_UP/(SCU_PLL_PDIV+1))*(SCU_PLL_NDIV+1);

			 stepping_K2DIV = (VCO/60000000)-1;

			 /* Setup devider settings for main PLL */
				SCU_PLL->PLLCON1 = ((SCU_PLL_K1DIV) | (SCU_PLL_NDIV<<8) | (stepping_K2DIV<<16) | (SCU_PLL_PDIV<<24));
		 }
		 else
		 {
				/* Setup devider settings for main PLL */
				SCU_PLL->PLLCON1 = ((SCU_PLL_K1DIV) | (SCU_PLL_NDIV<<8) | (SCU_PLL_K2DIV<<16) | (SCU_PLL_PDIV<<24));
		    SCU_TRAP->TRAPCLR = SCU_TRAP_TRAPCLR_SOSCWDGT_Msk | SCU_TRAP_TRAPCLR_SVCOLCKT_Msk;  /* clear request for System OCS Watchdog Trap and System VCO Lock Trap  */
			  return(1);
		 }

		 /*********************************************************/
		 /* Delay for next K2 step ~50탎 */
		 /*********************************************************/
	   SysTick->LOAD  = ((3000+100) & SysTick_LOAD_RELOAD_Msk) - 1;
	   SysTick->VAL   = 0;                                         /* Load the SysTick Counter Value */
	   SysTick->CTRL  = SysTick_CTRL_CLKSOURCE_Msk |
	                   SysTick_CTRL_ENABLE_Msk;                    /* Enable SysTick IRQ and SysTick Timer */

	   while (SysTick->VAL >= 100);								   /* wait for ~50탎  */
	   SysTick->CTRL  &= ~SysTick_CTRL_ENABLE_Msk;                 /* Stop SysTick Timer */
	   /********************************/

   /*********************************************************
	   here the ramp up of the system clock starts FSys < 90MHz
	   *********************************************************/
		if (CLOCK_FSYS > 90000000){
			 /*calulation for stepping*/
			 if (SCU_PLL_CLOCK_INPUT == SCU_CLOCK_CRYSTAL)VCO = (CLOCK_CRYSTAL_FREQUENCY/(SCU_PLL_PDIV+1))*(SCU_PLL_NDIV+1);
			 if ((SCU_PLL_CLOCK_INPUT == SCU_CLOCK_BACK_UP_AUTOMATIC) ||(SCU_PLL_CLOCK_INPUT == SCU_CLOCK_BACK_UP_FACTORY))
					VCO = (CLOCK_BACK_UP/(SCU_PLL_PDIV+1))*(SCU_PLL_NDIV+1);

			 stepping_K2DIV = (VCO/90000000)-1;

			 /* Setup devider settings for main PLL */
				SCU_PLL->PLLCON1 = ((SCU_PLL_K1DIV) | (SCU_PLL_NDIV<<8) | (stepping_K2DIV<<16) | (SCU_PLL_PDIV<<24));
		 }
		 else
		 {
				/* Setup devider settings for main PLL */
				SCU_PLL->PLLCON1 = ((SCU_PLL_K1DIV) | (SCU_PLL_NDIV<<8) | (SCU_PLL_K2DIV<<16) | (SCU_PLL_PDIV<<24));
	      SCU_TRAP->TRAPCLR = SCU_TRAP_TRAPCLR_SOSCWDGT_Msk | SCU_TRAP_TRAPCLR_SVCOLCKT_Msk;  /* clear request for System OCS Watchdog Trap and System VCO Lock Trap  */
				return(1);
		 }

		 /*********************************************************/
		 /* Delay for next K2 step ~50탎 */
		 /*********************************************************/
	   SysTick->LOAD  = ((4800+100) & SysTick_LOAD_RELOAD_Msk) - 1;
	   SysTick->VAL   = 0;                                         /* Load the SysTick Counter Value */
	   SysTick->CTRL  = SysTick_CTRL_CLKSOURCE_Msk |
	                   SysTick_CTRL_ENABLE_Msk;                    /* Enable SysTick IRQ and SysTick Timer */

	   while (SysTick->VAL >= 100);								   /* wait for ~50탎  */
	   SysTick->CTRL  &= ~SysTick_CTRL_ENABLE_Msk;                 /* Stop SysTick Timer */
	   /********************************/

	   /* Setup devider settings for main PLL */
	   SCU_PLL->PLLCON1 = ((SCU_PLL_K1DIV) | (SCU_PLL_NDIV<<8) | (SCU_PLL_K2DIV<<16) | (SCU_PLL_PDIV<<24));

	   SCU_TRAP->TRAPCLR = SCU_TRAP_TRAPCLR_SOSCWDGT_Msk | SCU_TRAP_TRAPCLR_SVCOLCKT_Msk;  /* clear request for System OCS Watchdog Trap and System VCO Lock Trap  */
	}
 }/* end this weak function enables DAVE3 clock App usage */
   return(1);

}
#endif

/**
  * @brief  -
  * @note   -
  * @param  None
  * @retval None
  */
#if (SCU_USB_CLOCK_SETUP == 1)
static int USBClockSetup(void)
{
/* this weak function enables DAVE3 clock App usage */
if(AllowPLLInitByStartup()){

	/* check if PLL is switched on */
if ((SCU_PLL->USBPLLCON &(SCU_PLL_USBPLLCON_VCOPWD_Msk | SCU_PLL_USBPLLCON_PLLPWD_Msk)) != 0){
	/* enable PLL first */
  SCU_PLL->USBPLLCON &= ~(SCU_PLL_USBPLLCON_VCOPWD_Msk | SCU_PLL_USBPLLCON_PLLPWD_Msk);
}

/* check and if not already running enable OSC_HP */
   if (SCU_OSC->OSCHPCTRL & SCU_OSC_OSCHPCTRL_MODE_Msk){
		 /* check if Main PLL is switched on for OSC WD*/
		 if ((SCU_PLL->PLLCON0 &(SCU_PLL_PLLCON0_VCOPWD_Msk | SCU_PLL_PLLCON0_PLLPWD_Msk)) != 0){
			/* enable PLL first */
  			SCU_PLL->PLLCON0 &= ~(SCU_PLL_PLLCON0_VCOPWD_Msk | SCU_PLL_PLLCON0_PLLPWD_Msk);
		 }
	   SCU_OSC->OSCHPCTRL &= ~(SCU_OSC_HP_MODE);	 /*enable the OSC_HP*/
	   /* setup OSC WDG devider */
	   SCU_OSC->OSCHPCTRL |= (SCU_OSCHPWDGDIV<<16);
	   /* restart OSC Watchdog */
	   SCU_PLL->PLLCON0 &= ~SCU_PLL_PLLCON0_OSCRES_Msk;

       /* Timeout for wait loop ~150ms */
	   /********************************/
	   SysTick->LOAD  = ((5000000+100) & SysTick_LOAD_RELOAD_Msk) - 1;/* set reload register */
	   SysTick->VAL   = 0;                                         /* Load the SysTick Counter Value */
	   SysTick->CTRL  = SysTick_CTRL_CLKSOURCE_Msk |
	                   SysTick_CTRL_ENABLE_Msk;                    /* Enable SysTick IRQ and SysTick Timer */
	   do
	   {
       ;/* wait for ~150ms  */
	   }while((((SCU_PLL->PLLSTAT) & (SCU_PLL_PLLSTAT_PLLHV_Msk | SCU_PLL_PLLSTAT_PLLLV_Msk |SCU_PLL_PLLSTAT_PLLSP_Msk)) != 0x380)&&(SysTick->VAL >= 500));

	   SysTick->CTRL  &= ~SysTick_CTRL_ENABLE_Msk;                 /* Stop SysTick Timer */
	   if (((SCU_PLL->PLLSTAT) & (SCU_PLL_PLLSTAT_PLLHV_Msk | SCU_PLL_PLLSTAT_PLLLV_Msk |SCU_PLL_PLLSTAT_PLLSP_Msk)) != 0x380)
	   return(0);/* Return Error */

  }


/* Setup USB PLL */
   /* Go to bypass the Main PLL */
   SCU_PLL->USBPLLCON |= SCU_PLL_USBPLLCON_VCOBYP_Msk;
   /* disconnect OSC_FI to PLL */
   SCU_PLL->USBPLLCON |= SCU_PLL_USBPLLCON_FINDIS_Msk;
   /* Setup devider settings for main PLL */
   SCU_PLL->USBPLLCON = ((SCU_USBPLL_NDIV<<8) | (SCU_USBPLL_PDIV<<24));
   /* Setup USBDIV settings USB clock */
   SCU_CLK->USBCLKCR = SCU_USBDIV;
   /* we may have to set OSCDISCDIS */
   SCU_PLL->USBPLLCON |= SCU_PLL_USBPLLCON_OSCDISCDIS_Msk;
   /* connect OSC_FI to PLL */
   SCU_PLL->USBPLLCON &= ~SCU_PLL_USBPLLCON_FINDIS_Msk;
   /* restart PLL Lock detection */
   SCU_PLL->USBPLLCON |= SCU_PLL_USBPLLCON_RESLD_Msk;
   /* wait for PLL Lock */
   while (!(SCU_PLL->USBPLLSTAT & SCU_PLL_USBPLLSTAT_VCOLOCK_Msk));

  }/* end this weak function enables DAVE3 clock App usage */
   return(1);

}
#endif

