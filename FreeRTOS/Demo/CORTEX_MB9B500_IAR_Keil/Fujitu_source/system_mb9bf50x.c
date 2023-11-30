/************************************************************************/
/*               (C) Fujitsu Semiconductor Europe GmbH (FSEU)           */
/*                                                                      */
/* The following software deliverable is intended for and must only be  */
/* used for reference and in an evaluation laboratory environment.      */
/* It is provided on an as-is basis without charge and is subject to    */
/* alterations.                                                         */
/* It is the user's obligation to fully test the software in its        */
/* environment and to ensure proper functionality, qualification and    */
/* compliance with component specifications.                            */
/*                                                                      */
/* In the event the software deliverable includes the use of open       */
/* source components, the provisions of the governing open source       */
/* license agreement shall apply with respect to such software          */
/* deliverable.                                                         */
/* FSEU does not warrant that the deliverables do not infringe any      */
/* third party intellectual property right (IPR). In the event that     */
/* the deliverables infringe a third party IPR it is the sole           */
/* responsibility of the customer to obtain necessary licenses to       */
/* continue the usage of the deliverable.                               */
/*                                                                      */
/* To the maximum extent permitted by applicable law FSEU disclaims all */
/* warranties, whether express or implied, in particular, but not       */
/* limited to, warranties of merchantability and fitness for a          */
/* particular purpose for which the deliverable is not designated.      */
/*                                                                      */
/* To the maximum extent permitted by applicable law, FSEU's liability  */
/* is restricted to intentional misconduct and gross negligence.        */
/* FSEU is not liable for consequential damages.                        */
/*                                                                      */
/* (V1.5)                                                               */
/************************************************************************/

#include <stdint.h>
#include "mb9bf506n.h"

/*--------------------- Clock Configuration ----------------------------------*/
//
// <e0> Clock Configuration
//   <h> System Clock Configuration
//     <o1.1>    SCM_CTL.MOSCE: Main clock oscillation enable
//     <o2.0..3> CSW_TMR.MOWT: Main clock stabilization wait time
//           <i> Default: ~ 500 ns
//                     < 0=> ~ 500 ns 
//                     < 1=> ~ 8 us
//                     < 2=> ~ 16 us
//                     < 3=> ~ 32 us
//                     < 4=> ~ 64 us
//                     < 5=> ~ 128 us
//                     < 6=> ~ 256 us
//                     < 7=> ~ 512 us
//                     < 8=> ~ 1.0 ms
//                     < 9=> ~ 2.0 ms
//                     <10=> ~ 4.0 ms
//                     <11=> ~ 8.0 ms
//                     <12=> ~ 33.0 ms
//                     <13=> ~ 131 ms
//                     <14=> ~ 524 ms
//                     <15=> ~ 2.0 s
//     <o1.3>    SCM_CTL.SOSCE: Sub clock oscillation enable
//     <o2.4..6> CSW_TMR.SOWT: SOWT: Sub clock stabilization wait time
//           <i> Default: ~ 31.19 ms
//                     <0=> ~ 31.19 ms 
//                     <1=> ~ 62.44 ms
//                     <2=> ~ 0.125 s
//                     <3=> ~ 0.25 s
//                     <4=> ~ 0.50 s
//                     <5=> ~ 1.00 s
//                     <6=> ~ 2.00 s
//                     <7=> ~ 4.00 s
//     <e1.4>    SCM_CTL.PLLE: PLL oscillation enable
//           <i> fPLLO Max = 120MHz, CLKPLL Min = 60MHz
//           <i> CLKPLL = (CLKMO / PLLK) * PLLN
//       <o4.4..7> PLL_CTL1.PLLK: PLL input clock frequency division
//                     <1-16><#-1>
//       <o5.0..4> PLL_CTL1.PLLN: PLL feedback frequency division
//                     <1-32><#-1>
//       <o4.0..3> PLL_CTL1.PLLM: PLL VCO clock frequency division
//                     <1-16><#-1>
//       <o3.0..2> PSW_TMR.POWT: PLL clock stabilization wait time  
//           <i> Default: ~ 128 us
//                     <0=> ~ 128 us 
//                     <1=> ~ 256 us
//                     <2=> ~ 512 us
//                     <3=> ~ 1.02 ms
//                     <4=> ~ 2.05 ms
//                     <5=> ~ 4.10 ms
//                     <6=> ~ 8.20 ms
//                     <7=> ~ 16.40 ms
//     </e>
//     <o1.5..7> SCM_CTL.RCS: Master clock switch control
//           <i> Default: Master Clock = CLKHC
//                     <0=> Master Clock = CLKHC 
//                     <1=> Master Clock = CLKMO
//                     <2=> Master Clock = CLKPLL
//                     <4=> Master Clock = CLKLC
//                     <5=> Master Clock = CLKSO
//   </h>
//
//   <h> Base Clock Prescaler
//     <o6.0..2> BSC_PSR.BSR: Base clock frequency division 
//           <i> Default: HCLK = Master Clock
//           <i> HCLK Max = 80MHz
//                     <0=> HCLK = Master Clock
//                     <1=> HCLK = Master Clock / 2
//                     <2=> HCLK = Master Clock / 3
//                     <3=> HCLK = Master Clock / 4
//                     <4=> HCLK = Master Clock / 6
//                     <5=> HCLK = Master Clock / 8
//                     <6=> HCLK = Master Clock / 16
//   </h>
//
//   <h> APB0 Prescaler
//     <o7.0..1> APBC0_PSR.APBC0: APB0 bus clock frequency division 
//           <i> PCLK0 Max = 40MHz
//           <i> Default: PCLK0 = HCLK
//                     <0=> PCLK0 = HCLK
//                     <1=> PCLK0 = HCLK / 2
//                     <2=> PCLK0 = HCLK / 4
//                     <3=> PCLK0 = HCLK / 8
//   </h>
//
//   <h> APB1 Prescaler
//     <o8.0..1> APBC1_PSR.APBC1: APB1 bus clock frequency 
//           <i> PCLK1 Max = 40MHz
//           <i> Default: PCLK1 = HCLK
//                     <0=> PCLK1 = HCLK
//                     <1=> PCLK1 = HCLK / 2
//                     <2=> PCLK1 = HCLK / 4
//                     <3=> PCLK1 = HCLK / 8
//     <o8.7>    APBC1_PSR.APBC1EN: APB1 clock enable
//   </h>
//
//   <h> APB2 Prescaler
//     <o9.0..1> APBC2_PSR.APBC2: APB2 bus clock frequency 
//           <i> PCLK2 Max = 40MHz
//           <i> Default: PCLK2 = HCLK
//                     <0=> PCLK2 = HCLK
//                     <1=> PCLK2 = HCLK / 2
//                     <2=> PCLK2 = HCLK / 4
//                     <3=> PCLK2 = HCLK / 8
//     <o9.7>    APBC2_PSR.APBC2EN: APB2 clock enable
//   </h>
//
//   <h> SW Watchdog Clock Prescaler
//     <o10.0..1>SWC_PSR.SWDS: Software watchdog clock frequency division 
//           <i> Default: SWDGOGCLK = PCLK0
//                     <0=> SWDGOGCLK = PCLK0
//                     <1=> SWDGOGCLK = PCLK0 / 2
//                     <2=> SWDGOGCLK = PCLK0 / 4
//                     <3=> SWDGOGCLK = PCLK0 / 8
//   </h>
//
//   <h> Trace Clock Prescaler
//     <o11.0>   TTC_PSR.TTC: Trace clock frequency division 
//           <i> Default: TPIUCLK = HCLK
//                     <0=> TPIUCLK = HCLK
//                     <1=> TPIUCLK = HCLK / 2
//   </h>
//
// </e>

#define CLOCK_SETUP           1
#define SCM_CTL_Val           0x00000052
#define CSW_TMR_Val           0x0000005C
#define PSW_TMR_Val           0x00000000
#define PLL_CTL1_Val          0x00000000
#define PLL_CTL2_Val          0x00000013
#define BSC_PSR_Val           0x00000000
#define APBC0_PSR_Val         0x00000001
#define APBC1_PSR_Val         0x00000082
#define APBC2_PSR_Val         0x00000081
#define SWC_PSR_Val           0x00000003
#define TTC_PSR_Val           0x00000000

/*--------------------- WatchDog Configuration -------------------------------*/
//
// <o0.0>  HW Watchdog disable 

#define HWWD_DISABLE          0x00000001

/*
//-------- <<< end of configuration section >>> ------------------------------
*/

/*----------------------------------------------------------------------------
  Check the register settings
 *----------------------------------------------------------------------------*/
#define CHECK_RANGE(val, min, max)                ((val < min) || (val > max))
#define CHECK_RSVD(val, mask)                     (val & mask)

/* Clock Configuration -------------------------------------------------------*/
#if (CHECK_RSVD((SCM_CTL_Val),    ~0x000000FA))
   #error "SCM_CTL: Invalid values of reserved bits!"
#endif

#if ((SCM_CTL_Val & 0xE0) == 0x40) && ((SCM_CTL_Val & 0x10) != 0x10)
   #error "SCM_CTL: CLKPLL is selected but PLL is not enabled!"
#endif

#if (CHECK_RSVD((CSW_TMR_Val),    ~0x0000007F))
   #error "CSW_TMR: Invalid values of reserved bits!"
#endif

#if ((SCM_CTL_Val & 0x10))       /* if PLL is used */
  #if (CHECK_RSVD((PSW_TMR_val),  ~0x00000007))
     #error "PSW_TMR: Invalid values of reserved bits!"
  #endif

  #if (CHECK_RSVD((PLL_CTL1_Val), ~0x000000FF))
     #error "PLL_CTL1: Invalid values of reserved bits!"
  #endif

  #if (CHECK_RSVD((PLL_CTL2_Val), ~0x0000001F))
     #error "PLL_CTL2: Invalid values of reserved bits!"
  #endif
#endif

#if (CHECK_RSVD((BSC_PSR_Val),    ~0x00000007))
   #error "BSC_PSR: Invalid values of reserved bits!"
#endif

#if (CHECK_RSVD((APBC0_PSR_Val),  ~0x00000003))
   #error "APBC0_PSR: Invalid values of reserved bits!"
#endif

#if (CHECK_RSVD((APBC1_PSR_Val),  ~0x00000083))
   #error "APBC1_PSR: Invalid values of reserved bits!"
#endif

#if (CHECK_RSVD((APBC2_PSR_Val),  ~0x00000083))
   #error "APBC2_PSR: Invalid values of reserved bits!"
#endif

#if (CHECK_RSVD((SWC_PSR_Val),    ~0x00000003))
   #error "SWC_PSR: Invalid values of reserved bits!"
#endif

#if (CHECK_RSVD((TTC_PSR_Val),    ~0x00000001))
   #error "TTC_PSR: Invalid values of reserved bits!"
#endif


/*----------------------------------------------------------------------------
  DEFINES
 *----------------------------------------------------------------------------*/
    
/*----------------------------------------------------------------------------
  Define clocks
 *----------------------------------------------------------------------------*/
#define __CLKMO        ( 4000000UL)         /* External   4MHz Crystal        */
#define __CLKSO        (   32768UL)         /* External  32KHz Crystal        */
#define __CLKHC        ( 4000000UL)         /* Internal   4MHz RC Oscillator  */
#define __CLKLC        (  100000UL)         /* Internal 100KHz RC Oscillator  */


/* CLKPLL = (CLKMO / PLLK) * PLLN  */
#define __PLLK         (((PLL_CTL1_Val >> 4) & 0x0F) + 1)
#define __PLLN         (((PLL_CTL2_Val     ) & 0x1F) + 1)
#define __PLLCLK       ((__CLKMO  * __PLLN) / __PLLK)

/* Determine core clock frequency according to settings */
#if   (((SCM_CTL_Val >> 5) & 0x07) == 0)
    #define __MASTERCLK     (__CLKHC)
#elif (((SCM_CTL_Val >> 5) & 0x07) == 1)
    #define __MASTERCLK     (__CLKMO)
#elif (((SCM_CTL_Val >> 5) & 0x07) == 2)
    #define __MASTERCLK     (__PLLCLK)
#elif (((SCM_CTL_Val >> 5) & 0x07) == 4)
    #define __MASTERCLK     (__CLKLC)
#elif (((SCM_CTL_Val >> 5) & 0x07) == 5)
    #define __MASTERCLK     (__CLKSO)
#else
    #define __MASTERCLK     (0UL)
#endif

#if   ((BSC_PSR_Val & 0x07) == 0)
    #define __HCLK         (__MASTERCLK / 1)
#elif ((BSC_PSR_Val & 0x07) == 1)
    #define __HCLK         (__MASTERCLK / 2)
#elif ((BSC_PSR_Val & 0x07) == 2)
    #define __HCLK         (__MASTERCLK / 3)
#elif ((BSC_PSR_Val & 0x07) == 3)
    #define __HCLK         (__MASTERCLK / 4)
#elif ((BSC_PSR_Val & 0x07) == 4)
    #define __HCLK         (__MASTERCLK / 6)
#elif ((BSC_PSR_Val & 0x07) == 5)
    #define __HCLK         (__MASTERCLK / 8)
#elif ((BSC_PSR_Val & 0x07) == 6)
    #define __HCLK         (__MASTERCLK /16)
#else
    #define __HCLK         (0UL)
#endif



/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
uint32_t SystemCoreClock = __HCLK;    /*!< System Clock Frequency (Core Clock)*/


/**
 * Retrieve the system core clock
 *
 * @param  none
 * @return none
 *
 * @brief  retrieve system core clock from register settings.
 */
void SystemCoreClockUpdate (void) {
  uint32_t masterClk;
  uint32_t u32RegisterRead;

  switch ((FM3_CRG->SCM_CTL >> 5) & 0x07) {
    case 0:                                 /* internal High-speed Cr osc.    */
      masterClk = __CLKHC;
      break;

    case 1:                                 /* external main osc.             */
      masterClk = __CLKMO;
      break;

    case 2:                                 /* PLL clock                      */
      u32RegisterRead = (__CLKMO  * (((FM3_CRG->PLL_CTL2) & 0x1F) + 1));
      masterClk = (u32RegisterRead / (((FM3_CRG->PLL_CTL1 >> 4) & 0x0F) + 1));
      break;

    case 4:                                 /* internal Low-speed CR osc.     */
      masterClk = __CLKLC;
      break;

    case 5:                                 /* external Sub osc.              */
      masterClk = __CLKSO;
      break;

    default:
      masterClk = 0Ul;
      break;
  }

  switch (FM3_CRG->BSC_PSR & 0x07) {
    case 0:
      SystemCoreClock = masterClk;
      break;

    case 1:
      SystemCoreClock = masterClk / 2;
      break;

    case 2:
      SystemCoreClock = masterClk / 3;
      break;

    case 3:
      SystemCoreClock = masterClk / 4;
      break;

    case 4:
      SystemCoreClock = masterClk / 6;
      break;

    case 5:
      SystemCoreClock = masterClk /8;
      break;

    case 6:
      SystemCoreClock = masterClk /16;
      break;

    default:
      SystemCoreClock = 0Ul;
      break;
  }

}

/*
 *  Set CR Trimming Data
 *
 * @param  none
 * @return none
 *
 * @brief  Update CR trimming with Flash
 *         trimming data.
 */
static void CrtrimSet(void)
{
    /* CR Trimming Data  */
    if( 0x000003FF != (FM3_FLASH_IF->CRTRMM & 0x000003FF) )
    {
	    /* UnLock (MCR_FTRM) */
        FM3_CRTRIM->MCR_RLR = 0x1ACCE554;
	    /* Set MCR_FTRM */
        FM3_CRTRIM->MCR_FTRM = FM3_FLASH_IF->CRTRMM;
	    /* Lock (MCR_FTRM) */
        FM3_CRTRIM->MCR_RLR = 0x00000000;
    }
}

/**
 * Initialize the system
 *
 * @param  none
 * @return none
 *
 * @brief  Setup the microcontroller system.
 *         Initialize the System.
 */
void SystemInit (void) {

  uint32_t u32RegisterRead;
  
#if (HWWD_DISABLE)                                   /* HW Watchdog Disable */
  FM3_HWWDT->WDG_LCK = 0x1ACCE551;                     /* HW Watchdog Unlock */
  FM3_HWWDT->WDG_LCK = 0xE5331AAE;
  FM3_HWWDT->WDG_CTL = 0;                              /* HW Watchdog stop */
#endif

#if (CLOCK_SETUP)                                    /* Clock Setup */
  FM3_CRG->BSC_PSR   = BSC_PSR_Val;                /* set System Clock presacaler */
  FM3_CRG->APBC0_PSR = APBC0_PSR_Val;              /* set APB0 presacaler */
  FM3_CRG->APBC1_PSR = APBC1_PSR_Val;              /* set APB1 presacaler */
  FM3_CRG->APBC2_PSR = APBC2_PSR_Val;              /* set APB2 presacaler */
  FM3_CRG->SWC_PSR   = SWC_PSR_Val | (1UL << 7);   /* set SW Watchdog presacaler */
  FM3_CRG->TTC_PSR   = TTC_PSR_Val;                /* set Trace Clock presacaler */

  FM3_CRG->CSW_TMR   = CSW_TMR_Val;                /* set oscillation stabilization wait time */
  if (SCM_CTL_Val & (1UL << 1)) {                    /* Main clock oscillator enabled ? */
    FM3_CRG->SCM_CTL |= (1UL << 1);                /* enable main oscillator */ 
    while (!(FM3_CRG->SCM_STR & (1UL << 1)));      /* wait for Main clock oscillation stable */
  }
  if (SCM_CTL_Val & (1UL << 3)) {                    /* Sub clock oscillator enabled ? */
    FM3_CRG->SCM_CTL |= (1UL << 3);                /* enable sub oscillator */ 
    while (!(FM3_CRG->SCM_STR & (1UL << 3)));      /* wait for Sub clock oscillation stable */
  }

  FM3_CRG->PSW_TMR   = PSW_TMR_Val;                /* set PLL stabilization wait time */
  FM3_CRG->PLL_CTL1  = PLL_CTL1_Val;               /* set PLLM and PLLK */
  FM3_CRG->PLL_CTL2  = PLL_CTL2_Val;               /* set PLLN          */
  if (SCM_CTL_Val & (1UL << 4)) {                    /* PLL enabled ? */
    FM3_CRG->SCM_CTL  |= (1UL << 4);               /* enable PLL */ 
    while (!(FM3_CRG->SCM_STR & (1UL << 4)));      /* wait for PLL stable */
  }

  FM3_CRG->SCM_CTL  |= (SCM_CTL_Val & 0xE0);       /* Set Master Clock switch */ 
  do
  {
    u32RegisterRead = (FM3_CRG->SCM_CTL & 0xE0);
  }while ((FM3_CRG->SCM_STR & 0xE0) != u32RegisterRead);
#endif
  CrtrimSet();
}



