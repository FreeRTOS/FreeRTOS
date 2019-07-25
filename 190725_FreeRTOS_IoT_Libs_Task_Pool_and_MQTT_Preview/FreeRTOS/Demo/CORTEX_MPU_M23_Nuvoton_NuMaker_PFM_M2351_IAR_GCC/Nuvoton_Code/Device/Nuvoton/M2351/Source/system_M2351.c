/**************************************************************************//**
 * @file     system_M2351.c
 * @version  V2.00
 * @brief    System Setting Source File
 *
 * @note
 * Copyright (C) 2016 Nuvoton Technology Corp. All rights reserved.
 *
 ******************************************************************************/
#if defined (__ARMCC_VERSION) && (__ARMCC_VERSION >= 6010050)       /* ARM Compiler 6 */
#include <arm_cmse.h>
#endif

#include <stdio.h>
#include <stdint.h>
#include "NuMicro.h"

#if defined (__ARM_FEATURE_CMSE) &&  (__ARM_FEATURE_CMSE == 3U)
#include "partition_M2351.h"
#endif

extern void *__Vectors;                   /* see startup file */


/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
uint32_t SystemCoreClock  = __HSI;              /*!< System Clock Frequency (Core Clock) */
uint32_t CyclesPerUs      = (__HSI / 1000000UL);/*!< Cycles per micro second             */
uint32_t PllClock         = __HSI;              /*!< PLL Output Clock Frequency          */
const uint32_t gau32ClkSrcTbl[] = {__HXT, __LXT, 0UL, __LIRC, 0UL, __HIRC48, 0UL, __HIRC};


/**
 * @brief    Update the Variable SystemCoreClock
 *
 * @param    None
 *
 * @return   None
 *
 * @details  This function is used to update the variable SystemCoreClock
 *           and must be called whenever the core clock is changed.
 */
void SystemCoreClockUpdate(void)
{
    /* Update PLL Clock */
    PllClock = CLK_GetPLLClockFreq();

    /* Update System Core Clock */
    SystemCoreClock = CLK_GetCPUFreq();

    /* Update Cycles per micro second */
    CyclesPerUs = (SystemCoreClock + 500000UL) / 1000000UL;
}



/**
 * @brief    System Initialization
 *
 * @param    None
 *
 * @return   None
 *
 * @details  The necessary initialization of system. Global variables are forbidden here.
 */
void SystemInit(void)
{
#if defined (__VTOR_PRESENT) && (__VTOR_PRESENT == 1U)
    SCB->VTOR = (uint32_t) &__Vectors;
#endif

#if defined (__ARM_FEATURE_CMSE) && (__ARM_FEATURE_CMSE == 3)
    TZ_SAU_Setup();
    SCU_Setup();
    FMC_NSBA_Setup();
#endif

#ifdef INIT_SYSCLK_AT_BOOTING

#endif

}


#if USE_ASSERT

/**
 * @brief      Assert Error Message
 *
 * @param[in]  file  the source file name
 * @param[in]  line  line number
 *
 * @return     None
 *
 * @details    The function prints the source file name and line number where
 *             the ASSERT_PARAM() error occurs, and then stops in an infinite loop.
 */
void AssertError(uint8_t * file, uint32_t line)
{

    printf("[%s] line %d : wrong parameters.\r\n", file, line);

    /* Infinite loop */
    while(1) ;
}
#endif


#if (defined(__ICCARM__) && (__VER__ >= 7080000) && (__VER__ < 8020000))

#if  (__ARM_FEATURE_CMSE == 3U)
/**
  \brief   Get Process Stack Pointer (non-secure)
  \details Returns the current value of the non-secure Process Stack Pointer (PSP) when in secure state.
  \return               PSP Register value
 */
uint32_t __TZ_get_PSP_NS(void)
{
    register uint32_t result;

    __ASM volatile("MRS %0, psp_ns"  : "=r"(result));
    return(result);
}


/**
  \brief   Set Process Stack Pointer (non-secure)
  \details Assigns the given value to the non-secure Process Stack Pointer (PSP) when in secure state.
  \param [in]    topOfProcStack  Process Stack Pointer value to set
 */
void __TZ_set_PSP_NS(uint32_t topOfProcStack)
{
    __ASM volatile("MSR psp_ns, %0" : : "r"(topOfProcStack));
}



/**
  \brief   Get Main Stack Pointer (non-secure)
  \details Returns the current value of the non-secure Main Stack Pointer (MSP) when in secure state.
  \return               MSP Register value
 */
int32_t __TZ_get_MSP_NS(void)
{
    register uint32_t result;

    __ASM volatile("MRS %0, msp_ns" : "=r"(result));
    return(result);
}



/**
  \brief   Set Main Stack Pointer (non-secure)
  \details Assigns the given value to the non-secure Main Stack Pointer (MSP) when in secure state.
  \param [in]    topOfMainStack  Main Stack Pointer value to set
 */
void __TZ_set_MSP_NS(uint32_t topOfMainStack)
{
    __ASM volatile("MSR msp_ns, %0" : : "r"(topOfMainStack));
}



/**
  \brief   Get Priority Mask (non-secure)
  \details Returns the current state of the non-secure priority mask bit from the Priority Mask Register when in secure state.
  \return               Priority Mask value
 */
uint32_t __TZ_get_PRIMASK_NS(void)
{
    uint32_t result;

    __ASM volatile("MRS %0, primask_ns" : "=r"(result));
    return(result);
}



/**
  \brief   Set Priority Mask (non-secure)
  \details Assigns the given value to the non-secure Priority Mask Register when in secure state.
  \param [in]    priMask  Priority Mask
 */
void __TZ_set_PRIMASK_NS(uint32_t priMask)
{
    __ASM volatile("MSR primask_ns, %0" : : "r"(priMask) : "memory");
}


#endif


#endif



