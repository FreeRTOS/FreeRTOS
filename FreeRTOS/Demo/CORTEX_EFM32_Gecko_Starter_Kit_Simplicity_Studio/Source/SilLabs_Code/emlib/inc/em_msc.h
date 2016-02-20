/***************************************************************************//**
 * @file em_msc.h
 * @brief Flash controller module (MSC) peripheral API
 * @version 4.2.1
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2015 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 *    claim that you wrote the original software.
 * 2. Altered source versions must be plainly marked as such, and must not be
 *    misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source distribution.
 *
 * DISCLAIMER OF WARRANTY/LIMITATION OF REMEDIES: Silicon Labs has no
 * obligation to support this Software. Silicon Labs is providing the
 * Software "AS IS", with no express or implied warranties of any kind,
 * including, but not limited to, any implied warranties of merchantability
 * or fitness for any particular purpose or warranties against infringement
 * of any proprietary rights of a third party.
 *
 * Silicon Labs will not be liable for any consequential, incidental, or
 * special damages, or any other relief, or for any claim by any third party,
 * arising from your use of this Software.
 *
 ******************************************************************************/

#ifndef __SILICON_LABS_EM_MSC_H__
#define __SILICON_LABS_EM_MSC_H__

#include "em_device.h"
#if defined(MSC_COUNT) && (MSC_COUNT > 0)

#include <stdint.h>
#include <stdbool.h>
#include "em_bus.h"

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup MSC
 * @brief Flash controller (MSC) peripheral API
 * @{
 ******************************************************************************/

/*******************************************************************************
 *************************   DEFINES   *****************************************
 ******************************************************************************/

/**
 * @brief
 *    The timeout used while waiting for the flash to become ready after
 *    a write. This number indicates the number of iterations to perform before
 *    issuing a timeout.
 * @note
 *    This timeout is set very large (in the order of 100x longer than
 *    necessary). This is to avoid any corner cases.
 *
 */
#define MSC_PROGRAM_TIMEOUT    10000000ul

/**
 * @brief
 *    By compiling with the define EM_MSC_RUN_FROM_FLASH the Flash
 *    controller (MSC) peripheral will remain in and execute from flash.
 *    This is useful for targets that don't want to allocate RAM space to
 *    hold the flash functions.  Without this define the MSC peripheral
 *    functions will be copied into and run out of RAM.
 * @note
 *    This define is commented out by default so the MSC controller API
 *    will run from RAM by default.
 *
 */
#if defined( DOXY_DOC_ONLY )
#define EM_MSC_RUN_FROM_FLASH
#else
//#define EM_MSC_RUN_FROM_FLASH
#endif

/*******************************************************************************
 *************************   TYPEDEFS   ****************************************
 ******************************************************************************/

/** Return codes for writing/erasing the flash */
typedef enum
{
  mscReturnOk          = 0,  /**< Flash write/erase successful. */
  mscReturnInvalidAddr = -1, /**< Invalid address. Write to an address that is not flash. */
  mscReturnLocked      = -2, /**< Flash address is locked. */
  mscReturnTimeOut     = -3, /**< Timeout while writing to flash. */
  mscReturnUnaligned   = -4  /**< Unaligned access to flash. */
} MSC_Status_TypeDef;


#if defined( _MSC_READCTRL_BUSSTRATEGY_MASK )
/** Strategy for prioritized bus access */
typedef enum
{
  mscBusStrategyCPU = MSC_READCTRL_BUSSTRATEGY_CPU,       /**< Prioritize CPU bus accesses */
  mscBusStrategyDMA = MSC_READCTRL_BUSSTRATEGY_DMA,       /**< Prioritize DMA bus accesses */
  mscBusStrategyDMAEM1 = MSC_READCTRL_BUSSTRATEGY_DMAEM1, /**< Prioritize DMAEM1 for bus accesses */
  mscBusStrategyNone = MSC_READCTRL_BUSSTRATEGY_NONE      /**< No unit has bus priority */
} MSC_BusStrategy_Typedef;
#endif

/** Code execution configuration */
typedef struct
{
  bool scbtEn;          /**< Enable Suppressed Conditional Branch Target Prefetch */
  bool prefetchEn;      /**< Enable MSC prefetching */
  bool ifcDis;          /**< Disable instruction cache */
  bool aiDis;           /**< Disable automatic cache invalidation on write or erase */
  bool iccDis;          /**< Disable automatic caching of fetches in interrupt context */
  bool useHprot;        /**< Use ahb_hprot to determine if the instruction is cacheable or not */
} MSC_ExecConfig_TypeDef;

/** Default MSC ExecConfig initialization */
#define MSC_EXECCONFIG_DEFAULT  \
{                               \
  false,                        \
  true,                         \
  false,                        \
  false,                        \
  false,                        \
  false,                        \
}

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */
/* Legacy type names */
#define mscBusStrategy_Typedef MSC_BusStrategy_Typedef
#define msc_Return_TypeDef MSC_Status_TypeDef
/** @endcond */

/*******************************************************************************
 *************************   PROTOTYPES   **************************************
 ******************************************************************************/

void MSC_Init(void);
void MSC_Deinit(void);
#if !defined( _EFM32_GECKO_FAMILY )
void MSC_ExecConfigSet(MSC_ExecConfig_TypeDef *execConfig);
#endif

/***************************************************************************//**
 * @brief
 *    Clear one or more pending MSC interrupts.
 *
 * @param[in] flags
 *    Pending MSC intterupt source to clear. Use a bitwise logic OR combination
 *   of valid interrupt flags for the MSC module (MSC_IF_nnn).
 ******************************************************************************/
__STATIC_INLINE void MSC_IntClear(uint32_t flags)
{
  MSC->IFC = flags;
}

/***************************************************************************//**
 * @brief
 *   Disable one or more MSC interrupts.
 *
 * @param[in] flags
 *   MSC interrupt sources to disable. Use a bitwise logic OR combination of
 *   valid interrupt flags for the MSC module (MSC_IF_nnn).
 ******************************************************************************/
__STATIC_INLINE void MSC_IntDisable(uint32_t flags)
{
  MSC->IEN &= ~(flags);
}


/***************************************************************************//**
 * @brief
 *   Enable one or more MSC interrupts.
 *
 * @note
 *   Depending on the use, a pending interrupt may already be set prior to
 *   enabling the interrupt. Consider using MSC_IntClear() prior to enabling
 *   if such a pending interrupt should be ignored.
 *
 * @param[in] flags
 *   MSC interrupt sources to enable. Use a bitwise logic OR combination of
 *   valid interrupt flags for the MSC module (MSC_IF_nnn).
 ******************************************************************************/
__STATIC_INLINE void MSC_IntEnable(uint32_t flags)
{
  MSC->IEN |= flags;
}


/***************************************************************************//**
 * @brief
 *   Get pending MSC interrupt flags.
 *
 * @note
 *   The event bits are not cleared by the use of this function.
 *
 * @return
 *   MSC interrupt sources pending. A bitwise logic OR combination of valid
 *   interrupt flags for the MSC module (MSC_IF_nnn).
 ******************************************************************************/
__STATIC_INLINE uint32_t MSC_IntGet(void)
{
  return(MSC->IF);
}


/***************************************************************************//**
 * @brief
 *   Get enabled and pending MSC interrupt flags.
 *   Useful for handling more interrupt sources in the same interrupt handler.
 *
 * @note
 *   Interrupt flags are not cleared by the use of this function.
 *
 * @return
 *   Pending and enabled MSC interrupt sources
 *   The return value is the bitwise AND of
 *   - the enabled interrupt sources in MSC_IEN and
 *   - the pending interrupt flags MSC_IF
 ******************************************************************************/
__STATIC_INLINE uint32_t MSC_IntGetEnabled(void)
{
  uint32_t ien;

  ien = MSC->IEN;
  return MSC->IF & ien;
}


/***************************************************************************//**
 * @brief
 *   Set one or more pending MSC interrupts from SW.
 *
 * @param[in] flags
 *   MSC interrupt sources to set to pending. Use a bitwise logic OR combination of
 *   valid interrupt flags for the MSC module (MSC_IF_nnn).
 ******************************************************************************/
__STATIC_INLINE void MSC_IntSet(uint32_t flags)
{
  MSC->IFS = flags;
}


#if defined( MSC_IF_CHOF ) && defined( MSC_IF_CMOF )
/***************************************************************************//**
 * @brief
 *   Starts measuring cache hit ratio.
 * @details
 *   This function starts the performance counters. It is defined inline to
 *   minimize the impact of this code on the measurement itself.
 ******************************************************************************/
__STATIC_INLINE void MSC_StartCacheMeasurement(void)
{
  /* Clear CMOF and CHOF to catch these later */
  MSC->IFC = MSC_IF_CHOF | MSC_IF_CMOF;

  /* Start performance counters */
#if defined( _MSC_CACHECMD_MASK )
  MSC->CACHECMD = MSC_CACHECMD_STARTPC;
#else
  MSC->CMD = MSC_CMD_STARTPC;
#endif
}


/***************************************************************************//**
 * @brief
 *   Stops measuring the hit rate.
 * @note
 *   This function is defined inline to minimize the impact of this
 *   code on the measurement itself.
 *   This code only works for relatively short sections of code. If you wish
 *   to measure longer sections of code you need to implement a IRQ Handler for
 *   The CHOF and CMOF overflow interrupts. Theses overflows needs to be
 *   counted and included in the total.
 *   The functions can then be implemented as follows:
 * @verbatim
 * volatile uint32_t hitOverflows
 * volatile uint32_t missOverflows
 *
 * void MSC_IRQHandler(void)
 * {
 *   uint32_t flags;
 *   flags = MSC->IF;
 *   if (flags & MSC_IF_CHOF)
 *   {
 *      MSC->IFC = MSC_IF_CHOF;
 *      hitOverflows++;
 *   }
 *   if (flags & MSC_IF_CMOF)
 *   {
 *     MSC->IFC = MSC_IF_CMOF;
 *     missOverflows++;
 *   }
 * }
 *
 * void startPerformanceCounters(void)
 * {
 *   hitOverflows = 0;
 *   missOverflows = 0;
 *
 *   MSC_IntEnable(MSC_IF_CHOF | MSC_IF_CMOF);
 *   NVIC_EnableIRQ(MSC_IRQn);
 *
 *   MSC_StartCacheMeasurement();
 * }
 * @endverbatim
 * @return
 *   Returns -1 if there has been no cache accesses.
 *   Returns -2 if there has been an overflow in the performance counters.
 *   If not, it will return the percentage of hits versus misses.
 ******************************************************************************/
__STATIC_INLINE int32_t MSC_GetCacheMeasurement(void)
{
  int32_t total;
  /* Stop the counter before computing the hit-rate */
#if defined( _MSC_CACHECMD_MASK )
  MSC->CACHECMD = MSC_CACHECMD_STOPPC;
#else
  MSC->CMD = MSC_CMD_STOPPC;
#endif

  /* Check for overflows in performance counters */
  if (MSC->IF & (MSC_IF_CHOF | MSC_IF_CMOF))
    return -2;

  /* Because the hits and misses are volatile, we need to split this up into
   * two statements to avoid a compiler warning regarding the order of volatile
   * accesses. */
  total  = MSC->CACHEHITS;
  total += MSC->CACHEMISSES;

  /* To avoid a division by zero. */
  if (total == 0)
    return -1;

  return (MSC->CACHEHITS * 100) / total;
}


/***************************************************************************//**
 * @brief
 *   Flush the contents of the instruction cache.
 ******************************************************************************/
__STATIC_INLINE void MSC_FlushCache(void)
{
#if defined( _MSC_CACHECMD_MASK )
  MSC->CACHECMD = MSC_CACHECMD_INVCACHE;
#else
  MSC->CMD = MSC_CMD_INVCACHE;
#endif
}


/***************************************************************************//**
 * @brief
 *   Enable or disable instruction cache functionality
 * @param[in] enable
 *   Enable instruction cache. Default is on.
 ******************************************************************************/
__STATIC_INLINE void MSC_EnableCache(bool enable)
{
  BUS_RegBitWrite(&(MSC->READCTRL), _MSC_READCTRL_IFCDIS_SHIFT, !enable);
}


#if defined( MSC_READCTRL_ICCDIS )
/***************************************************************************//**
 * @brief
 *   Enable or disable instruction cache functionality in IRQs
 * @param[in] enable
 *   Enable instruction cache. Default is on.
 ******************************************************************************/
__STATIC_INLINE void MSC_EnableCacheIRQs(bool enable)
{
  BUS_RegBitWrite(&(MSC->READCTRL), _MSC_READCTRL_ICCDIS_SHIFT, !enable);
}
#endif


/***************************************************************************//**
 * @brief
 *   Enable or disable instruction cache flushing when writing to flash
 * @param[in] enable
 *   Enable automatic cache flushing. Default is on.
 ******************************************************************************/
__STATIC_INLINE void MSC_EnableAutoCacheFlush(bool enable)
{
  BUS_RegBitWrite(&(MSC->READCTRL), _MSC_READCTRL_AIDIS_SHIFT, !enable);
}
#endif /* defined( MSC_IF_CHOF ) && defined( MSC_IF_CMOF ) */


#if defined( _MSC_READCTRL_BUSSTRATEGY_MASK )
/***************************************************************************//**
 * @brief
 *   Configure which unit should get priority on system bus.
 * @param[in] mode
 *   Unit to prioritize bus accesses for.
 ******************************************************************************/
__STATIC_INLINE void MSC_BusStrategy(mscBusStrategy_Typedef mode)
{
  MSC->READCTRL = (MSC->READCTRL & ~(_MSC_READCTRL_BUSSTRATEGY_MASK)) | mode;
}
#endif

#if defined(EM_MSC_RUN_FROM_FLASH)
#define MSC_FUNC_PREFIX
#define MSC_FUNC_POSTFIX
#elif defined(__CC_ARM)
#define MSC_FUNC_PREFIX
#define MSC_FUNC_POSTFIX
#elif defined(__ICCARM__)
#define MSC_FUNC_PREFIX   __ramfunc
#define MSC_FUNC_POSTFIX
#elif defined(__GNUC__) && defined(__CROSSWORKS_ARM)
#define MSC_FUNC_PREFIX
#define MSC_FUNC_POSTFIX  __attribute__ ((section(".fast")))
#elif defined(__GNUC__)
#define MSC_FUNC_PREFIX
#define MSC_FUNC_POSTFIX  __attribute__ ((section(".ram")))
#endif


MSC_FUNC_PREFIX MSC_Status_TypeDef
  MSC_WriteWord(uint32_t *address,
                void const *data,
                uint32_t numBytes) MSC_FUNC_POSTFIX;

#if !defined( _EFM32_GECKO_FAMILY )
MSC_FUNC_PREFIX MSC_Status_TypeDef
  MSC_WriteWordFast(uint32_t *address,
                    void const *data,
                    uint32_t numBytes) MSC_FUNC_POSTFIX;

#endif

MSC_FUNC_PREFIX MSC_Status_TypeDef
  MSC_ErasePage(uint32_t *startAddress) MSC_FUNC_POSTFIX;

#if defined( _MSC_MASSLOCK_MASK )
MSC_FUNC_PREFIX MSC_Status_TypeDef MSC_MassErase(void) MSC_FUNC_POSTFIX;
#endif

/** @} (end addtogroup MSC) */
/** @} (end addtogroup EM_Library) */

#ifdef __cplusplus
}
#endif

#endif /* defined(MSC_COUNT) && (MSC_COUNT > 0) */
#endif /* __SILICON_LABS_EM_MSC_H__ */
