/***************************************************************************//**
 * @file em_system.h
 * @brief System API
 * @version 4.0.0
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
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


#ifndef __SILICON_LABS_EM_SYSTEM_H_
#define __SILICON_LABS_EM_SYSTEM_H_

#include <stdbool.h>
#include "em_device.h"

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup SYSTEM
 * @{
 ******************************************************************************/

/*******************************************************************************
 ********************************   ENUMS   ************************************
 ******************************************************************************/

/** EFM32 part family identifiers. */
typedef enum
{
/* New style family #defines */
#if defined ( _DEVINFO_PART_DEVICE_FAMILY_EFM32G )
  systemPartFamilyEfm32Gecko   = _DEVINFO_PART_DEVICE_FAMILY_EFM32G,   /**< EFM32 Gecko Device Family */
#endif
#if defined ( _DEVINFO_PART_DEVICE_FAMILY_EFM32GG )
  systemPartFamilyEfm32Giant   = _DEVINFO_PART_DEVICE_FAMILY_EFM32GG,  /**< EFM32 Giant Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_EFM32TG )
  systemPartFamilyEfm32Tiny    = _DEVINFO_PART_DEVICE_FAMILY_EFM32TG,  /**< EFM32 Tiny Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_EFM32LG )
  systemPartFamilyEfm32Leopard = _DEVINFO_PART_DEVICE_FAMILY_EFM32LG,  /**< EFM32 Leopard Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_EFM32WG )
  systemPartFamilyEfm32Wonder  = _DEVINFO_PART_DEVICE_FAMILY_EFM32WG,  /**< EFM32 Wonder Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_EFM32ZG )
  systemPartFamilyEfm32Zero    = _DEVINFO_PART_DEVICE_FAMILY_EFM32ZG,  /**< EFM32 Zero Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_EFM32HG )
  systemPartFamilyEfm32Happy   = _DEVINFO_PART_DEVICE_FAMILY_EFM32HG,  /**< EFM32 Happy Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_EZR32WG )
  systemPartFamilyEzr32Wonder  = _DEVINFO_PART_DEVICE_FAMILY_EZR32WG,  /**< EZR32 Wonder Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_EZR32LG )
  systemPartFamilyEzr32Leopard = _DEVINFO_PART_DEVICE_FAMILY_EZR32LG,  /**< EZR32 Leopard Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_EZR32HG )
  systemPartFamilyEzr32Happy   = _DEVINFO_PART_DEVICE_FAMILY_EZR32HG,  /**< EZR32 Happy Device Family */
#endif
/* Legacy family #defines */
#if defined( _DEVINFO_PART_DEVICE_FAMILY_G )
  systemPartFamilyGecko   = _DEVINFO_PART_DEVICE_FAMILY_G,   /**< Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_GG )
  systemPartFamilyGiant   = _DEVINFO_PART_DEVICE_FAMILY_GG,  /**< Giant Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_TG )
  systemPartFamilyTiny    = _DEVINFO_PART_DEVICE_FAMILY_TG,  /**< Tiny Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_LG )
  systemPartFamilyLeopard = _DEVINFO_PART_DEVICE_FAMILY_LG,  /**< Leopard Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_WG )
  systemPartFamilyWonder  = _DEVINFO_PART_DEVICE_FAMILY_WG,  /**< Wonder Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_ZG )
  systemPartFamilyZero    = _DEVINFO_PART_DEVICE_FAMILY_ZG,  /**< Zero Gecko Device Family */
#endif
#if defined( _DEVINFO_PART_DEVICE_FAMILY_HG )
  systemPartFamilyHappy   = _DEVINFO_PART_DEVICE_FAMILY_HG,  /**< Happy Gecko Device Family */
#endif
  systemPartFamilyUnknown = 0xFF                             /**< Unknown Device Family.
                                                                  The family id is missing
                                                                  on unprogrammed parts. */
} SYSTEM_PartFamily_TypeDef;


/*******************************************************************************
 *******************************   STRUCTS   ***********************************
 ******************************************************************************/

/** Chip revision details */
typedef struct
{
  uint8_t minor; /**< Minor revision number */
  uint8_t major; /**< Major revision number */
  uint8_t family;/**< Device family number  */
} SYSTEM_ChipRevision_TypeDef;

#if defined( __FPU_PRESENT ) && ( __FPU_PRESENT == 1 )
/** Floating point coprocessor access modes. */
typedef enum
{
  fpuAccessDenied         = (0x0 << 20),  /**< Access denied, any attempted access generates a NOCP UsageFault. */
  fpuAccessPrivilegedOnly = (0x5 << 20),  /**< Privileged access only, an unprivileged access generates a NOCP UsageFault. */
  fpuAccessReserved       = (0xA << 20),  /**< Reserved. */
  fpuAccessFull           = (0xF << 20)   /**< Full access. */
} SYSTEM_FpuAccess_TypeDef;
#endif

/*******************************************************************************
 *****************************   PROTOTYPES   **********************************
 ******************************************************************************/

void     SYSTEM_ChipRevisionGet(SYSTEM_ChipRevision_TypeDef *rev);
uint32_t SYSTEM_GetCalibrationValue(volatile uint32_t *regAddress);

#if defined( __FPU_PRESENT ) && ( __FPU_PRESENT == 1 )
/***************************************************************************//**
 * @brief
 *   Set floating point coprocessor (FPU) access mode.
 *
 * @param[in] accessMode
 *   Floating point coprocessor access mode. See @ref SYSTEM_FpuAccess_TypeDef
 *   for details.
 ******************************************************************************/
__STATIC_INLINE void SYSTEM_FpuAccessModeSet(SYSTEM_FpuAccess_TypeDef accessMode)
{
  SCB->CPACR = (SCB->CPACR & ~(0xF << 20)) | accessMode;
}
#endif

/***************************************************************************//**
 * @brief
 *   Get the unique number for this part.
 *
 * @return
 *   Unique number for this part.
 ******************************************************************************/
__STATIC_INLINE uint64_t SYSTEM_GetUnique(void)
{
  return ((uint64_t) ((uint64_t) DEVINFO->UNIQUEH << 32) | (uint64_t) DEVINFO->UNIQUEL);
}

/***************************************************************************//**
 * @brief
 *   Get the production revision for this part.
 *
 * @return
 *   Production revision for this part.
 ******************************************************************************/
__STATIC_INLINE uint8_t SYSTEM_GetProdRev(void)
{
  return ((DEVINFO->PART & _DEVINFO_PART_PROD_REV_MASK)
                         >> _DEVINFO_PART_PROD_REV_SHIFT);
}

/***************************************************************************//**
 * @brief
 *   Get the SRAM size (in KB).
 *
 * @note
 *   This function retrievs the correct value by reading the chip device
 *   info structure. If your binary is made for one specific device only,
 *   the \#define SRAM_SIZE can be used instead.
 *
 * @return
 *   The size of the internal SRAM (in KB).
 ******************************************************************************/
__STATIC_INLINE uint16_t SYSTEM_GetSRAMSize(void)
{
#if defined(_EFM32_GECKO_FAMILY)
  /* Early Gecko devices had a bug where SRAM and Flash size were swapped. */
  if (SYSTEM_GetProdRev() < 5)
  {
    return (DEVINFO->MSIZE & _DEVINFO_MSIZE_FLASH_MASK)
                           >> _DEVINFO_MSIZE_FLASH_SHIFT;
  }
#endif
  return (DEVINFO->MSIZE & _DEVINFO_MSIZE_SRAM_MASK)
                         >> _DEVINFO_MSIZE_SRAM_SHIFT;
}

/***************************************************************************//**
 * @brief
 *   Get the flash size (in KB).
 *
 * @note
 *   This function retrievs the correct value by reading the chip device
 *   info structure. If your binary is made for one specific device only,
 *   the \#define FLASH_SIZE can be used instead.
 *
 * @return
 *   The size of the internal flash (in KB).
 ******************************************************************************/
__STATIC_INLINE uint16_t SYSTEM_GetFlashSize(void)
{
#if defined(_EFM32_GECKO_FAMILY)
  /* Early Gecko devices had a bug where SRAM and Flash size were swapped. */
  if (SYSTEM_GetProdRev() < 5)
  {
    return (DEVINFO->MSIZE & _DEVINFO_MSIZE_SRAM_MASK)
                           >> _DEVINFO_MSIZE_SRAM_SHIFT;
  }
#endif
  return (DEVINFO->MSIZE & _DEVINFO_MSIZE_FLASH_MASK)
                         >> _DEVINFO_MSIZE_FLASH_SHIFT;
}


/***************************************************************************//**
 * @brief
 *   Get the flash page size in bytes.
 *
 * @note
 *   This function retrievs the correct value by reading the chip device
 *   info structure. If your binary is made for one specific device only,
 *   the \#define FLASH_PAGE_SIZE can be used instead.
 *
 * @return
 *   The page size of the internal flash in bytes.
 ******************************************************************************/
__STATIC_INLINE uint32_t SYSTEM_GetFlashPageSize(void)
{
  uint32_t tmp;

#if defined( _EFM32_GIANT_FAMILY )
  tmp = SYSTEM_GetProdRev();
  if (tmp < 18)
  {
    /* Early Giant/Leopard devices did not have MEMINFO in DEVINFO. */
    return FLASH_PAGE_SIZE;
  }
#elif defined( _EFM32_ZERO_FAMILY )
  tmp = SYSTEM_GetProdRev();
  if (tmp < 24)
  {
    /* Early Zero devices have an incorrect DEVINFO flash page size */
    return FLASH_PAGE_SIZE;
  }
#endif
  tmp = (DEVINFO->MEMINFO & _DEVINFO_MEMINFO_FLASH_PAGE_SIZE_MASK)
                 >> _DEVINFO_MEMINFO_FLASH_PAGE_SIZE_SHIFT;

  return 1 << ((tmp + 10) & 0xFF);
}


/***************************************************************************//**
 * @brief
 *   Get part number of the MCU.
 *
 * @return
 *   The part number of the MCU.
 ******************************************************************************/
__STATIC_INLINE uint16_t SYSTEM_GetPartNumber(void)
{
  return (DEVINFO->PART & _DEVINFO_PART_DEVICE_NUMBER_MASK)
                        >> _DEVINFO_PART_DEVICE_NUMBER_SHIFT;
}

/***************************************************************************//**
 * @brief
 *   Get family identifier of the MCU.
 *
 * @note
 *   This function retrievs the family id by reading the chip's device info
 *   structure in flash memory. The user can retrieve the family id directly
 *   by reading the DEVINFO->PART item and decode with the mask and shift
 *   \#defines defined in \<part_family\>_devinfo.h (please refer to code
 *   below for details).
 *
 * @return
 *   The family identifier of the MCU.
 ******************************************************************************/
__STATIC_INLINE SYSTEM_PartFamily_TypeDef SYSTEM_GetFamily(void)
{
  return (SYSTEM_PartFamily_TypeDef)
    ((DEVINFO->PART & _DEVINFO_PART_DEVICE_FAMILY_MASK)
     >> _DEVINFO_PART_DEVICE_FAMILY_SHIFT);
}


/***************************************************************************//**
 * @brief
 *   Get the calibration temperature (in degrees Celsius).
 *
 * @return
 *   The calibration temperature in Celsius.
 ******************************************************************************/
__STATIC_INLINE uint8_t SYSTEM_GetCalibrationTemperature(void)
{
  return (DEVINFO->CAL & _DEVINFO_CAL_TEMP_MASK)
                       >> _DEVINFO_CAL_TEMP_SHIFT;
}

/** @} (end addtogroup SYSTEM) */
/** @} (end addtogroup EM_Library) */

#ifdef __cplusplus
}
#endif

#endif /* __SILICON_LABS_EM_SYSTEM_H_ */
