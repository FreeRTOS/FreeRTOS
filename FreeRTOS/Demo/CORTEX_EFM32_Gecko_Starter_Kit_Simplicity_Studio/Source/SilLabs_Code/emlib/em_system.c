/***************************************************************************//**
 * @file em_system.c
 * @brief System Peripheral API
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

#include "em_system.h"
#include "em_assert.h"

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup SYSTEM
 * @brief System Peripheral API
 * @{
 ******************************************************************************/

/*******************************************************************************
 **************************   GLOBAL FUNCTIONS   *******************************
 ******************************************************************************/

/***************************************************************************//**
 * @brief
 *   Get chip major/minor revision.
 *
 * @param[out] rev
 *   Location to place chip revision info.
 ******************************************************************************/
void SYSTEM_ChipRevisionGet(SYSTEM_ChipRevision_TypeDef *rev)
{
  uint8_t tmp;

  EFM_ASSERT(rev);

  /* CHIP FAMILY bit [5:2] */
  tmp  = (((ROMTABLE->PID1 & _ROMTABLE_PID1_FAMILYMSB_MASK) >> _ROMTABLE_PID1_FAMILYMSB_SHIFT) << 2);
  /* CHIP FAMILY bit [1:0] */
  tmp |=  ((ROMTABLE->PID0 & _ROMTABLE_PID0_FAMILYLSB_MASK) >> _ROMTABLE_PID0_FAMILYLSB_SHIFT);
  rev->family = tmp;

  /* CHIP MAJOR bit [3:0] */
  rev->major = (ROMTABLE->PID0 & _ROMTABLE_PID0_REVMAJOR_MASK) >> _ROMTABLE_PID0_REVMAJOR_SHIFT;

  /* CHIP MINOR bit [7:4] */
  tmp  = (((ROMTABLE->PID2 & _ROMTABLE_PID2_REVMINORMSB_MASK) >> _ROMTABLE_PID2_REVMINORMSB_SHIFT) << 4);
  /* CHIP MINOR bit [3:0] */
  tmp |=  ((ROMTABLE->PID3 & _ROMTABLE_PID3_REVMINORLSB_MASK) >> _ROMTABLE_PID3_REVMINORLSB_SHIFT);
  rev->minor = tmp;
}


#if defined(CALIBRATE)
/***************************************************************************//**
 * @brief
 *    Get factory calibration value for a given peripheral register.
 *
 * @param[in] regAddress
 *    Address of register to get a calibration value for.
 *
 * @return
 *    Calibration value for the requested register.
 ******************************************************************************/
uint32_t SYSTEM_GetCalibrationValue(volatile uint32_t *regAddress)
{
  int               regCount;
  CALIBRATE_TypeDef *p;

  regCount = 1;
  p        = CALIBRATE;

  for (;; )
  {
    if ((regCount > CALIBRATE_MAX_REGISTERS) ||
        (p->VALUE == 0xFFFFFFFF))
    {
      EFM_ASSERT(false);
      return 0;                 /* End of device calibration table reached. */
    }

    if (p->ADDRESS == (uint32_t)regAddress)
    {
      return p->VALUE;          /* Calibration value found ! */
    }

    p++;
    regCount++;
  }
}
#endif /* defined (CALIBRATE) */

/** @} (end addtogroup SYSTEM) */
/** @} (end addtogroup EM_Library) */
