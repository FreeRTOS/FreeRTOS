/***************************************************************************//**
 * @file em_idac.h
 * @brief Current Digital to Analog Converter (IDAC) peripheral API
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


#ifndef __SILICON_LABS_EM_IDAC_H_
#define __SILICON_LABS_EM_IDAC_H_

#include "em_device.h"

#if defined(IDAC_COUNT) && (IDAC_COUNT > 0)
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup IDAC
 * @{
 ******************************************************************************/

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */

/** Validation of IDAC register block pointer reference for assert statements. */
#define IDAC_REF_VALID(ref)    ((ref) == IDAC0)

/** @endcond */

/*******************************************************************************
 ********************************   ENUMS   ************************************
 ******************************************************************************/

/** Output mode. */
typedef enum
{
  idacOutputPin     = IDAC_CTRL_OUTMODE_PIN,     /**< Output to IDAC OUT pin */
  idacOutputADC     = IDAC_CTRL_OUTMODE_ADC      /**< Output to ADC */
} IDAC_OutMode_TypeDef;


/** Selects which Peripheral Reflex System (PRS) signal to use when
    PRS is set to control the IDAC output. */
typedef enum
{
  idacPRSSELCh0 = IDAC_CTRL_PRSSEL_PRSCH0,      /**< PRS channel 0. */
  idacPRSSELCh1 = IDAC_CTRL_PRSSEL_PRSCH1,      /**< PRS channel 1. */
  idacPRSSELCh2 = IDAC_CTRL_PRSSEL_PRSCH2,      /**< PRS channel 2. */
  idacPRSSELCh3 = IDAC_CTRL_PRSSEL_PRSCH3,      /**< PRS channel 3. */
#if  defined( IDAC_CTRL_PRSSEL_PRSCH4 )
  idacPRSSELCh4 = IDAC_CTRL_PRSSEL_PRSCH4,      /**< PRS channel 4. */
#endif
#if  defined( IDAC_CTRL_PRSSEL_PRSCH5 )
  idacPRSSELCh5 = IDAC_CTRL_PRSSEL_PRSCH5,      /**< PRS channel 5. */
#endif
#if  defined( IDAC_CTRL_PRSSEL_PRSCH6 )
  idacPRSSELCh6 = IDAC_CTRL_PRSSEL_PRSCH6,      /**< PRS channel 6. */
#endif
#if  defined( IDAC_CTRL_PRSSEL_PRSCH7 )
  idacPRSSELCh7 = IDAC_CTRL_PRSSEL_PRSCH7,      /**< PRS channel 7. */
#endif
#if  defined( IDAC_CTRL_PRSSEL_PRSCH8 )
  idacPRSSELCh8 = IDAC_CTRL_PRSSEL_PRSCH8,      /**< PRS channel 8. */
#endif
#if  defined( IDAC_CTRL_PRSSEL_PRSCH9 )
  idacPRSSELCh9 = IDAC_CTRL_PRSSEL_PRSCH9,      /**< PRS channel 9. */
#endif
#if  defined( IDAC_CTRL_PRSSEL_PRSCH10 )
  idacPRSSELCh10 = IDAC_CTRL_PRSSEL_PRSCH10,    /**< PRS channel 10 */
#endif
#if  defined( IDAC_CTRL_PRSSEL_PRSCH11 )
  idacPRSSELCh11 = IDAC_CTRL_PRSSEL_PRSCH11,    /**< PRS channel 11 */
#endif
} IDAC_PRSSEL_TypeDef;


/** Selects which current range to use. */
typedef enum
{
  idacCurrentRange0 = IDAC_CURPROG_RANGESEL_RANGE0, /**< current range 0. */
  idacCurrentRange1 = IDAC_CURPROG_RANGESEL_RANGE1, /**< current range 1. */
  idacCurrentRange2 = IDAC_CURPROG_RANGESEL_RANGE2, /**< current range 2. */
  idacCurrentRange3 = IDAC_CURPROG_RANGESEL_RANGE3, /**< current range 3. */
} IDAC_Range_TypeDef;

/*******************************************************************************
 *******************************   STRUCTS   ***********************************
 ******************************************************************************/

/** IDAC init structure, common for both channels. */
typedef struct
{
  /** Enable IDAC. */
  bool                  enable;

  /** Output mode */
  IDAC_OutMode_TypeDef  outMode;

  /**
   * Enable Peripheral reflex system (PRS) to control IDAC output. If false,
   * the IDAC output is controlled by writing to IDAC_OUTEN in IDAC_CTRL or
   * by calling IDAC_OutEnable().
   */
  bool                  prsEnable;

  /**
   * Peripheral reflex system channel selection. Only applicable if @p prsEnable
   * is enabled.
   */
  IDAC_PRSSEL_TypeDef   prsSel;

  /** Enable/disable current sink mode. */
  bool                  sinkEnable;

} IDAC_Init_TypeDef;

/** Default config for IDAC init structure. */
#define IDAC_INIT_DEFAULT                                             \
  { false,          /* Leave IDAC disabled when init done. */         \
    idacOutputPin,   /* Output to IDAC OUT pin. */                     \
    false,          /* Disable PRS triggering. */                     \
    idacPRSSELCh0,  /* Select PRS ch0 (if PRS triggering enabled). */ \
    false           /* Disable current sink mode. */                  \
  }


/*******************************************************************************
 *****************************   PROTOTYPES   **********************************
 ******************************************************************************/

/***************************************************************************//**
 * @brief
 *   Initialize IDAC.
 *
 * @details
 *   Initializes IDAC according to the initialization structure parameter, and
 *   sets the default calibration value stored in the DEVINFO structure.
 *
 * @note
 *   This function will disable the IDAC prior to configuration.
 *
 * @param[in] idac
 *   Pointer to IDAC peripheral register block.
 *
 * @param[in] init
 *   Pointer to IDAC initialization structure.
 ******************************************************************************/
void IDAC_Init(IDAC_TypeDef *idac, const IDAC_Init_TypeDef *init);


/***************************************************************************//**
 * @brief
 *   Enable/disable IDAC.
 *
 * @param[in] idac
 *   Pointer to IDAC peripheral register block.
 *
 * @param[in] enable
 *   true to enable IDAC, false to disable.
 ******************************************************************************/
void IDAC_Enable(IDAC_TypeDef *idac, bool enable);


/***************************************************************************//**
 * @brief
 *   Reset IDAC to same state as after a HW reset.
 *
 * @param[in] idac
 *   Pointer to IDAC peripheral register block.
 ******************************************************************************/
void IDAC_Reset(IDAC_TypeDef *idac);


/***************************************************************************//**
 * @brief
 *   Enable/disable Minimal Output Transition mode.
 *
 * @param[in] idac
 *   Pointer to IDAC peripheral register block.
 *
 * @param[in] enable
 *   true to enable Minimal Output Transition mode, false to disable.
 ******************************************************************************/
void IDAC_MinimalOutputTransitionMode(IDAC_TypeDef *idac, bool enable);


/***************************************************************************//**
 * @brief
 *   Set the current range of the IDAC output.
 *
 * @details
 *   This function sets the current range of the IDAC output. The function
 *   also updates the IDAC calibration register (IDAC_CAL) with the default
 *   calibration value (from DEVINFO, factory setting) corresponding to the
 *   specified range.
 *
 * @param[in] idac
 *   Pointer to IDAC peripheral register block.
 *
 * @param[in] range
 *   Current range value.
 ******************************************************************************/
void IDAC_RangeSet(IDAC_TypeDef *idac, const IDAC_Range_TypeDef range);


/***************************************************************************//**
 * @brief
 *   Set the current step of the IDAC output.
 *
 * @param[in] idac
 *   Pointer to IDAC peripheral register block.
 *
 * @param[in] step
 *   Step value for IDAC output. Valid range is 0-31.
 ******************************************************************************/
void IDAC_StepSet(IDAC_TypeDef *idac, const uint32_t step);


/***************************************************************************//**
 * @brief
 *   Enable/disable the IDAC OUT pin.
 *
 * @param[in] idac
 *   Pointer to IDAC peripheral register block.
 *
 * @param[in] enable
 *   true to enable the IDAC OUT pin, false to disable.
 ******************************************************************************/
void IDAC_OutEnable(IDAC_TypeDef *idac, bool enable);


/** @} (end addtogroup IDAC) */
/** @} (end addtogroup EM_Library) */

#ifdef __cplusplus
}
#endif

#endif /* defined(IDAC_COUNT) && (IDAC_COUNT > 0) */

#endif /* __SILICON_LABS_EM_IDAC_H_ */
