/**
  ******************************************************************************
  * @file    tsl_types.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all general structures definition.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT 2013 STMicroelectronics</center></h2>
  *
  * Licensed under MCD-ST Liberty SW License Agreement V2, (the "License");
  * You may not use this file except in compliance with the License.
  * You may obtain a copy of the License at:
  *
  *        http://www.st.com/software_license_agreement_liberty_v2
  *
  * Unless required by applicable law or agreed to in writing, software
  * distributed under the License is distributed on an "AS IS" BASIS,
  * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  * See the License for the specific language governing permissions and
  * limitations under the License.
  *
  ******************************************************************************
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __TSL_TYPES_H
#define __TSL_TYPES_H

/* Exported types ------------------------------------------------------------*/

/** Generic Boolean status
*/
typedef enum
{
  TSL_FALSE = 0, /**< A False value */
  TSL_TRUE  = 1  /**< A True value */
}
TSL_Bool_enum_T;

/** Generic status returned by functions
*/
typedef enum
{
  TSL_STATUS_OK      = 0, /**< The function has been executed correctly */
  TSL_STATUS_BUSY    = 1, /**< The function is in a Busy state */
  TSL_STATUS_ERROR   = 2  /**< The function has been executed not correctly */
} TSL_Status_enum_T;

/** DataReady status : 1 bit
  - Used by acquisition to indicate if a new measurement is ready or not.
*/
typedef enum
{
  TSL_DATA_NOT_READY = 0, /**< No new measurement or measurement treated */
  TSL_DATA_READY     = 1  /**< A new measurement is ready */
} TSL_DataReady_enum_T;

/** State change status
*/
typedef enum
{
  TSL_STATE_NOT_CHANGED = 0, /**< The object has the same state */
  TSL_STATE_CHANGED     = 1  /**< The object has changed of state */
} TSL_StateChange_enum_T;

#define TSL_ACQ_STATUS_ERROR_MASK (0x02) /**< Associated to TSL_AcqStatus_enum_T */

/** Acquisition status
*/
typedef enum
{
  TSL_ACQ_STATUS_OK        = 0, /**< The acquisition is correct */
  TSL_ACQ_STATUS_NOISE     = 1, /**< Noise detected during the acquisition */
  TSL_ACQ_STATUS_ERROR_MIN = TSL_ACQ_STATUS_ERROR_MASK, /**< The measure is below the minimum threshold */
  TSL_ACQ_STATUS_ERROR_MAX = (TSL_ACQ_STATUS_ERROR_MASK | 0x01) /**< The measure is above the maximum threshold */
} TSL_AcqStatus_enum_T;

/** Bank status
*/
typedef enum
{
  TSL_BANK_STATUS_DISABLED = 0, /**< The bank is disabled */
  TSL_BANK_STATUS_ENABLED  = 1  /**< The bank is enabled */
} TSL_BankStatus_enum_T;

/** Zone status
*/
typedef enum
{
  TSL_ZONE_STATUS_DISABLED = 0, /**< The zone is disabled */
  TSL_ZONE_STATUS_ENABLED  = 1  /**< The zone is enabled */
}TSL_ZoneStatus_enum_T;

#define TSL_OBJ_STATUS_ACQ_MASK   (0x01) /**< Associated to TSL_ObjStatus_enum_T */
#define TSL_OBJ_STATUS_BURST_MASK (0x02) /**< Associated to TSL_ObjStatus_enum_T */

/** Object status
*/
typedef enum
{
  TSL_OBJ_STATUS_OFF        = 0, /**< No burst and no acquisition */
  TSL_OBJ_STATUS_BURST_ONLY = TSL_OBJ_STATUS_BURST_MASK, /**< Burst only */
  TSL_OBJ_STATUS_ON         = (TSL_OBJ_STATUS_BURST_MASK | TSL_OBJ_STATUS_ACQ_MASK) /**< Burst and acquisition */
} TSL_ObjStatus_enum_T;

#define TSL_STATE_ERROR_BIT_MASK    (0x80) /**< Associated to TSL_StateMask_enum_T */
#define TSL_STATE_OFF_BIT_MASK      (0x40) /**< Associated to TSL_StateMask_enum_T */
#define TSL_STATE_DEBOUNCE_BIT_MASK (0x20) /**< Associated to TSL_StateMask_enum_T */
#define TSL_STATE_CALIB_BIT_MASK    (0x10) /**< Associated to TSL_StateMask_enum_T */
#define TSL_STATE_TOUCH_BIT_MASK    (0x08) /**< Associated to TSL_StateMask_enum_T */
#define TSL_STATE_DETECT_BIT_MASK   (0x04) /**< Associated to TSL_StateMask_enum_T */
#define TSL_STATE_PROX_BIT_MASK     (0x02) /**< Associated to TSL_StateMask_enum_T */
#define TSL_STATE_RELEASE_BIT_MASK  (0x01) /**< Associated to TSL_StateMask_enum_T */

/** Object state masks
*/
typedef enum
{
  // Calibration states
  TSL_STATEMASK_CALIB              = TSL_STATE_CALIB_BIT_MASK, /**< 0x10 */
  TSL_STATEMASK_DEB_CALIB          = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_CALIB_BIT_MASK), /**< 0x30 */
  // Release states
  TSL_STATEMASK_RELEASE            = TSL_STATE_RELEASE_BIT_MASK, /**< 0x01 */
  TSL_STATEMASK_DEB_RELEASE_PROX   = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_RELEASE_BIT_MASK | TSL_STATE_PROX_BIT_MASK), /**< 0x23 */
  TSL_STATEMASK_DEB_RELEASE_DETECT = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_RELEASE_BIT_MASK | TSL_STATE_DETECT_BIT_MASK), /**< 0x25 */
  TSL_STATEMASK_DEB_RELEASE_TOUCH  = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_RELEASE_BIT_MASK | TSL_STATE_TOUCH_BIT_MASK), /**< 0x29 */
  // Proximity states
  TSL_STATEMASK_PROX               = TSL_STATE_PROX_BIT_MASK, /**< 0x02 */
  TSL_STATEMASK_DEB_PROX           = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_PROX_BIT_MASK), /**< 0x22 */
  TSL_STATEMASK_DEB_PROX_DETECT    = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_PROX_BIT_MASK | TSL_STATE_DETECT_BIT_MASK), /**< 0x26 */
  TSL_STATEMASK_DEB_PROX_TOUCH     = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_PROX_BIT_MASK | TSL_STATE_TOUCH_BIT_MASK), /**< 0x2A */
  // Detect states
  TSL_STATEMASK_DETECT             = TSL_STATE_DETECT_BIT_MASK, /**< 0x04 */
  TSL_STATEMASK_DEB_DETECT         = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_DETECT_BIT_MASK), /**< 0x24 */
  // Touch state
  TSL_STATEMASK_TOUCH              = TSL_STATE_TOUCH_BIT_MASK, /**< 0x08 */
  // Error states
  TSL_STATEMASK_ERROR              = TSL_STATE_ERROR_BIT_MASK, /**< 0x80 */
  TSL_STATEMASK_DEB_ERROR_CALIB    = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_ERROR_BIT_MASK | TSL_STATE_CALIB_BIT_MASK), /**< 0xB0 */
  TSL_STATEMASK_DEB_ERROR_RELEASE  = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_ERROR_BIT_MASK | TSL_STATE_RELEASE_BIT_MASK), /**< 0xA1 */
  TSL_STATEMASK_DEB_ERROR_PROX     = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_ERROR_BIT_MASK | TSL_STATE_PROX_BIT_MASK), /**< 0xA2 */
  TSL_STATEMASK_DEB_ERROR_DETECT   = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_ERROR_BIT_MASK | TSL_STATE_DETECT_BIT_MASK), /**< 0xA4 */
  TSL_STATEMASK_DEB_ERROR_TOUCH    = (TSL_STATE_DEBOUNCE_BIT_MASK | TSL_STATE_ERROR_BIT_MASK | TSL_STATE_TOUCH_BIT_MASK), /**< 0xA8 */
  // OFF state
  TSL_STATEMASK_OFF                = TSL_STATE_OFF_BIT_MASK, /**< 0x40 */
  // Other states not associated to a state id
  TSL_STATEMASK_ACTIVE             = (TSL_STATE_PROX_BIT_MASK | TSL_STATE_DETECT_BIT_MASK | TSL_STATE_TOUCH_BIT_MASK | TSL_STATE_CALIB_BIT_MASK | TSL_STATE_DEBOUNCE_BIT_MASK), /**< 0x3E */
  TSL_STATEMASK_UNKNOWN            = 0 /**< 0x00 */
} TSL_StateMask_enum_T;

/** Object state identifiers
*/
typedef enum
{
  // Calibration states
  TSL_STATEID_CALIB              = 0,  /**<  0 - Object is in Calibration */
  TSL_STATEID_DEB_CALIB          = 1,  /**<  1 - Object is in Debounce Calibration */
  // Release states
  TSL_STATEID_RELEASE            = 2,  /**<  2 - Object is released */
  TSL_STATEID_DEB_RELEASE_PROX   = 3,  /**<  3 - Object is in Debounce Release from Proximity state */
  TSL_STATEID_DEB_RELEASE_DETECT = 4,  /**<  4 - Object is in Debounce Release from Detect state */
  TSL_STATEID_DEB_RELEASE_TOUCH  = 5,  /**<  5 - Object is in Debounce Release from Touch state */
  // Proximity states
  TSL_STATEID_PROX               = 6,  /**<  6 - Object is in Proximity */
  TSL_STATEID_DEB_PROX           = 7,  /**<  7 - Object is in Debounce Proximity from Release state */
  TSL_STATEID_DEB_PROX_DETECT    = 8,  /**<  8 - Object is in Debounce Proximity from Detect state */
  TSL_STATEID_DEB_PROX_TOUCH     = 9,  /**<  9 - Object is in Debounce Proximity from Detect state */
  // Detect states
  TSL_STATEID_DETECT             = 10, /**< 10 - Object is in Detect */
  TSL_STATEID_DEB_DETECT         = 11, /**< 11 - Object is in Debounce Detect */
  // Touch state
  TSL_STATEID_TOUCH              = 12, /**< 12 - Object is in Touch */
  // Error states
  TSL_STATEID_ERROR              = 13, /**< 13 - Object is in Error */
  TSL_STATEID_DEB_ERROR_CALIB    = 14, /**< 14 - Object is in Debounce Error from Calibration */
  TSL_STATEID_DEB_ERROR_RELEASE  = 15, /**< 15 - Object is in Debounce Error from Release */
  TSL_STATEID_DEB_ERROR_PROX     = 16, /**< 16 - Object is in Debounce Error from Proximity */
  TSL_STATEID_DEB_ERROR_DETECT   = 17, /**< 17 - Object is in Debounce Error from Detect */
  TSL_STATEID_DEB_ERROR_TOUCH    = 18, /**< 18 - Object is in Debounce Error from Touch */
  // Other states
  TSL_STATEID_OFF                = 19  /**< 19 - Object is OFF (no burst, no acquisition) */
} TSL_StateId_enum_T;

/** Object state
*/
typedef struct
{
  TSL_StateMask_enum_T StateMask; /**< Current state mask */
  void(* StateFunc)(void); /**< Function executed in the state */
}
TSL_State_T;

/** Touchkey methods
*/
typedef struct
{
  void(* Init)(void); /**< Used to initialize the TouchKey sensor */
  void(* Process)(void); /**< Used to execute the TouchKey sensor state machine */
}
TSL_TouchKeyMethods_T;

/** Linear/Rotary methods
*/
typedef struct
{
  void(* Init)(void); /**< Used to initialize the Linear/Rotary sensor */
  void(* Process)(void); /**< Used to execute the Linear/Rotary sensor state machine */
  TSL_Status_enum_T(* CalcPosition)(void); /**< Used to calculate the Linear/Rotary sensor position */
}
TSL_LinRotMethods_T;

#endif /* __TSL_TYPES_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
