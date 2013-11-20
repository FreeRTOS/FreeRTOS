/**
  ******************************************************************************
  * @file    STM32L152_Ex06_Linear_DISC\src\tsl_user.c 
  * @author  MCD Application Team
  * @version V1.0.3
  * @date    May-2013
  * @brief   Touch-Sensing user configuration and api file.
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

#include "tsl_user.h"
#include "stm32l_discovery_lcd.h"
#include "discover_functions.h"

// PB6 = LED_GREEN
// #define LED_GREEN_TOGGLE {GPIOB->ODR  ^= (1<<7);}
// #define LED_GREEN_OFF    {GPIOB->BSRRL = (1<<7);}
// #define LED_GREEN_ON     {GPIOB->BSRRH = (1<<7);}

// PB7 = LED_BLUE
// #define LED_BLUE_TOGGLE {GPIOB->ODR  ^= (1<<6);}
// #define LED_BLUE_OFF    {GPIOB->BSRRL = (1<<6);}
// #define LED_BLUE_ON     {GPIOB->BSRRH = (1<<6);}


unsigned char Slider_Position[7];
extern uint8_t t_bar[2];

//==============================================================================
// Channels
//==============================================================================

// Channel Source and Configuration: Always placed in ROM
const TSL_ChannelSrc_T MyChannels_Src[TSLPRM_TOTAL_CHANNELS] = {
  { CHANNEL_0_SRC, CHANNEL_0_SAMPLE_CONFIG, CHANNEL_0_CHANNEL_CONFIG },
  { CHANNEL_1_SRC, CHANNEL_1_SAMPLE_CONFIG, CHANNEL_1_CHANNEL_CONFIG },
  { CHANNEL_2_SRC, CHANNEL_2_SAMPLE_CONFIG, CHANNEL_2_CHANNEL_CONFIG }
};

// Channel Destination: Always placed in ROM
const TSL_ChannelDest_T MyChannels_Dest[TSLPRM_TOTAL_CHANNELS] = {
  { CHANNEL_0_DEST },
  { CHANNEL_1_DEST },
  { CHANNEL_2_DEST }
};

// Channel Data: Always placed in RAM
TSL_ChannelData_T MyChannels_Data[TSLPRM_TOTAL_CHANNELS];

//------
// Banks
//------

// Always placed in ROM
CONST TSL_Bank_T MyBanks[TSLPRM_TOTAL_BANKS] = {
  {&MyChannels_Src[0], &MyChannels_Dest[0], MyChannels_Data, BANK_0_NBCHANNELS, BANK_0_SHIELD_SAMPLE, BANK_0_SHIELD_CHANNEL} 
};


//==============================================================================
// Linear and Rotary sensors
//==============================================================================

// Data (RAM)
TSL_LinRotData_T MyLinRots_Data[TSLPRM_TOTAL_LINROTS];

// Parameters (RAM)
TSL_LinRotParam_T MyLinRots_Param[TSLPRM_TOTAL_LINROTS];


// State Machine (ROM)


CONST TSL_State_T MyLinRots_StateMachine[] =
{
  // Calibration states
  /*  0 */ { TSL_STATEMASK_CALIB,              TSL_linrot_CalibrationStateProcess },
  /*  1 */ { TSL_STATEMASK_DEB_CALIB,          TSL_linrot_DebCalibrationStateProcess },
  // Release states 
  /*  2 */ { TSL_STATEMASK_RELEASE,            TSL_linrot_ReleaseStateProcess },
#if TSLPRM_USE_PROX > 0
  /*  3 */ { TSL_STATEMASK_DEB_RELEASE_PROX,   TSL_linrot_DebReleaseProxStateProcess },
#else
  /*  3 */ { TSL_STATEMASK_DEB_RELEASE_PROX,   0 },
#endif
  /*  4 */ { TSL_STATEMASK_DEB_RELEASE_DETECT, TSL_linrot_DebReleaseDetectStateProcess },
  /*  5 */ { TSL_STATEMASK_DEB_RELEASE_TOUCH,  TSL_linrot_DebReleaseTouchStateProcess },
#if TSLPRM_USE_PROX > 0
  // Proximity states
  /*  6 */ { TSL_STATEMASK_PROX,               TSL_linrot_ProxStateProcess },
  /*  7 */ { TSL_STATEMASK_DEB_PROX,           TSL_linrot_DebProxStateProcess },
  /*  8 */ { TSL_STATEMASK_DEB_PROX_DETECT,    TSL_linrot_DebProxDetectStateProcess },
  /*  9 */ { TSL_STATEMASK_DEB_PROX_TOUCH,     TSL_linrot_DebProxTouchStateProcess },
#else
  /*  6 */ { TSL_STATEMASK_PROX,               0 },
  /*  7 */ { TSL_STATEMASK_DEB_PROX,           0 },
  /*  8 */ { TSL_STATEMASK_DEB_PROX_DETECT,    0 },
  /*  9 */ { TSL_STATEMASK_DEB_PROX_TOUCH,     0 },
#endif
  // Detect states
  /* 10 */ { TSL_STATEMASK_DETECT,             TSL_linrot_DetectStateProcess },
  /* 11 */ { TSL_STATEMASK_DEB_DETECT,         TSL_linrot_DebDetectStateProcess },
  // Touch state
  /* 12 */ { TSL_STATEMASK_TOUCH,              TSL_linrot_TouchStateProcess },
  // Error states
  /* 13 */ { TSL_STATEMASK_ERROR,              MyLinRots_ErrorStateProcess },
  /* 14 */ { TSL_STATEMASK_DEB_ERROR_CALIB,    TSL_linrot_DebErrorStateProcess },
  /* 15 */ { TSL_STATEMASK_DEB_ERROR_RELEASE,  TSL_linrot_DebErrorStateProcess },
  /* 16 */ { TSL_STATEMASK_DEB_ERROR_PROX,     TSL_linrot_DebErrorStateProcess },
  /* 17 */ { TSL_STATEMASK_DEB_ERROR_DETECT,   TSL_linrot_DebErrorStateProcess },
  /* 18 */ { TSL_STATEMASK_DEB_ERROR_TOUCH,    TSL_linrot_DebErrorStateProcess },
  // Other states
  /* 19 */ { TSL_STATEMASK_OFF,                MyLinRots_OffStateProcess }
};

// Methods for "extended" type (ROM)
CONST TSL_LinRotMethods_T MyLinRots_Methods =
{
  TSL_linrot_Init,
  TSL_linrot_Process,
  TSL_linrot_CalcPos
};

// Delta Normalization Process
// The MSB is the integer part, the LSB is the real part
// Examples:
// - To apply a factor 1.10:
//   0x01 to the MSB
//   0x1A to the LSB (0.10 x 256 = 25.6 -> rounded to 26 = 0x1A)
// - To apply a factor 0.90:
//   0x00 to the MSB
//   0xE6 to the LSB (0.90 x 256 = 230.4 -> rounded to 230 = 0xE6)
CONST uint16_t MyLinRot_DeltaCoeff[3] = {0x0200, 0x0100, 0x0300};

// LinRots list (ROM)
CONST TSL_LinRot_T MyLinRots[TSLPRM_TOTAL_LINROTS] =
{
  {&MyLinRots_Data[0], &MyLinRots_Param[0], &MyChannels_Data[CHANNEL_0_DEST],
  3, // Number of channels
  MyLinRot_DeltaCoeff,
  (TSL_tsignPosition_T *)TSL_POSOFF_3CH_LIN_H,
  TSL_SCTCOMP_3CH_LIN_H,
  TSL_POSCORR_3CH_LIN_H,  
  MyLinRots_StateMachine,
  &MyLinRots_Methods}
};

//----------------
// Generic Objects
//----------------

// List (ROM)
CONST TSL_Object_T MyObjects[TSLPRM_TOTAL_OBJECTS] =
{
  { TSL_OBJ_LINEAR, (TSL_LinRot_T *)&MyLinRots[0] }
};

// Group (RAM)
TSL_ObjectGroup_T MyObjGroup =
{
  &MyObjects[0],        // First object
  TSLPRM_TOTAL_OBJECTS, // Number of objects
  0x00,                 // State mask reset value
  TSL_STATE_NOT_CHANGED // Current state
};

//-------------------------------------------
// TSL Common Parameters placed in RAM or ROM
// --> external declaration in tsl_conf.h
//-------------------------------------------

TSL_Params_T TSL_Params =
{
  TSLPRM_ACQ_MIN,
  TSLPRM_ACQ_MAX,
  TSLPRM_CALIB_SAMPLES,
  TSLPRM_DTO,
#if TSLPRM_TOTAL_TKEYS > 0  
  MyTKeys_StateMachine,   // Default state machine for TKeys
  &MyTKeys_Methods,       // Default methods for TKeys
#endif
#if TSLPRM_TOTAL_LNRTS > 0
  MyLinRots_StateMachine, // Default state machine for LinRots
  &MyLinRots_Methods      // Default methods for LinRots
#endif
};


/* Private functions prototype -----------------------------------------------*/

void TSL_user_InitGPIOs(void);
void TSL_user_SetThresholds(void);

/* Global variables ----------------------------------------------------------*/

TSL_tTick_ms_T ECS_last_tick; // Hold the last time value for ECS
uint32_t process_sensor; // asserted when there is no ECS => a finger is on the linear sensor


/**
  * @brief  Initialize the STMTouch Driver
  * @param  None
  * @retval None
  */
void TSL_user_Init(void)
{
#if TSLPRM_USE_SHIELD == 0
  TSL_user_InitGPIOs();
#endif

  TSL_obj_GroupInit(&MyObjGroup); // Init Objects
  
  TSL_Init(MyBanks); // Init timing and acquisition modules
  
  TSL_user_SetThresholds(); // Init thresholds for each object individually
}


/**
  * @brief  Execute STMTouch Driver main State machine
  * @param  None
  * @retval status Return TSL_STATUS_OK if the acquisition is done
  */
TSL_Status_enum_T TSL_user_Action(void)
{
  static uint8_t idx_bank=0;
  static uint8_t ConfigDone=0;
  TSL_Status_enum_T status;
  
  if(!ConfigDone)
  {
    // Configure Bank
    TSL_acq_BankConfig(idx_bank);
 
    // Start Bank acquisition
    TSL_acq_BankStartAcq();
    
    // Set flag
    ConfigDone=1;
  }
  
  // Check Bank End of Acquisition
  if (TSL_acq_BankWaitEOC() == TSL_STATUS_OK)
  {
    // Get Bank Result
    TSL_acq_BankGetResult(idx_bank, 0, 0);
    ConfigDone=0;
    idx_bank++;
  }
  

  if(idx_bank == TSLPRM_TOTAL_BANKS)
  {
    idx_bank=0;
    
    // Process Objects
    TSL_obj_GroupProcess(&MyObjGroup);
  
    // DxS processing
    // Warning: TSLPRM_USE_DXS must be set !!!
    TSL_dxs_FirstObj(&MyObjGroup);

    // ECS every 100ms
    if (TSL_tim_CheckDelay_ms(100, &ECS_last_tick) == TSL_STATUS_OK)
    {
      LED_BLUE_TOGGLE;
      if (TSL_ecs_Process(&MyObjGroup) == TSL_STATUS_OK)
      {
        LED_GREEN_ON;
        process_sensor = 0;
      }
      else
      {
        LED_GREEN_OFF;
        process_sensor = 1;
      }
    }

    
    status = TSL_STATUS_OK; // All banks have been acquired and sensors processed
    
  }
  else
  {
    status = TSL_STATUS_BUSY;
  }
  
  return status;
}


/**
  * @brief  Manage the activity on sensors when touched/released (example)
  * @param  None
  * @retval None
  */
void ProcessSensors(void)
{
  uint16_t Max_Value = 256/(9-TSLPRM_LINROT_RESOLUTION);

  uint16_t Message[6];  
  uint32_t percent_value;
  Message[0] = ' ';
  Message[1] = ' ';
  Message[2] = ' ';
  /*Add "%" in message*/ 
  Message[3] = '°' ;
  Message[4] = '/' ;
  Message[5] = '%' ;

    if (!process_sensor) 
  {
    /*Display message*/
    LCD_GLASS_DisplayStrDeci(Message);  
    return;
  }
  
  /* get Slider position and convert it in percent*/
  percent_value = MyLinRots[0].p_Data->Position ;
  percent_value *= 10000;
  percent_value /= Max_Value;
  /*Convert percent value in char and store it in message*/    
  convert_into_char(percent_value,Message);
  /*Add "%" in message*/ 
  Message[3] = '°' ;
  Message[4] = '/' ;
  Message[5] = '%' ;
  /*Display message*/
  LCD_GLASS_DisplayStrDeci(Message);  
   
}

/**
  * @brief  Manage the activity on sensors when touched/released (example)
  * @param  None
  * @retval None
  */
void ProcessSensorsButtons(void)
{
  uint8_t Message[6];  
  
    /* Prepare Message to display*/
    Message[0] = ' ';
    Message[1] = '0';
    Message[2] = '0';
    Message[3] = '0';
    Message[4] = '0';
    Message[5] = ' ';

    if (process_sensor) 
    {
				
	#ifdef STM32L1XX_MDP // for medium density plus device
			if( MyLinRots[0].p_Data->Position > 118 )
					Message[4] = 255;         
				else if( MyLinRots[0].p_Data->Position > 80 )         
					Message[3] = 255;    
				else if( MyLinRots[0].p_Data->Position > 5 ) 
					Message[2] = 255;       
				else 
					Message[1] = 255; 
	#else // for medium density device
			if( MyLinRots[0].p_Data->Position < 127 )
			{
				if( MyLinRots[0].p_Data->Position > 110 )
					Message[4] = 255;         
				else if( MyLinRots[0].p_Data->Position > 80 )         
					Message[3] = 255;    
				else if( MyLinRots[0].p_Data->Position > 5 ) 
					Message[2] = 255;       
				else 
					Message[1] = 255; 
			}
	#endif		

		}
    LCD_GLASS_DisplayString(Message);
  
}



/**
  * @brief  Initializes the TouchSensing GPIOs.
  * @param  None
  * @retval None
  */
void TSL_user_InitGPIOs(void)
{
  // Configure the Shield IO (PX.y) to ground when not used.


}


/**
  * @brief  Set thresholds for each object (optional).
  * @param  None
  * @retval None
  */
void TSL_user_SetThresholds(void)
{
  // Example: Decrease the Detect thresholds for the TKEY 0
  //MyTKeys_Param[0].DetectInTh -= 10;
  //MyTKeys_Param[0].DetectOutTh -= 10;
  
}

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
