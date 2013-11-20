/**
  ******************************************************************************
  * @file    tsl_time.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the timings in general.
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

/* Includes ------------------------------------------------------------------*/
#include "tsl_time.h"
#include "tsl_globals.h"

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/
/* Private macros ------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private functions prototype -----------------------------------------------*/

/**
  * @brief  Management of the timing module interrupt service routine.
  * @param  None
  * @retval None
  */
void TSL_tim_ProcessIT(void)
{
  static TSL_tTick_ms_T count_1s = 0;

  // Count 1 global tick every xxx ms (defined by TSLPRM_TICK_FREQ parameter)
  TSL_Globals.Tick_ms++;

  // Check if 1 second has elapsed
  count_1s++;
  if (count_1s > (TSLPRM_TICK_FREQ - 1))
  {
    TSL_Globals.Tick_sec++; // 1 global tick every second
    if (TSL_Globals.Tick_sec > 63)  // Due to DTO counter on 6 bits...
    {
      TSL_Globals.Tick_sec = 0;
    }
    count_1s = 0;
  }

// Callback function
#if TSLPRM_USE_TIMER_CALLBACK > 0
  TSL_CallBack_TimerTick();
#endif

}


/**
  * @brief  Check if a delay (in ms) has elapsed.
  * This function must be called regularly due to counter Roll-over only managed one time.
  * @param[in] delay_ms  Delay in ms
  * @param[in] last_tick Variable holding the last tick value
  * @retval Status
  */
TSL_Status_enum_T TSL_tim_CheckDelay_ms(TSL_tTick_ms_T delay_ms, __IO TSL_tTick_ms_T *last_tick)
{
  TSL_tTick_ms_T tick;
  TSL_tTick_ms_T diff;

  disableInterrupts();

  tick = TSL_Globals.Tick_ms;

  if (delay_ms == 0)
  {
    enableInterrupts();
    return TSL_STATUS_ERROR;
  }

  // Counter Roll-over management
  if (tick >= *last_tick)
  {
    diff = tick - *last_tick;
  }
  else
  {
    diff = (0xFFFF - *last_tick) + tick + 1;
  }

#if (TSLPRM_TICK_FREQ == 125)
  if (diff >= (TSL_tTick_ms_T)(delay_ms >> 3)) // Divide by 8 for 8ms tick
#endif
#if (TSLPRM_TICK_FREQ == 250)
  if (diff >= (TSL_tTick_ms_T)(delay_ms >> 2)) // Divide by 4 for 4ms tick
#endif
#if (TSLPRM_TICK_FREQ == 500)
  if (diff >= (TSL_tTick_ms_T)(delay_ms >> 1)) // Divide by 2 for 2ms tick
#endif
#if (TSLPRM_TICK_FREQ == 1000)
  if (diff >= (TSL_tTick_ms_T)delay_ms) // Direct value for 1ms tick
#endif
#if (TSLPRM_TICK_FREQ == 2000)
  if (diff >= (TSL_tTick_ms_T)(delay_ms << 1)) // Multiply by 2 for 0.5ms tick
#endif
  {
    // Save current time
    *last_tick = tick;
    enableInterrupts();
    return TSL_STATUS_OK;
  }

  enableInterrupts();
  return TSL_STATUS_BUSY;

}


/**
  * @brief  Check if a delay (in s) has elapsed.
  * @param[in] delay_sec  Delay in seconds
  * @param[in] last_tick Variable holding the last tick value
  * @retval Status
  */
TSL_Status_enum_T TSL_tim_CheckDelay_sec(TSL_tTick_sec_T delay_sec, __IO TSL_tTick_sec_T *last_tick)
{
  TSL_tTick_sec_T tick;
  TSL_tTick_sec_T diff;

  disableInterrupts();

  tick = TSL_Globals.Tick_sec;

  if (delay_sec == 0)
  {
    enableInterrupts();
    return TSL_STATUS_ERROR;
  }

  // Counter Roll-over management
  if (tick >= *last_tick)
  {
    diff = (TSL_tTick_sec_T)(tick - *last_tick);
  }
  else
  {
    diff = (TSL_tTick_sec_T)((63 - *last_tick) + tick + 1); // DTO counter is on 6 bits
  }

  if (diff >= delay_sec)
  {
    // Save current time
    *last_tick = tick;
    enableInterrupts();
    return TSL_STATUS_OK;
  }

  enableInterrupts();
  return TSL_STATUS_BUSY;

}

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
