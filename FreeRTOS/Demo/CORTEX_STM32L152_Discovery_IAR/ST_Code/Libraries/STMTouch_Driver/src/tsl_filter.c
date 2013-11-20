/**
  ******************************************************************************
  * @file    tsl_filter.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the signal or delta filters.
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
#include "tsl_filter.h"

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/
/* Private macros ------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private functions prototype -----------------------------------------------*/

/* Noise Filter description
   ------------------------

The noise filter is a first order IRR digital filter based on the following formula:

S(n) = (1-k).S(n-1)+ k.N(n)

S(n) : sample number n of the filtered signal
N(n) : sample number n of the raw signal
k    : filter coefficient parameter in [0..1]

The filter sampling rate is the acquisition rate.

In order to optimize the implementation in the firmware, the above formula is
modified in order to have only one multiply operation:

S(n) = S(n-1) + k.(N(n) - S(n-1))

Additionally, we use k = K/256 with K an unsigned 8-bit integer.

The K is given by the ACQ_FILTER_COEFF constant.

S(n) = S(n-1) + K.(N(n) - S(n-1))/(2^8)

and the division can be done easily with bit shifting.

As we are in the digital world, this formula presents a drawback:
if the difference between S(n-1) and N(n) is less than 1/k, there will be no
difference between S(n-1) and S(n).

As a consequence, there will be a static error of up to 1/k.

In the STMTouch Driver, the S(n) is stored in the Meas element of the data
structure after each acquisition:

Meas(n) = S(n) = N(n)

The formula is then:

Meas(n) = Meas(n-1) + K.(Meas(n) - Meas(n-1))/(2^8)

In order to reduce the static error, we can use "Meas(n) = S(n).2^P".

The P is given by the ACQ_FILTER_RANGE constant.

This would shift the signal value left and provides a few additional low
significant bits useful to reduce the static error.

Warning: all thresholds must be shifted accordingly if the parameter P is
different from 0.

If we report this into the filter formula we obtain:

Meas(n) = Meas(n-1) + K.[ Meas(n)*2^P - Meas(n-1)]/2^8

In this case the static error is reduced to 1/(k.2^P)
*/

#define ACQ_FILTER_RANGE (0)   /* Range[0..5] - Warning: all thresholds must be shifted if different from 0 */

#define ACQ_FILTER_COEFF (128) /* Range[1..255] - First order filter coefficient (k = ACQ_FILTER_COEFF/256) */

/**
  * @brief Example of measure value filter
  * @param[in] measn1 Previous measure value
  * @param[in] measn  Current measure value
  * @retval Filtered measure
  */
TSL_tMeas_T TSL_filt_MeasFilter(TSL_tMeas_T measn1, TSL_tMeas_T measn)
{
  TSL_tMeas_T val;

  val = (TSL_tMeas_T)(measn << ACQ_FILTER_RANGE);

  if (measn1 != 0)
  {
    if (val > measn1)
    {
      val = measn1 + ((ACQ_FILTER_COEFF * (val - measn1)) >> 8);
    }
    else
    {
      val = measn1 - ((ACQ_FILTER_COEFF * (measn1 - val)) >> 8);
    }
  }

  return(val);
}


/**
  * @brief Example of delta value filter
  * @param[in] delta  Delta value to modify
  * @retval Filtered delta
  */
TSL_tDelta_T TSL_filt_DeltaFilter(TSL_tDelta_T delta)
{
  return(delta);
}

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
