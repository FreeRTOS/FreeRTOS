/** @file etpwm.c
 *   @brief ETPWM Driver Source File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - API Functions
 *   - Interrupt Handlers
 *   .
 *   which are relevant for the ETPWM driver.
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#include "etpwm.h"
#include "pinmux.h"
#include "sys_vim.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/** @fn void etpwmInit(void)
 *   @brief Initializes the eTPWM Driver
 *
 *   This function initializes the eTPWM module.
 *
 *   @note This function sets the time-base counters in up-count mode.
 *   Application can configure the module in a different mode using other functions in
 * this driver.(Sample code provided in the examples folder) In that case, application
 * need not call etpwmInit function. pinmuxInit needs to be called before this function.
 *
 */
/* SourceId : ETPWM_SourceId_001 */
/* DesignId : ETPWM_DesignId_001 */
/* Requirements : CONQ_EPWM_SR2 */
void etpwmInit( void )
{
    /* USER CODE BEGIN (1) */
    /* USER CODE END */

    /** @b initialize @b ETPWM1 */

    /** - Sets high speed time-base clock prescale bits */
    etpwmREG1->TBCTL = ( uint16 ) 0U << 7U;

    /** - Sets time-base clock prescale bits */
    etpwmREG1->TBCTL |= ( uint16 ) ( ( uint16 ) 0U << 10U );

    /** - Sets time period or frequency for ETPWM block both PWMA and PWMB*/
    etpwmREG1->TBPRD = 1000U;

    /** - Setup the duty cycle for PWMA */
    etpwmREG1->CMPA = 50U;

    /** - Setup the duty cycle for PWMB */
    etpwmREG1->CMPB = 50U;

    /** - Force EPWMxA output high when counter reaches zero and low when counter reaches
     * Compare A value */
    etpwmREG1->AQCTLA = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) );

    /** - Force EPWMxB output high when counter reaches zero and low when counter reaches
     * Compare B value */
    etpwmREG1->AQCTLB = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) );

    /** - Mode setting for Dead Band Module
     *     -Select the input mode for Dead Band Module
     *     -Select the output mode for Dead Band Module
     *     -Select Polarity of the output PWMs
     */
    etpwmREG1->DBCTL = ( ( uint16 ) ( ( uint16 ) 0U << 5U )   /* Source for Falling edge
                                                                 delay(0-PWMA, 1-PWMB) */
                         | ( uint16 ) ( ( uint16 ) 0u << 4U ) /* Source for Rising edge
                                                                 delay(0-PWMA, 1-PWMB)  */
                         | ( uint16 ) ( ( uint16 ) 0U << 3U ) /* Enable/Disable EPWMxB
                                                                 invert       */
                         | ( uint16 ) ( ( uint16 ) 0U << 2U ) /* Enable/Disable EPWMxA
                                                                 invert       */
                         | ( uint16 ) ( ( uint16 ) 0U << 1U ) /* Enable/Disable Rising
                                                                 Edge Delay   */
                         | ( uint16 ) ( ( uint16 ) 0U << 0U ) ); /* Enable/Disable Falling
                                                                    Edge Delay  */

    /** - Set the rising edge delay  */
    etpwmREG1->DBRED = 1U;

    /** - Set the falling edge delay  */
    etpwmREG1->DBFED = 1U;

    /** - Enable the chopper module for ETPWMx
     *     -Sets the One shot pulse width in a chopper modulated wave
     *     -Sets the dutycycle for the subsequent pulse train
     *     -Sets the period for the subsequent pulse train
     */
    etpwmREG1->PCCTL = ( ( uint16 ) ( ( uint16 ) 0U << 0U )   /* Enable/Disable chopper
                                                                 module */
                         | ( uint16 ) ( ( uint16 ) 1U << 1U ) /* One-shot Pulse Width */
                         | ( uint16 ) ( ( uint16 ) 3U << 8U ) /* Chopping Clock Duty Cycle
                                                               */
                         | ( uint16 ) ( ( uint16 ) 0U << 5U ) ); /* Chopping Clock
                                                                    Frequency */

    /** - Set trip source enable */
    etpwmREG1->TZSEL = 0x0000U  /** - Enable/Disable TZ1 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ2 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ3 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ4 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ5 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ6 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ1 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ2 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ3 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ4 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ5 as a CBC trip source      */
                     | 0x0000U; /** - Enable/Disable TZ6 as a CBC trip source      */

    /** - Set interrupt enable */
    etpwmREG1
        ->TZEINT = 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1  */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2  */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1  */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2  */
                 | 0x0000U  /** - Enable/Disable one-shot interrupt generation        */
                 | 0x0000U; /** - Enable/Disable cycle-by-cycle interrupt generation  */

    /** - Sets up the event for interrupt */
    etpwmREG1->ETSEL = ( uint16 ) NO_EVENT;

    if( ( etpwmREG1->ETSEL & 0x0007U ) != 0U )
    {
        etpwmREG1->ETSEL |= 0x0008U;
    }
    /** - Setup the frequency of the interrupt generation */
    etpwmREG1->ETPS = 1U;

    /** - Sets up the ADC SOC interrupt */
    etpwmREG1->ETSEL |= ( ( uint16 ) ( 0x0000U ) | ( uint16 ) ( 0x0000U )
                          | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )
                          | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U ) );

    /** - Sets up the ADC SOC period */
    etpwmREG1->ETPS |= ( ( uint16 ) ( ( uint16 ) 1U << 8U )
                         | ( uint16 ) ( ( uint16 ) 1U << 12U ) );

    /** @b initialize @b ETPWM2 */

    /** - Sets high speed time-base clock prescale bits */
    etpwmREG2->TBCTL = ( uint16 ) 0U << 7U;

    /** - Sets time-base clock prescale bits */
    etpwmREG2->TBCTL |= ( uint16 ) ( ( uint16 ) 0U << 10U );

    /** - Sets time period or frequency for ETPWM block both PWMA and PWMB*/
    etpwmREG2->TBPRD = 1000U;

    /** - Setup the duty cycle for PWMA */
    etpwmREG2->CMPA = 50U;

    /** - Setup the duty cycle for PWMB */
    etpwmREG2->CMPB = 50U;

    /** - Force EPWMxA output high when counter reaches zero and low when counter reaches
     * Compare A value */
    etpwmREG2->AQCTLA = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) );

    /** - Force EPWMxB output high when counter reaches zero and low when counter reaches
     * Compare B value */
    etpwmREG2->AQCTLB = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) );

    /** - Mode setting for Dead Band Module
     *     -Select the input mode for Dead Band Module
     *     -Select the output mode for Dead Band Module
     *     -Select Polarity of the output PWMs
     */
    etpwmREG2->DBCTL = ( ( uint16 ) ( ( uint16 ) 0U << 5U )   /* Source for Falling edge
                                                                 delay(0-PWMA, 1-PWMB) */
                         | ( uint16 ) ( ( uint16 ) 0U << 4U ) /* Source for Rising edge
                                                                 delay(0-PWMA, 1-PWMB)  */
                         | ( uint16 ) ( ( uint16 ) 0U << 3U ) /* Enable/Disable EPWMxB
                                                                 invert       */
                         | ( uint16 ) ( ( uint16 ) 0U << 2U ) /* Enable/Disable EPWMxA
                                                                 invert       */
                         | ( uint16 ) ( ( uint16 ) 0U << 1U ) /* Enable/Disable Rising
                                                                 Edge Delay   */
                         | ( uint16 ) ( ( uint16 ) 0U << 0U ) ); /* Enable/Disable Falling
                                                                    Edge Delay  */

    /** - Set the rising edge delay  */
    etpwmREG2->DBRED = 1U;

    /** - Set the falling edge delay  */
    etpwmREG2->DBFED = 1U;

    /** - Enable the chopper module for ETPWMx
     *     -Sets the One shot pulse width in a chopper modulated wave
     *     -Sets the dutycycle for the subsequent pulse train
     *     -Sets the period for the subsequent pulse train
     */
    etpwmREG2->PCCTL = ( ( uint16 ) ( ( uint16 ) 0U << 0U )   /* Enable/Disable chopper
                                                                 module */
                         | ( uint16 ) ( ( uint16 ) 1U << 1U ) /* One-shot Pulse Width */
                         | ( uint16 ) ( ( uint16 ) 3U << 8U ) /* Chopping Clock Duty Cycle
                                                               */
                         | ( uint16 ) ( ( uint16 ) 0U << 5U ) ); /* Chopping Clock
                                                                    Frequency */

    /** - Set trip source enable */
    etpwmREG2->TZSEL = 0x0000U  /** - Enable/Disable TZ1 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ2 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ3 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ4 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ5 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ6 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ1 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ2 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ3 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ4 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ5 as a CBC trip source      */
                     | 0x0000U; /** - Enable/Disable TZ6 as a CBC trip source      */

    /** - Set interrupt enable */
    etpwmREG2
        ->TZEINT = 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1  */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2  */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1  */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2  */
                 | 0x0000U  /** - Enable/Disable one-shot interrupt generation        */
                 | 0x0000U; /** - Enable/Disable cycle-by-cycle interrupt generation  */

    /** - Sets up the event for interrupt */
    etpwmREG2->ETSEL = ( uint16 ) NO_EVENT;

    if( ( etpwmREG2->ETSEL & 0x0007U ) != 0U )
    {
        etpwmREG2->ETSEL |= 0x0008U;
    }
    /** - Setup the frequency of the interrupt generation */
    etpwmREG2->ETPS = 1U;

    /** - Sets up the ADC SOC interrupt */
    etpwmREG2->ETSEL |= ( ( uint16 ) ( 0x0000U ) | ( uint16 ) ( 0x0000U )
                          | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )
                          | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U ) );

    /** - Sets up the ADC SOC period */
    etpwmREG2->ETPS |= ( ( uint16 ) ( ( uint16 ) 1U << 8U )
                         | ( uint16 ) ( ( uint16 ) 1U << 12U ) );

    /** @b initialize @b ETPWM3 */

    /** - Sets high speed time-base clock prescale bits */
    etpwmREG3->TBCTL = ( uint16 ) 0U << 7U;

    /** - Sets time-base clock prescale bits */
    etpwmREG3->TBCTL |= ( uint16 ) ( ( uint16 ) 0U << 10U );

    /** - Sets time period or frequency for ETPWM block both PWMA and PWMB*/
    etpwmREG3->TBPRD = 1000U;

    /** - Setup the duty cycle for PWMA */
    etpwmREG3->CMPA = 50U;

    /** - Setup the duty cycle for PWMB */
    etpwmREG3->CMPB = 50U;

    /** - Force EPWMxA output high when counter reaches zero and low when counter reaches
     * Compare A value */
    etpwmREG3->AQCTLA = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) );

    /** - Force EPWMxB output high when counter reaches zero and low when counter reaches
     * Compare B value */
    etpwmREG3->AQCTLB = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) );

    /** - Mode setting for Dead Band Module
     *     -Select the input mode for Dead Band Module
     *     -Select the output mode for Dead Band Module
     *     -Select Polarity of the output PWMs
     */
    etpwmREG3->DBCTL = ( ( uint16 ) ( ( uint16 ) 0U << 5U )   /* Source for Falling edge
                                                                 delay(0-PWMA, 1-PWMB) */
                         | ( uint16 ) ( ( uint16 ) 0U << 4U ) /* Source for Rising edge
                                                                 delay(0-PWMA, 1-PWMB)  */
                         | ( uint16 ) ( ( uint16 ) 0U << 3U ) /* Enable/Disable EPWMxB
                                                                 invert       */
                         | ( uint16 ) ( ( uint16 ) 0U << 2U ) /* Enable/Disable EPWMxA
                                                                 invert       */
                         | ( uint16 ) ( ( uint16 ) 0U << 1U ) /* Enable/Disable Rising
                                                                 Edge Delay   */
                         | ( uint16 ) ( ( uint16 ) 0U << 0U ) ); /* Enable/Disable Falling
                                                                    Edge Delay  */

    /** - Set the rising edge delay  */
    etpwmREG3->DBRED = 1U;

    /** - Set the falling edge delay  */
    etpwmREG3->DBFED = 1U;

    /** - Enable the chopper module for ETPWMx
     *     -Sets the One shot pulse width in a chopper modulated wave
     *     -Sets the dutycycle for the subsequent pulse train
     *     -Sets the period for the subsequent pulse train
     */
    etpwmREG3->PCCTL = ( ( uint16 ) ( ( uint16 ) 0U << 0U )   /* Enable/Disable chopper
                                                                 module */
                         | ( uint16 ) ( ( uint16 ) 1U << 1U ) /* One-shot Pulse Width */
                         | ( uint16 ) ( ( uint16 ) 3U << 8U ) /* Chopping Clock Duty Cycle
                                                               */
                         | ( uint16 ) ( ( uint16 ) 0U << 5U ) ); /* Chopping Clock
                                                                    Frequency */

    /** - Set trip source enable */
    etpwmREG3->TZSEL = 0x0000U  /** - Enable/Disable TZ1 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ2 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ3 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ4 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ5 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ6 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ1 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ2 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ3 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ4 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ5 as a CBC trip source     */
                     | 0x0000U; /** - Enable/Disable TZ6 as a CBC trip source      */

    /** - Set interrupt enable */
    etpwmREG3
        ->TZEINT = 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2 */
                 | 0x0000U  /** - Enable/Disable one-shot interrupt generation       */
                 | 0x0000U; /** - Enable/Disable cycle-by-cycle interrupt generation */

    /** - Sets up the event for interrupt */
    etpwmREG3->ETSEL = ( uint16 ) NO_EVENT;

    if( ( etpwmREG3->ETSEL & 0x0007U ) != 0U )
    {
        etpwmREG3->ETSEL |= 0x0008U;
    }
    /** - Setup the frequency of the interrupt generation */
    etpwmREG3->ETPS = 1U;

    /** - Sets up the ADC SOC interrupt */
    etpwmREG3->ETSEL |= ( ( uint16 ) ( 0x0000U ) | ( uint16 ) ( 0x0000U )
                          | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )
                          | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U ) );

    /** - Sets up the ADC SOC period */
    etpwmREG3->ETPS |= ( ( uint16 ) ( ( uint16 ) 1U << 8U )
                         | ( uint16 ) ( ( uint16 ) 1U << 12U ) );

    /** @b initialize @b ETPWM4 */

    /** - Sets high speed time-base clock prescale bits */
    etpwmREG4->TBCTL = ( uint16 ) 0U << 7U;

    /** - Sets time-base clock prescale bits */
    etpwmREG4->TBCTL |= ( uint16 ) ( ( uint16 ) 0U << 10U );

    /** - Sets time period or frequency for ETPWM block both PWMA and PWMB*/
    etpwmREG4->TBPRD = 1000U;

    /** - Setup the duty cycle for PWMA */
    etpwmREG4->CMPA = 50U;

    /** - Setup the duty cycle for PWMB */
    etpwmREG4->CMPB = 50U;

    /** - Force EPWMxA output high when counter reaches zero and low when counter reaches
     * Compare A value */
    etpwmREG4->AQCTLA = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) );

    /** - Force EPWMxB output high when counter reaches zero and low when counter reaches
     * Compare B value */
    etpwmREG4->AQCTLB = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) );

    /** - Mode setting for Dead Band Module
     *     -Select the input mode for Dead Band Module
     *     -Select the output mode for Dead Band Module
     *     -Select Polarity of the output PWMs
     */
    etpwmREG4->DBCTL = ( uint16 ) ( ( uint16 ) 0U << 5U )  /* Source for Falling edge
                                                              delay(0-PWMA, 1-PWMB) */
                     | ( uint16 ) ( ( uint16 ) 0U << 4U )  /* Source for Rising edge
                                                              delay(0-PWMA, 1-PWMB)  */
                     | ( uint16 ) ( ( uint16 ) 0U << 3U )  /* Enable/Disable EPWMxB
                                                              invert       */
                     | ( uint16 ) ( ( uint16 ) 0U << 2U )  /* Enable/Disable EPWMxA
                                                              invert       */
                     | ( uint16 ) ( ( uint16 ) 0U << 1U )  /* Enable/Disable Rising Edge
                                                              Delay   */
                     | ( uint16 ) ( ( uint16 ) 0U << 0U ); /* Enable/Disable Falling
                                                              Edge Delay  */

    /** - Set the rising edge delay  */
    etpwmREG4->DBRED = 1U;

    /** - Set the falling edge delay  */
    etpwmREG4->DBFED = 1U;

    /** - Enable the chopper module for ETPWMx
     *     -Sets the One shot pulse width in a chopper modulated wave
     *     -Sets the dutycycle for the subsequent pulse train
     *     -Sets the period for the subsequent pulse train
     */
    etpwmREG4->PCCTL = ( uint16 ) ( ( uint16 ) 0U << 0U ) /* Enable/Disable chopper module
                                                           */
                     | ( uint16 ) ( ( uint16 ) 1U << 1U ) /* One-shot Pulse Width */
                     | ( uint16 ) ( ( uint16 ) 3U << 8U ) /* Chopping Clock Duty Cycle */
                     | ( uint16 ) ( ( uint16 ) 0U << 5U ); /* Chopping Clock Frequency */

    /** - Set trip source enable */
    etpwmREG4->TZSEL = 0x0000U  /** - Enable/Disable TZ1 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ2 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ3 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ4 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ5 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ6 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ1 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ2 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ3 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ4 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ5 as a CBC trip source        */
                     | 0x0000U; /** - Enable/Disable TZ6 as a CBC trip source      */

    /** - Set interrupt enable */
    etpwmREG4
        ->TZEINT = 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2  */
                 | 0x0000U  /** - Enable/Disable one-shot interrupt generation        */
                 | 0x0000U; /** - Enable/Disable cycle-by-cycle interrupt generation  */

    /** - Sets up the event for interrupt */
    etpwmREG4->ETSEL = ( uint16 ) NO_EVENT;

    if( ( etpwmREG4->ETSEL & 0x0007U ) != 0U )
    {
        etpwmREG4->ETSEL |= 0x0008U;
    }
    /** - Setup the frequency of the interrupt generation */
    etpwmREG4->ETPS = 1U;

    /** - Sets up the ADC SOC interrupt */
    etpwmREG4->ETSEL |= ( uint16 ) ( 0x0000U ) | ( uint16 ) ( 0x0000U )
                      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )
                      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U );

    /** - Sets up the ADC SOC period */
    etpwmREG4->ETPS |= ( ( uint16 ) ( ( uint16 ) 1U << 8U )
                         | ( uint16 ) ( ( uint16 ) 1U << 12U ) );

    /** @b initialize @b ETPWM5 */

    /** - Sets high speed time-base clock prescale bits */
    etpwmREG5->TBCTL = ( uint16 ) 0U << 7U;

    /** - Sets time-base clock prescale bits */
    etpwmREG5->TBCTL |= ( uint16 ) ( ( uint16 ) 0U << 10U );

    /** - Sets time period or frequency for ETPWM block both PWMA and PWMB*/
    etpwmREG5->TBPRD = 1000U;

    /** - Setup the duty cycle for PWMA */
    etpwmREG5->CMPA = 50U;

    /** - Setup the duty cycle for PWMB */
    etpwmREG5->CMPB = 50U;

    /** - Force EPWMxA output high when counter reaches zero and low when counter reaches
     * Compare A value */
    etpwmREG5->AQCTLA = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) );

    /** - Force EPWMxB output high when counter reaches zero and low when counter reaches
     * Compare B value */
    etpwmREG5->AQCTLB = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) );

    /** - Mode setting for Dead Band Module
     *     -Select the input mode for Dead Band Module
     *     -Select the output mode for Dead Band Module
     *     -Select Polarity of the output PWMs
     */
    etpwmREG5->DBCTL = ( uint16 ) ( ( uint16 ) 0U << 5U )  /* Source for Falling edge
                                                              delay(0-PWMA, 1-PWMB) */
                     | ( uint16 ) ( ( uint16 ) 0U << 4U )  /* Source for Rising edge
                                                              delay(0-PWMA, 1-PWMB)  */
                     | ( uint16 ) ( ( uint16 ) 0U << 3U )  /* Enable/Disable EPWMxB
                                                              invert       */
                     | ( uint16 ) ( ( uint16 ) 0U << 2U )  /* Enable/Disable EPWMxA
                                                              invert       */
                     | ( uint16 ) ( ( uint16 ) 0U << 1U )  /* Enable/Disable Rising Edge
                                                              Delay   */
                     | ( uint16 ) ( ( uint16 ) 0U << 0U ); /* Enable/Disable Falling
                                                              Edge Delay  */

    /** - Set the rising edge delay  */
    etpwmREG5->DBRED = 1U;

    /** - Set the falling edge delay  */
    etpwmREG5->DBFED = 1U;

    /** - Enable the chopper module for ETPWMx
     *     -Sets the One shot pulse width in a chopper modulated wave
     *     -Sets the dutycycle for the subsequent pulse train
     *     -Sets the period for the subsequent pulse train
     */
    etpwmREG5->PCCTL = ( uint16 ) ( ( uint16 ) 0U << 0U ) /* Enable/Disable chopper module
                                                           */
                     | ( uint16 ) ( ( uint16 ) 1U << 1U ) /* One-shot Pulse Width */
                     | ( uint16 ) ( ( uint16 ) 3U << 8U ) /* Chopping Clock Duty Cycle */
                     | ( uint16 ) ( ( uint16 ) 0U << 5U ); /* Chopping Clock Frequency */

    /** - Set trip source enable */
    etpwmREG5->TZSEL = 0x0000U  /** - Enable/Disable TZ1 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ2 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ3 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ4 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ5 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ6 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ1 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ2 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ3 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ4 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ5 as a CBC trip source        */
                     | 0x0000U; /** - Enable/Disable TZ6 as a CBC trip source      */

    /** - Set interrupt enable */
    etpwmREG5
        ->TZEINT = 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2 */
                 | 0x0000U  /** - Enable/Disable one-shot interrupt generation       */
                 | 0x0000U; /** - Enable/Disable cycle-by-cycle interrupt generation */

    /** - Sets up the event for interrupt */
    etpwmREG5->ETSEL = ( uint16 ) NO_EVENT;

    if( ( etpwmREG5->ETSEL & 0x0007U ) != 0U )
    {
        etpwmREG5->ETSEL |= 0x0008U;
    }
    /** - Setup the frequency of the interrupt generation */
    etpwmREG5->ETPS = 1U;

    /** - Sets up the ADC SOC interrupt */
    etpwmREG5->ETSEL |= ( uint16 ) ( 0x0000U ) | ( uint16 ) ( 0x0000U )
                      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )
                      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U );

    /** - Sets up the ADC SOC period */
    etpwmREG5->ETPS |= ( ( uint16 ) ( ( uint16 ) 1U << 8U )
                         | ( uint16 ) ( ( uint16 ) 1U << 12U ) );

    /** @b initialize @b ETPWM6 */

    /** - Sets high speed time-base clock prescale bits */
    etpwmREG6->TBCTL = ( uint16 ) 0U << 7U;

    /** - Sets time-base clock prescale bits */
    etpwmREG6->TBCTL |= ( uint16 ) ( ( uint16 ) 0U << 10U );

    /** - Sets time period or frequency for ETPWM block both PWMA and PWMB*/
    etpwmREG6->TBPRD = 1000U;

    /** - Setup the duty cycle for PWMA */
    etpwmREG6->CMPA = 50U;

    /** - Setup the duty cycle for PWMB */
    etpwmREG6->CMPB = 50U;

    /** - Force EPWMxA output high when counter reaches zero and low when counter reaches
     * Compare A value */
    etpwmREG6->AQCTLA = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) );

    /** - Force EPWMxB output high when counter reaches zero and low when counter reaches
     * Compare B value */
    etpwmREG6->AQCTLB = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) );

    /** - Mode setting for Dead Band Module
     *     -Select the input mode for Dead Band Module
     *     -Select the output mode for Dead Band Module
     *     -Select Polarity of the output PWMs
     */
    etpwmREG6->DBCTL = ( uint16 ) ( ( uint16 ) 0U << 5U )  /* Source for Falling edge
                                                              delay(0-PWMA, 1-PWMB) */
                     | ( uint16 ) ( ( uint16 ) 0U << 4U )  /* Source for Rising edge
                                                              delay(0-PWMA, 1-PWMB)  */
                     | ( uint16 ) ( ( uint16 ) 0U << 3U )  /* Enable/Disable EPWMxB
                                                              invert       */
                     | ( uint16 ) ( ( uint16 ) 0U << 2U )  /* Enable/Disable EPWMxA
                                                              invert       */
                     | ( uint16 ) ( ( uint16 ) 0U << 1U )  /* Enable/Disable Rising Edge
                                                              Delay   */
                     | ( uint16 ) ( ( uint16 ) 0U << 0U ); /* Enable/Disable Falling
                                                              Edge Delay  */

    /** - Set the rising edge delay  */
    etpwmREG6->DBRED = 1U;

    /** - Set the falling edge delay  */
    etpwmREG6->DBFED = 1U;

    /** - Enable the chopper module for ETPWMx
     *     -Sets the One shot pulse width in a chopper modulated wave
     *     -Sets the dutycycle for the subsequent pulse train
     *     -Sets the period for the subsequent pulse train
     */
    etpwmREG6->PCCTL = ( uint16 ) ( ( uint16 ) 0U << 0U ) /* Enable/Disable chopper module
                                                           */
                     | ( uint16 ) ( ( uint16 ) 1U << 1U ) /* One-shot Pulse Width */
                     | ( uint16 ) ( ( uint16 ) 3U << 8U ) /* Chopping Clock Duty Cycle */
                     | ( uint16 ) ( ( uint16 ) 0U << 5U ); /* Chopping Clock Frequency */

    /** - Set trip source enable */
    etpwmREG6->TZSEL = 0x0000U  /** - Enable/Disable TZ1 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ2 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ3 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ4 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ5 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ6 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ1 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ2 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ3 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ4 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ5 as a CBC trip source      */
                     | 0x0000U; /** - Enable/Disable TZ6 as a CBC trip source      */

    /** - Set interrupt enable */
    etpwmREG6
        ->TZEINT = 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1 */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2 */
                 | 0x0000U  /** - Enable/Disable one-shot interrupt generation       */
                 | 0x0000U; /** - Enable/Disable cycle-by-cycle interrupt generation */

    /** - Sets up the event for interrupt */
    etpwmREG6->ETSEL = ( uint16 ) NO_EVENT;

    if( ( etpwmREG6->ETSEL & 0x0007U ) != 0U )
    {
        etpwmREG6->ETSEL |= 0x0008U;
    }
    /** - Setup the frequency of the interrupt generation */
    etpwmREG6->ETPS = 1U;

    /** - Sets up the ADC SOC interrupt */
    etpwmREG6->ETSEL |= ( uint16 ) ( 0x0000U ) | ( uint16 ) ( 0x0000U )
                      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )
                      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U );

    /** - Sets up the ADC SOC period */
    etpwmREG6->ETPS |= ( ( uint16 ) ( ( uint16 ) 1U << 8U )
                         | ( uint16 ) ( ( uint16 ) 1U << 12U ) );

    /** @b initialize @b ETPWM7 */

    /** - Sets high speed time-base clock prescale bits */
    etpwmREG7->TBCTL = ( uint16 ) 0U << 7U;

    /** - Sets time-base clock prescale bits */
    etpwmREG7->TBCTL |= ( uint16 ) ( ( uint16 ) 0U << 10U );

    /** - Sets time period or frequency for ETPWM block both PWMA and PWMB*/
    etpwmREG7->TBPRD = 1000U;

    /** - Setup the duty cycle for PWMA */
    etpwmREG7->CMPA = 50U;

    /** - Setup the duty cycle for PWMB */
    etpwmREG7->CMPB = 50U;

    /** - Force EPWMxA output high when counter reaches zero and low when counter reaches
     * Compare A value */
    etpwmREG7->AQCTLA = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) );

    /** - Force EPWMxB output high when counter reaches zero and low when counter reaches
     * Compare B value */
    etpwmREG7->AQCTLB = ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U )
                          | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) );

    /** - Mode setting for Dead Band Module
     *     -Select the input mode for Dead Band Module
     *     -Select the output mode for Dead Band Module
     *     -Select Polarity of the output PWMs
     */
    etpwmREG7->DBCTL = ( uint16 ) ( ( uint16 ) 0U << 5U )  /* Source for Falling edge
                                                              delay(0-PWMA, 1-PWMB) */
                     | ( uint16 ) ( ( uint16 ) 0U << 4U )  /* Source for Rising edge
                                                              delay(0-PWMA, 1-PWMB)  */
                     | ( uint16 ) ( ( uint16 ) 0U << 3U )  /* Enable/Disable EPWMxB
                                                              invert       */
                     | ( uint16 ) ( ( uint16 ) 0U << 2U )  /* Enable/Disable EPWMxA
                                                              invert       */
                     | ( uint16 ) ( ( uint16 ) 0U << 1U )  /* Enable/Disable Rising Edge
                                                              Delay   */
                     | ( uint16 ) ( ( uint16 ) 0U << 0U ); /* Enable/Disable Falling
                                                              Edge Delay  */

    /** - Set the rising edge delay  */
    etpwmREG7->DBRED = 1U;

    /** - Set the falling edge delay  */
    etpwmREG7->DBFED = 1U;

    /** - Enable the chopper module for ETPWMx
     *     -Sets the One shot pulse width in a chopper modulated wave
     *     -Sets the dutycycle for the subsequent pulse train
     *     -Sets the period for the subsequent pulse train
     */
    etpwmREG7->PCCTL = ( uint16 ) ( ( uint16 ) 0U << 0U ) /* Enable/Disable chopper module
                                                           */
                     | ( uint16 ) ( ( uint16 ) 1U << 1U ) /* One-shot Pulse Width */
                     | ( uint16 ) ( ( uint16 ) 3U << 8U ) /* Chopping Clock Duty Cycle */
                     | ( uint16 ) ( ( uint16 ) 0U << 5U ); /* Chopping Clock Frequency */

    /** - Set trip source enable */
    etpwmREG7->TZSEL = 0x0000U  /** - Enable/Disable TZ1 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ2 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ3 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ4 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ5 as a one-shot trip source */
                     | 0x0000U  /** - Enable/Disable TZ6 as a one-shot trip source  */
                     | 0x0000U  /** - Enable/Disable TZ1 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ2 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ3 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ4 as a CBC trip source      */
                     | 0x0000U  /** - Enable/Disable TZ5 as a CBC trip source       */
                     | 0x0000U; /** - Enable/Disable TZ6 as a CBC trip source      */

    /** - Set interrupt enable */
    etpwmREG7
        ->TZEINT = 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1  */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2  */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 1  */
                 | 0x0000U  /** - Enable/Disable Digital Comparator Output A Event 2  */
                 | 0x0000U  /** - Enable/Disable one-shot interrupt generation        */
                 | 0x0000U; /** - Enable/Disable cycle-by-cycle interrupt generation  */

    /** - Sets up the event for interrupt */
    etpwmREG7->ETSEL = ( uint16 ) NO_EVENT;

    if( ( etpwmREG7->ETSEL & 0x0007U ) != 0U )
    {
        etpwmREG7->ETSEL |= 0x0008U;
    }
    /** - Setup the frequency of the interrupt generation */
    etpwmREG7->ETPS = 1U;

    /** - Sets up the ADC SOC interrupt */
    etpwmREG7->ETSEL |= ( uint16 ) ( 0x0000U ) | ( uint16 ) ( 0x0000U )
                      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )
                      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U );

    /** - Sets up the ADC SOC period */
    etpwmREG7->ETPS |= ( ( uint16 ) ( ( uint16 ) 1U << 8U )
                         | ( uint16 ) ( ( uint16 ) 1U << 12U ) );

    /* USER CODE BEGIN (2) */
    /* USER CODE END */
}

/** @fn void etpwmStartTBCLK()
 *   @brief Start the time-base clocks of all eTPWMx modules
 *
 *   This function starts the time-base clocks of all eTPWMx modules.
 */
/* SourceId : ETPWM_SourceId_002 */
/* DesignId : ETPWM_DesignId_002 */
/* Requirements : CONQ_EPWM_SR45 */
void etpwmStartTBCLK( void )
{
    /* Enable Pin Muxing */
    pinMuxReg->KICKER0 = 0x83E70B13U;
    pinMuxReg->KICKER1 = 0x95A4F1E0U;

    pinMuxReg->PINMUX[ 166U ] = ( pinMuxReg->PINMUX[ 166U ]
                                  & PINMUX_ETPWM_TBCLK_SYNC_MASK )
                              | ( PINMUX_ETPWM_TBCLK_SYNC_ON );

    /* Disable Pin Muxing */
    pinMuxReg->KICKER0 = 0x00000000U;
    pinMuxReg->KICKER1 = 0x00000000U;
}

/** @fn void etpwmStopTBCLK()
 *   @brief Stop the time-base clocks of all eTPWMx modules
 *
 *   This function stops the time-base clocks of all eTPWMx modules.
 */
/* SourceId : ETPWM_SourceId_003 */
/* DesignId : ETPWM_DesignId_003 */
/* Requirements : CONQ_EPWM_SR46 */
void etpwmStopTBCLK( void )
{
    /* Enable Pin Muxing */
    pinMuxReg->KICKER0 = 0x83E70B13U;
    pinMuxReg->KICKER1 = 0x95A4F1E0U;

    pinMuxReg->PINMUX[ 166U ] = ( pinMuxReg->PINMUX[ 166U ]
                                  & PINMUX_ETPWM_TBCLK_SYNC_MASK )
                              | ( PINMUX_ETPWM_TBCLK_SYNC_OFF );

    /* Disable Pin Muxing */
    pinMuxReg->KICKER0 = 0x00000000U;
    pinMuxReg->KICKER1 = 0x00000000U;
}

/** @fn void etpwmSetClkDiv(etpwmBASE_t *etpwm, etpwmClkDiv_t clkdiv, etpwmHspClkDiv_t
 * hspclkdiv)
 *   @brief Sets the Time-base Clock divider
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param clkdiv    Time-base clock divider
 *                     - ClkDiv_by_1
 *                     - ClkDiv_by_2
 *                     - ClkDiv_by_4
 *                     - ClkDiv_by_8
 *                     - ClkDiv_by_16
 *                     - ClkDiv_by_32
 *                     - ClkDiv_by_64
 *                     - ClkDiv_by_128
 *   @param hspclkdiv High Speed Time-base clock divider
 *                     - HspClkDiv_by_1
 *                     - HspClkDiv_by_2
 *                     - HspClkDiv_by_4
 *                     - HspClkDiv_by_6
 *                     - HspClkDiv_by_8
 *                     - HspClkDiv_by_10
 *                     - HspClkDiv_by_12
 *                     - HspClkDiv_by_14
 *
 *   This function sets the TimeBase Clock and the High Speed time base clock divider
 *   TBCLK = VCLK4 / (HSPCLKDIV � CLKDIV)
 */
/* SourceId : ETPWM_SourceId_004 */
/* DesignId : ETPWM_DesignId_004 */
/* Requirements : CONQ_EPWM_SR3 */
void etpwmSetClkDiv( etpwmBASE_t * etpwm,
                     etpwmClkDiv_t clkdiv,
                     etpwmHspClkDiv_t hspclkdiv )
{
    etpwm->TBCTL &= ( uint16 ) ~( uint16 ) 0x1F80U;
    etpwm->TBCTL |= ( uint16 ) clkdiv | ( uint16 ) hspclkdiv;
}

/** @fn void etpwmSetTimebasePeriod(etpwmBASE_t *etpwm, uint16 period)
 *   @brief Sets period of timebase counter
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param period    16-bit Time-base period
 *
 *   This function sets period of timebase counter
 */
/* SourceId : ETPWM_SourceId_005 */
/* DesignId : ETPWM_DesignId_005 */
/* Requirements : CONQ_EPWM_SR4 */
void etpwmSetTimebasePeriod( etpwmBASE_t * etpwm, uint16 period )
{
    etpwm->TBPRD = period;
}

/** @fn void etpwmSetCount(etpwmBASE_t *etpwm, uint16 count)
 *   @brief Sets timebase counter
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param count     16-bit Counter value
 *
 *   This function sets the timebase counter
 */
/* SourceId : ETPWM_SourceId_006 */
/* DesignId : ETPWM_DesignId_006 */
/* Requirements : CONQ_EPWM_SR5 */
void etpwmSetCount( etpwmBASE_t * etpwm, uint16 count )
{
    etpwm->TBCTR = count;
}

/** @fn void etpwmDisableTimebasePeriodShadowMode(etpwmBASE_t *etpwm)
 *   @brief Disable shadow mode for time-base period register
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function disables shadow mode for time-base period register
 */
/* SourceId : ETPWM_SourceId_007 */
/* DesignId : ETPWM_DesignId_007 */
/* Requirements : CONQ_EPWM_SR6 */
void etpwmDisableTimebasePeriodShadowMode( etpwmBASE_t * etpwm )
{
    etpwm->TBCTL |= 0x0008U;
}

/** @fn void etpwmEnableTimebasePeriodShadowMode(etpwmBASE_t *etpwm)
 *   @brief Enable shadow mode for time-base period register
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function enables shadow mode for time-base period register
 */
/* SourceId : ETPWM_SourceId_008 */
/* DesignId : ETPWM_DesignId_008 */
/* Requirements : CONQ_EPWM_SR7 */
void etpwmEnableTimebasePeriodShadowMode( etpwmBASE_t * etpwm )
{
    etpwm->TBCTL &= ( uint16 ) ~( uint16 ) 0x0008U;
}

/** @fn void etpwmEnableCounterLoadOnSync(etpwmBASE_t *etpwm, uint16 phase, uint16
 * direction)
 *   @brief Enable counter register load from phase register when a sync event occurs
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param phase     Counter value to be loaded when a sync event occurs
 *   @param direction Direction of the counter after the sync event (Applied only if
 * counter is in updown-count mode, ignores otherwise)
 *                     - COUNT_UP
 *                     - COUNT_DOWN
 *                     - Pass 0 if not applied
 *
 *   This function enables counter register load from phase register when a sync event
 * occurs
 */
/* SourceId : ETPWM_SourceId_009 */
/* DesignId : ETPWM_DesignId_009 */
/* Requirements : CONQ_EPWM_SR8 */
void etpwmEnableCounterLoadOnSync( etpwmBASE_t * etpwm, uint16 phase, uint16 direction )
{
    etpwm->TBCTL &= ( uint16 ) ~( uint16 ) 0x2000U;
    etpwm->TBCTL |= 0x0004U | direction;
    etpwm->TBPHS = phase;
}

/** @fn void etpwmDisableCounterLoadOnSync(etpwmBASE_t *etpwm)
 *   @brief Disable counter register load from phase register when a sync event occurs
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function disables counter register load from phase register when a sync event
 * occurs
 */
/* SourceId : ETPWM_SourceId_010 */
/* DesignId : ETPWM_DesignId_010 */
/* Requirements : CONQ_EPWM_SR9 */
void etpwmDisableCounterLoadOnSync( etpwmBASE_t * etpwm )
{
    etpwm->TBCTL &= ( uint16 ) ~( uint16 ) 0x0004U;
}

/** @fn void etpwmSetSyncOut(etpwmBASE_t *etpwm, etpwmSyncMode_t syncmode)
 *   @brief Set the source of EPWMxSYNCO signal
 *
 *   @param etpwm      The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param syncOutSrc Synchronization Output Select
 *                      - SyncOut_EPWMxSYNCI
 *                      - SyncOut_CtrEqZero
 *                      - SyncOut_CtrEqCmpB
 *                      - SyncOut_Disable
 *
 *   This function sets the source of synchronization output signal
 */
/* SourceId : ETPWM_SourceId_011 */
/* DesignId : ETPWM_DesignId_011 */
/* Requirements : CONQ_EPWM_SR10 */
void etpwmSetSyncOut( etpwmBASE_t * etpwm, etpwmSyncOut_t syncOutSrc )
{
    etpwm->TBCTL &= ( uint16 ) ~( uint16 ) 0x0030U;
    etpwm->TBCTL |= syncOutSrc;
}

/** @fn void etpwmSetCounterMode(etpwmBASE_t *etpwm, etpwmCounterMode_t countermode)
 *   @brief Set the time-base counter mode
 *
 *   @param etpwm        The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param countermode  Counter Mode
 *                         - CounterMode_Up
 *                         - Countermode_Down
 *                         - CounterMode_UpDown
 *                         - CounterMode_Stop
 *
 *   This function sets the time-base counter mode of operation.
 */
/* SourceId : ETPWM_SourceId_012 */
/* DesignId : ETPWM_DesignId_012 */
/* Requirements : CONQ_EPWM_SR11 */
void etpwmSetCounterMode( etpwmBASE_t * etpwm, etpwmCounterMode_t countermode )
{
    etpwm->TBCTL &= ( uint16 ) ~( uint16 ) 0x0003U;
    etpwm->TBCTL |= countermode;
}

/** @fn void etpwmTriggerSWSync(etpwmBASE_t *etpwm)
 *   @brief Trigger a software synchronization pulse
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function triggers a software synchronization pulse. SWFSYNC is valid (operates)
 * only when EPWMxSYNCI as SyncOut
 */
/* SourceId : ETPWM_SourceId_013 */
/* DesignId : ETPWM_DesignId_013 */
/* Requirements : CONQ_EPWM_SR12 */
void etpwmTriggerSWSync( etpwmBASE_t * etpwm )
{
    etpwm->TBCTL |= 0x0040U;
}

/** @fn void etpwmSetRunMode(etpwmBASE_t *etpwm, etpwmRunMode_t runmode)
 *   @brief Set the pulse width modulation (ETPWM) run mode
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param runmode   Run mode
 *                      - RunMode_SoftStopAfterIncr  : Stop after the next time-base
 * counter increment
 *                      - RunMode_SoftStopAfterDecr  : Stop after the next time-base
 * counter decrement
 *                      - RunMode_SoftStopAfterCycle : Stop when counter completes a whole
 * cycle
 *                      - RunMode_FreeRun            : Free-run
 *
 *   This function select the behaviour of the ePWM time-base counter during emulation
 * events
 */
/* SourceId : ETPWM_SourceId_014 */
/* DesignId : ETPWM_DesignId_014 */
/* Requirements : CONQ_EPWM_SR13 */
void etpwmSetRunMode( etpwmBASE_t * etpwm, etpwmRunMode_t runmode )
{
    etpwm->TBCTL &= ( uint16 ) ~( uint16 ) 0xC000U;
    etpwm->TBCTL |= runmode;
}

/** @fn void etpwmSetCmpA(etpwmBASE_t *etpwm, uint16 value)
 *   @brief Set the Compare A value
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param value     16-bit Compare A value
 *
 *   This function sets the compare A value
 */
/* SourceId : ETPWM_SourceId_015 */
/* DesignId : ETPWM_DesignId_015 */
/* Requirements : CONQ_EPWM_SR14 */
void etpwmSetCmpA( etpwmBASE_t * etpwm, uint16 value )
{
    etpwm->CMPA = value;
}

/** @fn void etpwmSetCmpB(etpwmBASE_t *etpwm, uint16 value)
 *   @brief Set the Compare B value
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param value     16-bit Compare B value
 *
 *   This function sets the compare B register
 */
/* SourceId : ETPWM_SourceId_016 */
/* DesignId : ETPWM_DesignId_016 */
/* Requirements : CONQ_EPWM_SR15 */
void etpwmSetCmpB( etpwmBASE_t * etpwm, uint16 value )
{
    etpwm->CMPB = value;
}

/** @fn void etpwmEnableCmpAShadowMode(etpwmBASE_t *etpwm, etpwmLoadMode_t loadmode)
 *   @brief Enable shadow mode for Compare A register
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param loadmode  Active Counter-Compare A (CMPA) Load From Shadow Select Mode
 *                     - LoadMode_CtrEqZero       : Load on CTR = Zero
 *                     - LoadMode_CtrEqPeriod     : Load on CTR = PRD
 *                     - LoadMode_CtrEqZeroPeriod : Load on either CTR = Zero or CTR = PRD
 *                     - LoadMode_Freeze          : Freeze (no loads possible)
 *
 *   This function enables shadow mode for Compare A register
 */
/* SourceId : ETPWM_SourceId_017 */
/* DesignId : ETPWM_DesignId_017 */
/* Requirements : CONQ_EPWM_SR16 */
void etpwmEnableCmpAShadowMode( etpwmBASE_t * etpwm, etpwmLoadMode_t loadmode )
{
    etpwm->CMPCTL &= ( uint16 ) ~( uint16 ) 0x0013U;
    etpwm->CMPCTL |= loadmode;
}

/** @fn void etpwmDisableCmpAShadowMode(etpwmBASE_t *etpwm)
 *   @brief Disable shadow mode for Compare A register
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function disables shadow mode for Compare A register
 */
/* SourceId : ETPWM_SourceId_018 */
/* DesignId : ETPWM_DesignId_018 */
/* Requirements : CONQ_EPWM_SR17 */
void etpwmDisableCmpAShadowMode( etpwmBASE_t * etpwm )
{
    etpwm->CMPCTL |= 0x0010U;
}

/** @fn void etpwmEnableCmpBShadowMode(etpwmBASE_t *etpwm, etpwmLoadMode_t loadmode)
 *   @brief Enable shadow mode for Compare B register
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param loadmode  Active Counter-Compare B (CMPB) Load From Shadow Select Mode
 *                     - LoadMode_CtrEqZero       : Load on CTR = Zero
 *                     - LoadMode_CtrEqPeriod     : Load on CTR = PRD
 *                     - LoadMode_CtrEqZeroPeriod : Load on either CTR = Zero or CTR = PRD
 *                     - LoadMode_Freeze          : Freeze (no loads possible)
 *
 *   This function enables shadow mode for Compare B register
 */
/* SourceId : ETPWM_SourceId_019 */
/* DesignId : ETPWM_DesignId_019 */
/* Requirements : CONQ_EPWM_SR18 */
void etpwmEnableCmpBShadowMode( etpwmBASE_t * etpwm, etpwmLoadMode_t loadmode )
{
    etpwm->CMPCTL &= ( uint16 ) ~( uint16 ) 0x004CU;
    etpwm->CMPCTL |= ( uint16 ) ( ( uint16 ) loadmode << 2U );
}

/** @fn void etpwmDisableCmpBShadowMode(etpwmBASE_t *etpwm)
 *   @brief Disable shadow mode for Compare B register
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function disables shadow mode for Compare B register
 */
/* SourceId : ETPWM_SourceId_020 */
/* DesignId : ETPWM_DesignId_020 */
/* Requirements : CONQ_EPWM_SR19 */
void etpwmDisableCmpBShadowMode( etpwmBASE_t * etpwm )
{
    etpwm->CMPCTL |= 0x0040U;
}

/** @fn void etpwmSetActionQualPwmA(etpwmBASE_t *etpwm, etpwmActionQualConfig_t
 * actionqualconfig)
 *   @brief Configure Action Qualifier submodule to generate PWMA
 *
 *   @param etpwm            The pulse width modulation (ETPWM) object handle
 * (etpwmREG1..7)
 *   @param actionqualconfig Action Qualifier configuration
 *
 *   Example usage (Removing semicolons to avoid MISRA warnings):
 *       etpwmActionQualConfig_t configA
 *       configA.CtrEqZero_Action     = ActionQual_Set
 *       configA.CtrEqPeriod_Action   = ActionQual_Disabled
 *       configA.CtrEqCmpAUp_Action   = ActionQual_Clear
 *       configA.CtrEqCmpADown_Action = ActionQual_Disabled
 *       configA.CtrEqCmpBUp_Action   = ActionQual_Disabled
 *       configA.CtrEqCmpBDown_Action = ActionQual_Disabled
 *       void etpwmSetActionQualPwmA(etpwmREG1, configA)
 *
 *   This function configures Action Qualifier submodule to generate PWMA
 */
/* SourceId : ETPWM_SourceId_021 */
/* DesignId : ETPWM_DesignId_021 */
/* Requirements : CONQ_EPWM_SR20 */
void etpwmSetActionQualPwmA( etpwmBASE_t * etpwm,
                             etpwmActionQualConfig_t actionqualconfig )
{
    etpwm
        ->AQCTLA = ( ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqZero_Action << 0U )
                     | ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqPeriod_Action << 2U )
                     | ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqCmpAUp_Action << 4U )
                     | ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqCmpADown_Action
                                    << 6U )
                     | ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqCmpBUp_Action << 8U )
                     | ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqCmpBDown_Action
                                    << 10U ) );
}

/** @fn void etpwmSetActionQualPwmB(etpwmBASE_t *etpwm, etpwmActionQualConfig_t
 * actionqualconfig)
 *   @brief Configure Action Qualifier submodule to generate PWMB
 *
 *   @param etpwm            The pulse width modulation (ETPWM) object handle
 * (etpwmREG1..7)
 *   @param actionqualconfig Action Qualifier configuration
 *
 *   Example usage (Removing semicolons to avoid MISRA warnings):
 *       etpwmActionQualConfig_t configB
 *       configB.CtrEqZero_Action     = ActionQual_Set
 *       configB.CtrEqPeriod_Action   = ActionQual_Disabled
 *       configB.CtrEqCmpAUp_Action   = ActionQual_Disabled
 *       configB.CtrEqCmpADown_Action = ActionQual_Disabled
 *       configB.CtrEqCmpBUp_Action   = ActionQual_Clear
 *       configB.CtrEqCmpBDown_Action = ActionQual_Disabled
 *       void etpwmSetActionQualPwmB(etpwmREG1, configB)
 *
 *   This function configures Action Qualifier submodule to generate PWMB
 */
/* SourceId : ETPWM_SourceId_022 */
/* DesignId : ETPWM_DesignId_022 */
/* Requirements : CONQ_EPWM_SR21 */
void etpwmSetActionQualPwmB( etpwmBASE_t * etpwm,
                             etpwmActionQualConfig_t actionqualconfig )
{
    etpwm
        ->AQCTLB = ( ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqZero_Action << 0U )
                     | ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqPeriod_Action << 2U )
                     | ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqCmpAUp_Action << 4U )
                     | ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqCmpADown_Action
                                    << 6U )
                     | ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqCmpBUp_Action << 8U )
                     | ( uint16 ) ( ( uint16 ) actionqualconfig.CtrEqCmpBDown_Action
                                    << 10U ) );
}

/** @fn void etpwmEnableDeadBand(etpwmBASE_t *etpwm, etpwmDeadBandConfig_t deadbandconfig)
 *   @brief Enable DeadBand module
 *
 *   @param etpwm           The pulse width modulation (ETPWM) object handle
 * (etpwmREG1..7)
 *   @param deadbandconfig  DeadBand configuration
 *
 *   This function configures Action Qualifier submodule to generate PWMB
 */
/* SourceId : ETPWM_SourceId_023 */
/* DesignId : ETPWM_DesignId_023 */
/* Requirements : CONQ_EPWM_SR22 */
void etpwmEnableDeadBand( etpwmBASE_t * etpwm, etpwmDeadBandConfig_t deadbandconfig )
{
    uint16 halfCycleMask = ( uint16 ) ( ( deadbandconfig.halfCycleEnable ) ? 0x8000U
                                                                           : 0U );
    etpwm->DBCTL = ( ( uint16 ) deadbandconfig.inputmode
                     | ( uint16 ) deadbandconfig.outputmode
                     | ( uint16 ) deadbandconfig.polarity | halfCycleMask );
}

/** @fn void etpwmDisableDeadband(etpwmBASE_t *etpwm)
 *   @brief Disable DeadBand module
 *
 *   @param etpwm           The pulse width modulation (ETPWM) object handle
 * (etpwmREG1..7)
 *
 *   This function bypasses the Deadband submodule
 */
/* SourceId : ETPWM_SourceId_024 */
/* DesignId : ETPWM_DesignId_024 */
/* Requirements : CONQ_EPWM_SR23 */
void etpwmDisableDeadband( etpwmBASE_t * etpwm )
{
    etpwm->DBCTL = 0U;
}

/** @fn void etpwmSetDeadBandDelay(etpwmBASE_t *etpwm, uint16 Rdelay, uint16 Fdelay)
 *   @brief Sets the rising and falling edge delay
 *
 *   @param etpwm  The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param Rdelay 16-bit rising edge delay in terms of TCLK ticks
 *   @param Fdelay 16-bit falling edge delay in terms of TCLK ticks
 *
 *   This function sets the rising and falling edge delays in the DeadBand submodule
 */
/* SourceId : ETPWM_SourceId_025 */
/* DesignId : ETPWM_DesignId_025 */
/* Requirements : CONQ_EPWM_SR24 */
void etpwmSetDeadBandDelay( etpwmBASE_t * etpwm, uint16 Rdelay, uint16 Fdelay )
{
    etpwm->DBRED = Rdelay;
    etpwm->DBFED = Fdelay;
}

/** @fn void etpwmEnableChopping(etpwmBASE_t *etpwm, etpwmChoppingConfig_t choppingconfig)
 *   @brief Enable chopping
 *
 *   @param etpwm          The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param choppingconfig Chopper submodule configuration
 *
 *   This function enables the chopper submodule with the given configuration
 */
/* SourceId : ETPWM_SourceId_026 */
/* DesignId : ETPWM_DesignId_026 */
/* Requirements : CONQ_EPWM_SR25 */
void etpwmEnableChopping( etpwmBASE_t * etpwm, etpwmChoppingConfig_t choppingconfig )
{
    etpwm->PCCTL = ( ( uint16 ) 0x0001U | ( uint16 ) choppingconfig.oswdth
                     | ( uint16 ) choppingconfig.freq | ( uint16 ) choppingconfig.duty );
}

/** @fn void etpwmDisableChopping(etpwmBASE_t *etpwm)
 *   @brief Disable chopping
 *
 *   @param etpwm          The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function disables the chopper submodule
 */
/* SourceId : ETPWM_SourceId_027 */
/* DesignId : ETPWM_DesignId_027 */
/* Requirements : CONQ_EPWM_SR26 */
void etpwmDisableChopping( etpwmBASE_t * etpwm )
{
    etpwm->PCCTL = 0U;
}

/** @fn void etpwmEnableTripZoneSources(etpwmBASE_t *etpwm, etpwmTripZoneSrc_t sources)
 *   @brief Select the tripzone zources
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param sources   Trip zone sources (sources can be ORed)
 *                      - CycleByCycle_TZ1     : Enable TZ1 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_TZ2     : Enable TZ2 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_TZ3     : Enable TZ3 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_TZ4     : Enable TZ4 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_TZ5     : Enable TZ5 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_TZ6     : Enable TZ6 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_DCAEVT2 : Enable DCAEVT2 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_DCBEVT2 : Enable DCBEVT2 as a Cycle-by-cycle trip
 * source
 *                      - OneShot_TZ1          : Enable TZ1 as a One-shot trip source
 *                      - OneShot_TZ2          : Enable TZ2 as a One-shot trip source
 *                      - OneShot_TZ3          : Enable TZ3 as a One-shot trip source
 *                      - OneShot_TZ4          : Enable TZ4 as a One-shot trip source
 *                      - OneShot_TZ5          : Enable TZ5 as a One-shot trip source
 *                      - OneShot_TZ6          : Enable TZ6 as a One-shot trip source
 *                      - OneShot_DCAEVT1      : Enable DCAEVT1 as a One-shot trip source
 *                      - OneShot_DCBEVT1      : Enable DCBEVT1 as a One-shot trip source
 *
 *   This function selects the tripzone sources for cycle-by-cycle and one-shot trip
 */
/* SourceId : ETPWM_SourceId_028 */
/* DesignId : ETPWM_DesignId_028 */
/* Requirements : CONQ_EPWM_SR27 */
void etpwmEnableTripZoneSources( etpwmBASE_t * etpwm, etpwmTripZoneSrc_t sources )
{
    etpwm->TZSEL |= sources;
}

/** @fn void etpwmEnableTripZoneSources(etpwmBASE_t *etpwm, etpwmTripZoneSrc_t sources)
 *   @brief Disable the tripzone zources
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param sources   Trip zone sources (sources can be ORed)
 *                      - CycleByCycle_TZ1     : Disable TZ1 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_TZ2     : Disable TZ2 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_TZ3     : Disable TZ3 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_TZ4     : Disable TZ4 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_TZ5     : Disable TZ5 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_TZ6     : Disable TZ6 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_DCAEVT2 : Disable DCAEVT2 as a Cycle-by-cycle trip
 * source
 *                      - CycleByCycle_DCBEVT2 : Disable DCBEVT2 as a Cycle-by-cycle trip
 * source
 *                      - OneShot_TZ1          : Disable TZ1 as a One-shot trip source
 *                      - OneShot_TZ2          : Disable TZ2 as a One-shot trip source
 *                      - OneShot_TZ3          : Disable TZ3 as a One-shot trip source
 *                      - OneShot_TZ4          : Disable TZ4 as a One-shot trip source
 *                      - OneShot_TZ5          : Disable TZ5 as a One-shot trip source
 *                      - OneShot_TZ6          : Disable TZ6 as a One-shot trip source
 *                      - OneShot_DCAEVT1      : Disable DCAEVT1 as a One-shot trip source
 *                      - OneShot_DCBEVT1      : Disable DCBEVT1 as a One-shot trip source
 *
 *   This function disables the tripzone sources for cycle-by-cycle or one-shot trip
 */
/* SourceId : ETPWM_SourceId_029 */
/* DesignId : ETPWM_DesignId_029 */
/* Requirements : CONQ_EPWM_SR28 */
void etpwmDisableTripZoneSources( etpwmBASE_t * etpwm, etpwmTripZoneSrc_t sources )
{
    etpwm->TZSEL &= ( uint16 ) ~( uint16 ) sources;
}

/** @fn void etpwmSetTripAction(etpwmBASE_t *etpwm, etpwmTripActionConfig_t
 * tripactionconfig)
 *   @brief Set the action for each trip event
 *
 *   @param etpwm             The pulse width modulation (ETPWM) object handle
 * (etpwmREG1..7)
 *   @param tripactionconfig  Trip action configuration
 *
 *   This function sets the action for each trip event
 */
/* SourceId : ETPWM_SourceId_030 */
/* DesignId : ETPWM_DesignId_030 */
/* Requirements : CONQ_EPWM_SR29 */
void etpwmSetTripAction( etpwmBASE_t * etpwm, etpwmTripActionConfig_t tripactionconfig )
{
    etpwm->TZCTL = ( ( uint16 ) ( ( uint16 ) tripactionconfig.TripEvent_ActionOnPWMA
                                  << 0U )
                     | ( uint16 ) ( ( uint16 ) tripactionconfig.TripEvent_ActionOnPWMB
                                    << 2U )
                     | ( uint16 ) ( ( uint16 ) tripactionconfig.DCAEVT1_ActionOnPWMA
                                    << 4U )
                     | ( uint16 ) ( ( uint16 ) tripactionconfig.DCAEVT2_ActionOnPWMA
                                    << 6U )
                     | ( uint16 ) ( ( uint16 ) tripactionconfig.DCBEVT1_ActionOnPWMB
                                    << 8U )
                     | ( uint16 ) ( ( uint16 ) tripactionconfig.DCBEVT2_ActionOnPWMB
                                    << 10U ) );
}

/** @fn void etpwmEnableTripInterrupt(etpwmBASE_t *etpwm, etpwmTrip_t interrupts)
 *   @brief Enables interrupt(EPWMx_TZINT) for the trip event
 *
 *   @param etpwm       The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param interrupts  Interrupts to be enabled (Interrupts can be ORed)
 *                       - CycleByCycleTrip
 *                       - OneShotTrip
 *                       - DCAEVT1_inter
 *                       - DCAEVT2_inter
 *                       - DCBEVT1_inter
 *                       - DCBEVT2_inter
 *
 *   This function enables interrupt(EPWMx_TZINT) for the trip event
 */
/* SourceId : ETPWM_SourceId_031 */
/* DesignId : ETPWM_DesignId_031 */
/* Requirements : CONQ_EPWM_SR30 */
void etpwmEnableTripInterrupt( etpwmBASE_t * etpwm, etpwmTrip_t interrupts )
{
    etpwm->TZEINT |= interrupts;
}

/** @fn void etpwmDisableTripInterrupt(etpwmBASE_t *etpwm, etpwmTrip_t interrupts)
 *   @brief Disables interrupt(EPWMx_TZINT) for the trip event
 *
 *   @param etpwm       The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param interrupts  Trip Interrupts to be disabled (Interrupts can be ORed)
 *                       - CycleByCycleTrip
 *                       - OneShotTrip
 *                       - DCAEVT1_inter
 *                       - DCAEVT2_inter
 *                       - DCBEVT1_inter
 *                       - DCBEVT2_inter
 *
 *   This function disables interrupt(EPWMx_TZINT) for the trip event
 */
/* SourceId : ETPWM_SourceId_032 */
/* DesignId : ETPWM_DesignId_032 */
/* Requirements : CONQ_EPWM_SR31 */
void etpwmDisableTripInterrupt( etpwmBASE_t * etpwm, etpwmTrip_t interrupts )
{
    etpwm->TZEINT &= ( uint16 ) ~( uint16 ) interrupts;
}

/** @fn void etpwmClearTripCondition(etpwmBASE_t *etpwm, etpwmTrip_t trips)
 *   @brief Clears the trip event flag
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param trips     Trip events
 *                     - CycleByCycleTrip
 *                     - OneShotTrip
 *                     - DCAEVT1_inter
 *                     - DCAEVT2_inter
 *                     - DCBEVT1_inter
 *                     - DCBEVT2_inter
 *
 *   This function clears the trip event / Digital Compare output event flag
 */
/* SourceId : ETPWM_SourceId_033 */
/* DesignId : ETPWM_DesignId_033 */
/* Requirements : CONQ_EPWM_SR32 */
void etpwmClearTripCondition( etpwmBASE_t * etpwm, etpwmTrip_t trips )
{
    etpwm->TZCLR = trips;
}

/** @fn void etpwmClearTripInterruptFlag(etpwmBASE_t *etpwm)
 *   @brief Clears the trip interrupt flag
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function clears the trip interrupt flag
 */
/* SourceId : ETPWM_SourceId_034 */
/* DesignId : ETPWM_DesignId_034 */
/* Requirements : CONQ_EPWM_SR33 */
void etpwmClearTripInterruptFlag( etpwmBASE_t * etpwm )
{
    etpwm->TZCLR = 1U;
}

/** @fn void etpwmForceTripEvent(etpwmBASE_t *etpwm, etpwmTrip_t trip)
 *   @brief Force a trip event
 *
 *   @param etpwm     The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param trip      Trip events
 *                     - CycleByCycleTrip
 *                     - OneShotTrip
 *                     - DCAEVT1_inter
 *                     - DCAEVT2_inter
 *                     - DCBEVT1_inter
 *                     - DCBEVT2_inter
 *
 *   This function forces a trip event / Digital Compare trip event via software
 */
/* SourceId : ETPWM_SourceId_035 */
/* DesignId : ETPWM_DesignId_035 */
/* Requirements : CONQ_EPWM_SR34 */
void etpwmForceTripEvent( etpwmBASE_t * etpwm, etpwmTrip_t trip )
{
    etpwm->TZFRC = trip;
}

/** @fn void etpwmEnableSOCA(etpwmBASE_t *etpwm, etpwmEventSrc_t eventsource,
 * etpwmEventPeriod_t eventperiod)
 *   @brief Enable ADC Start of Conversion A pulse
 *
 *   @param etpwm        The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param eventsource  EPWMxSOCA Selection Options
 *                         - DCAEVT1       : DCAEVT1.soc event
 *                         - CTR_ZERO      : Event CTR = Zero
 *                         - CTR_PRD       : Event CTR = PRD
 *                         - CTR_ZERO_PRD  : Event CTR = Zero or CTR = PRD
 *                         - CTR_UP_CMPA   : Event CTR = CMPA when the timer is
 * incrementing
 *                         - CTR_D0WM_CMPA : Event CTR = CMPA when the timer is
 * decrementing
 *                         - CTR_UP_CMPB   : Event CTR = CMPB when the timer is
 * incrementing
 *                         - CTR_D0WM_CMPB : Event CTR = CMPB when the timer is
 * decrementing
 *   @param eventperiod  EPWMxSOCA Period Select
 *                         - EventPeriod_FirstEvent  : Generate SOCA pulse on the first
 * event
 *                         - EventPeriod_SecondEvent : Generate SOCA pulse on the second
 * event
 *                         - EventPeriod_ThirdEvent  : Generate SOCA pulse on the third
 * event
 *
 *   This function  enables ADC Start of Conversion A pulse
 */
/* SourceId : ETPWM_SourceId_036 */
/* DesignId : ETPWM_DesignId_036 */
/* Requirements : CONQ_EPWM_SR35 */
void etpwmEnableSOCA( etpwmBASE_t * etpwm,
                      etpwmEventSrc_t eventsource,
                      etpwmEventPeriod_t eventperiod )
{
    etpwm->ETSEL &= 0xF0FFU;
    etpwm->ETSEL |= ( uint16 ) ( ( uint16 ) 1U << 11U )
                  | ( uint16 ) ( ( uint16 ) eventsource << 8U );

    etpwm->ETPS &= 0xF0FFU;
    etpwm->ETPS |= ( uint16 ) ( ( uint16 ) eventperiod << 8U );
}

/** @fn void etpwmDisableSOCA(etpwmBASE_t *etpwm)
 *   @brief Disable ADC Start of Conversion A pulse
 *
 *   @param etpwm        The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function disables ADC Start of Conversion A pulse
 */
/* SourceId : ETPWM_SourceId_037 */
/* DesignId : ETPWM_DesignId_037 */
/* Requirements : CONQ_EPWM_SR36 */
void etpwmDisableSOCA( etpwmBASE_t * etpwm )
{
    etpwm->ETSEL &= 0xF0FFU;
}

/** @fn void etpwmEnableSOCB(etpwmBASE_t *etpwm, etpwmEventSrc_t eventsource,
 * etpwmEventPeriod_t eventperiod)
 *   @brief Enable ADC Start of Conversion B pulse
 *
 *   @param etpwm        The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param eventsource  EPWMxSOCB Selection Options
 *                         - DCBEVT1       : DCBEVT1.soc event
 *                         - CTR_ZERO      : Event CTR = Zero
 *                         - CTR_PRD       : Event CTR = PRD
 *                         - CTR_ZERO_PRD  : Event CTR = Zero or CTR = PRD
 *                         - CTR_UP_CMPA   : Event CTR = CMPA when the timer is
 * incrementing
 *                         - CTR_D0WM_CMPA : Event CTR = CMPA when the timer is
 * decrementing
 *                         - CTR_UP_CMPB   : Event CTR = CMPB when the timer is
 * incrementing
 *                         - CTR_D0WM_CMPB : Event CTR = CMPB when the timer is
 * decrementing
 *   @param eventperiod  EPWMxSOCB Period Select
 *                         - EventPeriod_FirstEvent  : Generate SOCB pulse on the first
 * event
 *                         - EventPeriod_SecondEvent : Generate SOCB pulse on the second
 * event
 *                         - EventPeriod_ThirdEvent  : Generate SOCB pulse on the third
 * event
 *
 *   This function enables ADC Start of Conversion B pulse
 */
/* SourceId : ETPWM_SourceId_038 */
/* DesignId : ETPWM_DesignId_038 */
/* Requirements : CONQ_EPWM_SR37 */
void etpwmEnableSOCB( etpwmBASE_t * etpwm,
                      etpwmEventSrc_t eventsource,
                      etpwmEventPeriod_t eventperiod )
{
    etpwm->ETSEL &= 0x0FFFU;
    etpwm->ETSEL |= ( uint16 ) ( ( uint16 ) 1U << 15U )
                  | ( uint16 ) ( ( uint16 ) eventsource << 12U );

    etpwm->ETPS &= 0x0FFFU;
    etpwm->ETPS |= ( uint16 ) ( ( uint16 ) eventperiod << 12U );
}

/** @fn void etpwmDisableSOCB(etpwmBASE_t *etpwm)
 *   @brief Disable ADC Start of Conversion B pulse
 *
 *   @param etpwm        The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function disables ADC Start of Conversion B pulse
 */
/* SourceId : ETPWM_SourceId_039 */
/* DesignId : ETPWM_DesignId_039 */
/* Requirements : CONQ_EPWM_SR38 */
void etpwmDisableSOCB( etpwmBASE_t * etpwm )
{
    etpwm->ETSEL &= 0x0FFFU;
}

/** @fn void etpwmEnableInterrupt(etpwmBASE_t *etpwm, etpwmEventSrc_t eventsource,
 * etpwmEventPeriod_t eventperiod)
 *   @brief Enable ePWM Interrupt
 *
 *   @param etpwm        The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param eventsource  EPWMx_INT Selection Options
 *                         - CTR_ZERO      : Event CTR = Zero
 *                         - CTR_PRD       : Event CTR = PRD
 *                         - CTR_ZERO_PRD  : Event CTR = Zero or CTR = PRD
 *                         - CTR_UP_CMPA   : Event CTR = CMPA when the timer is
 * incrementing
 *                         - CTR_D0WM_CMPA : Event CTR = CMPA when the timer is
 * decrementing
 *                         - CTR_UP_CMPB   : Event CTR = CMPB when the timer is
 * incrementing
 *                         - CTR_D0WM_CMPB : Event CTR = CMPB when the timer is
 * decrementing
 *   @param eventperiod  EPWMx_INT Period Select
 *                         - EventPeriod_FirstEvent  : Generate interrupt on the first
 * event
 *                         - EventPeriod_SecondEvent : Generate interrupt on the second
 * event
 *                         - EventPeriod_ThirdEvent  : Generate interrupt on the third
 * event
 *
 *   This function enables EPWMx_INT generation
 */
/* SourceId : ETPWM_SourceId_040 */
/* DesignId : ETPWM_DesignId_040 */
/* Requirements : CONQ_EPWM_SR39 */
void etpwmEnableInterrupt( etpwmBASE_t * etpwm,
                           etpwmEventSrc_t eventsource,
                           etpwmEventPeriod_t eventperiod )
{
    etpwm->ETSEL &= 0xFFF0U;
    etpwm->ETSEL |= ( uint16 ) ( ( uint16 ) 1U << 3U )
                  | ( uint16 ) ( ( uint16 ) eventsource << 0U );

    etpwm->ETPS &= 0xFFF0U;
    etpwm->ETPS |= ( uint16 ) ( ( uint16 ) eventperiod << 0U );
}

/** @fn void etpwmDisableInterrupt(etpwmBASE_t *etpwm)
 *   @brief Disable ePWM Interrupt
 *
 *   @param etpwm        The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *
 *   This function disables EPWMx_INT generation
 */
/* SourceId : ETPWM_SourceId_041 */
/* DesignId : ETPWM_DesignId_041 */
/* Requirements : CONQ_EPWM_SR40 */
void etpwmDisableInterrupt( etpwmBASE_t * etpwm )
{
    etpwm->ETSEL &= 0xFFF0U;
}

/** @fn uint16 etpwmGetEventStatus(etpwmBASE_t *etpwm)
 *   @brief Return event status flag
 *
 *   @param etpwm The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @return      event status flag
 *                  Bit 0: ePWM Interrupt(EPWMx_INT) Status Flag
 *                  Bit 2: ePWM ADC Start-of-Conversion A (EPWMxSOCA) Status Flag
 *                  Bit 3: ePWM ADC Start-of-Conversion B (EPWMxSOCB) Status Flag
 *
 *   This function returns the event status flags
 */
/* SourceId : ETPWM_SourceId_042 */
/* DesignId : ETPWM_DesignId_042 */
/* Requirements : CONQ_EPWM_SR47 */
uint16 etpwmGetEventStatus( etpwmBASE_t * etpwm )
{
    return etpwm->ETFLG;
}

/** @fn void etpwmClearEventFlag(etpwmBASE_t *etpwm, etpwmEvent_t events)
 *   @brief Clear event status flag
 *
 *   @param etpwm The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @param events status flag (flags can be ORed)
 *                  - Event_Interrupt
 *                  - Event_SOCA
 *                  - Event_SOCB
 *
 *   This function clears the event status flags
 */
/* SourceId : ETPWM_SourceId_043 */
/* DesignId : ETPWM_DesignId_043 */
/* Requirements : CONQ_EPWM_SR48 */
void etpwmClearEventFlag( etpwmBASE_t * etpwm, etpwmEvent_t events )
{
    etpwm->ETCLR = events;
}

/** @fn void etpwmTriggerEvent(etpwmBASE_t *etpwm, etpwmEvent_t events)
 *   @brief Force an event
 *
 *   @param etpwm The pulse width modulation (ETPWM) object handle (etpwmREG1..7)
 *   @return events (events can be ORed)
 *                  - Event_Interrupt
 *                  - Event_SOCA
 *                  - Event_SOCB
 *
 *   This function forces an event
 */
/* SourceId : ETPWM_SourceId_044 */
/* DesignId : ETPWM_DesignId_044 */
/* Requirements : CONQ_EPWM_SR49 */
void etpwmTriggerEvent( etpwmBASE_t * etpwm, etpwmEvent_t events )
{
    etpwm->ETFRC = events;
}

/** @fn void etpwmEnableDigitalCompareEvents(etpwmBASE_t *etpwm,
 * etpwmDigitalCompareConfig_t digitalcompareconfig)
 *   @brief Enable and configure digital compare events
 *
 *   @param etpwm                The pulse width modulation (ETPWM) object handle
 * (etpwmREG1..7)
 *   @param digitalcompareconfig Digital Compare modue configuration
 *
 *   Example usage (Removing semicolons to avoid MISRA warnings):
 *     etpwmDigitalCompareConfig_t config1
 *     config1.DCAH_src = TZ1
 *     config1.DCAL_src = TZ2
 *     config1.DCBH_src = TZ1
 *     config1.DCBL_src = TZ3
 *     config1.DCAEVT1_event = DCAH_High
 *     config1.DCAEVT2_event = DCAL_High
 *     config1.DCBEVT1_event = DCBL_High
 *     config1.DCBEVT2_event = DCBL_High_DCBH_low
 *     etpwmEnableDigitalCompareEvents(etpwmREG1, config1)
 *
 *   This function enbales and configures the digital compare events. HTis function can
 * also be used to disable digital compare events
 */
/* SourceId : ETPWM_SourceId_045 */
/* DesignId : ETPWM_DesignId_045 */
/* Requirements : CONQ_EPWM_SR41 */
void etpwmEnableDigitalCompareEvents( etpwmBASE_t * etpwm,
                                      etpwmDigitalCompareConfig_t digitalcompareconfig )
{
    etpwm->DCTRIPSEL = ( ( uint16 ) ( ( uint16 ) digitalcompareconfig.DCAH_src << 0U )
                         | ( uint16 ) ( ( uint16 ) digitalcompareconfig.DCAL_src << 4U )
                         | ( uint16 ) ( ( uint16 ) digitalcompareconfig.DCBH_src << 8U )
                         | ( uint16 ) ( ( uint16 ) digitalcompareconfig.DCBL_src
                                        << 12U ) );

    etpwm->TZDCSEL = ( ( uint16 ) ( ( uint16 ) digitalcompareconfig.DCAEVT1_event << 0U )
                       | ( uint16 ) ( ( uint16 ) digitalcompareconfig.DCAEVT2_event
                                      << 3U )
                       | ( uint16 ) ( ( uint16 ) digitalcompareconfig.DCBEVT1_event
                                      << 6U )
                       | ( uint16 ) ( ( uint16 ) digitalcompareconfig.DCBEVT2_event
                                      << 9U ) );
}

/** @fn void etpwm1GetConfigValue(etpwm_config_reg_t *config_reg, config_value_type_t
 *type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ETPWM_SourceId_046 */
/* DesignId : ETPWM_DesignId_046 */
/* Requirements : CONQ_EPWM_SR42 */
void etpwm1GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_TBCTL = ETPWM1_TBCTL_CONFIGVALUE;
        config_reg->CONFIG_TBPHS = ETPWM1_TBPHS_CONFIGVALUE;
        config_reg->CONFIG_TBPRD = ETPWM1_TBPRD_CONFIGVALUE;
        config_reg->CONFIG_CMPCTL = ETPWM1_CMPCTL_CONFIGVALUE;
        config_reg->CONFIG_CMPA = ETPWM1_CMPA_CONFIGVALUE;
        config_reg->CONFIG_CMPB = ETPWM1_CMPB_CONFIGVALUE;
        config_reg->CONFIG_AQCTLA = ETPWM1_AQCTLA_CONFIGVALUE;
        config_reg->CONFIG_AQCTLB = ETPWM1_AQCTLB_CONFIGVALUE;
        config_reg->CONFIG_DBCTL = ETPWM1_DBCTL_CONFIGVALUE;
        config_reg->CONFIG_DBRED = ETPWM1_DBRED_CONFIGVALUE;
        config_reg->CONFIG_DBFED = ETPWM1_DBFED_CONFIGVALUE;
        config_reg->CONFIG_TZSEL = ETPWM1_TZSEL_CONFIGVALUE;
        config_reg->CONFIG_TZDCSEL = ETPWM1_TZDCSEL_CONFIGVALUE;
        config_reg->CONFIG_TZCTL = ETPWM1_TZCTL_CONFIGVALUE;
        config_reg->CONFIG_TZEINT = ETPWM1_TZEINT_CONFIGVALUE;
        config_reg->CONFIG_ETSEL = ETPWM1_ETSEL_CONFIGVALUE;
        config_reg->CONFIG_ETPS = ETPWM1_ETPS_CONFIGVALUE;
        config_reg->CONFIG_PCCTL = ETPWM1_PCCTL_CONFIGVALUE;
        config_reg->CONFIG_DCTRIPSEL = ETPWM1_DCTRIPSEL_CONFIGVALUE;
        config_reg->CONFIG_DCACTL = ETPWM1_DCACTL_CONFIGVALUE;
        config_reg->CONFIG_DCBCTL = ETPWM1_DCBCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFCTL = ETPWM1_DCFCTL_CONFIGVALUE;
        config_reg->CONFIG_DCCAPCTL = ETPWM1_DCCAPCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOW = ETPWM1_DCFWINDOW_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOWCNT = ETPWM1_DCFWINDOWCNT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_TBCTL = etpwmREG1->TBCTL;
        config_reg->CONFIG_TBPHS = etpwmREG1->TBPHS;
        config_reg->CONFIG_TBPRD = etpwmREG1->TBPRD;
        config_reg->CONFIG_CMPCTL = etpwmREG1->CMPCTL;
        config_reg->CONFIG_CMPA = etpwmREG1->CMPA;
        config_reg->CONFIG_CMPB = etpwmREG1->CMPB;
        config_reg->CONFIG_AQCTLA = etpwmREG1->AQCTLA;
        config_reg->CONFIG_AQCTLB = etpwmREG1->AQCTLB;
        config_reg->CONFIG_DBCTL = etpwmREG1->DBCTL;
        config_reg->CONFIG_DBRED = etpwmREG1->DBRED;
        config_reg->CONFIG_DBFED = etpwmREG1->DBFED;
        config_reg->CONFIG_TZSEL = etpwmREG1->TZSEL;
        config_reg->CONFIG_TZDCSEL = etpwmREG1->TZDCSEL;
        config_reg->CONFIG_TZCTL = etpwmREG1->TZCTL;
        config_reg->CONFIG_TZEINT = etpwmREG1->TZEINT;
        config_reg->CONFIG_ETSEL = etpwmREG1->ETSEL;
        config_reg->CONFIG_ETPS = etpwmREG1->ETPS;
        config_reg->CONFIG_PCCTL = etpwmREG1->PCCTL;
        config_reg->CONFIG_DCTRIPSEL = etpwmREG1->DCTRIPSEL;
        config_reg->CONFIG_DCACTL = etpwmREG1->DCACTL;
        config_reg->CONFIG_DCBCTL = etpwmREG1->DCBCTL;
        config_reg->CONFIG_DCFCTL = etpwmREG1->DCFCTL;
        config_reg->CONFIG_DCCAPCTL = etpwmREG1->DCCAPCTL;
        config_reg->CONFIG_DCFWINDOW = etpwmREG1->DCFWINDOW;
        config_reg->CONFIG_DCFWINDOWCNT = etpwmREG1->DCFWINDOWCNT;
    }
}

/** @fn void etpwm2GetConfigValue(etpwm_config_reg_t *config_reg, config_value_type_t
 *type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ETPWM_SourceId_47 */
/* DesignId : ETPWM_DesignId_046 */
/* Requirements : CONQ_EPWM_SR42 */
void etpwm2GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_TBCTL = ETPWM2_TBCTL_CONFIGVALUE;
        config_reg->CONFIG_TBPHS = ETPWM2_TBPHS_CONFIGVALUE;
        config_reg->CONFIG_TBPRD = ETPWM2_TBPRD_CONFIGVALUE;
        config_reg->CONFIG_CMPCTL = ETPWM2_CMPCTL_CONFIGVALUE;
        config_reg->CONFIG_CMPA = ETPWM2_CMPA_CONFIGVALUE;
        config_reg->CONFIG_CMPB = ETPWM2_CMPB_CONFIGVALUE;
        config_reg->CONFIG_AQCTLA = ETPWM2_AQCTLA_CONFIGVALUE;
        config_reg->CONFIG_AQCTLB = ETPWM2_AQCTLB_CONFIGVALUE;
        config_reg->CONFIG_DBCTL = ETPWM2_DBCTL_CONFIGVALUE;
        config_reg->CONFIG_DBRED = ETPWM2_DBRED_CONFIGVALUE;
        config_reg->CONFIG_DBFED = ETPWM2_DBFED_CONFIGVALUE;
        config_reg->CONFIG_TZSEL = ETPWM2_TZSEL_CONFIGVALUE;
        config_reg->CONFIG_TZDCSEL = ETPWM2_TZDCSEL_CONFIGVALUE;
        config_reg->CONFIG_TZCTL = ETPWM2_TZCTL_CONFIGVALUE;
        config_reg->CONFIG_TZEINT = ETPWM2_TZEINT_CONFIGVALUE;
        config_reg->CONFIG_ETSEL = ETPWM2_ETSEL_CONFIGVALUE;
        config_reg->CONFIG_ETPS = ETPWM2_ETPS_CONFIGVALUE;
        config_reg->CONFIG_PCCTL = ETPWM2_PCCTL_CONFIGVALUE;
        config_reg->CONFIG_DCTRIPSEL = ETPWM2_DCTRIPSEL_CONFIGVALUE;
        config_reg->CONFIG_DCACTL = ETPWM2_DCACTL_CONFIGVALUE;
        config_reg->CONFIG_DCBCTL = ETPWM2_DCBCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFCTL = ETPWM2_DCFCTL_CONFIGVALUE;
        config_reg->CONFIG_DCCAPCTL = ETPWM2_DCCAPCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOW = ETPWM2_DCFWINDOW_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOWCNT = ETPWM2_DCFWINDOWCNT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_TBCTL = etpwmREG2->TBCTL;
        config_reg->CONFIG_TBPHS = etpwmREG2->TBPHS;
        config_reg->CONFIG_TBPRD = etpwmREG2->TBPRD;
        config_reg->CONFIG_CMPCTL = etpwmREG2->CMPCTL;
        config_reg->CONFIG_CMPA = etpwmREG2->CMPA;
        config_reg->CONFIG_CMPB = etpwmREG2->CMPB;
        config_reg->CONFIG_AQCTLA = etpwmREG2->AQCTLA;
        config_reg->CONFIG_AQCTLB = etpwmREG2->AQCTLB;
        config_reg->CONFIG_DBCTL = etpwmREG2->DBCTL;
        config_reg->CONFIG_DBRED = etpwmREG2->DBRED;
        config_reg->CONFIG_DBFED = etpwmREG2->DBFED;
        config_reg->CONFIG_TZSEL = etpwmREG2->TZSEL;
        config_reg->CONFIG_TZDCSEL = etpwmREG2->TZDCSEL;
        config_reg->CONFIG_TZCTL = etpwmREG2->TZCTL;
        config_reg->CONFIG_TZEINT = etpwmREG2->TZEINT;
        config_reg->CONFIG_ETSEL = etpwmREG2->ETSEL;
        config_reg->CONFIG_ETPS = etpwmREG2->ETPS;
        config_reg->CONFIG_PCCTL = etpwmREG2->PCCTL;
        config_reg->CONFIG_DCTRIPSEL = etpwmREG2->DCTRIPSEL;
        config_reg->CONFIG_DCACTL = etpwmREG2->DCACTL;
        config_reg->CONFIG_DCBCTL = etpwmREG2->DCBCTL;
        config_reg->CONFIG_DCFCTL = etpwmREG2->DCFCTL;
        config_reg->CONFIG_DCCAPCTL = etpwmREG2->DCCAPCTL;
        config_reg->CONFIG_DCFWINDOW = etpwmREG2->DCFWINDOW;
        config_reg->CONFIG_DCFWINDOWCNT = etpwmREG2->DCFWINDOWCNT;
    }
}

/** @fn void etpwm3GetConfigValue(etpwm_config_reg_t *config_reg, config_value_type_t
 *type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ETPWM_SourceId_048 */
/* DesignId : ETPWM_DesignId_046 */
/* Requirements : CONQ_EPWM_SR42 */
void etpwm3GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_TBCTL = ETPWM3_TBCTL_CONFIGVALUE;
        config_reg->CONFIG_TBPHS = ETPWM3_TBPHS_CONFIGVALUE;
        config_reg->CONFIG_TBPRD = ETPWM3_TBPRD_CONFIGVALUE;
        config_reg->CONFIG_CMPCTL = ETPWM3_CMPCTL_CONFIGVALUE;
        config_reg->CONFIG_CMPA = ETPWM3_CMPA_CONFIGVALUE;
        config_reg->CONFIG_CMPB = ETPWM3_CMPB_CONFIGVALUE;
        config_reg->CONFIG_AQCTLA = ETPWM3_AQCTLA_CONFIGVALUE;
        config_reg->CONFIG_AQCTLB = ETPWM3_AQCTLB_CONFIGVALUE;
        config_reg->CONFIG_DBCTL = ETPWM3_DBCTL_CONFIGVALUE;
        config_reg->CONFIG_DBRED = ETPWM3_DBRED_CONFIGVALUE;
        config_reg->CONFIG_DBFED = ETPWM3_DBFED_CONFIGVALUE;
        config_reg->CONFIG_TZSEL = ETPWM3_TZSEL_CONFIGVALUE;
        config_reg->CONFIG_TZDCSEL = ETPWM3_TZDCSEL_CONFIGVALUE;
        config_reg->CONFIG_TZCTL = ETPWM3_TZCTL_CONFIGVALUE;
        config_reg->CONFIG_TZEINT = ETPWM3_TZEINT_CONFIGVALUE;
        config_reg->CONFIG_ETSEL = ETPWM3_ETSEL_CONFIGVALUE;
        config_reg->CONFIG_ETPS = ETPWM3_ETPS_CONFIGVALUE;
        config_reg->CONFIG_PCCTL = ETPWM3_PCCTL_CONFIGVALUE;
        config_reg->CONFIG_DCTRIPSEL = ETPWM3_DCTRIPSEL_CONFIGVALUE;
        config_reg->CONFIG_DCACTL = ETPWM3_DCACTL_CONFIGVALUE;
        config_reg->CONFIG_DCBCTL = ETPWM3_DCBCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFCTL = ETPWM3_DCFCTL_CONFIGVALUE;
        config_reg->CONFIG_DCCAPCTL = ETPWM3_DCCAPCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOW = ETPWM3_DCFWINDOW_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOWCNT = ETPWM3_DCFWINDOWCNT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_TBCTL = etpwmREG3->TBCTL;
        config_reg->CONFIG_TBPHS = etpwmREG3->TBPHS;
        config_reg->CONFIG_TBPRD = etpwmREG3->TBPRD;
        config_reg->CONFIG_CMPCTL = etpwmREG3->CMPCTL;
        config_reg->CONFIG_CMPA = etpwmREG3->CMPA;
        config_reg->CONFIG_CMPB = etpwmREG3->CMPB;
        config_reg->CONFIG_AQCTLA = etpwmREG3->AQCTLA;
        config_reg->CONFIG_AQCTLB = etpwmREG3->AQCTLB;
        config_reg->CONFIG_DBCTL = etpwmREG3->DBCTL;
        config_reg->CONFIG_DBRED = etpwmREG3->DBRED;
        config_reg->CONFIG_DBFED = etpwmREG3->DBFED;
        config_reg->CONFIG_TZSEL = etpwmREG3->TZSEL;
        config_reg->CONFIG_TZDCSEL = etpwmREG3->TZDCSEL;
        config_reg->CONFIG_TZCTL = etpwmREG3->TZCTL;
        config_reg->CONFIG_TZEINT = etpwmREG3->TZEINT;
        config_reg->CONFIG_ETSEL = etpwmREG3->ETSEL;
        config_reg->CONFIG_ETPS = etpwmREG3->ETPS;
        config_reg->CONFIG_PCCTL = etpwmREG3->PCCTL;
        config_reg->CONFIG_DCTRIPSEL = etpwmREG3->DCTRIPSEL;
        config_reg->CONFIG_DCACTL = etpwmREG3->DCACTL;
        config_reg->CONFIG_DCBCTL = etpwmREG3->DCBCTL;
        config_reg->CONFIG_DCFCTL = etpwmREG3->DCFCTL;
        config_reg->CONFIG_DCCAPCTL = etpwmREG3->DCCAPCTL;
        config_reg->CONFIG_DCFWINDOW = etpwmREG3->DCFWINDOW;
        config_reg->CONFIG_DCFWINDOWCNT = etpwmREG3->DCFWINDOWCNT;
    }
}

/** @fn void etpwm4GetConfigValue(etpwm_config_reg_t *config_reg, config_value_type_t
 *type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ETPWM_SourceId_049 */
/* DesignId : ETPWM_DesignId_046 */
/* Requirements : CONQ_EPWM_SR42 */
void etpwm4GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_TBCTL = ETPWM4_TBCTL_CONFIGVALUE;
        config_reg->CONFIG_TBPHS = ETPWM4_TBPHS_CONFIGVALUE;
        config_reg->CONFIG_TBPRD = ETPWM4_TBPRD_CONFIGVALUE;
        config_reg->CONFIG_CMPCTL = ETPWM4_CMPCTL_CONFIGVALUE;
        config_reg->CONFIG_CMPA = ETPWM4_CMPA_CONFIGVALUE;
        config_reg->CONFIG_CMPB = ETPWM4_CMPB_CONFIGVALUE;
        config_reg->CONFIG_AQCTLA = ETPWM4_AQCTLA_CONFIGVALUE;
        config_reg->CONFIG_AQCTLB = ETPWM4_AQCTLB_CONFIGVALUE;
        config_reg->CONFIG_DBCTL = ETPWM4_DBCTL_CONFIGVALUE;
        config_reg->CONFIG_DBRED = ETPWM4_DBRED_CONFIGVALUE;
        config_reg->CONFIG_DBFED = ETPWM4_DBFED_CONFIGVALUE;
        config_reg->CONFIG_TZSEL = ETPWM4_TZSEL_CONFIGVALUE;
        config_reg->CONFIG_TZDCSEL = ETPWM4_TZDCSEL_CONFIGVALUE;
        config_reg->CONFIG_TZCTL = ETPWM4_TZCTL_CONFIGVALUE;
        config_reg->CONFIG_TZEINT = ETPWM4_TZEINT_CONFIGVALUE;
        config_reg->CONFIG_ETSEL = ETPWM4_ETSEL_CONFIGVALUE;
        config_reg->CONFIG_ETPS = ETPWM4_ETPS_CONFIGVALUE;
        config_reg->CONFIG_PCCTL = ETPWM4_PCCTL_CONFIGVALUE;
        config_reg->CONFIG_DCTRIPSEL = ETPWM4_DCTRIPSEL_CONFIGVALUE;
        config_reg->CONFIG_DCACTL = ETPWM4_DCACTL_CONFIGVALUE;
        config_reg->CONFIG_DCBCTL = ETPWM4_DCBCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFCTL = ETPWM4_DCFCTL_CONFIGVALUE;
        config_reg->CONFIG_DCCAPCTL = ETPWM4_DCCAPCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOW = ETPWM4_DCFWINDOW_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOWCNT = ETPWM4_DCFWINDOWCNT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_TBCTL = etpwmREG4->TBCTL;
        config_reg->CONFIG_TBPHS = etpwmREG4->TBPHS;
        config_reg->CONFIG_TBPRD = etpwmREG4->TBPRD;
        config_reg->CONFIG_CMPCTL = etpwmREG4->CMPCTL;
        config_reg->CONFIG_CMPA = etpwmREG4->CMPA;
        config_reg->CONFIG_CMPB = etpwmREG4->CMPB;
        config_reg->CONFIG_AQCTLA = etpwmREG4->AQCTLA;
        config_reg->CONFIG_AQCTLB = etpwmREG4->AQCTLB;
        config_reg->CONFIG_DBCTL = etpwmREG4->DBCTL;
        config_reg->CONFIG_DBRED = etpwmREG4->DBRED;
        config_reg->CONFIG_DBFED = etpwmREG4->DBFED;
        config_reg->CONFIG_TZSEL = etpwmREG4->TZSEL;
        config_reg->CONFIG_TZDCSEL = etpwmREG4->TZDCSEL;
        config_reg->CONFIG_TZCTL = etpwmREG4->TZCTL;
        config_reg->CONFIG_TZEINT = etpwmREG4->TZEINT;
        config_reg->CONFIG_ETSEL = etpwmREG4->ETSEL;
        config_reg->CONFIG_ETPS = etpwmREG4->ETPS;
        config_reg->CONFIG_PCCTL = etpwmREG4->PCCTL;
        config_reg->CONFIG_DCTRIPSEL = etpwmREG4->DCTRIPSEL;
        config_reg->CONFIG_DCACTL = etpwmREG4->DCACTL;
        config_reg->CONFIG_DCBCTL = etpwmREG4->DCBCTL;
        config_reg->CONFIG_DCFCTL = etpwmREG4->DCFCTL;
        config_reg->CONFIG_DCCAPCTL = etpwmREG4->DCCAPCTL;
        config_reg->CONFIG_DCFWINDOW = etpwmREG4->DCFWINDOW;
        config_reg->CONFIG_DCFWINDOWCNT = etpwmREG4->DCFWINDOWCNT;
    }
}

/** @fn void etpwm5GetConfigValue(etpwm_config_reg_t *config_reg, config_value_type_t
 *type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ETPWM_SourceId_050 */
/* DesignId : ETPWM_DesignId_046 */
/* Requirements : CONQ_EPWM_SR42 */
void etpwm5GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_TBCTL = ETPWM5_TBCTL_CONFIGVALUE;
        config_reg->CONFIG_TBPHS = ETPWM5_TBPHS_CONFIGVALUE;
        config_reg->CONFIG_TBPRD = ETPWM5_TBPRD_CONFIGVALUE;
        config_reg->CONFIG_CMPCTL = ETPWM5_CMPCTL_CONFIGVALUE;
        config_reg->CONFIG_CMPA = ETPWM5_CMPA_CONFIGVALUE;
        config_reg->CONFIG_CMPB = ETPWM5_CMPB_CONFIGVALUE;
        config_reg->CONFIG_AQCTLA = ETPWM5_AQCTLA_CONFIGVALUE;
        config_reg->CONFIG_AQCTLB = ETPWM5_AQCTLB_CONFIGVALUE;
        config_reg->CONFIG_DBCTL = ETPWM5_DBCTL_CONFIGVALUE;
        config_reg->CONFIG_DBRED = ETPWM5_DBRED_CONFIGVALUE;
        config_reg->CONFIG_DBFED = ETPWM5_DBFED_CONFIGVALUE;
        config_reg->CONFIG_TZSEL = ETPWM5_TZSEL_CONFIGVALUE;
        config_reg->CONFIG_TZDCSEL = ETPWM5_TZDCSEL_CONFIGVALUE;
        config_reg->CONFIG_TZCTL = ETPWM5_TZCTL_CONFIGVALUE;
        config_reg->CONFIG_TZEINT = ETPWM5_TZEINT_CONFIGVALUE;
        config_reg->CONFIG_ETSEL = ETPWM5_ETSEL_CONFIGVALUE;
        config_reg->CONFIG_ETPS = ETPWM5_ETPS_CONFIGVALUE;
        config_reg->CONFIG_PCCTL = ETPWM5_PCCTL_CONFIGVALUE;
        config_reg->CONFIG_DCTRIPSEL = ETPWM5_DCTRIPSEL_CONFIGVALUE;
        config_reg->CONFIG_DCACTL = ETPWM5_DCACTL_CONFIGVALUE;
        config_reg->CONFIG_DCBCTL = ETPWM5_DCBCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFCTL = ETPWM5_DCFCTL_CONFIGVALUE;
        config_reg->CONFIG_DCCAPCTL = ETPWM5_DCCAPCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOW = ETPWM5_DCFWINDOW_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOWCNT = ETPWM5_DCFWINDOWCNT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_TBCTL = etpwmREG5->TBCTL;
        config_reg->CONFIG_TBPHS = etpwmREG5->TBPHS;
        config_reg->CONFIG_TBPRD = etpwmREG5->TBPRD;
        config_reg->CONFIG_CMPCTL = etpwmREG5->CMPCTL;
        config_reg->CONFIG_CMPA = etpwmREG5->CMPA;
        config_reg->CONFIG_CMPB = etpwmREG5->CMPB;
        config_reg->CONFIG_AQCTLA = etpwmREG5->AQCTLA;
        config_reg->CONFIG_AQCTLB = etpwmREG5->AQCTLB;
        config_reg->CONFIG_DBCTL = etpwmREG5->DBCTL;
        config_reg->CONFIG_DBRED = etpwmREG5->DBRED;
        config_reg->CONFIG_DBFED = etpwmREG5->DBFED;
        config_reg->CONFIG_TZSEL = etpwmREG5->TZSEL;
        config_reg->CONFIG_TZDCSEL = etpwmREG5->TZDCSEL;
        config_reg->CONFIG_TZCTL = etpwmREG5->TZCTL;
        config_reg->CONFIG_TZEINT = etpwmREG5->TZEINT;
        config_reg->CONFIG_ETSEL = etpwmREG5->ETSEL;
        config_reg->CONFIG_ETPS = etpwmREG5->ETPS;
        config_reg->CONFIG_PCCTL = etpwmREG5->PCCTL;
        config_reg->CONFIG_DCTRIPSEL = etpwmREG5->DCTRIPSEL;
        config_reg->CONFIG_DCACTL = etpwmREG5->DCACTL;
        config_reg->CONFIG_DCBCTL = etpwmREG5->DCBCTL;
        config_reg->CONFIG_DCFCTL = etpwmREG5->DCFCTL;
        config_reg->CONFIG_DCCAPCTL = etpwmREG5->DCCAPCTL;
        config_reg->CONFIG_DCFWINDOW = etpwmREG5->DCFWINDOW;
        config_reg->CONFIG_DCFWINDOWCNT = etpwmREG5->DCFWINDOWCNT;
    }
}

/** @fn void etpwm6GetConfigValue(etpwm_config_reg_t *config_reg, config_value_type_t
 *type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ETPWM_SourceId_051 */
/* DesignId : ETPWM_DesignId_046 */
/* Requirements : CONQ_EPWM_SR42 */
void etpwm6GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_TBCTL = ETPWM6_TBCTL_CONFIGVALUE;
        config_reg->CONFIG_TBPHS = ETPWM6_TBPHS_CONFIGVALUE;
        config_reg->CONFIG_TBPRD = ETPWM6_TBPRD_CONFIGVALUE;
        config_reg->CONFIG_CMPCTL = ETPWM6_CMPCTL_CONFIGVALUE;
        config_reg->CONFIG_CMPA = ETPWM6_CMPA_CONFIGVALUE;
        config_reg->CONFIG_CMPB = ETPWM6_CMPB_CONFIGVALUE;
        config_reg->CONFIG_AQCTLA = ETPWM6_AQCTLA_CONFIGVALUE;
        config_reg->CONFIG_AQCTLB = ETPWM6_AQCTLB_CONFIGVALUE;
        config_reg->CONFIG_DBCTL = ETPWM6_DBCTL_CONFIGVALUE;
        config_reg->CONFIG_DBRED = ETPWM6_DBRED_CONFIGVALUE;
        config_reg->CONFIG_DBFED = ETPWM6_DBFED_CONFIGVALUE;
        config_reg->CONFIG_TZSEL = ETPWM6_TZSEL_CONFIGVALUE;
        config_reg->CONFIG_TZDCSEL = ETPWM6_TZDCSEL_CONFIGVALUE;
        config_reg->CONFIG_TZCTL = ETPWM6_TZCTL_CONFIGVALUE;
        config_reg->CONFIG_TZEINT = ETPWM6_TZEINT_CONFIGVALUE;
        config_reg->CONFIG_ETSEL = ETPWM6_ETSEL_CONFIGVALUE;
        config_reg->CONFIG_ETPS = ETPWM6_ETPS_CONFIGVALUE;
        config_reg->CONFIG_PCCTL = ETPWM6_PCCTL_CONFIGVALUE;
        config_reg->CONFIG_DCTRIPSEL = ETPWM6_DCTRIPSEL_CONFIGVALUE;
        config_reg->CONFIG_DCACTL = ETPWM6_DCACTL_CONFIGVALUE;
        config_reg->CONFIG_DCBCTL = ETPWM6_DCBCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFCTL = ETPWM6_DCFCTL_CONFIGVALUE;
        config_reg->CONFIG_DCCAPCTL = ETPWM6_DCCAPCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOW = ETPWM6_DCFWINDOW_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOWCNT = ETPWM6_DCFWINDOWCNT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_TBCTL = etpwmREG6->TBCTL;
        config_reg->CONFIG_TBPHS = etpwmREG6->TBPHS;
        config_reg->CONFIG_TBPRD = etpwmREG6->TBPRD;
        config_reg->CONFIG_CMPCTL = etpwmREG6->CMPCTL;
        config_reg->CONFIG_CMPA = etpwmREG6->CMPA;
        config_reg->CONFIG_CMPB = etpwmREG6->CMPB;
        config_reg->CONFIG_AQCTLA = etpwmREG6->AQCTLA;
        config_reg->CONFIG_AQCTLB = etpwmREG6->AQCTLB;
        config_reg->CONFIG_DBCTL = etpwmREG6->DBCTL;
        config_reg->CONFIG_DBRED = etpwmREG6->DBRED;
        config_reg->CONFIG_DBFED = etpwmREG6->DBFED;
        config_reg->CONFIG_TZSEL = etpwmREG6->TZSEL;
        config_reg->CONFIG_TZDCSEL = etpwmREG6->TZDCSEL;
        config_reg->CONFIG_TZCTL = etpwmREG6->TZCTL;
        config_reg->CONFIG_TZEINT = etpwmREG6->TZEINT;
        config_reg->CONFIG_ETSEL = etpwmREG6->ETSEL;
        config_reg->CONFIG_ETPS = etpwmREG6->ETPS;
        config_reg->CONFIG_PCCTL = etpwmREG6->PCCTL;
        config_reg->CONFIG_DCTRIPSEL = etpwmREG6->DCTRIPSEL;
        config_reg->CONFIG_DCACTL = etpwmREG6->DCACTL;
        config_reg->CONFIG_DCBCTL = etpwmREG6->DCBCTL;
        config_reg->CONFIG_DCFCTL = etpwmREG6->DCFCTL;
        config_reg->CONFIG_DCCAPCTL = etpwmREG6->DCCAPCTL;
        config_reg->CONFIG_DCFWINDOW = etpwmREG6->DCFWINDOW;
        config_reg->CONFIG_DCFWINDOWCNT = etpwmREG6->DCFWINDOWCNT;
    }
}

/** @fn void etpwm7GetConfigValue(etpwm_config_reg_t *config_reg, config_value_type_t
 *type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ETPWM_SourceId_052 */
/* DesignId : ETPWM_DesignId_046 */
/* Requirements : CONQ_EPWM_SR42 */
void etpwm7GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_TBCTL = ETPWM1_TBCTL_CONFIGVALUE;
        config_reg->CONFIG_TBPHS = ETPWM7_TBPHS_CONFIGVALUE;
        config_reg->CONFIG_TBPRD = ETPWM7_TBPRD_CONFIGVALUE;
        config_reg->CONFIG_CMPCTL = ETPWM7_CMPCTL_CONFIGVALUE;
        config_reg->CONFIG_CMPA = ETPWM7_CMPA_CONFIGVALUE;
        config_reg->CONFIG_CMPB = ETPWM7_CMPB_CONFIGVALUE;
        config_reg->CONFIG_AQCTLA = ETPWM7_AQCTLA_CONFIGVALUE;
        config_reg->CONFIG_AQCTLB = ETPWM7_AQCTLB_CONFIGVALUE;
        config_reg->CONFIG_DBCTL = ETPWM7_DBCTL_CONFIGVALUE;
        config_reg->CONFIG_DBRED = ETPWM7_DBRED_CONFIGVALUE;
        config_reg->CONFIG_DBFED = ETPWM7_DBFED_CONFIGVALUE;
        config_reg->CONFIG_TZSEL = ETPWM7_TZSEL_CONFIGVALUE;
        config_reg->CONFIG_TZDCSEL = ETPWM7_TZDCSEL_CONFIGVALUE;
        config_reg->CONFIG_TZCTL = ETPWM7_TZCTL_CONFIGVALUE;
        config_reg->CONFIG_TZEINT = ETPWM7_TZEINT_CONFIGVALUE;
        config_reg->CONFIG_ETSEL = ETPWM7_ETSEL_CONFIGVALUE;
        config_reg->CONFIG_ETPS = ETPWM7_ETPS_CONFIGVALUE;
        config_reg->CONFIG_PCCTL = ETPWM7_PCCTL_CONFIGVALUE;
        config_reg->CONFIG_DCTRIPSEL = ETPWM7_DCTRIPSEL_CONFIGVALUE;
        config_reg->CONFIG_DCACTL = ETPWM7_DCACTL_CONFIGVALUE;
        config_reg->CONFIG_DCBCTL = ETPWM7_DCBCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFCTL = ETPWM7_DCFCTL_CONFIGVALUE;
        config_reg->CONFIG_DCCAPCTL = ETPWM7_DCCAPCTL_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOW = ETPWM7_DCFWINDOW_CONFIGVALUE;
        config_reg->CONFIG_DCFWINDOWCNT = ETPWM7_DCFWINDOWCNT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_TBCTL = etpwmREG7->TBCTL;
        config_reg->CONFIG_TBPHS = etpwmREG7->TBPHS;
        config_reg->CONFIG_TBPRD = etpwmREG7->TBPRD;
        config_reg->CONFIG_CMPCTL = etpwmREG7->CMPCTL;
        config_reg->CONFIG_CMPA = etpwmREG7->CMPA;
        config_reg->CONFIG_CMPB = etpwmREG7->CMPB;
        config_reg->CONFIG_AQCTLA = etpwmREG7->AQCTLA;
        config_reg->CONFIG_AQCTLB = etpwmREG7->AQCTLB;
        config_reg->CONFIG_DBCTL = etpwmREG7->DBCTL;
        config_reg->CONFIG_DBRED = etpwmREG7->DBRED;
        config_reg->CONFIG_DBFED = etpwmREG7->DBFED;
        config_reg->CONFIG_TZSEL = etpwmREG7->TZSEL;
        config_reg->CONFIG_TZDCSEL = etpwmREG7->TZDCSEL;
        config_reg->CONFIG_TZCTL = etpwmREG7->TZCTL;
        config_reg->CONFIG_TZEINT = etpwmREG7->TZEINT;
        config_reg->CONFIG_ETSEL = etpwmREG7->ETSEL;
        config_reg->CONFIG_ETPS = etpwmREG7->ETPS;
        config_reg->CONFIG_PCCTL = etpwmREG7->PCCTL;
        config_reg->CONFIG_DCTRIPSEL = etpwmREG7->DCTRIPSEL;
        config_reg->CONFIG_DCACTL = etpwmREG7->DCACTL;
        config_reg->CONFIG_DCBCTL = etpwmREG7->DCBCTL;
        config_reg->CONFIG_DCFCTL = etpwmREG7->DCFCTL;
        config_reg->CONFIG_DCCAPCTL = etpwmREG7->DCCAPCTL;
        config_reg->CONFIG_DCFWINDOW = etpwmREG7->DCFWINDOW;
        config_reg->CONFIG_DCFWINDOWCNT = etpwmREG7->DCFWINDOWCNT;
    }
}

/* USER CODE BEGIN (31) */
/* USER CODE END */
