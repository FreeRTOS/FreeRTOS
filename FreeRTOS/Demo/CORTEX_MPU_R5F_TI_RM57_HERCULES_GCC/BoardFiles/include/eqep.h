/** @file eqep.h
 *   @brief EQEP Driver Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
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

#ifndef __eQEP_H__
#define __eQEP_H__

#include "reg_eqep.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

#define QEP_BASE_ADDR ( 0x00006B00U ) /*<base address of QEP */

/*QDECCTL Register */
#define eQEP_QDECCTL_QSRC \
    ( ( uint16 ) ( ( uint16 ) 3U << 14U ) ) /*<position counter source selection   */
#define eQEP_QDECCTL_SOEN \
    ( ( uint16 ) ( ( uint16 ) 1U << 13U ) ) /*<sync output enable                  */
#define eQEP_QDECCTL_SPSEL \
    ( ( uint16 ) ( ( uint16 ) 1U << 12U ) ) /*<sync output pin selection           */
#define eQEP_QDECCTL_XCR \
    ( ( uint16 ) ( ( uint16 ) 1U << 11U ) ) /*<external clock rate                 */
#define eQEP_QDECCTL_SWAP \
    ( ( uint16 ) ( ( uint16 ) 1U << 10U ) ) /*<swap quadrature clock inputs        */
#define eQEP_QDECCTL_IGATE \
    ( ( uint16 ) ( ( uint16 ) 1U << 9U ) ) /*<index pulse gating option           */
#define eQEP_QDECCTL_QAP \
    ( ( uint16 ) ( ( uint16 ) 1U << 8U ) ) /*<QEPA input polarity                 */
#define eQEP_QDECCTL_QBP \
    ( ( uint16 ) ( ( uint16 ) 1U << 7U ) ) /*<QEPB input polarity                 */
#define eQEP_QDECCTL_QIP \
    ( ( uint16 ) ( ( uint16 ) 1U << 6U ) ) /*<QEPI input polarity                 */
#define eQEP_QDECCTL_QSP \
    ( ( uint16 ) ( ( uint16 ) 1U << 5U ) ) /*<QEPS input polarity                 */

/*QEPCTL Register */
#define eQEP_QEPCTL_FREESOFT \
    ( ( uint16 ) ( ( uint16 ) 3U << 14U ) ) /*<emulation control bit */
#define eQEP_QEPCTL_PCRM \
    ( ( uint16 ) ( ( uint16 ) 3U << 12U ) ) /*<emulation control bit */
#define eQEP_QEPCTL_SEI                                                                \
    ( ( uint16 ) ( ( uint16 ) 3U << 10U ) ) /*<strobe event initialization of position \
                                               counter                */
#define eQEP_QEPCTL_IEI                                                              \
    ( ( uint16 ) ( ( uint16 ) 3U << 8U ) ) /*<index event initialization of position \
                                              counter                 */
#define eQEP_QEPCTL_SWI                                                           \
    ( ( uint16 ) ( ( uint16 ) 1U << 7U ) ) /*<software initialization of position \
                                              counter                    */
#define eQEP_QEPCTL_SEL \
    ( ( uint16 ) ( ( uint16 ) 1U << 6U ) ) /*<strobe event latch of position counter */
#define eQEP_QEPCTL_IEL                                                                \
    ( ( uint16 ) ( ( uint16 ) 3U << 4U ) ) /*<index event latch of position counter    \
                                              ((uint16)((uint16)software index marker) \
                                            */
#define eQEP_QEPCTL_QPEN                                                            \
    ( ( uint16 ) ( ( uint16 ) 1U << 3U ) ) /*<quad position counter enable/software \
                                              reset                    */
#define eQEP_QEPCTL_QCLM \
    ( ( uint16 ) ( ( uint16 ) 1U << 2U ) ) /*<QEP capture latch mode */
#define eQEP_QEPCTL_UTE                                             \
    ( ( uint16 ) ( ( uint16 ) 1U << 1U ) ) /*<QEP unit timer enable \
                                            */
#define eQEP_QEPCTL_WDE                                             \
    ( ( uint16 ) ( ( uint16 ) 1U << 0U ) ) /*<watchdog timer enable \
                                            */

/*QPOSCTL Register */
#define eQEP_QPOSCTL_PCSHDW \
    ( ( uint16 ) ( ( uint16 ) 1U << 15U ) ) /*<position compare shadow enable */
#define eQEP_QPOSCTL_PCLOAD \
    ( ( uint16 ) ( ( uint16 ) 1U << 14U ) ) /*<position compare shadow load mode */
#define eQEP_QPOSCTL_PCPOL \
    ( ( uint16 ) ( ( uint16 ) 1U << 13U ) ) /*<load when QPOSCNT = QPOSCMP */
#define eQEP_QPOSCTL_PCE \
    ( ( uint16 ) ( ( uint16 ) 1U << 12U ) ) /*<position compare enable/disable */
#define eQEP_QPOSCTL_PCSPW                                                              \
    ( ( uint16 ) ( ( uint16 ) 4095U << 0U ) ) /*<selection position compare sync output \
                                                 pulse width                 */

/*QCAPCTL Register */
#define eQEP_QCAPCTL_CEN \
    ( ( uint16 ) ( ( uint16 ) 1U << 15U ) ) /*<enable QEP capture                */
#define eQEP_QCAPCTL_CCPS \
    ( ( uint16 ) ( ( uint16 ) 7U << 4U ) ) /*<qep capture timer clock prescaler */
#define eQEP_QCAPCTL_UPPS \
    ( ( uint16 ) ( ( uint16 ) 15U << 0U ) ) /*<unit position event prescaler     */

/*QEINT Register */
#define eQEP_QEINT_UTO \
    ( ( uint16 ) ( ( uint16 ) 1U << 11U ) ) /*<unit timeout interrupt enable */
#define eQEP_QEINT_IEL \
    ( ( uint16 ) ( ( uint16 ) 1U << 10U ) ) /*<index event latch interrupt enable */
#define eQEP_QEINT_SEL \
    ( ( uint16 ) ( ( uint16 ) 1U << 9U ) ) /*<strobe event latch	interrupt enable */
#define eQEP_QEINT_PCM                                                                \
    ( ( uint16 ) ( ( uint16 ) 1U << 8U ) ) /*<position compare match interrupt enable \
                                            */
#define eQEP_QEINT_PCR \
    ( ( uint16 ) ( ( uint16 ) 1U << 7U ) ) /*<position compare ready interrupt enable */
#define eQEP_QEINT_PCO                                                                   \
    ( ( uint16 ) ( ( uint16 ) 1U << 6U ) ) /*<position counter overflow interrupt enable \
                                            */
#define eQEP_QEINT_PCU                                                             \
    ( ( uint16 ) ( ( uint16 ) 1U << 5U ) ) /*<position counter underflow interrupt \
                                              enable      */
#define eQEP_QEINT_WTO \
    ( ( uint16 ) ( ( uint16 ) 1U << 4U ) ) /*<watchdog time out interrupt enable */
#define eQEP_QEINT_QDC                                                              \
    ( ( uint16 ) ( ( uint16 ) 1U << 3U ) ) /*<quadrature direction change interrupt \
                                              enable     */
#define eQEP_QEINT_QPE \
    ( ( uint16 ) ( ( uint16 ) 1U << 2U ) ) /*<quadrature phase error interrupt enable */
#define eQEP_QEINT_PCE \
    ( ( uint16 ) ( ( uint16 ) 1U << 1U ) ) /*<position counter error interrupt enable */

/*QFLG Register */
#define eQEP_QFLG_UTO \
    ( ( uint16 ) ( ( uint16 ) 1U << 11U ) ) /*<unit timeout interrupt flag */
#define eQEP_QFLG_IEL \
    ( ( uint16 ) ( ( uint16 ) 1U << 10U ) ) /*<index event latch interrupt flag */
#define eQEP_QFLG_SEL \
    ( ( uint16 ) ( ( uint16 ) 1U << 9U ) ) /*<strobe event latch	interrupt flag */
#define eQEP_QFLG_PCM \
    ( ( uint16 ) ( ( uint16 ) 1U << 8U ) ) /*<position compare match interrupt flag */
#define eQEP_QFLG_PCR \
    ( ( uint16 ) ( ( uint16 ) 1U << 7U ) ) /*<position compare ready interrupt flag */
#define eQEP_QFLG_PCO                                                                  \
    ( ( uint16 ) ( ( uint16 ) 1U << 6U ) ) /*<position counter overflow interrupt flag \
                                            */
#define eQEP_QFLG_PCU                                                                   \
    ( ( uint16 ) ( ( uint16 ) 1U << 5U ) ) /*<position counter underflow interrupt flag \
                                            */
#define eQEP_QFLG_WTO \
    ( ( uint16 ) ( ( uint16 ) 1U << 4U ) ) /*<watchdog time out interrupt flag */
#define eQEP_QFLG_QDC                                                                    \
    ( ( uint16 ) ( ( uint16 ) 1U << 3U ) ) /*<quadrature direction change interrupt flag \
                                            */
#define eQEP_QFLG_QPE \
    ( ( uint16 ) ( ( uint16 ) 1U << 2U ) ) /*<quadrature phase error interrupt flag */
#define eQEP_QFLG_PCE \
    ( ( uint16 ) ( ( uint16 ) 1U << 1U ) ) /*<position counter error interrupt flag */

/*QCLR Register */
#define eQEP_QCLR_UTO \
    ( ( uint16 ) ( ( uint16 ) 1U << 11U ) ) /*<clear unit timeout interrupt flag */
#define eQEP_QCLR_IEL \
    ( ( uint16 ) ( ( uint16 ) 1U << 10U ) ) /*<clear index event latch interrupt flag */
#define eQEP_QCLR_SEL \
    ( ( uint16 ) ( ( uint16 ) 1U << 9U ) ) /*<clear strobe event latch interrupt flag */
#define eQEP_QCLR_PCM                                                                \
    ( ( uint16 ) ( ( uint16 ) 1U << 8U ) ) /*<clear position compare match interrupt \
                                              flag        */
#define eQEP_QCLR_PCR                                                                \
    ( ( uint16 ) ( ( uint16 ) 1U << 7U ) ) /*<clear position compare ready interrupt \
                                              flag        */
#define eQEP_QCLR_PCO                                                                   \
    ( ( uint16 ) ( ( uint16 ) 1U << 6U ) ) /*<clear position counter overflow interrupt \
                                              flag     */
#define eQEP_QCLR_PCU                                                                    \
    ( ( uint16 ) ( ( uint16 ) 1U << 5U ) ) /*<clear position counter underflow interrupt \
                                              flag    */
#define eQEP_QCLR_WTO \
    ( ( uint16 ) ( ( uint16 ) 1U << 4U ) ) /*<clear watchdog time out interrupt flag */
#define eQEP_QCLR_QDC                                                           \
    ( ( uint16 ) ( ( uint16 ) 1U << 3U ) ) /*<clear quadrature direction change \
                                              interrupt flag   */
#define eQEP_QCLR_QPE                                                                \
    ( ( uint16 ) ( ( uint16 ) 1U << 2U ) ) /*<clear quadrature phase error interrupt \
                                              flag        */
#define eQEP_QCLR_PCE                                                                \
    ( ( uint16 ) ( ( uint16 ) 1U << 1U ) ) /*<clear position counter error interrupt \
                                              flag        */

/*QFRC Register */
#define eQEP_QFRC_UTO \
    ( ( uint16 ) ( ( uint16 ) 1U << 11U ) ) /*<force unit timeout interrupt */
#define eQEP_QFRC_IEL \
    ( ( uint16 ) ( ( uint16 ) 1U << 10U ) ) /*<force index event latch interrupt */
#define eQEP_QFRC_SEL \
    ( ( uint16 ) ( ( uint16 ) 1U << 9U ) ) /*<force strobe event latch interrupt */
#define eQEP_QFRC_PCM \
    ( ( uint16 ) ( ( uint16 ) 1U << 8U ) ) /*<force position compare match interrupt */
#define eQEP_QFRC_PCR \
    ( ( uint16 ) ( ( uint16 ) 1U << 7U ) ) /*<force position compare ready interrupt */
#define eQEP_QFRC_PCO                                                                   \
    ( ( uint16 ) ( ( uint16 ) 1U << 6U ) ) /*<force position counter overflow interrupt \
                                            */
#define eQEP_QFRC_PCU                                                                    \
    ( ( uint16 ) ( ( uint16 ) 1U << 5U ) ) /*<force position counter underflow interrupt \
                                            */
#define eQEP_QFRC_WTO \
    ( ( uint16 ) ( ( uint16 ) 1U << 4U ) ) /*<force watchdog time out interrupt */
#define eQEP_QFRC_QDC                                                           \
    ( ( uint16 ) ( ( uint16 ) 1U << 3U ) ) /*<force quadrature direction change \
                                              interrupt        */
#define eQEP_QFRC_QPE \
    ( ( uint16 ) ( ( uint16 ) 1U << 2U ) ) /*<force quadrature phase error interrupt */
#define eQEP_QFRC_PCE \
    ( ( uint16 ) ( ( uint16 ) 1U << 1U ) ) /*<force position counter error interrupt */

/*QEPSTS Register */
#define eQEP_QEPSTS_UPEVNT \
    ( ( uint16 ) ( ( uint16 ) 1U << 7U ) ) /*<unit position event flag */
#define eQEP_QEPSTS_FDF \
    ( ( uint16 ) ( ( uint16 ) 1U << 6U ) ) /*<direction on the first index marker */
#define eQEP_QEPSTS_QDF \
    ( ( uint16 ) ( ( uint16 ) 1U << 5U ) ) /*<quadrature direction flag */
#define eQEP_QEPSTS_QDLF                                           \
    ( ( uint16 ) ( ( uint16 ) 1U << 4U ) ) /*<direction latch flag \
                                            */
#define eQEP_QEPSTS_COEF \
    ( ( uint16 ) ( ( uint16 ) 1U << 3U ) ) /*<capture overflow error flag */
#define eQEP_QEPSTS_CDEF \
    ( ( uint16 ) ( ( uint16 ) 1U << 2U ) ) /*<capture direction error flag */
#define eQEP_QEPSTS_FIMF \
    ( ( uint16 ) ( ( uint16 ) 1U << 1U ) ) /*<first index marker flag */
#define eQEP_QEPSTS_PCEF \
    ( ( uint16 ) ( ( uint16 ) 1U << 0U ) ) /*<position counter error flag */

/*PC mode  */
#define eQEP_QUADRATURE_COUNT         0x00U
#define eQEP_DIRECTION_COUNT          0x01U
#define eQEP_UP_COUNT                 0x02U
#define eQEP_DOWN_COUNT               0x03U

/*External Clock Rate */
#define eQEP_RESOLUTION_2x            0x00U
#define eQEP_RESOLUTION_1x            0x01U

/*Direction */
#define eQEP_CLOCKWISE                0x01U
#define eQEP_COUNTERCLOCKWISE         0x01U

/*Edge */
#define eQEP_RISING_EDGE              0x00U
#define eQEP_FALLING_EDGE             0x01U
#define eQEP_DIRECTON_DEPENDENT       0x01U

/*Index event latch of position counter */
#define eQEP_LATCH_RISING_EDGE        0x01U
#define eQEP_LATCH_FALLING_EDGE       0x02U
#define eQEP_LATCH_SW_INDEX_MARKER    0x03U

/*Position counter reset mode */
#define eQEP_INDEX_EVENT              0x00U
#define eQEP_MAX_POSITION             0x01U
#define eQEP_FIRST_INDEX_EVENT        0x02U
#define eQEP_UNITTIME_EVENT           0x03U

/*eQEP capture timer clock prescaler and Unit position event prescaler */
#define eQEP_PS_1                     0x00U
#define eQEP_PS_2                     0x01U
#define eQEP_PS_4                     0x02U
#define eQEP_PS_8                     0x03U
#define eQEP_PS_16                    0x04U
#define eQEP_PS_32                    0x05U
#define eQEP_PS_64                    0x06U
#define eQEP_PS_128                   0x07U
#define eQEP_PS_256                   0x08U
#define eQEP_PS_512                   0x09U
#define eQEP_PS_1024                  0x0AU
#define eQEP_PS_2048                  0x0BU

/*eQEP capture latch mode */
#define eQEP_ON_POSITION_COUNTER_READ 0x00U
#define eQEP_ON_UNIT_TIMOUT_EVENT     0x01U

/*Sync output pin selection */
#define eQEP_INDEX_PIN                0x00U
#define eQEP_STROBE_PIN               0x01U

/*Position-compare shadow load mode */
#define eQEP_QPOSCNT_EQ_0             0x00U
#define eQEP_QPOSCNT_EQ_QPSCMP        0x01U

/*Polarity of sync output */
#define eQEP_ACTIVE_HIGH              0x00U
#define eQEP_ACTIVE_LOW               0x01U

/***************************************************************************
 * the typedefs
 */
/** @brief QEP counting mode
 */
typedef enum
{
    eQEP_Qsrc_Quad_Count_Mode = ( ( uint16 ) 0U << 14U ), /*<quadrature count mode */
    eQEP_Qsrc_Dir_Count_Mode = ( ( uint16 ) 1U << 14U ),  /*<direction count mode  */
    eQEP_Qsrc_Up_Count_Mode = ( ( uint16 ) 2U << 14U ),   /*<up count mode for frequency
                                                             measurement (QCLK=XCLK,
                                                             QDIR=1U)   */
    eQEP_Qsrc_Down_Count_Mode = ( ( uint16 ) 3U << 14U )  /*<down count mode for frequency
                                                             measurement (QCLK=XCLK,
                                                             QDIR=0U) */
} eQEP_Qsrc_t;

/** @brief Sync output pin selection
 */
typedef enum
{
    eQEP_Spsel_Index_Pin_Sync_Output = ( ( uint16 ) 0U << 12U ), /*<index pin for sync
                                                                    output  */
    eQEP_Spsel_Strobe_Pin_Sync_Output = ( ( uint16 ) 1U << 12U ) /*<strobe pin for sync
                                                                    output */
} eQEP_Spsel_t;

/** @brief External clock rate
 */
typedef enum
{
    eQEP_Xcr_2x_Res = ( ( uint16 ) 0U << 11U ), /*<2x resolution: count the rising/falling
                                                   edge  */
    eQEP_Xcr_1x_Res = ( ( uint16 ) 1U << 11U )  /*<1x resolution: count the rising edge
                                                   only     */
} eQEP_Xcr_t;

/** @brief Swap A/B channels
 */
typedef enum
{
    eQEP_Swap_Not_Swapped = ( ( uint16 ) 0U << 10U ), /*<quad inputs not swapped  */
    eQEP_Swap_Swapped = ( ( uint16 ) 1U << 10U )      /*<quad inputs swapped      */
} eQEP_Swap_t;

/** @brief Index gating
 */
typedef enum
{
    eQEP_Igate_Disable = ( ( uint16 ) 0U << 9U ), /*<disable gating of index pulse  */
    eQEP_Igate_Enable = ( ( uint16 ) 1U << 9U )   /*<enable gating of index pulse   */
} eQEP_Igate_t;

/** @brief Channel A polarity
 */
typedef enum
{
    eQEP_Qap_No_Effect = ( ( uint16 ) 0U << 8U ), /*<no effect           */
    eQEP_Qap_Inverted = ( ( uint16 ) 1U << 8U )   /*<negates QEPA input  */
} eQEP_Qap_t;

/** @brief Channel B polarity
 */
typedef enum
{
    eQEP_Qbp_No_Effect = ( ( uint16 ) 0U << 7U ), /*<no effect           */
    eQEP_Qbp_Inverted = ( ( uint16 ) 1U << 7U )   /*<negates QEPB input  */
} eQEP_Qbp_t;

/** @brief Index polarity
 */
typedef enum
{
    eQEP_Qip_No_Effect = ( ( uint16 ) 0U << 6U ), /*<no effect          */
    eQEP_Qip_Inverted = ( ( uint16 ) 1U << 6U )   /*<negates QEPI input */
} eQEP_Qip_t;

/** @brief Channel S polarity
 */
typedef enum
{
    eQEP_Qsp_No_Effect = ( ( uint16 ) 0U << 5U ), /*<no effect*/
    eQEP_Qsp_Inverted = ( ( uint16 ) 1U << 5U )   /*<negates QEPS input */
} eQEP_Qsp_t;

/** @brief Emulation control bits
 */
typedef enum
{
    QEPCTL_Freesoft_Immediate_Halt = ( ( uint16 ) 0U << 14U ), /*<position, watchdog, unit
                                                                  timer, capture timer
                                                                  stops immediately */
    QEPCTL_Freesoft_Rollover_Halt = ( ( uint16 ) 1U << 14U ),  /*<position, watchdog, unit
                                                                  timer  continues until
                                                                  rollover, capture  counts
                                                                  until next unit period
                                                                  event  */
    QEPCTL_Freesoft_Unaffected_Halt = ( ( uint16 ) 2U << 14U ) /*<position, watchdog, unit
                                                                  timer, capture timer
                                                                  unaffected by emu
                                                                  suspend */
} QEPCTL_Freesoft_t;

/** @brief Position counter reset mode
 */
typedef enum
{
    QEPCTL_Pcrm_Index_Reset = ( ( uint16 ) 0U << 12U ), /*<position counter reset on index
                                                           event      */
    QEPCTL_Pcrm_Max_Reset = ( ( uint16 ) 1U << 12U ),   /*<position counter reset on max
                                                           position     */
    QEPCTL_Pcrm_First_Index_Reset = ( ( uint16 ) 2U << 12U ), /*<position counter reset on
                                                                 first index event*/
    QEPCTL_Pcrm_Unit_Time_Reset = ( ( uint16 ) 3U << 12U )    /*<position counter reset on
                                                                 unit time event  */
} QEPCTL_Pcrm_t;

/** @brief Strobe event initialization of position counter
 */
typedef enum
{
    QEPCTL_Sei_Nothing = ( ( uint16 ) 0U << 10U ),          /*<does nothing          */
    QEPCTL_Sei_Rising_Edge_Init = ( ( uint16 ) 2U << 10U ), /*<initializes on rising edge
                                                               of QEPS signal          */
    QEPCTL_Sei_Rising_Falling_Edge_Init = ( ( uint16 ) 3U << 10U ) /*<initializes on
                                                                      rising/falling edge
                                                                      of QEPS signal  */
} QEPCTL_Sei_t;

/** @brief Index event initialization of position counter
 */
typedef enum
{
    QEPCTL_Iei_Nothing = ( ( uint16 ) 0U << 8U ),          /*<does nothing          */
    QEPCTL_Iei_Rising_Edge_Init = ( ( uint16 ) 2U << 8U ), /*<initializes on rising edge
                                                              of QEPI signal  */
    QEPCTL_Iei_Rising_Falling_Edge_Init = ( ( uint16 ) 3U << 8U ) /*<initializes on
                                                                     falling edge of QEPI
                                                                     signal */
} QEPCTL_Iei_t;

/** @brief Software initialization of position counter
 */
typedef enum
{
    QEPCTL_Swi_Nothing = ( ( uint16 ) 0U << 7U ),          /*<does nothing          */
    QEPCTL_Swi_Auto_Init_Counter = ( ( uint16 ) 1U << 7U ) /*<init position counter
                                                              (QPOSCNT=QPOSINIT) */
} QEPCTL_Swi_t;

/** @brief Strobe event latch of position counter
 */
typedef enum
{
    QEPCTL_Sel_Rising_Edge = ( ( uint16 ) 0U << 6U ), /*<Position counter latched on
                                                         rising edge of QEPS strobe
                                                         (QPOSSLAT = POSCCNT) */
    QEPCTL_Sel_Rising_Falling_Edge = ( ( uint16 ) 1U << 6U ) /*<Clockwise: position
                                                                counter latched on rising
                                                                edge, counter clockwise:
                                                                latched on falling edge */
} QEPCTL_Sel_t;

/** @brief Index event latch of position counter (software index marker)
 */
typedef enum
{
    QEPCTL_Iel_Rising_Edge = ( ( uint16 ) 1U << 4U ),  /*<latches position counter on
                                                          rising edge of index signal  */
    QEPCTL_Iel_Falling_Edge = ( ( uint16 ) 2U << 4U ), /*<ditto on falling edge of index
                                                          signal                    */
    QEPCTL_Iel_Software_Index_Marker = ( ( uint16 ) 3U << 4U ) /*<software index marker.
                                                                  See data sheet. */
} QEPCTL_Iel_t;

/** @brief QEP capture latch mode
 */
typedef enum
{
    QEPCTL_Qclm_Latch_on_CPU_Read = ( ( uint16 ) 0U << 2U ), /*<latch on position counter
                                                                read by cpu  */
    QEPCTL_Qclm_Latch_on_Unit_Timeout = ( ( uint16 ) 1U << 2U ) /*<latch on unit time out
                                                                 */
} QEPCTL_Qclm_t;

/** @brief Position compare shadow enable
 */
typedef enum
{
    QPOSCTL_Pcshdw_Load_Immediate = ( ( uint16 ) 0U << 15U ), /*<shadow disabled, load
                                                                 immediate */
    QPOSCTL_Pcshdw_Shadow_Enabled = ( ( uint16 ) 1U << 15U )  /*<shadow enabled  */
} QPOSCTL_Pcshdw_t;

/** @brief Position compare shadow load mode
 */
typedef enum
{
    QPOSCTL_Pcload_Load_Posn_Count_Zero = ( ( uint16 ) 0U << 14U ), /*<load on qposcnt = 0
                                                                     */
    QPOSCTL_Pcload_Load_Posn_Count_Equal_Compare = ( ( uint16 ) 1U << 14U ) /*<load when
                                                                               qposcnt =
                                                                               qposcmp  */
} QPOSCTL_Pcload_t;

/** @brief Polarity of sync output
 */
typedef enum
{
    QPOSCTL_Pcpol_Active_High = ( ( uint16 ) 0U << 13U ), /*<active high pulse output  */
    QPOSCTL_Pcpol_Active_Low = ( ( uint16 ) 1U << 13U )   /*<active low pulse output   */
} QPOSCTL_Pcpol_t;

/** @brief QEP capture timer clock prescaler
 */
typedef enum
{
    QCAPCTL_Ccps_Capture_Div_1 = ( ( uint16 ) 0U << 4U ),  /*<capclk = sysclkout/1   */
    QCAPCTL_Ccps_Capture_Div_2 = ( ( uint16 ) 1U << 4U ),  /*<capclk = sysclkout/2   */
    QCAPCTL_Ccps_Capture_Div_4 = ( ( uint16 ) 2U << 4U ),  /*<capclk = sysclkout/4   */
    QCAPCTL_Ccps_Capture_Div_8 = ( ( uint16 ) 3U << 4U ),  /*<capclk = sysclkout/8   */
    QCAPCTL_Ccps_Capture_Div_16 = ( ( uint16 ) 4U << 4U ), /*<capclk = sysclkout/16  */
    QCAPCTL_Ccps_Capture_Div_32 = ( ( uint16 ) 5U << 4U ), /*<capclk = sysclkout/32  */
    QCAPCTL_Ccps_Capture_Div_64 = ( ( uint16 ) 6U << 4U ), /*<capclk = sysclkout/64  */
    QCAPCTL_Ccps_Capture_Div_128 = ( ( uint16 ) 7U << 4U ) /*<capclk = sysclkout/128 */
} QCAPCTL_Ccps_t;

/** @brief Unit position event prescaler
 */
typedef enum
{
    QCAPCTL_Upps_Div_1_Prescale = ( ( uint16 ) 0U << 0U ),     /*<upevnt = qclk/1    */
    QCAPCTL_Upps_Div_2_Prescale = ( ( uint16 ) 1U << 0U ),     /*<upevnt = qclk/2    */
    QCAPCTL_Upps_Div_4_Prescale = ( ( uint16 ) 2U << 0U ),     /*<upevnt = qclk/4    */
    QCAPCTL_Upps_Div_8_Prescale = ( ( uint16 ) 3U << 0U ),     /*<upevnt = qclk/8    */
    QCAPCTL_Upps_Div_16_Prescale = ( ( uint16 ) 4U << 0U ),    /*<upevnt = qclk/16   */
    QCAPCTL_Upps_Div_32_Prescale = ( ( uint16 ) 5U << 0U ),    /*<upevnt = qclk/32   */
    QCAPCTL_Upps_Div_64_Prescale = ( ( uint16 ) 6U << 0U ),    /*<upevnt = qclk/64   */
    QCAPCTL_Upps_Div_128_Prescale = ( ( uint16 ) 7U << 0U ),   /*<upevnt = qclk/128  */
    QCAPCTL_Upps_Div_256_Prescale = ( ( uint16 ) 8U << 0U ),   /*<upevnt = qclk/256  */
    QCAPCTL_Upps_Div_512_Prescale = ( ( uint16 ) 9U << 0U ),   /*<upevnt = qclk/512  */
    QCAPCTL_Upps_Div_1024_Prescale = ( ( uint16 ) 10U << 0U ), /*<upevnt = qclk/1024 */
    QCAPCTL_Upps_Div_2048_Prescale = ( ( uint16 ) 11U << 0U )  /*<upevnt = qclk/2048 */
} QCAPCTL_Upps_t;

/** @brief QEP interrupt enable flags
 */
typedef enum
{
    QEINT_Uto = ( ( uint16 ) 1U << 11U ), /*<unit time out interrupt enable */
    QEINT_Iel = ( ( uint16 ) 1U << 10U ), /*<index event latch interrupt enable */
    QEINT_Sel = ( ( uint16 ) 1U << 9U ),  /*<strobe event latch interrupt enable  */
    QEINT_Pcm = ( ( uint16 ) 1U << 8U ),  /*<position compare match interrupt enable  */
    QEINT_Pcr = ( ( uint16 ) 1U << 7U ),  /*<position compare ready interrupt enable  */
    QEINT_Pco = ( ( uint16 ) 1U << 6U ), /*<position compare overflow interrupt enable  */
    QEINT_Pcu = ( ( uint16 ) 1U << 5U ), /*<position compare underflow interrupt enable */
    QEINT_Wto = ( ( uint16 ) 1U << 4U ), /*<position compare watchdog time out interrupt
                                            enable */
    QEINT_Qdc = ( ( uint16 ) 1U << 3U ), /*<quadrature direction change interrupt enable
                                          */
    QEINT_Qpe = ( ( uint16 ) 1U << 2U ), /*<quadrature phase error interrupt enable */
    QEINT_Pce = ( ( uint16 ) 1U << 1U )  /*<position counter interrupt enable  */
} QEINT_t;

/* Configuration registers */
typedef struct eqep_config_reg
{
    uint32 CONFIG_QPOSINIT;
    uint32 CONFIG_QPOSMAX;
    uint32 CONFIG_QPOSCMP;
    uint32 CONFIG_QUPRD;
    uint16 CONFIG_QWDPRD;
    uint16 CONFIG_QDECCTL;
    uint16 CONFIG_QEPCTL;
    uint16 CONFIG_QCAPCTL;
    uint16 CONFIG_QPOSCTL;
    uint16 CONFIG_QEINT;
} eqep_config_reg_t;

#define EQEP1_QPOSINIT_CONFIGVALUE ( ( uint32 ) 0x00000000U )
#define EQEP1_QPOSMAX_CONFIGVALUE  ( ( uint32 ) 0x00000000U )
#define EQEP1_QPOSCMP_CONFIGVALUE  ( ( uint32 ) 0x00000000U )
#define EQEP1_QUPRD_CONFIGVALUE    ( ( uint32 ) 0x00000000U )
#define EQEP1_QWDPRD_CONFIGVALUE   ( ( uint16 ) 0x0000U )
#define EQEP1_QDECCTL_CONFIGVALUE                                        \
    ( ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_DIRECTION_COUNT << 14U ) \
                   | ( uint16 ) ( ( uint16 ) 0U << 13U )                 \
                   | ( uint16 ) ( ( uint16 ) eQEP_INDEX_PIN << 12U )     \
                   | ( uint16 ) ( ( uint16 ) eQEP_RESOLUTION_1x << 11U ) \
                   | ( uint16 ) ( ( uint16 ) 0U << 10U )                 \
                   | ( uint16 ) ( ( uint16 ) 0U << 9U )                  \
                   | ( uint16 ) ( ( uint16 ) 0U << 8U )                  \
                   | ( uint16 ) ( ( uint16 ) 0U << 7U )                  \
                   | ( uint16 ) ( ( uint16 ) 0U << 6U )                  \
                   | ( uint16 ) ( ( uint16 ) 0U << 5U ) | ( uint16 ) 0x0000U ) )

#define EQEP1_QEPCTL_CONFIGVALUE                                                   \
    ( ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_MAX_POSITION << 12U )              \
                   | ( uint16 ) ( ( uint16 ) 0U << 11U )                           \
                   | ( uint16 ) ( ( uint16 ) eQEP_DIRECTON_DEPENDENT << 10U )      \
                   | ( uint16 ) ( ( uint16 ) 0U << 9U )                            \
                   | ( uint16 ) ( ( uint16 ) eQEP_RISING_EDGE << 8U )              \
                   | ( uint16 ) ( ( uint16 ) 0U << 7U )                            \
                   | ( uint16 ) ( ( uint16 ) eQEP_RISING_EDGE << 6U )              \
                   | ( uint16 ) ( ( uint16 ) eQEP_LATCH_RISING_EDGE << 4U )        \
                   | ( uint16 ) ( ( uint16 ) eQEP_ON_POSITION_COUNTER_READ << 2U ) \
                   | ( uint16 ) 0x0000U ) )

#define EQEP1_QCAPCTL_CONFIGVALUE                            \
    ( ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_PS_8 << 4U ) \
                   | ( uint16 ) ( ( uint16 ) eQEP_PS_512 ) | ( uint16 ) 0x0000U ) )

#define EQEP1_QPOSCTL_CONFIGVALUE                                            \
    ( ( uint16 ) ( ( uint16 ) ( ( uint16 ) 0U << 15U )                       \
                   | ( uint16 ) ( ( uint16 ) eQEP_QPOSCNT_EQ_QPSCMP << 14U ) \
                   | ( uint16 ) ( ( uint16 ) eQEP_ACTIVE_HIGH << 13U )       \
                   | ( uint16 ) ( ( uint16 ) 0x000U ) | ( uint16 ) 0x0000U ) )

#define EQEP1_QEINT_CONFIGVALUE                          \
    ( ( uint16 ) ( ( uint16 ) ( ( uint16 ) 0U << 11U )   \
                   | ( uint16 ) ( ( uint16 ) 0U << 10U ) \
                   | ( uint16 ) ( ( uint16 ) 0U << 9U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 8U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 7U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 6U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 5U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 4U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 3U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 2U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 1U ) ) )
#define EQEP2_QPOSINIT_CONFIGVALUE ( ( uint32 ) 0x00000000U )
#define EQEP2_QPOSMAX_CONFIGVALUE  ( ( uint32 ) 0x00000000U )
#define EQEP2_QPOSCMP_CONFIGVALUE  ( ( uint32 ) 0U )
#define EQEP2_QUPRD_CONFIGVALUE    ( ( uint32 ) 0U )
#define EQEP2_QWDPRD_CONFIGVALUE   ( ( uint16 ) 0U )
#define EQEP2_QDECCTL_CONFIGVALUE                                        \
    ( ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_DIRECTION_COUNT << 14U ) \
                   | ( uint16 ) ( ( uint16 ) 0U << 13U )                 \
                   | ( uint16 ) ( ( uint16 ) eQEP_INDEX_PIN << 12U )     \
                   | ( uint16 ) ( ( uint16 ) eQEP_RESOLUTION_1x << 11U ) \
                   | ( uint16 ) ( ( uint16 ) 0U << 10U )                 \
                   | ( uint16 ) ( ( uint16 ) 0U << 9U )                  \
                   | ( uint16 ) ( ( uint16 ) 0U << 8U )                  \
                   | ( uint16 ) ( ( uint16 ) 0U << 7U )                  \
                   | ( uint16 ) ( ( uint16 ) 0U << 6U )                  \
                   | ( uint16 ) ( ( uint16 ) 0U << 5U ) | ( uint16 ) 0x0000U ) )

#define EQEP2_QEPCTL_CONFIGVALUE                                                   \
    ( ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_MAX_POSITION << 12U )              \
                   | ( uint16 ) ( ( uint16 ) 0U << 11U )                           \
                   | ( uint16 ) ( ( uint16 ) eQEP_DIRECTON_DEPENDENT << 10U )      \
                   | ( uint16 ) ( ( uint16 ) 0U << 9U )                            \
                   | ( uint16 ) ( ( uint16 ) eQEP_RISING_EDGE << 8U )              \
                   | ( uint16 ) ( ( uint16 ) 0U << 7U )                            \
                   | ( uint16 ) ( ( uint16 ) eQEP_RISING_EDGE << 6U )              \
                   | ( uint16 ) ( ( uint16 ) eQEP_LATCH_RISING_EDGE << 4U )        \
                   | ( uint16 ) ( ( uint16 ) eQEP_ON_POSITION_COUNTER_READ << 2U ) \
                   | ( uint16 ) 0x0000U ) )

#define EQEP2_QCAPCTL_CONFIGVALUE                            \
    ( ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_PS_8 << 4U ) \
                   | ( ( uint16 ) eQEP_PS_512 ) | ( uint16 ) 0x0000U ) )

#define EQEP2_QPOSCTL_CONFIGVALUE                                            \
    ( ( uint16 ) ( ( uint16 ) ( ( uint16 ) 0U << 15U )                       \
                   | ( uint16 ) ( ( uint16 ) eQEP_QPOSCNT_EQ_QPSCMP << 14U ) \
                   | ( uint16 ) ( ( uint16 ) eQEP_ACTIVE_HIGH << 13U )       \
                   | ( uint16 ) ( ( uint16 ) 0U ) | ( uint16 ) 0x0000U ) )

#define EQEP2_QEINT_CONFIGVALUE                          \
    ( ( uint16 ) ( ( uint16 ) ( ( uint16 ) 0U << 11U )   \
                   | ( uint16 ) ( ( uint16 ) 0U << 10U ) \
                   | ( uint16 ) ( ( uint16 ) 0U << 9U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 8U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 7U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 6U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 5U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 4U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 3U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 2U )  \
                   | ( uint16 ) ( ( uint16 ) 0U << 1U ) ) )

/**
 *  @defgroup eQEP eQEP
 *  @brief Enhanced QEP Module.
 *
 *  The enhanced quadrature encoder pulse (eQEP) module is used for direct interface with
 *a linear or rotary incremental encoder to get position, direction, and speed information
 *from a rotating machine for use in a high-performance motion and position-control
 *system. This microcontroller implements 2 instances of the eQEP module.
 *
 *	Related Files
 *   - reg_eqep.h
 *   - eqep.h
 *   - eqep.c
 *  @addtogroup eQEP
 *  @{
 */

/***************************************************************************
 *the function prototypes
 */

void QEPInit( void );

void eqepClearAllInterruptFlags( eqepBASE_t * eqep );

void eqepClearInterruptFlag( eqepBASE_t * eqep, QEINT_t QEINT_type );

void eqepClearPosnCounter( eqepBASE_t * eqep );

void eqepDisableAllInterrupts( eqepBASE_t * eqep );

void eqepDisableCapture( eqepBASE_t * eqep );

void eqepDisableGateIndex( eqepBASE_t * eqep );

void eqepDisableInterrupt( eqepBASE_t * eqep, QEINT_t QEINT_type );

void eqepDisablePosnCompare( eqepBASE_t * eqep );

void eqepDisablePosnCompareShadow( eqepBASE_t * eqep );

void eqepDisableSyncOut( eqepBASE_t * eqep );

void eqepDisableUnitTimer( eqepBASE_t * eqep );

void eqepDisableWatchdog( eqepBASE_t * eqep );

void eqepEnableCapture( eqepBASE_t * eqep );

void eqepEnableCounter( eqepBASE_t * eqep );

void eqepEnableGateIndex( eqepBASE_t * eqep );

void eqepEnableInterrupt( eqepBASE_t * eqep, QEINT_t QEINT_type );

void eqepEnablePosnCompare( eqepBASE_t * eqep );

void eqepEnablePosnCompareShadow( eqepBASE_t * eqep );

void eqepEnableSyncOut( eqepBASE_t * eqep );

void eqepEnableUnitTimer( eqepBASE_t * eqep );

void eqepEnableWatchdog( eqepBASE_t * eqep );

void eqepForceInterrupt( eqepBASE_t * eqep, QEINT_t QEINT_type );

uint16 eqepReadCapturePeriodLatch( eqepBASE_t * eqep );

uint16 eqepReadCaptureTimerLatch( eqepBASE_t * eqep );

uint16 eqepReadInterruptFlag( eqepBASE_t * eqep, QEINT_t QEINT_type );

uint32 eqepReadPosnCompare( eqepBASE_t * eqep );

uint32 eqepReadPosnCount( eqepBASE_t * eqep );

uint32 eqepReadPosnIndexLatch( eqepBASE_t * eqep );

uint32 eqepReadPosnLatch( eqepBASE_t * eqep );

uint32 eqepReadPosnStrobeLatch( eqepBASE_t * eqep );

uint16 eqepReadStatus( eqepBASE_t * eqep );

void eqepResetCounter( eqepBASE_t * eqep );

void eqepSetCaptureLatchMode( eqepBASE_t * eqep, QEPCTL_Qclm_t QEPCTL_Qclm );

void eqepSetCapturePeriod( eqepBASE_t * eqep, uint16 period );

void eqepSetCapturePrescale( eqepBASE_t * eqep, QCAPCTL_Ccps_t QCAPCTL_Ccps );

void eqepSetEmuControl( eqepBASE_t * eqep, QEPCTL_Freesoft_t QEPCTL_Freesoft );

void eqepSetExtClockRate( eqepBASE_t * eqep, eQEP_Xcr_t eQEP_Xcr );

void eqepSetIndexEventInit( eqepBASE_t * eqep, QEPCTL_Iei_t QEPCTL_Iei );

void eqepSetIndexEventLatch( eqepBASE_t * eqep, QEPCTL_Iel_t QEPCTL_Iel );

void eqepSetIndexPolarity( eqepBASE_t * eqep, eQEP_Qip_t eQEP_Qip );

void eqepSetMaxPosnCount( eqepBASE_t * eqep, uint32 max_count );

void eqepSetPosnComparePulseWidth( eqepBASE_t * eqep, uint16 pulse_width );

void eqepSetPosnCompareShadowLoad( eqepBASE_t * eqep, QPOSCTL_Pcload_t QPOSCTL_Pcload );

void eqepSetPosnCountResetMode( eqepBASE_t * eqep, QEPCTL_Pcrm_t QEPCTL_Pcrm );

void eqepSetPosnInitCount( eqepBASE_t * eqep, uint32 init_count );

void eqepSetSelectSyncPin( eqepBASE_t * eqep, eQEP_Spsel_t eQEP_SPsel );

void eqepSetSoftInit( eqepBASE_t * eqep, QEPCTL_Swi_t QEPCTL_Swi );

void eqepSetStrobeEventInit( eqepBASE_t * eqep, QEPCTL_Sei_t QEPCTL_Sei );

void eqepSetStrobeEventLatch( eqepBASE_t * eqep, QEPCTL_Sel_t QEPCTL_Sel );

void eqepSetStrobePolarity( eqepBASE_t * eqep, eQEP_Qsp_t eQEP_Qsp );

void eqepSetSwapQuadInputs( eqepBASE_t * eqep, eQEP_Swap_t eQEP_Swap );

void eqepSetSynchOutputComparePolarity( eqepBASE_t * eqep,
                                        QPOSCTL_Pcpol_t QPOSCTL_Pcpol );

void eqepSetUnitPeriod( eqepBASE_t * eqep, uint32 unit_period );

void eqepSetUnitPosnPrescale( eqepBASE_t * eqep, QCAPCTL_Upps_t QCAPCTL_Upps );

void eqepSetWatchdogPeriod( eqepBASE_t * eqep, uint16 watchdog_period );

void eqepSetupStrobeEventLatch( eqepBASE_t * eqep, QEPCTL_Sel_t QEPCTL_Sel );

void eqepSetAPolarity( eqepBASE_t * eqep, eQEP_Qap_t eQEP_Qap );

void eqepSetBPolarity( eqepBASE_t * eqep, eQEP_Qbp_t eQEP_Qbp );

void eqepSetQEPSource( eqepBASE_t * eqep, eQEP_Qsrc_t eQEP_Qsrc );

void eqepWritePosnCompare( eqepBASE_t * eqep, uint32 posn );

/** @brief Interrupt callback
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] flags			Copy of  interrupt flags
 */
void eqepNotification( eqepBASE_t * eqep, uint16 flags );

void eqep1GetConfigValue( eqep_config_reg_t * config_reg, config_value_type_t type );
void eqep2GetConfigValue( eqep_config_reg_t * config_reg, config_value_type_t type );

/**@}*/
#ifdef __cplusplus
}
#endif /*extern "C" */

#endif /*end of _eQEP_H_ definition */
