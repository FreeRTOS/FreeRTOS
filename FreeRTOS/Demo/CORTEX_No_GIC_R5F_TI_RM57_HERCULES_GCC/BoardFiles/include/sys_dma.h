/** @file sys_dma.h
 *   @brief DMA Driver Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the DMA driver.
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

#ifndef DMA_H_
#define DMA_H_

#include "reg_dma.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

typedef enum dmaChannel
{
    DMA_CH0 = 0U,
    DMA_CH1,
    DMA_CH2,
    DMA_CH3,
    DMA_CH4,
    DMA_CH5,
    DMA_CH6,
    DMA_CH7,
    DMA_CH8,
    DMA_CH9,
    DMA_CH10,
    DMA_CH11,
    DMA_CH12,
    DMA_CH13,
    DMA_CH14,
    DMA_CH15,
    DMA_CH16,
    DMA_CH17,
    DMA_CH18,
    DMA_CH19,
    DMA_CH20,
    DMA_CH21,
    DMA_CH22,
    DMA_CH23,
    DMA_CH24,
    DMA_CH25,
    DMA_CH26,
    DMA_CH27,
    DMA_CH28,
    DMA_CH29,
    DMA_CH30,
    DMA_CH31
} dmaChannel_t;

typedef enum dmaRequest
{
    DMA_REQ0 = 0U,
    DMA_REQ1,
    DMA_REQ2,
    DMA_REQ3,
    DMA_REQ4,
    DMA_REQ5,
    DMA_REQ6,
    DMA_REQ7,
    DMA_REQ8,
    DMA_REQ9,
    DMA_REQ10,
    DMA_REQ11,
    DMA_REQ12,
    DMA_REQ13,
    DMA_REQ14,
    DMA_REQ15,
    DMA_REQ16,
    DMA_REQ17,
    DMA_REQ18,
    DMA_REQ19,
    DMA_REQ20,
    DMA_REQ21,
    DMA_REQ22,
    DMA_REQ23,
    DMA_REQ24,
    DMA_REQ25,
    DMA_REQ26,
    DMA_REQ27,
    DMA_REQ28,
    DMA_REQ29,
    DMA_REQ30,
    DMA_REQ31,
    DMA_REQ32,
    DMA_REQ33,
    DMA_REQ34,
    DMA_REQ35,
    DMA_REQ36,
    DMA_REQ37,
    DMA_REQ38,
    DMA_REQ39,
    DMA_REQ40,
    DMA_REQ41,
    DMA_REQ42,
    DMA_REQ43,
    DMA_REQ44,
    DMA_REQ45,
    DMA_REQ46,
    DMA_REQ47
} dmaRequest_t;

typedef enum dmaTriggerType
{
    DMA_HW,
    DMA_SW
} dmaTriggerType_t;

typedef enum dmaPriorityQueue
{
    LOWPRIORITY,
    HIGHPRIORITY
} dmaPriorityQueue_t;

typedef enum dmaInterrupt
{
    FTC, /**<  Frame transfer complete Interrupt      */
    LFS, /**<  Last frame transfer started Interrupt  */
    HBC, /**<  First half of block complete Interrupt */
    BTC  /**<  Block transfer complete Interrupt      */
} dmaInterrupt_t;

typedef enum dmaIntGroup
{
    DMA_INTA = 0U, /**< Group A Interrupt                                   */
    DMA_INTB = 1U  /**< Group B Interrupt  (Reserved for Lock-step devices) */
} dmaIntGroup_t;

typedef enum dmaMPURegion
{
    DMA_REGION0 = 0U,
    DMA_REGION1 = 1U,
    DMA_REGION2 = 2U,
    DMA_REGION3 = 3U,
    DMA_REGION4 = 4U,
    DMA_REGION5 = 5U,
    DMA_REGION6 = 6U,
    DMA_REGION7 = 7U
} dmaMPURegion_t;

typedef enum dmaRegionAccess
{
    FULLACCESS = 0U,
    READONLY = 1U,
    WRITEONLY = 2U,
    NOACCESS = 3U
} dmaRegionAccess_t;

typedef enum dmaMPUInt
{
    INTERRUPT_DISABLE = 0U,
    INTERRUPTA_ENABLE = 1U,
    INTERRUPTB_ENABLE = 3U
} dmaMPUInt_t;

enum dmaPort
{
    PORTB_READ_PORTB_WRITE = 0x3U,
    PORTA_READ_PORTA_WRITE = 0x2U,
    PORTA_READ_PORTB_WRITE = 0x1U,
    PORTB_READ_PORTA_WRITE = 0x0U
};

enum dmaElementSize
{
    ACCESS_8_BIT = 0U,
    ACCESS_16_BIT = 1U,
    ACCESS_32_BIT = 2U,
    ACCESS_64_BIT = 3U
};

enum dmaTransferType
{
    FRAME_TRANSFER = 0U,
    BLOCK_TRANSFER = 1U
};

enum dmaAddressMode
{
    ADDR_FIXED = 0U,
    ADDR_INC1 = 1U,
    ADDR_OFFSET = 3U
};

enum dmaAutoInitMode
{
    AUTOINIT_OFF = 0U,
    AUTOINIT_ON = 1U
};

typedef struct dmaCTRLPKT
{
    uint32 SADD;      /* Initial source address           */
    uint32 DADD;      /* Initial destination address      */
    uint32 CHCTRL;    /* Next channel to be triggered + 1 */
    uint32 FRCNT;     /* Frame   count                    */
    uint32 ELCNT;     /* Element count                    */
    uint32 ELDOFFSET; /* Element destination offset       */
    uint32 ELSOFFSET; /* Element source offset            */
    uint32 FRDOFFSET; /* Frame destination offset         */
    uint32 FRSOFFSET; /* Frame source offset              */
    uint32 PORTASGN;  /* DMA port                         */
    uint32 RDSIZE;    /* Read element size                */
    uint32 WRSIZE;    /* Write element size               */
    uint32 TTYPE;     /* Trigger type - frame/block       */
    uint32 ADDMODERD; /* Addressing mode for source       */
    uint32 ADDMODEWR; /* Addressing mode for destination  */
    uint32 AUTOINIT;  /* Auto-init mode                   */
} g_dmaCTRL;

void dmaEnable( void );
void dmaDisable( void );
void dmaSetCtrlPacket( dmaChannel_t channel, g_dmaCTRL g_dmaCTRLPKT );
void dmaSetChEnable( dmaChannel_t channel, dmaTriggerType_t type );
void dmaReqAssign( dmaChannel_t channel, dmaRequest_t reqline );
void dmaSetPriority( dmaChannel_t channel, dmaPriorityQueue_t priority );
void dmaEnableInterrupt( dmaChannel_t channel,
                         dmaInterrupt_t inttype,
                         dmaIntGroup_t group );
void dmaDisableInterrupt( dmaChannel_t channel, dmaInterrupt_t inttype );
void dmaDefineRegion( dmaMPURegion_t region, uint32 start_add, uint32 end_add );
void dmaEnableRegion( dmaMPURegion_t region,
                      dmaRegionAccess_t access,
                      dmaMPUInt_t intenable );
void dmaDisableRegion( dmaMPURegion_t region );
void dmaEnableECC( void );
void dmaDisableECC( void );

uint32 dmaGetReq( dmaChannel_t channel );
boolean dmaIsBusy( void );
boolean dmaIsChannelActive( dmaChannel_t channel );
boolean dmaGetInterruptStatus( dmaChannel_t channel, dmaInterrupt_t inttype );

/** @fn void dmaGroupANotification(dmaInterrupt_t inttype, uint32 channel)
 *   @brief Interrupt callback
 *   @param[in] inttype  Interrupt type
 *                        - FTC
 *                        - LFS
 *                        - HBC
 *                        - BTC
 *   @param[in] channel  channel number 0..15
 * This is a callback that is provided by the application and is called apon
 * an interrupt.  The parameter passed to the callback is a copy of the
 * interrupt flag register.
 */
void dmaGroupANotification( dmaInterrupt_t inttype, uint32 channel );

/* USER CODE BEGIN (1) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif /*extern "C" */

#endif /* DMA_H_ */
