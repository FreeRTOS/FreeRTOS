/** @file dma.h
 *   @brief DMA Driver Definition File
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

#ifndef __DMA_H__
#define __DMA_H__

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "reg_dma.h"

#ifdef __cplusplus
extern "C" {
#endif
/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @def BLOCK_TRANSFER
 *   @brief Alias name for DMA Block transfer
 *   @note This value should be used while setting the DMA control packet
 */
#define BLOCK_TRANSFER    1U

/** @def FRAME_TRANSFER
 *   @brief Alias name for DMA Frame transfer
 *   @note This value should be used while setting the DMA control packet
 */
#define FRAME_TRANSFER    0U

/** @def AUTOINIT_ON
 *   @brief Alias name for Auto Initialization ON
 *   @note This value should be used while setting the DMA control packet
 */
#define AUTOINIT_ON       1U

/** @def AUTOINIT_OFF
 *   @brief Alias name for Auto Initialization OFF
 *   @note This value should be used while setting the DMA control packet
 */
#define AUTOINIT_OFF      0U

/** @def ADDR_FIXED
 *   @brief Alias name for Fixed Addressing mode
 *   @note This value should be used while setting the DMA control packet
 */
#define ADDR_FIXED        0U

/** @def ADDR_INC1
 *   @brief Alias name for Post-increment Addressing mode
 *   @note This value should be used while setting the DMA control packet
 */
#define ADDR_INC1         1U

/** @def ADDR_OFFSET
 *   @brief Alias name for Offset Addressing mode
 *   @note This value should be used while setting the DMA control packet
 */
#define ADDR_OFFSET       3U

/** @def INTERRUPT_ENABLE
 *   @brief Alias name for Interrupt enable
 *   @note @note This value should be used for API argument @a intenable
 */
#define INTERRUPT_ENABLE  1U

/** @def INTERRUPT_DISABLE
 *   @brief Alias name for Interrupt disable
 *   @note @note This value should be used for API argument @a intenable
 */
#define INTERRUPT_DISABLE 0U

/** @def DMA_GCTRL_BUSBUSY
 *   @brief Bit mask for BUS BUSY in GCTRL Register
 *   @note @note This value should be used for API argument @a intenable
 */
#define DMA_GCTRL_BUSBUSY ( 0x00004000U )

/** @enum dmaREQTYPE
 *   @brief DMA TRANSFER Type definitions
 *
 *   Used to define DMA transfer type
 */
enum dmaREQTYPE
{
    DMA_HW = 0x0U, /**<  Hardware trigger  */
    DMA_SW = 0x1U  /**<  Software trigger  */
};

/** @enum dmaCHANNEL
 *   @brief DMA CHANNEL definitions
 *
 *   Used to define DMA Channel Number
 */
enum dmaCHANNEL
{
    DMA_CH0 = 0x00U,
    DMA_CH1 = 0x01U,
    DMA_CH2 = 0x02U,
    DMA_CH3 = 0x03U,
    DMA_CH4 = 0x04U,
    DMA_CH5 = 0x05U,
    DMA_CH6 = 0x06U,
    DMA_CH7 = 0x07U,
    DMA_CH8 = 0x08U,
    DMA_CH9 = 0x09U,
    DMA_CH10 = 0x0AU,
    DMA_CH11 = 0x0BU,
    DMA_CH12 = 0x0CU,
    DMA_CH13 = 0x0DU,
    DMA_CH14 = 0x0EU,
    DMA_CH15 = 0x0FU,
    DMA_CH16 = 0x10U,
    DMA_CH17 = 0x11U,
    DMA_CH18 = 0x12U,
    DMA_CH19 = 0x13U,
    DMA_CH20 = 0x14U,
    DMA_CH21 = 0x15U,
    DMA_CH22 = 0x16U,
    DMA_CH23 = 0x17U,
    DMA_CH24 = 0x18U,
    DMA_CH25 = 0x19U,
    DMA_CH26 = 0x1AU,
    DMA_CH27 = 0x1BU,
    DMA_CH28 = 0x1CU,
    DMA_CH29 = 0x1DU,
    DMA_CH30 = 0x1EU,
    DMA_CH31 = 0x1FU
};

/** @enum dmaACCESS
 *   @brief DMA ACESS WIDTH definitions
 *
 *   Used to define DMA access width
 */
typedef enum dmaACCESS
{
    ACCESS_8_BIT = 0U,
    ACCESS_16_BIT = 1U,
    ACCESS_32_BIT = 2U,
    ACCESS_64_BIT = 3U
} dmaACCESS_t;

/** @enum dmaPRIORITY
 *   @brief DMA Channel Priority
 *
 *   Used to define to which priority queue a DMA channel is assigned to
 */
typedef enum dmaPRIORITY
{
    LOWPRIORITY = 0U,
    HIGHPRIORITY = 1U
} dmaPRIORITY_t;

/** @enum dmaREGION
 *   @brief DMA Memory Protection Region
 *
 *   Used to define DMA Memory Protection Region
 */
typedef enum dmaREGION
{
    DMA_REGION0 = 0U,
    DMA_REGION1 = 1U,
    DMA_REGION2 = 2U,
    DMA_REGION3 = 3U
} dmaREGION_t;

/** @enum dmaRegionAccess
 *   @brief DMA Memory Protection Region Access
 *
 *   Used to define access permission of DMA memory protection regions
 */
typedef enum dmaRegionAccess
{
    FULLACCESS = 0U,
    READONLY = 1U,
    WRITEONLY = 2U,
    NOACCESS = 3U
} dmaRegionAccess_t;

/** @enum dmaInterrupt
 *   @brief DMA Interrupt
 *
 *   Used to define DMA interrupts
 */
typedef enum dmaInterrupt
{
    FTC = 1U, /**<  Frame transfer complete Interrupt      */
    LFS = 2U, /**<  Last frame transfer started Interrupt  */
    HBC = 3U, /**<  First half of block complete Interrupt */
    BTC = 4U  /**<  Block transfer complete Interrupt      */
} dmaInterrupt_t;

/** @struct g_dmaCTRL
 *   @brief Interrupt mode globals
 *
 */
typedef struct dmaCTRLPKT
{
    uint32 SADD;      /* initial source address             */
    uint32 DADD;      /* initial destination address        */
    uint32 CHCTRL;    /* next ctrl packet to be trigger + 1 */
    uint32 FRCNT;     /* frame   count                      */
    uint32 ELCNT;     /* element count                      */
    uint32 ELDOFFSET; /* element destination offset         */
    uint32 ELSOFFSET; /* element source offset              */
    uint32 FRDOFFSET; /* frame detination offset            */
    uint32 FRSOFFSET; /* frame source offset                */
    uint32 PORTASGN;  /* dma port                           */
    uint32 RDSIZE;    /* read element size                  */
    uint32 WRSIZE;    /* write element size                 */
    uint32 TTYPE;     /* trigger type - frame/block         */
    uint32 ADDMODERD; /* addresssing mode for source        */
    uint32 ADDMODEWR; /* addresssing mode for destination   */
    uint32 AUTOINIT;  /* auto-init mode                     */
    uint32 COMBO;     /* next ctrl packet trigger(Not used) */
} g_dmaCTRL;

typedef volatile struct
{
    struct /* 0x000-0x400 */
    {
        uint32 ISADDR;
        uint32 IDADDR;
        uint32 ITCOUNT;
        uint32 rsvd1;
        uint32 CHCTRL;
        uint32 EIOFF;
        uint32 FIOFF;
        uint32 rsvd2;
    } PCP[ 32U ];

    struct /* 0x400-0x800   */
    {
        uint32 res[ 256U ];
    } RESERVED;

    struct /* 0x800-0xA00 */
    {
        uint32 CSADDR;
        uint32 CDADDR;
        uint32 CTCOUNT;
        uint32 rsvd3;
    } WCP[ 32U ];
} dmaRAMBASE_t;

#define dmaRAMREG ( ( dmaRAMBASE_t * ) 0xFFF80000U )

typedef struct dma_config_reg
{
    uint32 CONFIG_CHPRIOS;
    uint32 CONFIG_GCHIENAS;
    uint32 CONFIG_DREQASI[ 8U ];
    uint32 CONFIG_FTCINTENAS;
    uint32 CONFIG_LFSINTENAS;
    uint32 CONFIG_HBCINTENAS;
    uint32 CONFIG_BTCINTENAS;
    uint32 CONFIG_DMAPCR;
    uint32 CONFIG_DMAMPCTRL;
} dma_config_reg_t;

/**
 * @defgroup DMA DMA
 * @brief Direct Memory Access Controller
 *
 * The DMA controller is used to transfer data between two locations in the memory map in
 * the background of CPU operations. Typically, the DMA is used to:
 * - Transfer blocks of data between external and internal data memories
 * - Restructure portions of internal data memory
 * - Continually service a peripheral
 * - Page program sections to internal program memory
 *
 * Related files:
 * - reg_dma.h
 * - sys_dma.h
 * - sys_dma.c
 *
 * @addtogroup DMA
 * @{
 */
/* DMA Interface Functions */
void dmaEnable( void );
void dmaDisable( void );
void dmaSetCtrlPacket( uint32 channel, g_dmaCTRL g_dmaCTRLPKT );
void dmaSetChEnable( uint32 channel, uint32 type );
void dmaReqAssign( uint32 channel, uint32 reqline );
uint32 dmaGetReq( uint32 channel );
void dmaSetPriority( uint32 channel, dmaPRIORITY_t priority );
void dmaEnableInterrupt( uint32 channel, dmaInterrupt_t inttype );
void dmaDisableInterrupt( uint32 channel, dmaInterrupt_t inttype );
void dmaDefineRegion( dmaREGION_t region, uint32 start_add, uint32 end_add );
void dmaEnableRegion( dmaREGION_t region, dmaRegionAccess_t access, boolean intenable );
void dmaDisableRegion( dmaREGION_t region );
void dmaEnableParityCheck( void );
void dmaDisableParityCheck( void );
void dmaGetConfigValue( dma_config_reg_t * config_reg, config_value_type_t type );

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

/* USER CODE BEGIN (2) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif

#endif /* ifndef __DMA_H__ */
