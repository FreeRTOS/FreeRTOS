/** @file dma.c
 *   @brief DMA Driver Implementation File
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

#include "sys_dma.h"
#include "sys_vim.h"

/** @fn void dmaEnable(void)
 *   @brief enables DMA module
 *
 *   This function brings DMA out of reset
 */
/* SourceId : DMA_SourceId_001 */
/* DesignId : DMA_DesignId_001 */
/* Requirements: HL_SR167 */
void dmaEnable( void )
{
    dmaREG->GCTRL = 0x00010000U;  /* enable dma      */
    dmaREG->GCTRL |= 0x00000300U; /* stop at suspend */
}

/** @fn void dmaDisable(void)
 *   @brief disables DMA module
 *
 *   This function disables DMA module
 */
/* SourceId : DMA_SourceId_002 */
/* DesignId : DMA_DesignId_002 */
/* Requirements: HL_SR168 */
void dmaDisable( void )
{
    /* Wait until DMA's external bus has completed data transfer */
    /*SAFETYMCUSW 134 S MR: 12.2 <APPROVED> "Tool issue" */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( dmaREG->GCTRL & DMA_GCTRL_BUSBUSY ) != 0U )
    {
    } /* Wait */

    /* Disable DMA module */
    dmaREG->GCTRL = 0U;
}

/** @fn void dmaReqAssign(uint32 channel,uint32 reqline)
 *   @brief Assign DMA request lines to channels
 *   @param[in] channel DMA channel
 *   @param[in] reqline DMA request line
 *
 *   This function assigns DMA request lines to channels
 */
/* SourceId : DMA_SourceId_003 */
/* DesignId : DMA_DesignId_005 */
/* Requirements: HL_SR169 */
void dmaReqAssign( uint32 channel, uint32 reqline )
{
    register uint32 i = 0U, j = 0U;

    i = channel >> 2U;         /* Find the register to configure */
    j = channel - ( i << 2U ); /* Find the offset of the type    */
    j = 3U - j;                /* reverse the byte order         */
    j = j << 3U;               /* find the bit location          */

    /* mapping channel 'i' to request line 'j' */
    dmaREG->DREQASI[ i ] &= ~( uint32 ) ( ( uint32 ) 0xFFU << j );
    dmaREG->DREQASI[ i ] |= ( reqline << j );
}

/** @fn uint32 dmaGetReq(uint32 channel)
 *   @brief Gets the request line number mapped to the selected channel
 *   @param[in] channel DMA channel
 *
 *   This function returns the request line number mapped to the selected channel
 */
/* SourceId : DMA_SourceId_004 */
/* DesignId : DMA_DesignId_006 */
/* Requirements: HL_SR170 */
uint32 dmaGetReq( uint32 channel )
{
    register uint32 i = 0U, j = 0U;

    i = channel >> 2U;         /* Find the register to configure */
    j = channel - ( i << 2U ); /* Find the offset of the type    */
    j = 3U - j;                /* reverse the byte order         */
    j = j << 3U;               /* find the bit location          */
    return ( ( dmaREG->DREQASI[ i ] >> j ) & 0xFFU );
}

/** @fn void dmaSetCtrlPacket(uint32 channel)
 *   @brief Set control packet
 *
 *   This function sets control packet
 */
/* SourceId : DMA_SourceId_005 */
/* DesignId : DMA_DesignId_003 */
/* Requirements: HL_SR171 */
void dmaSetCtrlPacket( uint32 channel, g_dmaCTRL g_dmaCTRLPKT )
{
    register uint32 i = 0U, j = 0U;

    dmaRAMREG->PCP[ channel ].ISADDR = g_dmaCTRLPKT.SADD;

    dmaRAMREG->PCP[ channel ].IDADDR = g_dmaCTRLPKT.DADD;

    dmaRAMREG->PCP[ channel ].ITCOUNT = ( g_dmaCTRLPKT.FRCNT << 16U )
                                      | g_dmaCTRLPKT.ELCNT;

    dmaRAMREG->PCP[ channel ].CHCTRL = ( g_dmaCTRLPKT.RDSIZE << 14U )
                                     | ( g_dmaCTRLPKT.WRSIZE << 12U )
                                     | ( g_dmaCTRLPKT.TTYPE << 8U )
                                     | ( g_dmaCTRLPKT.ADDMODERD << 3U )
                                     | ( g_dmaCTRLPKT.ADDMODEWR << 1U )
                                     | ( g_dmaCTRLPKT.AUTOINIT );

    dmaRAMREG->PCP[ channel ].CHCTRL |= ( g_dmaCTRLPKT.CHCTRL << 16U );

    dmaRAMREG->PCP[ channel ].EIOFF = ( g_dmaCTRLPKT.ELDOFFSET << 16U )
                                    | ( g_dmaCTRLPKT.ELSOFFSET );

    dmaRAMREG->PCP[ channel ].FIOFF = ( g_dmaCTRLPKT.FRDOFFSET << 16U )
                                    | ( g_dmaCTRLPKT.FRSOFFSET );

    i = channel >> 3U;         /* Find the register to write                    */
    j = channel - ( i << 3U ); /* Find the offset of the 4th bit                */
    j = 7U - j;                /* Reverse the order of the 4th bit offset       */
    j = j << 2U;               /* Find the bit location of the 4th bit to write */

    dmaREG->PAR[ i ] &= ~( uint32 ) ( ( uint32 ) 0xFU << j );
    dmaREG->PAR[ i ] |= ( g_dmaCTRLPKT.PORTASGN << j );
}

/** @fn void dmaSetChEnable(uint32 channel,uint32 type)
 *   @brief Enable channel
 *   @param[in] channel DMA channel
 *   @param[in] type Type of triggering
 *                    - DMA_HW: Enables the selected DMA channel for hardware triggering
 *                    - DMA_SW: Enables the selected DMA channel for software triggering
 *
 *   This function enables the DMA channel for hardware or software triggering
 */
/* SourceId : DMA_SourceId_006 */
/* DesignId : DMA_DesignId_004 */
/* Requirements: HL_SR172 */
void dmaSetChEnable( uint32 channel, uint32 type )
{
    if( type == ( uint32 ) DMA_HW )
    {
        dmaREG->HWCHENAS = ( uint32 ) 1U << channel;
    }
    else if( type == ( uint32 ) DMA_SW )
    {
        dmaREG->SWCHENAS = ( uint32 ) 1U << channel;
    }
    else
    {
        /* Empty  */
    }
}

/** @fn void dmaSetPriority(uint32 channel, dmaPRIORITY_t priority)
 *   @brief Assign Priority to the channel
 *   @param[in] channel DMA channel
 *   @param[in] priority Priority queue to which channel needs to be assigned
 *                        - LOWPRIORITY : The selected channel will be assigned to low
 * priority queue
 *                        - HIGHPRIORITY: The selected channel will be assigned to high
 * priority queue
 *
 *   This function assigns the selected priority to the selected channel
 */
/* SourceId : DMA_SourceId_007 */
/* DesignId : DMA_DesignId_007 */
/* Requirements: HL_SR173 */
void dmaSetPriority( uint32 channel, dmaPRIORITY_t priority )
{
    if( priority == LOWPRIORITY )
    {
        dmaREG->CHPRIOR = ( uint32 ) 1U << channel;
    }
    else
    {
        dmaREG->CHPRIOS = ( uint32 ) 1U << channel;
    }
}

/** @fn void dmaEnableInterrupt(uint32 channel, dmaInterrupt_t inttype)
 *   @brief Enable selected interrupt
 *   @param[in] channel DMA channel
 *   @param[in] inttype Interrupt to be enabled
 *                       - FTC: Frame Transfer Complete Interrupt will be disabled for the
 * selected channel
 *                       - LFS: Last Frame Transfer Started Interrupt will be disabled for
 * the selected channel
 *                       - HBC: First Half Of Block Complete Interrupt will be disabled
 * for the selected channel
 *                       - BTC: Block transfer complete Interrupt will be disabled for the
 * selected channel
 *                       - BER: Bus Error Interrupt will be disabled for the selected
 * channel
 *
 *   This function enables the selected interrupt for the selected channel
 */
/* SourceId : DMA_SourceId_008 */
/* DesignId : DMA_DesignId_008 */
/* Requirements: HL_SR174 */
void dmaEnableInterrupt( uint32 channel, dmaInterrupt_t inttype )
{
    dmaREG->GCHIENAS = ( uint32 ) 1U << channel;

    switch( inttype )
    {
        case FTC:
            dmaREG->FTCINTENAS = ( uint32 ) 1U << channel;
            break;

        case LFS:
            dmaREG->LFSINTENAS = ( uint32 ) 1U << channel;
            break;

        case HBC:
            dmaREG->HBCINTENAS = ( uint32 ) 1U << channel;
            break;

        case BTC:
            dmaREG->BTCINTENAS = ( uint32 ) 1U << channel;
            break;

        default:
            break;
    }
}

/** @fn void dmaDisableInterrupt(uint32 channel, dmaInterrupt_t inttype)
 *   @brief Disable selected interrupt
 *   @param[in] channel DMA channel
 *   @param[in] inttype Interrupt to be disabled
 *                       - FTC: Frame Transfer Complete Interrupt will be disabled for the
 * selected channel
 *                       - LFS: Last Frame Transfer Started Interrupt will be disabled for
 * the selected channel
 *                       - HBC: First Half Of Block Complete Interrupt will be disabled
 * for the selected channel
 *                       - BTC: Block transfer complete Interrupt will be disabled for the
 * selected channel
 *                       - BER: Bus Error Interrupt will be disabled for the selected
 * channel
 *
 *   This function disables the selected interrupt for the selected channel
 */
/* SourceId : DMA_SourceId_009 */
/* DesignId : DMA_DesignId_009 */
/* Requirements: HL_SR175 */
void dmaDisableInterrupt( uint32 channel, dmaInterrupt_t inttype )
{
    switch( inttype )
    {
        case FTC:
            dmaREG->FTCINTENAR = ( uint32 ) 1U << channel;
            break;

        case LFS:
            dmaREG->LFSINTENAR = ( uint32 ) 1U << channel;
            break;

        case HBC:
            dmaREG->HBCINTENAR = ( uint32 ) 1U << channel;
            break;

        case BTC:
            dmaREG->BTCINTENAR = ( uint32 ) 1U << channel;
            break;

        default:
            break;
    }
}

/** @fn void dmaDefineRegion(dmaREGION_t region, uint32 start_add, uint32 end_add)
 *   @brief Configure start and end address of the region
 *   @param[in] region Memory Region
 *                     - DMA_REGION0
 *                     - DMA_REGION1
 *                     - DMA_REGION2
 *                     - DMA_REGION3
 *   @param[in] start_add Start address of the the region
 *   @param[in] end_add End address of the region
 *
 *   This function configure start and end address of the selected region
 */
/* SourceId : DMA_SourceId_010 */
/* DesignId : DMA_DesignId_010 */
/* Requirements: HL_SR176 */
void dmaDefineRegion( dmaREGION_t region, uint32 start_add, uint32 end_add )
{
    dmaREG->DMAMPR[ region ].STARTADD = start_add;
    dmaREG->DMAMPR[ region ].ENDADD = end_add;
}

/** @fn void dmaEnableRegion(dmaREGION_t region, dmaRegionAccess_t access, boolean
 * intenable)
 *   @brief Enable the selected region
 *   @param[in] region Memory Region
 *                     - DMA_REGION0
 *                     - DMA_REGION1
 *                     - DMA_REGION2
 *                     - DMA_REGION3
 *   @param[in] access Access permission of the selected region
 *                      - FULLACCESS
 *                      - READONLY
 *                      - WRITEONLY
 *                      - NOACCESS
 *   @param[in] intenable Interrupt to be enabled or not
 *                         - INTERRUPT_ENABLE : Enable interrupt for the selected region
 *                         - INTERRUPT_DISABLE: Disable interrupt for the selected region
 *
 *   This function enables the selected region with selected access permission with or
 * without interrupt enable
 */
/* SourceId : DMA_SourceId_011 */
/* DesignId : DMA_DesignId_011 */
/* Requirements: HL_SR177 */
void dmaEnableRegion( dmaREGION_t region, dmaRegionAccess_t access, boolean intenable )
{
    dmaREG->DMAMPCTRL &= ~( uint32 ) ( ( uint32 ) 0xFFU << ( region * 8U ) );

    /* Enable the region */
    dmaREG->DMAMPCTRL |= ( uint32 ) 1U << ( region * 8U );

    /* Set access permission for the region */
    dmaREG->DMAMPCTRL |= ( uint32 ) access << ( ( region * 8U ) + 1U );

    if( intenable )
    {
        /* Enable interrupt */
        dmaREG->DMAMPCTRL |= ( uint32 ) 1U << ( ( region * 8U ) + 3U );
    }
}

/** @fn void dmaDisableRegion(dmaREGION_t region)
 *   @brief Disable the selected region
 *   @param[in] region Memory Region
 *                     - DMA_REGION0
 *                     - DMA_REGION1
 *                     - DMA_REGION2
 *                     - DMA_REGION3
 *
 *   This function disables the selected region(no address checking done).
 */
/* SourceId : DMA_SourceId_012 */
/* DesignId : DMA_DesignId_012 */
/* Requirements: HL_SR178 */
void dmaDisableRegion( dmaREGION_t region )
{
    dmaREG->DMAMPCTRL &= ~( uint32 ) ( ( uint32 ) 1U << ( ( uint32 ) region * 8U ) );
}

/** @fn void dmaEnableParityCheck(void)
 *   @brief Enable Parity Check
 *
 *   This function enables parity check
 */
/* SourceId : DMA_SourceId_013 */
/* DesignId : DMA_DesignId_013 */
/* Requirements: HL_SR179 */
void dmaEnableParityCheck( void )
{
    dmaREG->DMAPCR = 0xAU;
}

/** @fn void dmaDisableParityCheck(void)
 *   @brief Disable Parity Check
 *
 *   This function disables parity check
 */
/* SourceId : DMA_SourceId_014 */
/* DesignId : DMA_DesignId_014 */
/* Requirements: HL_SR180 */
void dmaDisableParityCheck( void )
{
    dmaREG->DMAPCR = 0x5U;
}

/** @fn void dmaGetConfigValue(dma_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *   @param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *   @param[in] type:    whether initial or current value of the configuration registers
 * need to be stored
 *                       - InitialValue: initial value of the configuration registers will
 * be stored in the struct pointed by config_reg
 *                       - CurrentValue: initial value of the configuration registers will
 * be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : DMA_SourceId_015 */
/* DesignId : DMA_DesignId_015 */
/* Requirements: HL_SR183 */
void dmaGetConfigValue( dma_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    { /* Do not pass Initial value as parameter as there is no DMA initialization API */
    }
    else
    {
        config_reg->CONFIG_CHPRIOS = dmaREG->CHPRIOS;
        config_reg->CONFIG_GCHIENAS = dmaREG->GCHIENAS;
        config_reg->CONFIG_DREQASI[ 0U ] = dmaREG->DREQASI[ 0U ];
        config_reg->CONFIG_DREQASI[ 1U ] = dmaREG->DREQASI[ 1U ];
        config_reg->CONFIG_DREQASI[ 2U ] = dmaREG->DREQASI[ 2U ];
        config_reg->CONFIG_DREQASI[ 3U ] = dmaREG->DREQASI[ 3U ];
        config_reg->CONFIG_DREQASI[ 4U ] = dmaREG->DREQASI[ 4U ];
        config_reg->CONFIG_DREQASI[ 5U ] = dmaREG->DREQASI[ 5U ];
        config_reg->CONFIG_DREQASI[ 6U ] = dmaREG->DREQASI[ 6U ];
        config_reg->CONFIG_DREQASI[ 7U ] = dmaREG->DREQASI[ 7U ];
        config_reg->CONFIG_FTCINTENAS = dmaREG->FTCINTENAS;
        config_reg->CONFIG_LFSINTENAS = dmaREG->LFSINTENAS;
        config_reg->CONFIG_HBCINTENAS = dmaREG->HBCINTENAS;
        config_reg->CONFIG_BTCINTENAS = dmaREG->BTCINTENAS;
        config_reg->CONFIG_DMAPCR = dmaREG->DMAPCR;
        config_reg->CONFIG_DMAMPCTRL = dmaREG->DMAMPCTRL;
    }
}
