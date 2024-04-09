/** @file lin.c
 *   @brief LIN Driver Implementation File
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

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "lin.h"
#include "sys_vim.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @fn void linInit(void)
 *   @brief Initializes the lin Driver
 *
 *   This function initializes the lin module.
 */
/* SourceId : LIN_SourceId_001 */
/* DesignId : LIN_DesignId_001 */
/* Requirements : HL_SR253 */
void linInit( void )
{
    /* USER CODE BEGIN (2) */
    /* USER CODE END */
    /** @b initialize @b LIN */

    /** - Release from reset */
    linREG->GCR0 = 1U;

    /** - Start LIN configuration
     *     - Keep state machine in software reset
     */
    linREG->GCR1 = 0U;

    /**   - Enable LIN Mode */
    linREG->GCR1 = 0x40U;

    /** - Setup control register 1
     *     - Enable transmitter
     *     - Enable receiver
     *     - Stop when debug mode is entered
     *     - Disable Loopback mode
     *     - Disable / Enable HGENCTRL (Mask filtering with ID-Byte)
     *     - Use enhance checksum
     *     - Enable multi buffer mode
     *     - Disable automatic baudrate adjustment
     *     - Disable sleep mode
     *     - Set LIN module as master
     *     - Enable/Disable parity
     *     - Disable data length control in ID4 and ID5
     */
    linREG->GCR1 |= 0x03000C40U | ( uint32 ) ( ( uint32 ) 1U << 12U )
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )
                  | ( uint32 ) ( ( uint32 ) 1U << 5U );

    /** - Setup maximum baud rate prescaler */
    linREG->MBRSR = ( uint32 ) 4954U;

    /** - Setup baud rate prescaler */
    linREG->BRS = ( uint32 ) 343U;

    /** - Setup RX and TX reception masks */
    linREG->MASK = ( ( uint32 ) ( ( uint32 ) 0xFFU << 16U ) | ( uint32 ) 0xFFU );

    /** - Setup compare
     *     - Sync delimiter
     *     - Sync break extension
     */
    linREG->COMP = ( ( uint32 ) ( ( uint32 ) ( 1U - 1U ) << 8U )
                     | ( ( uint32 ) 13U - 13U ) );

    /** - Setup response length */
    linREG->FORMAT = ( ( linREG->FORMAT & 0xFFF8FFFFU )
                       | ( uint32 ) ( ( ( uint32 ) 8U - 1U ) << 16U ) );

    /** - Set LIN pins functional mode
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG->PIO0 = ( ( uint32 ) 4U | ( uint32 ) 2U | ( uint32 ) 0U );

    /** - Set LIN pins default output value
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG->PIO3 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins output direction
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG->PIO1 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins open drain enable
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG->PIO6 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins pullup/pulldown enable
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG->PIO7 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins pullup/pulldown select
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG->PIO8 = ( ( uint32 ) 4U | ( uint32 ) 2U | ( uint32 ) 1U );

    /** - Set interrupt level
     *     - Bit error level
     *     - Physical bus error level
     *     - Checksum error level
     *     - Inconsistent sync field error level
     *     - No response error level
     *     - Framing error level
     *     - Overrun error level
     *     - Parity error level
     *     - Identifier level
     *     - RX level
     *     - TX level
     *     - Timeout after 3 wakeup signals level
     *     - Timeout after wakeup signal level
     *     - Timeout level
     *     - Wakeup level
     *     - Break detect level
     */
    linREG->SETINTLVL = ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                          | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                          | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                          | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                          | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                          | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                          | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                          | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U );

    /** - Set interrupt enable
     *     - Enable/Disable bit error
     *     - Enable/Disable physical bus error level
     *     - Enable/Disable checksum error level
     *     - Enable/Disable inconsistent sync field error level
     *     - Enable/Disable no response error level
     *     - Enable/Disable framing error level
     *     - Enable/Disable overrun error level
     *     - Enable/Disable parity error level
     *     - Enable/Disable identifier level
     *     - Enable/Disable RX level
     *     - Enable/Disable TX level
     *     - Enable/Disable timeout after 3 wakeup signals level
     *     - Enable/Disable timeout after wakeup signal level
     *     - Enable/Disable timeout level
     *     - Enable/Disable wakeup level
     *     - Enable/Disable break detect level
     */
    linREG->SETINT = ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                       | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                       | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                       | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                       | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                       | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                       | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                       | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U );

    /** - Finaly start LIN */
    linREG->GCR1 |= 0x00000080U;

    /* USER CODE BEGIN (3) */
    /* USER CODE END */
}

/** @fn void linSetFunctional(linBASE_t *lin, uint32 port)
 *   @brief Change functional behavior of pins at runtime.
 *   @param[in] lin   - lin module base address
 *   @param[in] port  - Value to write to PIO0 register
 *
 *   Change the value of the PCFUN register at runtime, this allows to
 *   dynamically change the functionality of the LIN pins between functional
 *   and GIO mode.
 */
/* SourceId : LIN_SourceId_002 */
/* DesignId : LIN_DesignId_002 */
/* Requirements : HL_SR254 */
void linSetFunctional( linBASE_t * lin, uint32 port )
{
    /* USER CODE BEGIN (4) */
    /* USER CODE END */

    lin->PIO0 = port;

    /* USER CODE BEGIN (5) */
    /* USER CODE END */
}

/** @fn void linSendHeader(linBASE_t *lin, uint8 identifier)
 *   @brief Send lin header.
 *   @param[in] lin  - lin module base address
 *   @param[in] identifier - lin header id
 *
 *   Send lin header including sync break field, sync field and identifier.
 */
/* SourceId : LIN_SourceId_003 */
/* DesignId : LIN_DesignId_003 */
/* Requirements : HL_SR255 */
void linSendHeader( linBASE_t * lin, uint8 identifier )
{
    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    lin->ID = ( ( lin->ID & 0xFFFFFF00U ) | ( uint32 ) identifier );

    /* USER CODE BEGIN (7) */
    /* USER CODE END */
}

/** @fn void linSendWakupSignal(linBASE_t *lin)
 *   @brief Send lin wakeup signal.
 *   @param[in] lin  - lin module base address
 *
 *   Send lin wakeup signal to terminate the sleep mode of any lin node connected to the
 * BUS.
 */
/* SourceId : LIN_SourceId_004 */
/* DesignId : LIN_DesignId_004 */
/* Requirements : HL_SR256 */
void linSendWakupSignal( linBASE_t * lin )
{
    /* USER CODE BEGIN (8) */
    /* USER CODE END */

    lin->TDx[ 0U ] = 0xF0U;
    lin->GCR2 |= 0x00000100U;

    /* USER CODE BEGIN (9) */
    /* USER CODE END */
}

/** @fn void linEnterSleep(linBASE_t *lin)
 *   @brief Take Module to Sleep.
 *   @param[in] lin  - lin module base address
 *
 *   Application must call this function to take Module to Sleep when Sleep command is
 * received. This function can also be called to forcefully enter Sleep when no activity
 * on BUS.
 */
/* SourceId : LIN_SourceId_005 */
/* DesignId : LIN_DesignId_005 */
/* Requirements : HL_SR257 */
void linEnterSleep( linBASE_t * lin )
{
    /* USER CODE BEGIN (10) */
    /* USER CODE END */
    lin->GCR2 |= 0x00000001U;
    /* USER CODE BEGIN (11) */
    /* USER CODE END */
}

/** @fn void linSoftwareReset(linBASE_t *lin)
 *   @brief Perform software reset.
 *   @param[in] lin  - lin module base address
 *
 *   Perform software reset of lin module.
 *   This function will reset the lin state machine and clear all pending flags.
 *   It is required to call this function after a wakeup signal has been sent.
 */
/* SourceId : LIN_SourceId_006 */
/* DesignId : LIN_DesignId_006 */
/* Requirements : HL_SR258 */
void linSoftwareReset( linBASE_t * lin )
{
    /* USER CODE BEGIN (12) */
    /* USER CODE END */

    lin->GCR1 &= ~( uint32 ) ( 0x00000080U );
    lin->GCR1 |= 0x00000080U;

    /* USER CODE BEGIN (13) */
    /* USER CODE END */
}

/** @fn uint32 linIsTxReady(linBASE_t *lin)
 *   @brief Check if Tx buffer empty
 *   @param[in] lin - lin module base address
 *
 *   @return The TX ready flag
 *
 *   Checks to see if the Tx buffer ready flag is set, returns
 *   0 is flags not set otherwise will return the Tx flag itself.
 */
/* SourceId : LIN_SourceId_007 */
/* DesignId : LIN_DesignId_007 */
/* Requirements : HL_SR259 */
uint32 linIsTxReady( linBASE_t * lin )
{
    /* USER CODE BEGIN (14) */
    /* USER CODE END */

    return lin->FLR & LIN_TX_READY;
}

/** @fn void linSetLength(linBASE_t *lin, uint32 length)
 *   @brief Send Data
 *   @param[in] lin    - lin module base address
 *   @param[in] length - number of data words in bytes. Range: 1-8.
 *
 *   Send data response length in bytes.
 */
/* SourceId : LIN_SourceId_008 */
/* DesignId : LIN_DesignId_008 */
/* Requirements : HL_SR260 */
void linSetLength( linBASE_t * lin, uint32 length )
{
    /* USER CODE BEGIN (15) */
    /* USER CODE END */

    lin->FORMAT = ( ( lin->FORMAT & 0xFFF8FFFFU ) | ( ( length - 1U ) << 16U ) );

    /* USER CODE BEGIN (16) */
    /* USER CODE END */
}

/** @fn void linSend(linBASE_t *lin, uint8 * data)
 *   @brief Send Data
 *   @param[in] lin    - lin module base address
 *   @param[in] data   - pointer to data to send
 *
 *   Send a block of data pointed to by 'data'.
 *   The number of data to transmit must be set with 'linSetLength' before.
 */
/* SourceId : LIN_SourceId_009 */
/* DesignId : LIN_DesignId_009 */
/* Requirements : HL_SR261 */
void linSend( linBASE_t * lin, uint8 * data )
{
    uint32 i;
    uint32 length = ( uint32 ) ( ( uint32 ) ( lin->FORMAT & 0x00070000U ) >> 16U );
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
     * allowed in this driver" */
    /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
    uint8 * pData = data + length;

    /* USER CODE BEGIN (17) */
    /* USER CODE END */

    for( i = 0U; i <= length; i++ )
    {
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        lin->TDx[ length - i ] = *pData;
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
        pData--;
    }

    /* USER CODE BEGIN (18) */
    /* USER CODE END */
}

/** @fn uint32 linIsRxReady(linBASE_t *lin)
 *   @brief Check if Rx buffer full
 *   @param[in] lin - lin module base address
 *
 *   @return The Rx ready flag
 *
 *   Checks to see if the Rx buffer full flag is set, returns
 *   0 is flags not set otherwise will return the Rx flag itself.
 */
/* SourceId : LIN_SourceId_010 */
/* DesignId : LIN_DesignId_010 */
/* Requirements : HL_SR262 */
uint32 linIsRxReady( linBASE_t * lin )
{
    /* USER CODE BEGIN (19) */
    /* USER CODE END */

    return lin->FLR & LIN_RX_INT;
}

/** @fn uint32 linTxRxError(linBASE_t *lin)
 *   @brief Return Tx and Rx Error flags
 *   @param[in] lin - lin module base address
 *
 *   @return The Tx and Rx error flags
 *
 *   Returns the bit, physical bus, checksum, inconsistent sync field,
 *   no response, framing, overrun, parity and timeout error flags.
 *   It also clears the error flags before returning.
 */
/* SourceId : LIN_SourceId_011 */
/* DesignId : LIN_DesignId_011 */
/* Requirements : HL_SR263 */
uint32 linTxRxError( linBASE_t * lin )
{
    uint32 status = lin->FLR
                  & ( LIN_BE_INT | LIN_PBE_INT | LIN_CE_INT | LIN_ISFE_INT | LIN_NRE_INT
                      | LIN_FE_INT | LIN_OE_INT | LIN_PE_INT | LIN_TOA3WUS_INT
                      | LIN_TOAWUS_INT | LIN_TO_INT );

    lin->FLR = LIN_BE_INT | LIN_PBE_INT | LIN_CE_INT | LIN_ISFE_INT | LIN_NRE_INT
             | LIN_FE_INT | LIN_OE_INT | LIN_PE_INT | LIN_TOA3WUS_INT | LIN_TOAWUS_INT
             | LIN_TO_INT;

    /* USER CODE BEGIN (20) */
    /* USER CODE END */

    return status;
}

/** @fn uint32 linGetIdentifier(linBASE_t *lin)
 *   @brief Get last received identifier
 *   @param[in] lin - lin module base address
 *
 *   @return Identifier
 *
 *   Read last received identifier.
 */
/* SourceId : LIN_SourceId_012 */
/* DesignId : LIN_DesignId_012 */
/* Requirements : HL_SR262 */
uint32 linGetIdentifier( linBASE_t * lin )
{
    /* USER CODE BEGIN (21) */
    /* USER CODE END */
    return ( uint32 ) ( ( uint32 ) ( lin->ID & 0x00FF0000U ) >> 16U );
}

/** @fn void linGetData(linBASE_t *lin, uint8 * const data)
 *   @brief Read received data
 *   @param[in] lin    - lin module base address
 *   @param[in] data   - pointer to data buffer
 *
 *   Read a block of bytes and place it into the data buffer pointed to by 'data'.
 */
/* SourceId : LIN_SourceId_013 */
/* DesignId : LIN_DesignId_013 */
/* Requirements : HL_SR265 */
void linGetData( linBASE_t * lin, uint8 * const data )
{
    uint32 i;
    uint32 length = ( uint32 ) ( ( uint32 ) ( lin->FORMAT & 0x00070000U ) >> 16U );
    uint8 * pData = data;

    /* USER CODE BEGIN (22) */
    /* USER CODE END */

    for( i = 0U; i <= length; i++ )
    {
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        *pData = lin->RDx[ i ];
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
        pData++;
    }

    /* USER CODE BEGIN (23) */
    /* USER CODE END */
}

/** @fn void linEnableLoopback(linBASE_t *lin, loopBackType_t Loopbacktype)
 *   @brief Enable Loopback mode for self test
 *   @param[in] lin        - lin module base address
 *   @param[in] Loopbacktype  - Digital or Analog
 *
 *   This function enables the Loopback mode for self test.
 */
/* SourceId : LIN_SourceId_014 */
/* DesignId : LIN_DesignId_016 */
/* Requirements : HL_SR268 */
void linEnableLoopback( linBASE_t * lin, loopBackType_t Loopbacktype )
{
    /* USER CODE BEGIN (24) */
    /* USER CODE END */

    /* Clear Loopback incase enabled already */
    lin->IODFTCTRL = 0U;

    /* Enable Loopback either in Analog or Digital Mode */
    lin->IODFTCTRL = ( ( uint32 ) ( 0x00000A00U )
                       | ( uint32 ) ( ( uint32 ) Loopbacktype << 1U ) );

    /* USER CODE BEGIN (25) */
    /* USER CODE END */
}

/** @fn void linDisableLoopback(linBASE_t *lin)
 *   @brief Enable Loopback mode for self test
 *   @param[in] lin        - lin module base address
 *
 *   This function disable the Loopback mode.
 */
/* SourceId : LIN_SourceId_015 */
/* DesignId : LIN_DesignId_017 */
/* Requirements : HL_SR269 */
void linDisableLoopback( linBASE_t * lin )
{
    /* USER CODE BEGIN (26) */
    /* USER CODE END */

    /* Disable Loopback Mode */
    lin->IODFTCTRL = 0x00000500U;

    /* USER CODE BEGIN (27) */
    /* USER CODE END */
}

/** @fn linEnableNotification(linBASE_t *lin, uint32 flags)
 *   @brief Enable interrupts
 *   @param[in] lin   - lin module base address
 *   @param[in] flags - Interrupts to be enabled, can be ored value of:
 *                      LIN_BE_INT      - bit error,
 *                      LIN_PBE_INT     - physical bus error,
 *                      LIN_CE_INT      - checksum error,
 *                      LIN_ISFE_INT    - inconsistent sync field error,
 *                      LIN_NRE_INT     - no response error,
 *                      LIN_FE_INT      - framing error,
 *                      LIN_OE_INT      - overrun error,
 *                      LIN_PE_INT      - parity error,
 *                      LIN_ID_INT      - received matching identifier,
 *                      LIN_RX_INT      - receive buffer ready,
 *                      LIN_TOA3WUS_INT - time out after 3 wakeup signals,
 *                      LIN_TOAWUS_INT  - time out after wakeup signal,
 *                      LIN_TO_INT      - time out signal,
 *                      LIN_WAKEUP_INT  - wakeup,
 *                      LIN_BREAK_INT   - break detect
 */
/* SourceId : LIN_SourceId_016 */
/* DesignId : LIN_DesignId_014 */
/* Requirements : HL_SR266 */
void linEnableNotification( linBASE_t * lin, uint32 flags )
{
    /* USER CODE BEGIN (28) */
    /* USER CODE END */

    lin->SETINT = flags;

    /* USER CODE BEGIN (29) */
    /* USER CODE END */
}

/** @fn linDisableNotification(linBASE_t *lin, uint32 flags)
 *   @brief Disable interrupts
 *   @param[in] lin   - lin module base address
 *   @param[in] flags - Interrupts to be disabled, can be or'ed value of:
 *                      LIN_BE_INT      - bit error,
 *                      LIN_PBE_INT     - physical bus error,
 *                      LIN_CE_INT      - checksum error,
 *                      LIN_ISFE_INT    - inconsistent sync field error,
 *                      LIN_NRE_INT     - no response error,
 *                      LIN_FE_INT      - framing error,
 *                      LIN_OE_INT      - overrun error,
 *                      LIN_PE_INT      - parity error,
 *                      LIN_ID_INT      - received matching identifier,
 *                      LIN_RX_INT      - receive buffer ready,
 *                      LIN_TOA3WUS_INT - time out after 3 wakeup signals,
 *                      LIN_TOAWUS_INT  - time out after wakeup signal,
 *                      LIN_TO_INT      - time out signal,
 *                      LIN_WAKEUP_INT  - wakeup,
 *                      LIN_BREAK_INT   - break detect
 */
/* SourceId : LIN_SourceId_017 */
/* DesignId : LIN_DesignId_015 */
/* Requirements : HL_SR267 */
void linDisableNotification( linBASE_t * lin, uint32 flags )
{
    /* USER CODE BEGIN (30) */
    /* USER CODE END */

    lin->CLEARINT = flags;

    /* USER CODE BEGIN (31) */
    /* USER CODE END */
}

/** @fn void linGetConfigValue(lin_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the LIN configuration registers
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
/* SourceId : LIN_SourceId_018 */
/* DesignId : LIN_DesignId_018 */
/* Requirements : HL_SR272 */
void linGetConfigValue( lin_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_GCR0 = LIN_GCR0_CONFIGVALUE;
        config_reg->CONFIG_GCR1 = LIN_GCR1_CONFIGVALUE;
        config_reg->CONFIG_GCR2 = LIN_GCR2_CONFIGVALUE;
        config_reg->CONFIG_SETINT = LIN_SETINT_CONFIGVALUE;
        config_reg->CONFIG_SETINTLVL = LIN_SETINTLVL_CONFIGVALUE;
        config_reg->CONFIG_FORMAT = LIN_FORMAT_CONFIGVALUE;
        config_reg->CONFIG_BRSR = LIN_BRSR_CONFIGVALUE;
        config_reg->CONFIG_FUN = LIN_FUN_CONFIGVALUE;
        config_reg->CONFIG_DIR = LIN_DIR_CONFIGVALUE;
        config_reg->CONFIG_ODR = LIN_ODR_CONFIGVALUE;
        config_reg->CONFIG_PD = LIN_PD_CONFIGVALUE;
        config_reg->CONFIG_PSL = LIN_PSL_CONFIGVALUE;
        config_reg->CONFIG_COMP = LIN_COMP_CONFIGVALUE;
        config_reg->CONFIG_MASK = LIN_MASK_CONFIGVALUE;
        config_reg->CONFIG_MBRSR = LIN_MBRSR_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_GCR0 = linREG->GCR0;
        config_reg->CONFIG_GCR1 = linREG->GCR1;
        config_reg->CONFIG_GCR2 = linREG->GCR2;
        config_reg->CONFIG_SETINT = linREG->SETINT;
        config_reg->CONFIG_SETINTLVL = linREG->SETINTLVL;
        config_reg->CONFIG_FORMAT = linREG->FORMAT;
        config_reg->CONFIG_BRSR = linREG->BRS;
        config_reg->CONFIG_FUN = linREG->PIO0;
        config_reg->CONFIG_DIR = linREG->PIO1;
        config_reg->CONFIG_ODR = linREG->PIO6;
        config_reg->CONFIG_PD = linREG->PIO7;
        config_reg->CONFIG_PSL = linREG->PIO8;
        config_reg->CONFIG_COMP = linREG->COMP;
        config_reg->CONFIG_MASK = linREG->MASK;
        config_reg->CONFIG_MBRSR = linREG->MBRSR;
    }
}

/** @fn uint32 linGetStatusFlag(linBASE_t *lin)
 *   @brief Get LIN status register value
 *   @param[in] lin - lin module base address
 *
 *   @return Status Flag register content
 *
 *   Read current Status Flag register.
 */
/* SourceId : LIN_SourceId_021 */
/* DesignId : LIN_DesignId_020 */
/* Requirements : HL_SR544 */
uint32 linGetStatusFlag( linBASE_t * lin )
{
    return lin->FLR;
}

/** @fn void linClearStatusFlag(linBASE_t *lin, uint32 flags)
 *   @brief Clear LIN status register
 *   @param[in] lin - lin module base address
 *   @param[in] flags - Interrupts to be disabled, can be or'ed value of:
 *                      LIN_BE_INT      - bit error,
 *                      LIN_PBE_INT     - physical bus error,
 *                      LIN_CE_INT      - checksum error,
 *                      LIN_ISFE_INT    - inconsistent sync field error,
 *                      LIN_NRE_INT     - no response error,
 *                      LIN_FE_INT      - framing error,
 *                      LIN_OE_INT      - overrun error,
 *                      LIN_PE_INT      - parity error,
 *                      LIN_ID_INT      - received matching identifier,
 *                      LIN_RX_INT      - receive buffer ready,
 *                      LIN_TOA3WUS_INT - time out after 3 wakeup signals,
 *                      LIN_TOAWUS_INT  - time out after wakeup signal,
 *                      LIN_TO_INT      - time out signal,
 *                      LIN_WAKEUP_INT  - wakeup,
 *                      LIN_BREAK_INT   - break detect,
 *                      LIN_BUSY_FLAG   - Bus Busy Flag,
 *                      LIN_TXEMPTY_INT - Transmit Empty Flag
 *
 *   Clear Status Flags passed as parameter.
 */
/* SourceId : LIN_SourceId_022 */
/* DesignId : LIN_DesignId_021 */
/* Requirements : HL_SR545 */
void linClearStatusFlag( linBASE_t * lin, uint32 flags )
{
    /* USER CODE BEGIN (38) */
    /* USER CODE END */
    lin->FLR = flags;
    /* USER CODE BEGIN (39) */
    /* USER CODE END */
}
