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

/* SourceId : LIN_SourceId_001 */
/* DesignId : LIN_DesignId_001 */
/* Requirements : CONQ_LIN_SR5 */
/** @fn void linInit(void)
 *   @brief Initializes the lin Driver
 *
 *   This function initializes the lin module.
 */
void linInit( void )
{
    /* USER CODE BEGIN (2) */
    /* USER CODE END */
    /** @b initialize @b LIN */

    /** - Release from reset */
    linREG1->GCR0 = 1U;

    /** - Start LIN configuration
     *     - Keep state machine in software reset
     */
    linREG1->GCR1 = 0U;

    /**   - Enable LIN Mode */
    linREG1->GCR1 = 0x40U;

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
     *     - Set LIN module either as master/salve
     *     - Enable/Disable parity
     *     - Disable data length control in ID4 and ID5
     */
    linREG1->GCR1 |= 0x03000C40U | ( uint32 ) ( ( uint32 ) 1U << 12U )
                   | ( uint32 ) ( ( uint32 ) 0U << 2U )
                   | ( uint32 ) ( ( uint32 ) 1U << 5U );

    /** - Setup maximum baud rate prescaler */
    linREG1->MBRSR = ( uint32 ) 3370U;

    /** - Setup baud rate prescaler */
    linREG1->BRS = ( uint32 ) 233U;

    /** - Setup RX and TX reception masks */
    linREG1->MASK = ( ( uint32 ) ( ( uint32 ) 0xFFU << 16U ) | ( uint32 ) 0xFFU );

    /** - Setup compare
     *     - Sync delimiter
     *     - Sync break extension
     */
    linREG1->COMP = ( ( uint32 ) ( ( uint32 ) ( 1U - 1U ) << 8U )
                      | ( ( uint32 ) 13U - 13U ) );

    /** - Setup response length */
    linREG1->FORMAT = ( ( linREG1->FORMAT & 0xFFF8FFFFU )
                        | ( uint32 ) ( ( ( uint32 ) 8U - 1U ) << 16U ) );

    /** - Set LIN pins functional mode
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG1->PIO0 = ( ( uint32 ) 4U | ( uint32 ) 2U | ( uint32 ) 0U );

    /** - Set LIN pins default output value
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG1->PIO3 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins output direction
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG1->PIO1 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins open drain enable
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG1->PIO6 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins pullup/pulldown enable
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG1->PIO7 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins pullup/pulldown select
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG1->PIO8 = ( ( uint32 ) 4U | ( uint32 ) 2U | ( uint32 ) 1U );

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
    linREG1->SETINTLVL = ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
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
    linREG1->SETINT = ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U );

    /** - Finaly start LIN */
    linREG1->GCR1 |= 0x00000080U;

    /** @b initialize @b LIN */

    /** - Release from reset */
    linREG2->GCR0 = 1U;

    /** - Start LIN configuration
     *     - Keep state machine in software reset
     */
    linREG2->GCR1 = 0U;

    /**   - Enable LIN Mode */
    linREG2->GCR1 = 0x40U;

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
     *     - Set LIN module either as master/salve
     *     - Enable/Disable parity
     *     - Disable data length control in ID4 and ID5
     */
    linREG2->GCR1 |= 0x03000C40U | ( uint32 ) ( ( uint32 ) 1U << 12U )
                   | ( uint32 ) ( ( uint32 ) 0U << 2U )
                   | ( uint32 ) ( ( uint32 ) 1U << 5U );

    /** - Setup maximum baud rate prescaler */
    linREG2->MBRSR = ( uint32 ) 3370U;

    /** - Setup baud rate prescaler */
    linREG2->BRS = ( uint32 ) 233U;

    /** - Setup RX and TX reception masks */
    linREG2->MASK = ( ( uint32 ) ( ( uint32 ) 0xFFU << 16U ) | ( uint32 ) 0xFFU );

    /** - Setup compare
     *     - Sync delimiter
     *     - Sync break extension
     */
    linREG2->COMP = ( ( uint32 ) ( ( uint32 ) ( 1U - 1U ) << 8U )
                      | ( ( uint32 ) 13U - 13U ) );

    /** - Setup response length */
    linREG2->FORMAT = ( ( linREG2->FORMAT & 0xFFF8FFFFU )
                        | ( uint32 ) ( ( ( uint32 ) 8U - 1U ) << 16U ) );

    /** - Set LIN pins functional mode
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG2->PIO0 = ( ( uint32 ) 4U | ( uint32 ) 2U | ( uint32 ) 0U );

    /** - Set LIN pins default output value
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG2->PIO3 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins output direction
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG2->PIO1 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins open drain enable
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG2->PIO6 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins pullup/pulldown enable
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG2->PIO7 = ( ( uint32 ) 0U | ( uint32 ) 0U | ( uint32 ) 0U );

    /** - Set LIN pins pullup/pulldown select
     *     - TX
     *     - RX
     *     - CLK
     */
    linREG2->PIO8 = ( ( uint32 ) 4U | ( uint32 ) 2U | ( uint32 ) 1U );

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
    linREG2->SETINTLVL = ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
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
    linREG2->SETINT = ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                        | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U );

    /** - Finaly start LIN */
    linREG2->GCR1 |= 0x00000080U;

    /* USER CODE BEGIN (3) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_002 */
/* DesignId : LIN_DesignId_002 */
/* Requirements : CONQ_LIN_SR6 */
/** @fn void linSetFunctional(linBASE_t *lin, uint32 port)
 *   @brief Change functional behavior of pins at runtime.
 *   @param[in] lin   - lin module base address
 *   @param[in] port  - Value to write to PIO0 register
 *
 *   Change the value of the PCFUN register at runtime, this allows to
 *   dynamically change the functionality of the LIN pins between functional
 *   and GIO mode.
 */
void linSetFunctional( linBASE_t * lin, uint32 port )
{
    /* USER CODE BEGIN (4) */
    /* USER CODE END */

    lin->PIO0 = port;

    /* USER CODE BEGIN (5) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_003 */
/* DesignId : LIN_DesignId_003 */
/* Requirements : CONQ_LIN_SR7 */
/** @fn void linSendHeader(linBASE_t *lin, uint8 identifier)
 *   @brief Send lin header.
 *   @param[in] lin  - lin module base address
 *   @param[in] identifier - lin header id
 *
 *   Send lin header including sync break field, sync field and identifier.
 */
void linSendHeader( linBASE_t * lin, uint8 identifier )
{
    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    lin->ID = ( ( lin->ID & 0xFFFFFF00U ) | ( uint32 ) identifier );

    /* USER CODE BEGIN (7) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_004 */
/* DesignId : LIN_DesignId_004 */
/* Requirements : CONQ_LIN_SR8 */
/** @fn void linSendWakupSignal(linBASE_t *lin)
 *   @brief Send lin wakeup signal.
 *   @param[in] lin  - lin module base address
 *
 *   Send lin wakeup signal to terminate the sleep mode of any lin node connected to the
 * BUS.
 */
void linSendWakupSignal( linBASE_t * lin )
{
    /* USER CODE BEGIN (8) */
    /* USER CODE END */

    lin->TDx[ 0U ] = 0xF0U;
    lin->GCR2 |= 0x00000100U;

    /* USER CODE BEGIN (9) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_005 */
/* DesignId : LIN_DesignId_005 */
/* Requirements : CONQ_LIN_SR9 */
/** @fn void linEnterSleep(linBASE_t *lin)
 *   @brief Take Module to Sleep.
 *   @param[in] lin  - lin module base address
 *
 *   Application must call this function to take Module to Sleep when Sleep command is
 * received. This function can also be called to forcefully enter Sleep when no activity
 * on BUS.
 */
void linEnterSleep( linBASE_t * lin )
{
    /* USER CODE BEGIN (10) */
    /* USER CODE END */
    lin->GCR2 |= 0x00000001U;
    /* USER CODE BEGIN (11) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_006 */
/* DesignId : LIN_DesignId_006 */
/* Requirements : CONQ_LIN_SR10 */
/** @fn void linSoftwareReset(linBASE_t *lin)
 *   @brief Perform software reset.
 *   @param[in] lin  - lin module base address
 *
 *   Perform software reset of lin module.
 *   This function will reset the lin state machine and clear all pending flags.
 *   It is required to call this function after a wakeup signal has been sent.
 */
void linSoftwareReset( linBASE_t * lin )
{
    /* USER CODE BEGIN (12) */
    /* USER CODE END */

    lin->GCR1 &= ~( uint32 ) ( 0x00000080U );
    lin->GCR1 |= 0x00000080U;

    /* USER CODE BEGIN (13) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_007 */
/* DesignId : LIN_DesignId_007 */
/* Requirements : CONQ_LIN_SR11 */
/** @fn uint32 linIsTxReady(linBASE_t *lin)
 *   @brief Check if Tx buffer empty
 *   @param[in] lin - lin module base address
 *
 *   @return The TX ready flag
 *
 *   Checks to see if the Tx buffer ready flag is set, returns
 *   0 is flags not set otherwise will return the Tx flag itself.
 */
uint32 linIsTxReady( linBASE_t * lin )
{
    /* USER CODE BEGIN (14) */
    /* USER CODE END */

    return lin->FLR & LIN_TX_READY;
}

/* SourceId : LIN_SourceId_008 */
/* DesignId : LIN_DesignId_008 */
/* Requirements : CONQ_LIN_SR12 */
/** @fn void linSetLength(linBASE_t *lin, uint32 length)
 *   @brief Send Data
 *   @param[in] lin    - lin module base address
 *   @param[in] length - number of data words in bytes. Range: 1-8.
 *
 *   Send data response length in bytes.
 */
void linSetLength( linBASE_t * lin, uint32 length )
{
    /* USER CODE BEGIN (15) */
    /* USER CODE END */

    lin->FORMAT = ( ( lin->FORMAT & 0xFFF8FFFFU ) | ( ( length - 1U ) << 16U ) );

    /* USER CODE BEGIN (16) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_009 */
/* DesignId : LIN_DesignId_009 */
/* Requirements : CONQ_LIN_SR13 */
/** @fn void linSend(linBASE_t *lin, uint8 * data)
 *   @brief Send Data
 *   @param[in] lin    - lin module base address
 *   @param[in] data   - pointer to data to send
 *
 *   Send a block of data pointed to by 'data'.
 *   The number of data to transmit must be set with 'linSetLength' before.
 */
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

/* SourceId : LIN_SourceId_010 */
/* DesignId : LIN_DesignId_010 */
/* Requirements : CONQ_LIN_SR14 */
/** @fn uint32 linIsRxReady(linBASE_t *lin)
 *   @brief Check if Rx buffer full
 *   @param[in] lin - lin module base address
 *
 *   @return The Rx ready flag
 *
 *   Checks to see if the Rx buffer full flag is set, returns
 *   0 is flags not set otherwise will return the Rx flag itself.
 */
uint32 linIsRxReady( linBASE_t * lin )
{
    /* USER CODE BEGIN (19) */
    /* USER CODE END */

    return lin->FLR & LIN_RX_INT;
}

/* SourceId : LIN_SourceId_011 */
/* DesignId : LIN_DesignId_011 */
/* Requirements : CONQ_LIN_SR15 */
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

/* SourceId : LIN_SourceId_012 */
/* DesignId : LIN_DesignId_012 */
/* Requirements : CONQ_LIN_SR16 */
/** @fn uint32 linGetIdentifier(linBASE_t *lin)
 *   @brief Get last received identifier
 *   @param[in] lin - lin module base address
 *
 *   @return Identifier
 *
 *   Read last received identifier.
 */
uint32 linGetIdentifier( linBASE_t * lin )
{
    /* USER CODE BEGIN (21) */
    /* USER CODE END */
    return ( uint32 ) ( ( uint32 ) ( lin->ID & 0x00FF0000U ) >> 16U );
}

/* SourceId : LIN_SourceId_013 */
/* DesignId : LIN_DesignId_013 */
/* Requirements : CONQ_LIN_SR17 */
/** @fn void linGetData(linBASE_t *lin, uint8 * const data)
 *   @brief Read received data
 *   @param[in] lin    - lin module base address
 *   @param[in] data   - pointer to data buffer
 *
 *   Read a block of bytes and place it into the data buffer pointed to by 'data'.
 */
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
        pData++;
    }

    /* USER CODE BEGIN (23) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_014 */
/* DesignId : LIN_DesignId_016 */
/* Requirements : CONQ_LIN_SR20 */
/** @fn void linEnableLoopback(linBASE_t *lin, loopBackType_t Loopbacktype)
 *   @brief Enable Loopback mode for self test
 *   @param[in] lin        - lin module base address
 *   @param[in] Loopbacktype  - Digital or Analog
 *
 *   This function enables the Loopback mode for self test.
 */
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

/* SourceId : LIN_SourceId_015 */
/* DesignId : LIN_DesignId_017 */
/* Requirements : CONQ_LIN_SR21 */
/** @fn void linDisableLoopback(linBASE_t *lin)
 *   @brief Enable Loopback mode for self test
 *   @param[in] lin        - lin module base address
 *
 *   This function disable the Loopback mode.
 */
void linDisableLoopback( linBASE_t * lin )
{
    /* USER CODE BEGIN (26) */
    /* USER CODE END */

    /* Disable Loopback Mode */
    lin->IODFTCTRL = 0x00000500U;

    /* USER CODE BEGIN (27) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_016 */
/* DesignId : LIN_DesignId_014 */
/* Requirements : CONQ_LIN_SR18 */
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
void linEnableNotification( linBASE_t * lin, uint32 flags )
{
    /* USER CODE BEGIN (28) */
    /* USER CODE END */

    lin->SETINT = flags;

    /* USER CODE BEGIN (29) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_017 */
/* DesignId : LIN_DesignId_015 */
/* Requirements : CONQ_LIN_SR19 */
/** @fn linDisableNotification(linBASE_t *lin, uint32 flags)
 *   @brief Disable interrupts
 *   @param[in] lin   - lin module base address
 *   @param[in] flags - Interrupts to be disabled, can be ored value of:
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
void linDisableNotification( linBASE_t * lin, uint32 flags )
{
    /* USER CODE BEGIN (30) */
    /* USER CODE END */

    lin->CLEARINT = flags;

    /* USER CODE BEGIN (31) */
    /* USER CODE END */
}

/* SourceId : LIN_SourceId_018 */
/* DesignId : LIN_DesignId_018 */
/* Requirements : CONQ_LIN_SR25 */
/** @fn void lin1GetConfigValue(lin_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the LIN1 configuration registers
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

void lin1GetConfigValue( lin_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_GCR0 = LIN1_GCR0_CONFIGVALUE;
        config_reg->CONFIG_GCR1 = LIN1_GCR1_CONFIGVALUE;
        config_reg->CONFIG_GCR2 = LIN1_GCR2_CONFIGVALUE;
        config_reg->CONFIG_SETINT = LIN1_SETINT_CONFIGVALUE;
        config_reg->CONFIG_SETINTLVL = LIN1_SETINTLVL_CONFIGVALUE;
        config_reg->CONFIG_FORMAT = LIN1_FORMAT_CONFIGVALUE;
        config_reg->CONFIG_BRSR = LIN1_BRSR_CONFIGVALUE;
        config_reg->CONFIG_FUN = LIN1_FUN_CONFIGVALUE;
        config_reg->CONFIG_DIR = LIN1_DIR_CONFIGVALUE;
        config_reg->CONFIG_ODR = LIN1_ODR_CONFIGVALUE;
        config_reg->CONFIG_PD = LIN1_PD_CONFIGVALUE;
        config_reg->CONFIG_PSL = LIN1_PSL_CONFIGVALUE;
        config_reg->CONFIG_COMP = LIN1_COMP_CONFIGVALUE;
        config_reg->CONFIG_MASK = LIN1_MASK_CONFIGVALUE;
        config_reg->CONFIG_MBRSR = LIN1_MBRSR_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Register read back support" */
        config_reg->CONFIG_GCR0 = linREG1->GCR0;
        config_reg->CONFIG_GCR1 = linREG1->GCR1;
        config_reg->CONFIG_GCR2 = linREG1->GCR2;
        config_reg->CONFIG_SETINT = linREG1->SETINT;
        config_reg->CONFIG_SETINTLVL = linREG1->SETINTLVL;
        config_reg->CONFIG_FORMAT = linREG1->FORMAT;
        config_reg->CONFIG_BRSR = linREG1->BRS;
        config_reg->CONFIG_FUN = linREG1->PIO0;
        config_reg->CONFIG_DIR = linREG1->PIO1;
        config_reg->CONFIG_ODR = linREG1->PIO6;
        config_reg->CONFIG_PD = linREG1->PIO7;
        config_reg->CONFIG_PSL = linREG1->PIO8;
        config_reg->CONFIG_COMP = linREG1->COMP;
        config_reg->CONFIG_MASK = linREG1->MASK;
        config_reg->CONFIG_MBRSR = linREG1->MBRSR;
    }
}

/* SourceId : LIN_SourceId_019 */
/* DesignId : LIN_DesignId_018 */
/* Requirements : CONQ_LIN_SR26 */
/** @fn void lin2GetConfigValue(lin_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the LIN2 configuration registers
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

void lin2GetConfigValue( lin_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_GCR0 = LIN2_GCR0_CONFIGVALUE;
        config_reg->CONFIG_GCR1 = LIN2_GCR1_CONFIGVALUE;
        config_reg->CONFIG_GCR2 = LIN2_GCR2_CONFIGVALUE;
        config_reg->CONFIG_SETINT = LIN2_SETINT_CONFIGVALUE;
        config_reg->CONFIG_SETINTLVL = LIN2_SETINTLVL_CONFIGVALUE;
        config_reg->CONFIG_FORMAT = LIN2_FORMAT_CONFIGVALUE;
        config_reg->CONFIG_BRSR = LIN2_BRSR_CONFIGVALUE;
        config_reg->CONFIG_FUN = LIN2_FUN_CONFIGVALUE;
        config_reg->CONFIG_DIR = LIN2_DIR_CONFIGVALUE;
        config_reg->CONFIG_ODR = LIN2_ODR_CONFIGVALUE;
        config_reg->CONFIG_PD = LIN2_PD_CONFIGVALUE;
        config_reg->CONFIG_PSL = LIN2_PSL_CONFIGVALUE;
        config_reg->CONFIG_COMP = LIN2_COMP_CONFIGVALUE;
        config_reg->CONFIG_MASK = LIN2_MASK_CONFIGVALUE;
        config_reg->CONFIG_MBRSR = LIN2_MBRSR_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Register read back support" */
        config_reg->CONFIG_GCR0 = linREG2->GCR0;
        config_reg->CONFIG_GCR1 = linREG2->GCR1;
        config_reg->CONFIG_GCR2 = linREG2->GCR2;
        config_reg->CONFIG_SETINT = linREG2->SETINT;
        config_reg->CONFIG_SETINTLVL = linREG2->SETINTLVL;
        config_reg->CONFIG_FORMAT = linREG2->FORMAT;
        config_reg->CONFIG_BRSR = linREG2->BRS;
        config_reg->CONFIG_FUN = linREG2->PIO0;
        config_reg->CONFIG_DIR = linREG2->PIO1;
        config_reg->CONFIG_ODR = linREG2->PIO6;
        config_reg->CONFIG_PD = linREG2->PIO7;
        config_reg->CONFIG_PSL = linREG2->PIO8;
        config_reg->CONFIG_COMP = linREG2->COMP;
        config_reg->CONFIG_MASK = linREG2->MASK;
        config_reg->CONFIG_MBRSR = linREG2->MBRSR;
    }
}

/* SourceId : LIN_SourceId_024 */
/* DesignId :  */
/* Requirements :  */
/** @fn uint32 linGetStatusFlag(linBASE_t *lin)
 *   @brief Get LIN status register value
 *   @param[in] lin - lin module base address
 *
 *   @return Status Flag register content
 *
 *   Read current Status Flag register.
 */
uint32 linGetStatusFlag( linBASE_t * lin )
{
    return lin->FLR;
}

/* SourceId : LIN_SourceId_025 */
/* DesignId :  */
/* Requirements :  */
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
void linClearStatusFlag( linBASE_t * lin, uint32 flags )
{
    /* USER CODE BEGIN (44) */
    /* USER CODE END */
    lin->FLR = flags;
    /* USER CODE BEGIN (45) */
    /* USER CODE END */
}
