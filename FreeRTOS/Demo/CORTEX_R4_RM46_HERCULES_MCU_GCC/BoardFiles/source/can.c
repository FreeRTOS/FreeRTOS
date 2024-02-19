/** @file can.c
 *   @brief CAN Driver Source File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - API Functions
 *   - Interrupt Handlers
 *   .
 *   which are relevant for the CAN driver.
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

/* Include Files */

#include "can.h"
#include "sys_vim.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/* Global and Static Variables */

#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )
#else
static const uint32 s_canByteOrder[ 8U ] = { 3U, 2U, 1U, 0U, 7U, 6U, 5U, 4U };
#endif

/* USER CODE BEGIN (2) */
/* USER CODE END */

/** @fn void canInit(void)
 *   @brief Initializes CAN Driver
 *
 *   This function initializes the CAN driver.
 *
 */
/* USER CODE BEGIN (3) */
/* USER CODE END */
/* SourceId : CAN_SourceId_001 */
/* DesignId : CAN_DesignId_001 */
/* Requirements : HL_SR207 */
void canInit( void )
{
    /* USER CODE BEGIN (4) */
    /* USER CODE END */
    /** @b Initialize @b CAN1: */

    /** - Setup control register
     *     - Disable automatic wakeup on bus activity
     *     - Local power down mode disabled
     *     - Disable DMA request lines
     *     - Enable global Interrupt Line 0 and 1
     *     - Disable debug mode
     *     - Release from software reset
     *     - Enable/Disable parity or ECC
     *     - Enable/Disable auto bus on timer
     *     - Setup message completion before entering debug state
     *     - Setup normal operation mode
     *     - Request write access to the configuration registers
     *     - Setup automatic retransmission of messages
     *     - Disable error interrupts
     *     - Disable status interrupts
     *     - Enter initialization mode
     */
    canREG1->CTL = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) ( ( uint32 ) 0x00000005U << 10U ) | ( uint32 ) 0x00020043U;

    /** - Clear all pending error flags and reset current status */
    canREG1->ES |= 0xFFFFFFFFU;

    /** - Assign interrupt level for messages */
    canREG1->INTMUXx[ 0U ] = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    canREG1->INTMUXx[ 1U ] = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Setup auto bus on timer period */
    canREG1->ABOTR = ( uint32 ) 0U;

    /** - Setup IF1 for data transmission
     *     - Wait until IF1 is ready for use
     *     - Set IF1 control byte
     */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware Status
     * check for execution sequence" */
    while( ( canREG1->IF1STAT & 0x80U ) == 0x80U )
    {
    } /* Wait */

    canREG1->IF1CMD = 0x87U;

    /** - Setup IF2 for reading data
     *     - Wait until IF1 is ready for use
     *     - Set IF1 control byte
     */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware Status
     * check for execution sequence" */
    while( ( canREG1->IF2STAT & 0x80U ) == 0x80U )
    {
    } /* Wait */

    canREG1->IF2CMD = 0x17U;

    /** - Setup bit timing
     *     - Setup baud rate prescaler extension
     *     - Setup TSeg2
     *     - Setup TSeg1
     *     - Setup sample jump width
     *     - Setup baud rate prescaler
     */
    canREG1->BTR = ( uint32 ) ( ( uint32 ) 0U << 16U )
                 | ( uint32 ) ( ( uint32 ) ( 3U - 1U ) << 12U )
                 | ( uint32 ) ( ( uint32 ) ( ( 4U + 3U ) - 1U ) << 8U )
                 | ( uint32 ) ( ( uint32 ) ( 3U - 1U ) << 6U ) | ( uint32 ) 19U;

    /** - CAN1 Port output values */
    canREG1->TIOC = ( uint32 ) ( ( uint32 ) 1U << 18U )
                  | ( uint32 ) ( ( uint32 ) 0U << 17U )
                  | ( uint32 ) ( ( uint32 ) 0U << 16U )
                  | ( uint32 ) ( ( uint32 ) 1U << 3U )
                  | ( uint32 ) ( ( uint32 ) 1U << 2U )
                  | ( uint32 ) ( ( uint32 ) 1U << 1U );

    canREG1->RIOC = ( uint32 ) ( ( uint32 ) 1U << 18U )
                  | ( uint32 ) ( ( uint32 ) 0U << 17U )
                  | ( uint32 ) ( ( uint32 ) 0U << 16U )
                  | ( uint32 ) ( ( uint32 ) 1U << 3U )
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )
                  | ( uint32 ) ( ( uint32 ) 0U << 1U );

    /** - Leave configuration and initialization mode  */
    canREG1->CTL &= ~( uint32 ) ( 0x00000041U );

    /** @b Initialize @b CAN2: */

    /** - Setup control register
     *     - Disable automatic wakeup on bus activity
     *     - Local power down mode disabled
     *     - Disable DMA request lines
     *     - Enable global Interrupt Line 0 and 1
     *     - Disable debug mode
     *     - Release from software reset
     *     - Enable/Disable parity or ECC
     *     - Enable/Disable auto bus on timer
     *     - Setup message completion before entering debug state
     *     - Setup normal operation mode
     *     - Request write access to the configuration registers
     *     - Setup automatic retransmission of messages
     *     - Disable error interrupts
     *     - Disable status interrupts
     *     - Enter initialization mode
     */
    canREG2->CTL = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) ( ( uint32 ) 0x00000005U << 10U ) | 0x00020043U;

    /** - Clear all pending error flags and reset current status */
    canREG2->ES |= 0xFFFFFFFFU;

    /** - Assign interrupt level for messages */
    canREG2->INTMUXx[ 0U ] = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    canREG2->INTMUXx[ 1U ] = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Setup auto bus on timer period */
    canREG2->ABOTR = ( uint32 ) 0U;

    /** - Setup IF1 for data transmission
     *     - Wait until IF1 is ready for use
     *     - Set IF1 control byte
     */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware Status
     * check for execution sequence" */
    while( ( canREG2->IF1STAT & 0x80U ) == 0x80U )
    {
    } /* Wait */

    canREG2->IF1CMD = 0x87U;

    /** - Setup IF2 for reading data
     *     - Wait until IF1 is ready for use
     *     - Set IF1 control byte
     */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware Status
     * check for execution sequence" */
    while( ( canREG2->IF2STAT & 0x80U ) == 0x80U )
    {
    } /* Wait */

    canREG2->IF2CMD = 0x17U;

    /** - Setup bit timing
     *     - Setup baud rate prescaler extension
     *     - Setup TSeg2
     *     - Setup TSeg1
     *     - Setup sample jump width
     *     - Setup baud rate prescaler
     */
    canREG2->BTR = ( uint32 ) ( ( uint32 ) 0U << 16U )
                 | ( uint32 ) ( ( uint32 ) ( 3U - 1U ) << 12U )
                 | ( uint32 ) ( ( uint32 ) ( ( 4U + 3U ) - 1U ) << 8U )
                 | ( uint32 ) ( ( uint32 ) ( 3U - 1U ) << 6U ) | ( uint32 ) 19U;

    /** - CAN2 Port output values */
    canREG2->TIOC = ( uint32 ) ( ( uint32 ) 1U << 18U )
                  | ( uint32 ) ( ( uint32 ) 0U << 17U )
                  | ( uint32 ) ( ( uint32 ) 0U << 16U )
                  | ( uint32 ) ( ( uint32 ) 1U << 3U )
                  | ( uint32 ) ( ( uint32 ) 1U << 2U )
                  | ( uint32 ) ( ( uint32 ) 1U << 1U );

    canREG2->RIOC = ( uint32 ) ( ( uint32 ) 1U << 18U )
                  | ( uint32 ) ( ( uint32 ) 0U << 17U )
                  | ( uint32 ) ( ( uint32 ) 0U << 16U )
                  | ( uint32 ) ( ( uint32 ) 1U << 3U )
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )
                  | ( uint32 ) ( ( uint32 ) 0U << 1U );

    /** - Leave configuration and initialization mode  */
    canREG2->CTL &= ~( uint32 ) ( 0x00000041U );

    /** @b Initialize @b CAN3: */

    /** - Setup control register
     *     - Disable automatic wakeup on bus activity
     *     - Local power down mode disabled
     *     - Disable DMA request lines
     *     - Enable global Interrupt Line 0 and 1
     *     - Disable debug mode
     *     - Release from software reset
     *     - Enable/Disable parity or ECC
     *     - Enable/Disable auto bus on timer
     *     - Setup message completion before entering debug state
     *     - Setup normal operation mode
     *     - Request write access to the configuration registers
     *     - Setup automatic retransmission of messages
     *     - Disable error interrupts
     *     - Disable status interrupts
     *     - Enter initialization mode
     */
    canREG3->CTL = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) ( ( uint32 ) 0x00000005U << 10U ) | 0x00020043U;

    /** - Clear all pending error flags and reset current status */
    canREG3->ES |= 0xFFFFFFFFU;

    /** - Assign interrupt level for messages */
    canREG3->INTMUXx[ 0U ] = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    canREG3->INTMUXx[ 1U ] = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                           | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Setup auto bus on timer period */
    canREG3->ABOTR = ( uint32 ) 0U;

    /** - Setup IF1 for data transmission
     *     - Wait until IF1 is ready for use
     *     - Set IF1 control byte
     */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware Status
     * check for execution sequence" */
    while( ( canREG3->IF1STAT & 0x80U ) == 0x80U )
    {
    } /* Wait */

    canREG3->IF1CMD = 0x87U;

    /** - Setup IF2 for reading data
     *     - Wait until IF1 is ready for use
     *     - Set IF1 control byte
     */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware Status
     * check for execution sequence" */
    while( ( canREG3->IF2STAT & 0x80U ) == 0x80U )
    {
    } /* Wait */

    canREG3->IF2CMD = 0x17U;

    /** - Setup bit timing
     *     - Setup baud rate prescaler extension
     *     - Setup TSeg2
     *     - Setup TSeg1
     *     - Setup sample jump width
     *     - Setup baud rate prescaler
     */
    canREG3->BTR = ( uint32 ) ( ( uint32 ) 0U << 16U )
                 | ( uint32 ) ( ( uint32 ) ( 3U - 1U ) << 12U )
                 | ( uint32 ) ( ( uint32 ) ( ( 4U + 3U ) - 1U ) << 8U )
                 | ( uint32 ) ( ( uint32 ) ( 3U - 1U ) << 6U )
                 | ( uint32 ) ( uint32 ) 19U;

    /** - CAN3 Port output values */
    canREG3->TIOC = ( uint32 ) ( ( uint32 ) 1U << 18U )
                  | ( uint32 ) ( ( uint32 ) 0U << 17U )
                  | ( uint32 ) ( ( uint32 ) 0U << 16U )
                  | ( uint32 ) ( ( uint32 ) 1U << 3U )
                  | ( uint32 ) ( ( uint32 ) 1U << 2U )
                  | ( uint32 ) ( ( uint32 ) 1U << 1U );

    canREG3->RIOC = ( uint32 ) ( ( uint32 ) 1U << 18U )
                  | ( uint32 ) ( ( uint32 ) 0U << 17U )
                  | ( uint32 ) ( ( uint32 ) 0U << 16U )
                  | ( uint32 ) ( ( uint32 ) 1U << 3U )
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )
                  | ( uint32 ) ( ( uint32 ) 0U << 1U );

    /** - Leave configuration and initialization mode  */
    canREG3->CTL &= ~( uint32 ) ( 0x00000041U );

    /**   @note This function has to be called before the driver can be used.\n
     *           This function has to be executed in privileged mode.\n
     */

    /* USER CODE BEGIN (5) */
    /* USER CODE END */
}

/* USER CODE BEGIN (6) */
/* USER CODE END */

/** @fn uint32 canTransmit(canBASE_t *node, uint32 messageBox, const uint8 * data)
 *   @brief Transmits a CAN message
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] messageBox Message box number of CAN node:
 *              - canMESSAGE_BOX1: CAN message box 1
 *              - canMESSAGE_BOXn: CAN message box n [n: 1-64]
 *              - canMESSAGE_BOX64: CAN message box 64
 *   @param[in] data Pointer to CAN TX data
 *   @return The function will return:
 *           - 0: When the setup of the TX message box wasn't successful
 *           - 1: When the setup of the TX message box was successful
 *
 *   This function writes a CAN message into a CAN message box.
 *	This function is not reentrant. However, if a CAN interrupt occurs, the values of
 *	the IF registers are backup up and restored at the end of the ISR, since these are a
 *shared resource.
 *
 */
/* SourceId : CAN_SourceId_002 */
/* DesignId : CAN_DesignId_002 */
/* Requirements : HL_SR208 */
uint32 canTransmit( canBASE_t * node, uint32 messageBox, const uint8 * data )
{
    uint32 i;
    uint32 success = 0U;
    uint32 regIndex = ( messageBox - 1U ) >> 5U;
    uint32 bitIndex = 1U << ( ( messageBox - 1U ) & 0x1FU );

    /* USER CODE BEGIN (7) */
    /* USER CODE END */

    /** - Check for pending message:
     *     - pending message, return 0
     *     - no pending message, start new transmission
     */
    if( ( node->TXRQx[ regIndex ] & bitIndex ) != 0U )
    {
        success = 0U;
    }

    else
    {
        /** - Wait until IF1 is ready for use */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware
         * Status check for execution sequence" */
        while( ( node->IF1STAT & 0x80U ) == 0x80U )
        {
        } /* Wait */

        /** - Configure IF1 for
         *     - Message direction - Write
         *     - Data Update
         *     - Start Transmission
         */
        node->IF1CMD = 0x87U;

        /** - Copy TX data into IF1 */
        for( i = 0U; i < 8U; i++ )
        {
#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            node->IF1DATx[ i ] = *data;
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
            data++;
#else
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            node->IF1DATx[ s_canByteOrder[ i ] ] = *data;
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
            data++;
#endif /* if ( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) ) */
        }

        /** - Copy TX data into message box */
        /*SAFETYMCUSW 93 S MR: 6.1,6.2,10.1,10.2,10.3,10.4 <APPROVED> "LDRA Tool issue" */
        node->IF1NO = ( uint8 ) messageBox;

        success = 1U;
    }

    /**   @note The function canInit has to be called before this function can be used.\n
     *           The user is responsible to initialize the message box.
     */

    /* USER CODE BEGIN (8) */
    /* USER CODE END */

    return success;
}

/* USER CODE BEGIN (9) */
/* USER CODE END */

/** @fn uint32 canGetData(canBASE_t *node, uint32 messageBox, uint8 * const data)
 *   @brief Gets received a CAN message
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] messageBox Message box number of CAN node:
 *              - canMESSAGE_BOX1: CAN message box 1
 *              - canMESSAGE_BOXn: CAN message box n [n: 1-64]
 *              - canMESSAGE_BOX64: CAN message box 64
 *   @param[out] data Pointer to store CAN RX data
 *   @return The function will return:
 *           - 0: When RX message box hasn't received new data
 *           - 1: When RX data are stored in the data buffer
 *           - 3: When RX data are stored in the data buffer and a message was lost
 *
 *   This function writes a CAN message into a CAN message box.
 *
 */
/* SourceId : CAN_SourceId_003 */
/* DesignId : CAN_DesignId_003 */
/* Requirements : HL_SR209 */
uint32 canGetData( canBASE_t * node, uint32 messageBox, uint8 * const data )
{
    uint32 i;
    uint32 size;
    uint8 * pData = data;
    uint32 success = 0U;
    uint32 regIndex = ( messageBox - 1U ) >> 5U;
    uint32 bitIndex = 1U << ( ( messageBox - 1U ) & 0x1FU );

    /* USER CODE BEGIN (10) */
    /* USER CODE END */

    /** - Check if new data have been arrived:
     *     - no new data, return 0
     *     - new data, get received message
     */
    if( ( node->NWDATx[ regIndex ] & bitIndex ) == 0U )
    {
        success = 0U;
    }

    else
    {
        /** - Wait until IF2 is ready for use */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware
         * Status check for execution sequence" */
        while( ( node->IF2STAT & 0x80U ) == 0x80U )
        {
        } /* Wait */

        /** - Configure IF2 for
         *     - Message direction - Read
         *     - Data Read
         *     - Clears NewDat bit in the message object.
         */
        node->IF2CMD = 0x17U;

        /** - Copy data into IF2 */
        /*SAFETYMCUSW 93 S MR: 6.1,6.2,10.1,10.2,10.3,10.4 <APPROVED> "LDRA Tool issue" */
        node->IF2NO = ( uint8 ) messageBox;

        /** - Wait until data are copied into IF2 */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware
         * Status check for execution sequence" */
        while( ( node->IF2STAT & 0x80U ) == 0x80U )
        {
        } /* Wait */

        /** - Get number of received bytes
         *   - Value from 0x8 to 0xF equals length 8.
         */
        size = node->IF2MCTL & 0xFU;

        if( size > 0x8U )
        {
            size = 0x8U;
        }

        /** - Copy RX data into destination buffer */
        for( i = 0U; i < size; i++ )
        {
#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            *pData = node->IF2DATx[ i ];
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
            pData++;
#else
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            *pData = node->IF2DATx[ s_canByteOrder[ i ] ];
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
            pData++;
#endif /* if ( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) ) */
        }

        success = 1U;
    }

    /** - Check if data have been lost:
     *     - no data lost, return 1
     *     - data lost, return 3
     */
    if( ( node->IF2MCTL & 0x4000U ) == 0x4000U )
    {
        success = 3U;
    }

    /**   @note The function canInit has to be called before this function can be used.\n
     *           The user is responsible to initialize the message box.
     */

    /* USER CODE BEGIN (11) */
    /* USER CODE END */

    return success;
}

/** @fn uint32 canGetID(canBASE_t *node, uint32 messageBox)
 *   @brief Gets the Message Box's ID
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] messageBox Message box number of CAN node:
 *              - canMESSAGE_BOX1: CAN message box 1
 *              - canMESSAGE_BOXn: CAN message box n [n: 1-64]
 *              - canMESSAGE_BOX64: CAN message box 64
 *   @param[out] data Pointer to store CAN RX data
 *   @return The function will return the ID of the message box.
 *
 *   This function gets the identifier of a CAN message box.
 *
 */
/* SourceId : CAN_SourceId_026 */
/* DesignId : CAN_DesignId_020 */
/* Requirements : HL_SR537 */
uint32 canGetID( canBASE_t * node, uint32 messageBox )
{
    uint32 msgBoxID = 0U;

    /** - Wait until IF2 is ready for use */
    while( ( node->IF2STAT & 0x80U ) == 0x80U )
    {
    } /* Wait */

    /** - Configure IF2 for
     *     - Message direction - Read
     *     - Data Read
     *     - Clears NewDat bit in the message object.
     */
    node->IF2CMD = 0x20U;

    /** - Copy message box number into IF2 */
    /*SAFETYMCUSW 93 S MR: 6.1,6.2,10.1,10.2,10.3,10.4 <APPROVED> "LDRA Tool issue" */
    node->IF2NO = ( uint8 ) messageBox;

    /** - Wait until data are copied into IF2 */
    while( ( node->IF2STAT & 0x80U ) == 0x80U )
    {
    } /* Wait */

    /* Read Message Box ID from Arbitration register. */
    msgBoxID = ( node->IF2ARB & 0x1FFFFFFFU );

    return msgBoxID;
}

/** @fn uint32 canUpdateID(canBASE_t *node, uint32 messageBox, uint32 msgBoxArbitVal)
 *   @brief Change CAN Message Box ID.
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] messageBox Message box number of CAN node:
 *              - canMESSAGE_BOX1: CAN message box 1
 *              - canMESSAGE_BOXn: CAN message box n [n: 1-64]
 *              - canMESSAGE_BOX64: CAN message box 64
 *	@param[in] msgBoxArbitVal (32 bit value):
 *				Bit 31 - Not used.
 *				Bit 30 - 0 - The 11-bit ("standard") identifier is used for this message
 *object. 1 - The 29-bit ("extended") identifier is used for this message object. Bit 29 -
 *0 - Direction = Receive 1 - Direction = Transmit Bit 28:0 - Message Identifier.
 *   @return
 *
 *
 *   This function changes the Identifier and other arbitration parameters of a CAN
 *Message Box.
 *
 */
/* SourceId : CAN_SourceId_027 */
/* DesignId : CAN_DesignId_021 */
/* Requirements : HL_SR538 */
void canUpdateID( canBASE_t * node, uint32 messageBox, uint32 msgBoxArbitVal )
{
    /** - Wait until IF2 is ready for use */
    while( ( node->IF2STAT & 0x80U ) == 0x80U )
    {
    } /* Wait */

    /** - Configure IF2 for
     *     - Message direction - Read
     *     - Data Read
     *     - Clears NewDat bit in the message object.
     */
    node->IF2CMD = 0xA0U;
    /* Copy passed value into the arbitration register. */
    node->IF2ARB &= 0x80000000U;
    node->IF2ARB |= ( msgBoxArbitVal & 0x7FFFFFFFU );

    /** - Update message box number. */
    /*SAFETYMCUSW 93 S MR: 6.1,6.2,10.1,10.2,10.3,10.4 <APPROVED> "LDRA Tool issue" */
    node->IF2NO = ( uint8 ) messageBox;

    /** - Wait until data are copied into IF2 */
    while( ( node->IF2STAT & 0x80U ) == 0x80U )
    {
    } /* Wait */
}

/* USER CODE BEGIN (12) */
/* USER CODE END */

/** @fn uint32 canSendRemoteFrame(canBASE_t *node, uint32 messageBox)
 *   @brief Transmits a CAN Remote Frame.
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] messageBox Message box number of CAN node:
 *              - canMESSAGE_BOX1: CAN message box 1
 *              - canMESSAGE_BOXn: CAN message box n [n: 1-64]
 *              - canMESSAGE_BOX64: CAN message box 64
 *   @param[in] data Pointer to CAN TX data
 *   @return The function will return:
 *           - 0: When the setup of Send Remote Frame from message box wasn't successful
 *           - 1: When the setup of Send Remote Frame from message box was successful
 *
 *   This function triggers Remote Frame Transmission from CAN message box.
 *   Note : Enable RTR must be set in the Message x Configuration in the GUI( x: 1 - 64)
 *
 */
/* SourceId : CAN_SourceId_028 */
/* DesignId : CAN_DesignId_022 */
/* Requirements : HL_SR531 */
uint32 canSendRemoteFrame( canBASE_t * node, uint32 messageBox )
{
    uint32 success = 0U;
    uint32 regIndex = ( messageBox - 1U ) >> 5U;
    uint32 bitIndex = 1U << ( ( messageBox - 1U ) & 0x1FU );

    /** - Check for pending message:
     *     - pending message, return 0
     *     - no pending message, start new transmission
     */
    if( ( node->TXRQx[ regIndex ] & bitIndex ) != 0U )
    {
        success = 0U;
    }

    else
    {
        /** - Wait until IF1 is ready for use */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware
         * Status check for execution sequence" */
        while( ( node->IF1STAT & 0x80U ) == 0x80U )
        {
        } /* Wait */

        /** - Request Transmission by setting TxRqst in message box */
        node->IF1CMD = ( uint8 ) 0x84U;

        /** - Trigger Remote Frame Transmit from message box */
        /*SAFETYMCUSW 93 S MR: 6.1,6.2,10.1,10.2,10.3,10.4 <APPROVED> "LDRA Tool issue" */
        node->IF1NO = ( uint8 ) messageBox;

        success = 1U;
    }

    /**   @note The function canInit has to be called before this function can be used.\n
     *           The user is responsible to initialize the message box.
     */
    return success;
}

/** @fn uint32 canFillMessageObjectData(canBASE_t *node, uint32 messageBox, const uint8 *
 * data)
 *   @brief Fills the Message Object with the data but does not initiate transmission.
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] messageBox Message box number of CAN node:
 *              - canMESSAGE_BOX1: CAN message box 1
 *              - canMESSAGE_BOXn: CAN message box n [n: 1-64]
 *              - canMESSAGE_BOX64: CAN message box 64
 *   @return The function will return:
 *           - 0: When the Fill up of the TX message box wasn't successful
 *           - 1: When the Fill up of the TX message box was successful
 *
 *   This function fills the Message Object with the data but does not initiate
 * transmission.
 *
 */
/* SourceId : CAN_SourceId_029 */
/* DesignId : CAN_DesignId_023 */
/* Requirements : HL_SR532 */
uint32 canFillMessageObjectData( canBASE_t * node, uint32 messageBox, const uint8 * data )
{
    uint32 i;
    uint32 success = 0U;
    uint32 regIndex = ( messageBox - 1U ) >> 5U;
    uint32 bitIndex = 1U << ( ( messageBox - 1U ) & 0x1FU );

    /** - Check for pending message:
     *     - pending message, return 0
     *     - no pending message, start new transmission
     */
    if( ( node->TXRQx[ regIndex ] & bitIndex ) != 0U )
    {
        success = 0U;
    }
    else
    {
        /** - Wait until IF1 is ready for use */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware
         * Status check for execution sequence" */
        while( ( node->IF1STAT & 0x80U ) == 0x80U )
        {
        } /* Wait */

        /** - Configure IF1 for
         *     - Message direction - Write
         *     - Data Update
         */
        node->IF1CMD = 0x83U;

        /** - Copy TX data into IF1 */
        for( i = 0U; i < 8U; i++ )
        {
#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            node->IF1DATx[ i ] = *data;
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
            data++;
#else
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            node->IF1DATx[ s_canByteOrder[ i ] ] = *data;
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
            data++;
#endif /* if ( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) ) */
        }

        /** - Copy TX data into message box */
        /*SAFETYMCUSW 93 S MR: 6.1,6.2,10.1,10.2,10.3,10.4 <APPROVED> "LDRA Tool issue" */
        node->IF1NO = ( uint8 ) messageBox;

        success = 1U;
    }

    return success;
}

/** @fn uint32 canIsTxMessagePending(canBASE_t *node, uint32 messageBox)
 *   @brief Gets Tx message box transmission status
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] messageBox Message box number of CAN node:
 *              - canMESSAGE_BOX1: CAN message box 1
 *              - canMESSAGE_BOXn: CAN message box n [n: 1-64]
 *              - canMESSAGE_BOX64: CAN message box 64
 *   @return The function will return the tx request flag
 *
 *   Checks to see if the Tx message box has a pending Tx request, returns
 *   0 is flag not set otherwise will return the Tx request flag itself.
 */
/* SourceId : CAN_SourceId_004 */
/* DesignId : CAN_DesignId_004 */
/* Requirements : HL_SR210 */
uint32 canIsTxMessagePending( canBASE_t * node, uint32 messageBox )
{
    uint32 flag;
    uint32 regIndex = ( messageBox - 1U ) >> 5U;
    uint32 bitIndex = 1U << ( ( messageBox - 1U ) & 0x1FU );

    /* USER CODE BEGIN (13) */
    /* USER CODE END */

    /** - Read Tx request register */
    flag = node->TXRQx[ regIndex ] & bitIndex;

    /* USER CODE BEGIN (14) */
    /* USER CODE END */

    return flag;
}

/* USER CODE BEGIN (15) */
/* USER CODE END */

/** @fn uint32 canIsRxMessageArrived(canBASE_t *node, uint32 messageBox)
 *   @brief Gets Rx message box reception status
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] messageBox Message box number of CAN node:
 *              - canMESSAGE_BOX1: CAN message box 1
 *              - canMESSAGE_BOXn: CAN message box n [n: 1-64]
 *              - canMESSAGE_BOX64: CAN message box 64
 *   @return The function will return the new data flag
 *
 *   Checks to see if the Rx message box has pending Rx data, returns
 *   0 is flag not set otherwise will return the Tx request flag itself.
 */
/* SourceId : CAN_SourceId_005 */
/* DesignId : CAN_DesignId_005 */
/* Requirements : HL_SR211 */
uint32 canIsRxMessageArrived( canBASE_t * node, uint32 messageBox )
{
    uint32 flag;
    uint32 regIndex = ( messageBox - 1U ) >> 5U;
    uint32 bitIndex = 1U << ( ( messageBox - 1U ) & 0x1FU );

    /* USER CODE BEGIN (16) */
    /* USER CODE END */

    /** - Read Tx request register */
    flag = node->NWDATx[ regIndex ] & bitIndex;

    /* USER CODE BEGIN (17) */
    /* USER CODE END */

    return flag;
}

/* USER CODE BEGIN (18) */
/* USER CODE END */

/** @fn uint32 canIsMessageBoxValid(canBASE_t *node, uint32 messageBox)
 *   @brief Checks if message box is valid
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] messageBox Message box number of CAN node:
 *              - canMESSAGE_BOX1: CAN message box 1
 *              - canMESSAGE_BOXn: CAN message box n [n: 1-64]
 *              - canMESSAGE_BOX64: CAN message box 64
 *   @return The function will return the new data flag
 *
 *   Checks to see if the message box is valid for operation, returns
 *   0 is flag not set otherwise will return the validation flag itself.
 */
/* SourceId : CAN_SourceId_006 */
/* DesignId : CAN_DesignId_006 */
/* Requirements : HL_SR212 */
uint32 canIsMessageBoxValid( canBASE_t * node, uint32 messageBox )
{
    uint32 flag;
    uint32 regIndex = ( messageBox - 1U ) >> 5U;
    uint32 bitIndex = 1U << ( ( messageBox - 1U ) & 0x1FU );

    /* USER CODE BEGIN (19) */
    /* USER CODE END */

    /** - Read Tx request register */
    flag = node->MSGVALx[ regIndex ] & bitIndex;

    /* USER CODE BEGIN (20) */
    /* USER CODE END */

    return flag;
}

/* USER CODE BEGIN (21) */
/* USER CODE END */

/** @fn uint32 canGetLastError(canBASE_t *node)
 *   @brief Gets last RX/TX-Error of CAN message traffic
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @return The function will return:
 *           - canERROR_OK (0): When no CAN error occurred
 *           - canERROR_STUFF (1): When a stuff error occurred on RX message
 *           - canERROR_FORMAT (2): When a form/format error occurred on RX message
 *           - canERROR_ACKNOWLEDGE (3): When a TX message wasn't acknowledged
 *           - canERROR_BIT1 (4): When a TX message monitored dominant level where
 * recessive is expected
 *           - canERROR_BIT0 (5): When a TX message monitored recessive level where
 * dominant is expected
 *           - canERROR_CRC (6): When a RX message has wrong CRC value
 *           - canERROR_NO (7): When no error occurred since last call of this function
 *
 *   This function returns the last occurred error code of an RX or TX message,
 *   since the last call of this function.
 *
 */
/* SourceId : CAN_SourceId_007 */
/* DesignId : CAN_DesignId_007 */
/* Requirements : HL_SR213 */
uint32 canGetLastError( canBASE_t * node )
{
    uint32 errorCode;

    /* USER CODE BEGIN (22) */
    /* USER CODE END */

    /** - Get last error code */
    errorCode = node->ES & 7U;

    /**   @note The function canInit has to be called before this function can be used. */

    /* USER CODE BEGIN (23) */
    /* USER CODE END */

    return errorCode;
}

/* USER CODE BEGIN (24) */
/* USER CODE END */

/** @fn uint32 canGetErrorLevel(canBASE_t *node)
 *   @brief Gets error level of a CAN node
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @return The function will return:
 *           - canLEVEL_ACTIVE (0x00): When RX- and TX error counters are below 96
 *           - canLEVEL_WARNING (0x40): When RX- or TX error counter are between 96 and
 * 127
 *           - canLEVEL_PASSIVE (0x20): When RX- or TX error counter are between 128 and
 * 255
 *           - canLEVEL_BUS_OFF (0x80): When RX- or TX error counter are above 255
 *
 *   This function returns the current error level of a CAN node.
 *
 */
/* SourceId : CAN_SourceId_008 */
/* DesignId : CAN_DesignId_008 */
/* Requirements : HL_SR214 */
uint32 canGetErrorLevel( canBASE_t * node )
{
    uint32 errorLevel;

    /* USER CODE BEGIN (25) */
    /* USER CODE END */

    /** - Get error level */
    errorLevel = node->ES & 0xE0U;

    /**   @note The function canInit has to be called before this function can be used. */

    /* USER CODE BEGIN (26) */
    /* USER CODE END */

    return errorLevel;
}

/* USER CODE BEGIN (27) */
/* USER CODE END */

/** @fn void canEnableErrorNotification(canBASE_t *node)
 *   @brief Enable error notification
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *
 *   This function will enable the notification for the reaching the error levels warning,
 * passive and bus off.
 */
/* SourceId : CAN_SourceId_009 */
/* DesignId : CAN_DesignId_009 */
/* Requirements : HL_SR215 */
void canEnableErrorNotification( canBASE_t * node )
{
    /* USER CODE BEGIN (28) */
    /* USER CODE END */

    node->CTL |= 8U;

    /**   @note The function canInit has to be called before this function can be used. */

    /* USER CODE BEGIN (29) */
    /* USER CODE END */
}

/* USER CODE BEGIN (30) */
/* USER CODE END */

/** @fn void canEnableStatusChangeNotification(canBASE_t *node)
 *   @brief Enable Status Change notification
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *
 *   This function will enable the notification for the status change RxOK, TxOK, PDA,
 * WakeupPnd Interrupt.
 */
/* SourceId : CAN_SourceId_030 */
/* DesignId : CAN_DesignId_024 */
/* Requirements : HL_SR533 */
void canEnableStatusChangeNotification( canBASE_t * node )
{
    node->CTL |= 4U;

    /**   @note The function canInit has to be called before this function can be used. */
}

/** @fn void canDisableStatusChangeNotification(canBASE_t *node)
 *   @brief Disable Status Change notification
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *
 *   This function will disable the notification for the status change RxOK, TxOK, PDA,
 * WakeupPnd Interrupt.
 */
/* SourceId : CAN_SourceId_031 */
/* DesignId : CAN_DesignId_025 */
/* Requirements : HL_SR534 */
void canDisableStatusChangeNotification( canBASE_t * node )
{
    node->CTL &= ~( uint32 ) ( 4U );

    /**   @note The function canInit has to be called before this function can be used. */
}

/* USER CODE BEGIN (31) */
/* USER CODE END */

/** @fn void canDisableErrorNotification(canBASE_t *node)
 *   @brief Disable error notification
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *
 *   This function will disable the notification for the reaching the error levels
 * warning, passive and bus off.
 */
/* SourceId : CAN_SourceId_010 */
/* DesignId : CAN_DesignId_010 */
/* Requirements : HL_SR216 */
void canDisableErrorNotification( canBASE_t * node )
{
    /* USER CODE BEGIN (32) */
    /* USER CODE END */

    node->CTL &= ~( uint32 ) ( 8U );

    /**   @note The function canInit has to be called before this function can be used. */

    /* USER CODE BEGIN (33) */
    /* USER CODE END */
}

/** @fn void canEnableloopback(canBASE_t *node, canloopBackType_t Loopbacktype)
 *   @brief Disable error notification
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] Loopbacktype Type of Loopback:
 *              - Internal_Lbk: Internal Loop Back
 *              - External_Lbk: External Loop Back
 *              - Internal_Silent_Lbk: Internal Loop Back with Silent mode.
 *
 *   This function will enable can loopback mode
 */
/* SourceId : CAN_SourceId_011 */
/* DesignId : CAN_DesignId_011 */
/* Requirements : HL_SR521 */
void canEnableloopback( canBASE_t * node, canloopBackType_t Loopbacktype )
{
    /* Enter Test Mode */
    node->CTL |= ( uint32 ) ( ( uint32 ) 1U << 7U );

    /* Configure Loopback */
    node->TEST |= ( uint32 ) Loopbacktype;

    /**   @note The function canInit has to be called before this function can be used. */
}

/** @fn void canDisableloopback(canBASE_t *node)
 *   @brief Disable error notification
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *
 *   This function will disable can loopback mode
 */
/* SourceId : CAN_SourceId_012 */
/* DesignId : CAN_DesignId_012 */
/* Requirements : HL_SR522 */
void canDisableloopback( canBASE_t * node )
{
    node->TEST &= ~( uint32 ) ( 0x00000118U );

    /* Exit Test Mode */
    node->CTL &= ~( uint32 ) ( ( uint32 ) 1U << 7U );

    /**   @note The function canInit has to be called before this function can be used. */
}

/** @fn void canIoSetDirection(canBASE_t *node,uint32 TxDir,uint32 RxDir)
 *   @brief Set Port Direction
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] TxDir - TX Pin direction
 *   @param[in] RxDir - RX Pin direction
 *
 *   Set the direction of CAN pins at runtime when configured as IO pins.
 */
/* SourceId : CAN_SourceId_013 */
/* DesignId : CAN_DesignId_013 */
/* Requirements : HL_SR217 */
void canIoSetDirection( canBASE_t * node, uint32 TxDir, uint32 RxDir )
{
    /* USER CODE BEGIN (34) */
    /* USER CODE END */

    node->TIOC = ( ( node->TIOC & 0xFFFFFFFBU ) | ( TxDir << 2U ) );
    node->RIOC = ( ( node->RIOC & 0xFFFFFFFBU ) | ( RxDir << 2U ) );

    /* USER CODE BEGIN (35) */
    /* USER CODE END */
}

/** @fn void canIoSetPort(canBASE_t *node, uint32 TxValue, uint32 RxValue)
 *   @brief Write Port Value
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *   @param[in] TxValue - TX Pin value 0 or 1
 *   @param[in] RxValue - RX Pin value 0 or 1
 *
 *   Writes a value to TX and RX pin of a given CAN module when configured as IO pins.
 */
/* SourceId : CAN_SourceId_014 */
/* DesignId : CAN_DesignId_014 */
/* Requirements : HL_SR218 */
void canIoSetPort( canBASE_t * node, uint32 TxValue, uint32 RxValue )
{
    /* USER CODE BEGIN (36) */
    /* USER CODE END */

    node->TIOC = ( ( node->TIOC & 0xFFFFFFFDU ) | ( TxValue << 1U ) );
    node->RIOC = ( ( node->RIOC & 0xFFFFFFFDU ) | ( RxValue << 1U ) );

    /* USER CODE BEGIN (37) */
    /* USER CODE END */
}

/** @fn uint32 canIoTxGetBit(canBASE_t *node)
 *   @brief Read TX Bit
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *
 *   Reads a the current value from the TX pin of the given CAN port
 */
/* SourceId : CAN_SourceId_015 */
/* DesignId : CAN_DesignId_015 */
/* Requirements : HL_SR219 */
uint32 canIoTxGetBit( canBASE_t * node )
{
    /* USER CODE BEGIN (38) */
    /* USER CODE END */

    return ( node->TIOC & 1U );
}

/** @fn uint32 canIoRxGetBit(canBASE_t *node)
 *   @brief Read RX Bit
 *   @param[in] node Pointer to CAN node:
 *              - canREG1: CAN1 node pointer
 *              - canREG2: CAN2 node pointer
 *              - canREG3: CAN3 node pointer
 *
 *   Reads a the current value from the RX pin of the given CAN port
 */
/* SourceId : CAN_SourceId_016 */
/* DesignId : CAN_DesignId_016 */
/* Requirements : HL_SR220 */
uint32 canIoRxGetBit( canBASE_t * node )
{
    /* USER CODE BEGIN (39) */
    /* USER CODE END */

    return ( node->RIOC & 1U );
}

/** @fn void can1GetConfigValue(can_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the CAN1 configuration registers
 *
 *    @param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *    @param[in] type:     whether initial or current value of the configuration registers
 * need to be stored
 *                        - InitialValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *                        - CurrentValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : CAN_SourceId_017 */
/* DesignId : CAN_DesignId_017 */
/* Requirements : HL_SR224 */
void can1GetConfigValue( can_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTL = CAN1_CTL_CONFIGVALUE;
        config_reg->CONFIG_ES = CAN1_ES_CONFIGVALUE;
        config_reg->CONFIG_BTR = CAN1_BTR_CONFIGVALUE;
        config_reg->CONFIG_TEST = CAN1_TEST_CONFIGVALUE;
        config_reg->CONFIG_ABOTR = CAN1_ABOTR_CONFIGVALUE;
        config_reg->CONFIG_INTMUX0 = CAN1_INTMUX0_CONFIGVALUE;
        config_reg->CONFIG_INTMUX1 = CAN1_INTMUX2_CONFIGVALUE;
        config_reg->CONFIG_INTMUX2 = CAN1_INTMUX2_CONFIGVALUE;
        config_reg->CONFIG_INTMUX3 = CAN1_INTMUX3_CONFIGVALUE;
        config_reg->CONFIG_TIOC = CAN1_TIOC_CONFIGVALUE;
        config_reg->CONFIG_RIOC = CAN1_RIOC_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_CTL = canREG1->CTL;
        config_reg->CONFIG_ES = canREG1->ES;
        config_reg->CONFIG_BTR = canREG1->BTR;
        config_reg->CONFIG_TEST = canREG1->TEST;
        config_reg->CONFIG_ABOTR = canREG1->ABOTR;
        config_reg->CONFIG_INTMUX0 = canREG1->INTMUXx[ 0 ];
        config_reg->CONFIG_INTMUX1 = canREG1->INTMUXx[ 1 ];
        config_reg->CONFIG_INTMUX2 = canREG1->INTMUXx[ 2 ];
        config_reg->CONFIG_INTMUX3 = canREG1->INTMUXx[ 3 ];
        config_reg->CONFIG_TIOC = canREG1->TIOC;
        config_reg->CONFIG_RIOC = canREG1->RIOC;
    }
}

/** @fn void can2GetConfigValue(can_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the CAN2 configuration registers
 *
 *    @param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *    @param[in] type:     whether initial or current value of the configuration registers
 * need to be stored
 *                        - InitialValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *                        - CurrentValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : CAN_SourceId_018 */
/* DesignId : CAN_DesignId_017 */
/* Requirements : HL_SR224 */
void can2GetConfigValue( can_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTL = CAN2_CTL_CONFIGVALUE;
        config_reg->CONFIG_ES = CAN2_ES_CONFIGVALUE;
        config_reg->CONFIG_BTR = CAN2_BTR_CONFIGVALUE;
        config_reg->CONFIG_TEST = CAN2_TEST_CONFIGVALUE;
        config_reg->CONFIG_ABOTR = CAN2_ABOTR_CONFIGVALUE;
        config_reg->CONFIG_INTMUX0 = CAN2_INTMUX0_CONFIGVALUE;
        config_reg->CONFIG_INTMUX1 = CAN2_INTMUX2_CONFIGVALUE;
        config_reg->CONFIG_INTMUX2 = CAN2_INTMUX2_CONFIGVALUE;
        config_reg->CONFIG_INTMUX3 = CAN2_INTMUX3_CONFIGVALUE;
        config_reg->CONFIG_TIOC = CAN2_TIOC_CONFIGVALUE;
        config_reg->CONFIG_RIOC = CAN2_RIOC_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_CTL = canREG2->CTL;
        config_reg->CONFIG_ES = canREG2->ES;
        config_reg->CONFIG_BTR = canREG2->BTR;
        config_reg->CONFIG_TEST = canREG2->TEST;
        config_reg->CONFIG_ABOTR = canREG2->ABOTR;
        config_reg->CONFIG_INTMUX0 = canREG2->INTMUXx[ 0 ];
        config_reg->CONFIG_INTMUX1 = canREG2->INTMUXx[ 1 ];
        config_reg->CONFIG_INTMUX2 = canREG2->INTMUXx[ 2 ];
        config_reg->CONFIG_INTMUX3 = canREG2->INTMUXx[ 3 ];
        config_reg->CONFIG_TIOC = canREG2->TIOC;
        config_reg->CONFIG_RIOC = canREG2->RIOC;
    }
}

/** @fn void can3GetConfigValue(can_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the CAN3 configuration registers
 *
 *    @param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *    @param[in] type:     whether initial or current value of the configuration registers
 * need to be stored
 *                        - InitialValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *                        - CurrentValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : CAN_SourceId_019 */
/* DesignId : CAN_DesignId_017 */
/* Requirements : HL_SR224 */
void can3GetConfigValue( can_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTL = CAN3_CTL_CONFIGVALUE;
        config_reg->CONFIG_ES = CAN3_ES_CONFIGVALUE;
        config_reg->CONFIG_BTR = CAN3_BTR_CONFIGVALUE;
        config_reg->CONFIG_TEST = CAN3_TEST_CONFIGVALUE;
        config_reg->CONFIG_ABOTR = CAN3_ABOTR_CONFIGVALUE;
        config_reg->CONFIG_INTMUX0 = CAN3_INTMUX0_CONFIGVALUE;
        config_reg->CONFIG_INTMUX1 = CAN3_INTMUX2_CONFIGVALUE;
        config_reg->CONFIG_INTMUX2 = CAN3_INTMUX2_CONFIGVALUE;
        config_reg->CONFIG_INTMUX3 = CAN3_INTMUX3_CONFIGVALUE;
        config_reg->CONFIG_TIOC = CAN3_TIOC_CONFIGVALUE;
        config_reg->CONFIG_RIOC = CAN3_RIOC_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_CTL = canREG3->CTL;
        config_reg->CONFIG_ES = canREG3->ES;
        config_reg->CONFIG_BTR = canREG3->BTR;
        config_reg->CONFIG_TEST = canREG3->TEST;
        config_reg->CONFIG_ABOTR = canREG3->ABOTR;
        config_reg->CONFIG_INTMUX0 = canREG3->INTMUXx[ 0 ];
        config_reg->CONFIG_INTMUX1 = canREG3->INTMUXx[ 1 ];
        config_reg->CONFIG_INTMUX2 = canREG3->INTMUXx[ 2 ];
        config_reg->CONFIG_INTMUX3 = canREG3->INTMUXx[ 3 ];
        config_reg->CONFIG_TIOC = canREG3->TIOC;
        config_reg->CONFIG_RIOC = canREG3->RIOC;
    }
}
