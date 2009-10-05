/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _CAN_H
#define _CAN_H

//------------------------------------------------------------------------------
//      Definitions
//------------------------------------------------------------------------------
#define AT91C_CAN_TIMEOUT         100000

#define AT91C_TEST_NOK                 0
#define AT91C_TEST_OK                  1

#define CAN_STATUS_SUCCESS             0
#define CAN_STATUS_LOCKED              1
#define CAN_STATUS_ABORTED             2
#define CAN_STATUS_RESET               3

#if defined (AT91C_BASE_CAN)
    #define AT91C_BASE_CAN0      AT91C_BASE_CAN
#endif
#if defined (AT91C_ID_CAN)
    #define AT91C_ID_CAN0        AT91C_ID_CAN
#endif
#if defined (AT91C_BASE_CAN_MB0)
    #define AT91C_BASE_CAN0_MB0  AT91C_BASE_CAN_MB0
    #define AT91C_BASE_CAN0_MB1  AT91C_BASE_CAN_MB1
    #define AT91C_BASE_CAN0_MB2  AT91C_BASE_CAN_MB2
    #define AT91C_BASE_CAN0_MB3  AT91C_BASE_CAN_MB3
    #define AT91C_BASE_CAN0_MB4  AT91C_BASE_CAN_MB4
    #define AT91C_BASE_CAN0_MB5  AT91C_BASE_CAN_MB5
    #define AT91C_BASE_CAN0_MB6  AT91C_BASE_CAN_MB6
    #define AT91C_BASE_CAN0_MB7  AT91C_BASE_CAN_MB7
#endif
#if defined (AT91C_BASE_CAN_MB8)
    #define AT91C_BASE_CAN0_MB8   AT91C_BASE_CAN_MB8
    #define AT91C_BASE_CAN0_MB9   AT91C_BASE_CAN_MB9
    #define AT91C_BASE_CAN0_MB10  AT91C_BASE_CAN_MB10
    #define AT91C_BASE_CAN0_MB11  AT91C_BASE_CAN_MB11
    #define AT91C_BASE_CAN0_MB12  AT91C_BASE_CAN_MB12
    #define AT91C_BASE_CAN0_MB13  AT91C_BASE_CAN_MB13
    #define AT91C_BASE_CAN0_MB14  AT91C_BASE_CAN_MB14
    #define AT91C_BASE_CAN0_MB15  AT91C_BASE_CAN_MB15
#endif

#define NUM_MAILBOX_MAX 16

//------------------------------------------------------------------------------
//         Types
//------------------------------------------------------------------------------
typedef struct
{
    volatile unsigned char state;
    volatile unsigned char can_number;
    volatile unsigned char mailbox_number;
    volatile unsigned char test_can;
    volatile unsigned int  mode_reg;
    volatile unsigned int  acceptance_mask_reg;
    volatile unsigned int  identifier;
    volatile unsigned int  data_low_reg;
    volatile unsigned int  data_high_reg;
    volatile unsigned int  control_reg;
    volatile unsigned int  mailbox_in_use;
    volatile int           size;
} CanTransfer;

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------
extern unsigned char CAN_Init( unsigned int baudrate, 
                               CanTransfer *canTransferRead, 
                               CanTransfer *canTransferWrite );
extern void CAN_BasicTestSuite(void);
extern void CAN_disable( void );
extern void CAN_ResetAllMailbox( void );
extern void CAN_ResetTransfer( CanTransfer *pTransfer );
extern void CAN_InitMailboxRegisters( CanTransfer *pTransfer );
extern unsigned char CAN_IsInIdle( CanTransfer *pTransfer );

extern unsigned char CAN_Write( CanTransfer *pTransfer );
extern unsigned char CAN_Read( CanTransfer *pTransfer );

extern void CAN_BasicTestSuiteWithoutInterrupt( void );
extern unsigned char CAN_IsInIdle( CanTransfer *pTransfer );
#endif // _CAN_H

