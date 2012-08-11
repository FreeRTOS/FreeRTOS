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

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <board.h>
#include <pio/pio.h>
#include <utility/trace.h>
#include <aic/aic.h>
#include "can.h"

//------------------------------------------------------------------------------
//         Local definitions
//------------------------------------------------------------------------------
// CAN state
#define CAN_DISABLED       0
#define CAN_HALTED         1
#define CAN_IDLE           2
#define CAN_SENDING        3
#define CAN_RECEIVING      4

// MOT: Mailbox Object Type
#define CAN_MOT_DISABLE    0 // Mailbox is disabled
#define CAN_MOT_RECEPT     1 // Reception Mailbox
#define CAN_MOT_RECEPT_OW  2 // Reception mailbox with overwrite
#define CAN_MOT_TRANSMIT   3 // Transmit mailbox
#define CAN_MOT_CONSUMER   4 // Consumer mailbox
#define CAN_MOT_PRODUCER   5 // Producer mailbox

//------------------------------------------------------------------------------
//         Local variables
//------------------------------------------------------------------------------
#if defined (PINS_CAN_TRANSCEIVER_TXD)
static const Pin pins_can_transceiver_txd[] = {PINS_CAN_TRANSCEIVER_TXD};
#endif
#if defined (PINS_CAN_TRANSCEIVER_RXD)
static const Pin pins_can_transceiver_rxd[] = {PINS_CAN_TRANSCEIVER_RXD};
#endif
static const Pin pin_can_transceiver_rs   = PIN_CAN_TRANSCEIVER_RS;
#if defined (PIN_CAN_TRANSCEIVER_RXEN)
static const Pin pin_can_transceiver_rxen = PIN_CAN_TRANSCEIVER_RXEN;
#endif

static CanTransfer *pCAN0Transfer=NULL;
#ifdef AT91C_BASE_CAN1
static CanTransfer *pCAN1Transfer=NULL;
#endif

//------------------------------------------------------------------------------
//         Local functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// CAN Error Detection
/// \param status     error type
/// \param can_number can nulber
//------------------------------------------------------------------------------
static void CAN_ErrorHandling( unsigned int status, unsigned char can_number)
{
    if( (status&AT91C_CAN_ERRA) ==  AT91C_CAN_ERRA) {
        trace_LOG( trace_ERROR, "-E- (CAN) CAN is in active Error Active mode\n\r");
    }
    else if( (status&AT91C_CAN_ERRP) ==  AT91C_CAN_ERRP) {
        trace_LOG( trace_ERROR, "-E- (CAN) CAN is in Error Passive mode\n\r");
    }
    else if( (status&AT91C_CAN_BOFF) ==  AT91C_CAN_BOFF) {
        trace_LOG( trace_ERROR, "-E- (CAN) CAN is in Buff Off mode\n\r");
        // CAN reset
        trace_LOG( trace_ERROR, "-E- (CAN) CAN%d reset\n\r", can_number);
        // CAN Controller Disable
        if (can_number == 0) {
            AT91C_BASE_CAN0->CAN_MR &= ~AT91C_CAN_CANEN;
            // CAN Controller Enable
            AT91C_BASE_CAN0->CAN_MR |= AT91C_CAN_CANEN;
        }
#ifdef AT91C_BASE_CAN1
        else if (can_number == 1) {
            AT91C_BASE_CAN1->CAN_MR &= ~AT91C_CAN_CANEN;
            // CAN Controller Enable
            AT91C_BASE_CAN1->CAN_MR |= AT91C_CAN_CANEN;
        }
#endif
    }

    // Error for Frame dataframe
    // CRC error
    if( (status&AT91C_CAN_CERR) ==  AT91C_CAN_CERR) {
        trace_LOG( trace_ERROR, "-E- (CAN) CRC Error\n\r");
    }
    // Bit-stuffing error
    else if( (status&AT91C_CAN_SERR) ==  AT91C_CAN_SERR) {
        trace_LOG( trace_ERROR, "-E- (CAN) Stuffing Error\n\r");
    }
    // Bit error
    else if( (status&AT91C_CAN_BERR) ==  AT91C_CAN_BERR) {
        trace_LOG( trace_ERROR, "-E- (CAN) Bit Error\n\r");
    }
    // Form error
    else if( (status&AT91C_CAN_FERR) ==  AT91C_CAN_FERR) {
        trace_LOG( trace_ERROR, "-E- (CAN) Form Error\n\r");
    }
    // Acknowledgment error
    else if( (status&AT91C_CAN_AERR) ==  AT91C_CAN_AERR) {
        trace_LOG( trace_ERROR, "-E- (CAN) Acknowledgment Error\n\r");
    }

    // Error interrupt handler
    // Represent the current status of the CAN bus and are not latched.
    // See CAN, par. Error Interrupt Handler
    // AT91C_CAN_WARN
    // AT91C_CAN_ERRA
}

//------------------------------------------------------------------------------
// Generic CAN Interrupt handler
/// \param can_number can nulber
//------------------------------------------------------------------------------
static void CAN_Handler( unsigned char can_number ) 
{
    AT91PS_CAN base_can;
    AT91PS_CAN_MB CAN_Mailbox;

    unsigned int status;
    unsigned int can_msr;
    unsigned int* pCan_mcr;
    unsigned int message_mode;
    unsigned char numMailbox;
    unsigned char state0;
    unsigned char state1;

    if( can_number == 0 ) {
        base_can = AT91C_BASE_CAN0;
        CAN_Mailbox = AT91C_BASE_CAN0_MB0;
        state0 = pCAN0Transfer->state;
    }
#ifdef AT91C_BASE_CAN1
    else {
        base_can = AT91C_BASE_CAN1;
        CAN_Mailbox = AT91C_BASE_CAN1_MB0;
        state1 = pCAN1Transfer->state;
    }
#endif
    status = (base_can->CAN_SR) & (base_can->CAN_IMR);
    base_can->CAN_IDR = status;

    trace_LOG( trace_DEBUG, "CAN0 status=0x%X\n\r", status);
    if(status & AT91C_CAN_WAKEUP) {
        if( can_number == 0 ) {
            pCAN0Transfer->test_can = AT91C_TEST_OK;
            pCAN0Transfer->state = CAN_IDLE;
        }
#ifdef AT91C_BASE_CAN1
        else {
            pCAN1Transfer->test_can = AT91C_TEST_OK;
            pCAN1Transfer->state = CAN_IDLE;
        }
#endif
    }
    // Mailbox event ?
    else if ((status&0x0000FFFF) != 0) {
        trace_LOG( trace_DEBUG, "Mailbox event\n\r");

        // Handle Mailbox interrupts
        for (numMailbox = 0; numMailbox < NUM_MAILBOX_MAX; numMailbox++) {

            can_msr = *(unsigned int*)((unsigned int)CAN_Mailbox+(unsigned int)(0x10+(0x20*numMailbox)));
            if ((AT91C_CAN_MRDY & can_msr) == AT91C_CAN_MRDY) {
                // Mailbox object type
                message_mode =  ((*(unsigned int*)((unsigned int)CAN_Mailbox+(unsigned int)(0x00+(0x20*numMailbox))))>>24)&0x7;
                trace_LOG( trace_DEBUG, "message_mode 0x%X\n\r", message_mode);
                trace_LOG( trace_DEBUG, "numMailbox 0x%X\n\r", numMailbox);

                if( message_mode == 0 ) {
                    trace_LOG( trace_ERROR, "-E-Error in MOT\n\r");
                }
                else if( ( message_mode == CAN_MOT_RECEPT ) 
                      || ( message_mode == CAN_MOT_RECEPT_OW ) 
                      || ( message_mode == CAN_MOT_PRODUCER ) ) {
                    trace_LOG( trace_DEBUG, "Mailbox is in RECEPTION\n\r");
                    trace_LOG( trace_DEBUG, "Length 0x%X\n\r", (can_msr>>16)&0xF);
                    trace_LOG( trace_DEBUG, "CAN_MB_MID 0x%X\n\r", ((*(unsigned int*)((unsigned int)CAN_Mailbox+(unsigned int)(0x08+(0x20*numMailbox)))&AT91C_CAN_MIDvA)>>18));

                    trace_LOG( trace_DEBUG, "can_number %d\n\r", can_number);
                    if( can_number == 0 ) {
                        //CAN_MB_MDLx
                        pCAN0Transfer->data_low_reg = 
                           (*(unsigned int*)((unsigned int)CAN_Mailbox+(unsigned int)(0x14+(0x20*numMailbox))));
                        //CAN_MB_MDHx
                        pCAN0Transfer->data_high_reg = 
                           (*(unsigned int*)((unsigned int)CAN_Mailbox+(unsigned int)(0x18+(0x20*numMailbox))));
                        pCAN0Transfer->size = (can_msr>>16)&0xF;
                        pCAN0Transfer->mailbox_number = numMailbox;
                        state0 = CAN_IDLE;
                    }
#ifdef AT91C_BASE_CAN1
                    else {
                        //CAN_MB_MDLx
                        pCAN1Transfer->data_low_reg = 
                           (*(unsigned int*)((unsigned int)CAN_Mailbox+(unsigned int)(0x14+(0x20*numMailbox))));
                        //CAN_MB_MDHx
                        pCAN1Transfer->data_high_reg = 
                           (*(unsigned int*)((unsigned int)CAN_Mailbox+(unsigned int)(0x18+(0x20*numMailbox))));
                        pCAN1Transfer->size = (can_msr>>16)&0xF;
                        pCAN1Transfer->mailbox_number = numMailbox;
                        state1 = CAN_IDLE;
                    }
#endif
                    // Message Data has been received
                    pCan_mcr = (unsigned int*)((unsigned int)CAN_Mailbox+0x1C+(0x20*numMailbox));
                    *pCan_mcr = AT91C_CAN_MTCR;

                }
                else {
                    trace_LOG( trace_DEBUG, "Mailbox is in TRANSMIT\n\r");
                    trace_LOG( trace_DEBUG, "Length 0x%X\n\r", (can_msr>>16)&0xF);
                    trace_LOG( trace_DEBUG, "can_number %d\n\r", can_number);
                    if( can_number == 0 ) {
                        state0 = CAN_IDLE;
                    }
                    else {
                        state1 = CAN_IDLE;
                    }
                }
            }
        }
        if( can_number == 0 ) {
            pCAN0Transfer->state = state0;
        }
#ifdef AT91C_BASE_CAN1
        else {
            pCAN1Transfer->state = state1;
        }
#endif
    }
    if ((status&0xFFCF0000) != 0) {
        CAN_ErrorHandling(status, 0);
    }
}

//------------------------------------------------------------------------------
/// CAN 0 Interrupt handler
//------------------------------------------------------------------------------
static void CAN0_Handler(void)
{
    CAN_Handler( 0 );
}

//------------------------------------------------------------------------------
/// CAN 1 Interrupt handler
//------------------------------------------------------------------------------
#if defined AT91C_BASE_CAN1
static void CAN1_Handler(void)
{
    CAN_Handler( 1 );
}
#endif

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Configure the corresponding mailbox
/// \param pTransfer can transfer structure
//------------------------------------------------------------------------------
void CAN_InitMailboxRegisters( CanTransfer *pTransfer )
{
    AT91PS_CAN    base_can;
    AT91PS_CAN_MB CAN_Mailbox;

    if( pTransfer->can_number == 0 ) {
        base_can = AT91C_BASE_CAN0;
        CAN_Mailbox = AT91C_BASE_CAN0_MB0;
    }
#ifdef AT91C_BASE_CAN1
    else {
        base_can = AT91C_BASE_CAN1;
        CAN_Mailbox = AT91C_BASE_CAN1_MB0;
    }
#endif
    CAN_Mailbox = (AT91PS_CAN_MB)((unsigned int)CAN_Mailbox+(unsigned int)(0x20*pTransfer->mailbox_number));

    pTransfer->mailbox_in_use |= 1<<(pTransfer->mailbox_number);
    // MailBox Control Register
    CAN_Mailbox->CAN_MB_MCR = 0x0;
    // MailBox Mode Register
    CAN_Mailbox->CAN_MB_MMR = 0x00;
    // CAN Message Acceptance Mask Register
    CAN_Mailbox->CAN_MB_MAM = pTransfer->acceptance_mask_reg;
    // MailBox ID Register
    // Disable the mailbox before writing to CAN_MIDx registers
    if( pTransfer->identifier != 0 ) {
        CAN_Mailbox->CAN_MB_MAM |= AT91C_CAN_MIDE;
        CAN_Mailbox->CAN_MB_MID = pTransfer->identifier;
    }
    else {
        CAN_Mailbox->CAN_MB_MAM &= ~AT91C_CAN_MIDE;
    }
    // MailBox Mode Register
    CAN_Mailbox->CAN_MB_MMR = pTransfer->mode_reg;
    // MailBox Data Low Register
    CAN_Mailbox->CAN_MB_MDL = pTransfer->data_low_reg;
    // MailBox Data High Register
    CAN_Mailbox->CAN_MB_MDH = pTransfer->data_high_reg;
    // MailBox Control Register
    CAN_Mailbox->CAN_MB_MCR = pTransfer->control_reg;
}

//------------------------------------------------------------------------------
/// Reset the MBx
//------------------------------------------------------------------------------
void CAN_ResetAllMailbox( void )
{
    unsigned char i;
  
#if defined (AT91C_BASE_CAN0_MB0)
    CAN_ResetTransfer( pCAN0Transfer );
    for( i=0; i<8; i++ ) {
        pCAN0Transfer->can_number = 0;
        pCAN0Transfer->mailbox_number = i;
        pCAN0Transfer->mode_reg = AT91C_CAN_MOT_DIS;
        pCAN0Transfer->acceptance_mask_reg = 0;
        pCAN0Transfer->identifier = 0;
        pCAN0Transfer->data_low_reg = 0x00000000;
        pCAN0Transfer->data_high_reg = 0x00000000;
        pCAN0Transfer->control_reg = 0x00000000;
        CAN_InitMailboxRegisters( pCAN0Transfer );
    }
#endif
#if defined (AT91C_BASE_CAN0_MB8)
    for( i=0; i<8; i++ ) {
        pCAN0Transfer->can_number = 0;
        pCAN0Transfer->mailbox_number = i+8;
        pCAN0Transfer->mode_reg = AT91C_CAN_MOT_DIS;
        pCAN0Transfer->acceptance_mask_reg = 0;
        pCAN0Transfer->identifier = 0;
        pCAN0Transfer->data_low_reg = 0x00000000;
        pCAN0Transfer->data_high_reg = 0x00000000;
        pCAN0Transfer->control_reg = 0x00000000;
        CAN_InitMailboxRegisters( pCAN0Transfer );
    }
#endif

#if defined (AT91C_BASE_CAN1_MB0)
    if( pCAN1Transfer != NULL ) {
        CAN_ResetTransfer( pCAN1Transfer );
        for( i=0; i<8; i++ ) {
            pCAN1Transfer->can_number = 1;
            pCAN1Transfer->mailbox_number = i;
            pCAN1Transfer->mode_reg = AT91C_CAN_MOT_DIS;
            pCAN1Transfer->acceptance_mask_reg = 0;
            pCAN1Transfer->identifier = 0;
            pCAN1Transfer->data_low_reg = 0x00000000;
            pCAN1Transfer->data_high_reg = 0x00000000;
            pCAN1Transfer->control_reg = 0x00000000;
            CAN_InitMailboxRegisters( pCAN1Transfer );
        }
    }
#endif
#if defined (AT91C_BASE_CAN1_MB8)
    if( pCAN1Transfer != NULL ) {
        for( i=0; i<8; i++ ) {
            pCAN1Transfer->can_number = 1;
            pCAN1Transfer->mailbox_number = i+8;
            pCAN1Transfer->mode_reg = AT91C_CAN_MOT_DIS;
            pCAN1Transfer->acceptance_mask_reg = 0;
            pCAN1Transfer->identifier = 0;
            pCAN1Transfer->data_low_reg = 0x00000000;
            pCAN1Transfer->data_high_reg = 0x00000000;
            pCAN1Transfer->control_reg = 0x00000000;
            CAN_InitMailboxRegisters( pCAN1Transfer );
        }
    }
#endif

}

//------------------------------------------------------------------------------
/// CAN reset Transfer descriptor
/// \param pTransfer can transfer structure
//------------------------------------------------------------------------------
void CAN_ResetTransfer( CanTransfer *pTransfer )
{
    pTransfer->state = CAN_IDLE;
    pTransfer->can_number = 0;
    pTransfer->mailbox_number = 0;
    pTransfer->test_can = 0;
    pTransfer->mode_reg = 0;
    pTransfer->acceptance_mask_reg = 0;
    pTransfer->identifier = 0;
    pTransfer->data_low_reg = 0;
    pTransfer->data_high_reg = 0;
    pTransfer->control_reg = 0;
    pTransfer->mailbox_in_use = 0;
    pTransfer->size = 0;
}

//------------------------------------------------------------------------------
/// Wait for CAN synchronisation
/// \return return 1 for good initialisation, otherwise return 0
//------------------------------------------------------------------------------
static unsigned char CAN_Synchronisation( void )
{
    unsigned int tick=0;

    trace_LOG( trace_INFO, "CAN_Synchronisation\n\r");

    pCAN0Transfer->test_can = AT91C_TEST_NOK;
#ifdef AT91C_BASE_CAN1
    if( pCAN1Transfer != NULL ) {
        pCAN1Transfer->test_can = AT91C_TEST_NOK;
    }
#endif
    // Enable CAN and Wait for WakeUp Interrupt
    AT91C_BASE_CAN0->CAN_IER = AT91C_CAN_WAKEUP;
    // CAN Controller Enable
    AT91C_BASE_CAN0->CAN_MR = AT91C_CAN_CANEN;
    // Enable Autobaud/Listen mode
    // dangerous, CAN not answer in this mode

     while( (pCAN0Transfer->test_can != AT91C_TEST_OK)
         && (tick < AT91C_CAN_TIMEOUT) ) {
        tick++;
    }
    if (tick == AT91C_CAN_TIMEOUT) {
        trace_LOG( trace_ERROR, "-E- CAN0 Initialisations FAILED\n\r");
        return 0;
    } else {
        trace_LOG( trace_INFO, "-I- CAN0 Initialisations Completed\n\r");
    }

#if defined AT91C_BASE_CAN1
    if( pCAN1Transfer != NULL ) {
        AT91C_BASE_CAN1->CAN_IER = AT91C_CAN_WAKEUP;
        // CAN Controller Enable
        AT91C_BASE_CAN1->CAN_MR = AT91C_CAN_CANEN;

        tick = 0;
        // Wait for WAKEUP flag raising <=> 11-recessive-bit were scanned by the transceiver
        while( ((pCAN1Transfer->test_can != AT91C_TEST_OK)) 
            && (tick < AT91C_CAN_TIMEOUT) ) {
            tick++;
        }

        if (tick == AT91C_CAN_TIMEOUT) {
            trace_LOG( trace_ERROR, "-E- CAN1 Initialisations FAILED\n\r");
            return 0;
        } else {
            trace_LOG( trace_INFO, "-I- CAN1 Initialisations Completed\n\r");
        }
    }
#endif
    return 1;
}

//------------------------------------------------------------------------------
/// Write a CAN transfer
/// \param pTransfer can transfer structure
/// \return return CAN_STATUS_SUCCESS if command passed, otherwise 
///         return CAN_STATUS_LOCKED
//------------------------------------------------------------------------------
unsigned char CAN_Write( CanTransfer *pTransfer )
{
    AT91PS_CAN base_can;

    if (pTransfer->state == CAN_RECEIVING)  {
        pTransfer->state = CAN_IDLE;
    }

    if (pTransfer->state != CAN_IDLE)  {
        return CAN_STATUS_LOCKED;
    }

    trace_LOG( trace_DEBUG, "CAN_Write\n\r");
    pTransfer->state = CAN_SENDING;
    if( pTransfer->can_number == 0 ) {
        base_can = AT91C_BASE_CAN0;
    }
#ifdef AT91C_BASE_CAN1
    else {
        base_can = AT91C_BASE_CAN1;
    }
#endif
    base_can->CAN_TCR = pTransfer->mailbox_in_use;
    base_can->CAN_IER = pTransfer->mailbox_in_use;

    return CAN_STATUS_SUCCESS;

}


//------------------------------------------------------------------------------
/// Read a CAN transfer
/// \param pTransfer can transfer structure
/// \return return CAN_STATUS_SUCCESS if command passed, otherwise 
///         return CAN_STATUS_LOCKED
//------------------------------------------------------------------------------
unsigned char CAN_Read( CanTransfer *pTransfer )
{
    AT91PS_CAN base_can;

    if (pTransfer->state != CAN_IDLE)  {
        return CAN_STATUS_LOCKED;
    }

    trace_LOG( trace_DEBUG, "CAN_Read\n\r");
    pTransfer->state = CAN_RECEIVING;


    if( pTransfer->can_number == 0 ) {
        base_can = AT91C_BASE_CAN0;
    }
#ifdef AT91C_BASE_CAN1
    else {
        base_can = AT91C_BASE_CAN1;
    }
#endif
    // enable interrupt
    base_can->CAN_IER = pTransfer->mailbox_in_use;

    return CAN_STATUS_SUCCESS;
}

//------------------------------------------------------------------------------
/// Test if CAN is in IDLE state
/// \param pTransfer can transfer structure
/// \return return 0 if CAN is in IDLE, otherwise return 1
//------------------------------------------------------------------------------
unsigned char CAN_IsInIdle( CanTransfer *pTransfer )
{
  return( pTransfer->state != CAN_IDLE );
}

//------------------------------------------------------------------------------
/// Basic CAN test without Interrupt
//------------------------------------------------------------------------------
void CAN_BasicTestSuiteWithoutInterrupt(void)
{
#if defined AT91C_BASE_CAN1
    unsigned int status;
    unsigned int tick=0;

    trace_LOG( trace_INFO, "Without Interrupt ");
    trace_LOG( trace_INFO, "CAN0 Mailbox 0 transmitting to CAN1 Mailbox 0\n\r");
    // Init CAN0 Mailbox 0, transmit
    CAN_ResetTransfer( pCAN0Transfer );
    pCAN0Transfer->can_number = 0;
    pCAN0Transfer->mailbox_number = 0;
    pCAN0Transfer->mode_reg = AT91C_CAN_MOT_TX | AT91C_CAN_PRIOR;
    pCAN0Transfer->acceptance_mask_reg = 0x00000000;
    pCAN0Transfer->identifier = AT91C_CAN_MIDvA & (0x07<<18);
    pCAN0Transfer->data_low_reg = 0x11223344;
    pCAN0Transfer->data_high_reg = 0x01234567;
    pCAN0Transfer->control_reg = (AT91C_CAN_MDLC & (0x8<<16));
    CAN_InitMailboxRegisters( pCAN0Transfer );

    // Init CAN1 Mailbox 0, receive, 
    CAN_ResetTransfer( pCAN1Transfer );
    pCAN1Transfer->can_number = 1;
    pCAN1Transfer->mailbox_number = 0;
    pCAN1Transfer->mode_reg = AT91C_CAN_MOT_RX;
    pCAN1Transfer->acceptance_mask_reg = AT91C_CAN_MIDvA | AT91C_CAN_MIDvB;
    pCAN1Transfer->identifier = AT91C_CAN_MIDvA & (0x07<<18);
    pCAN1Transfer->data_low_reg = 0x00000000;
    pCAN1Transfer->data_high_reg = 0x00000000;
    pCAN1Transfer->control_reg = 0x00000000;
    CAN_InitMailboxRegisters( pCAN1Transfer );

    // Transfer Request for Mailbox 0
    AT91C_BASE_CAN0->CAN_TCR = AT91C_CAN_MB0;

    tick = 0;
    do {
        // CAN Message Status Register
        status = AT91C_BASE_CAN0_MB0->CAN_MB_MSR;
    }
    while( !(status & AT91C_CAN_MRDY) && (++tick < AT91C_CAN_TIMEOUT) );

    if (tick == AT91C_CAN_TIMEOUT) {
        trace_LOG( trace_ERROR, "-E- Test FAILED\n\r");
    } 
    else {
        trace_LOG( trace_DEBUG, "-I- Transfer completed: CAN1 Mailbox 0 MRDY flag has raised\n\r");
        if( AT91C_BASE_CAN0_MB0->CAN_MB_MDL != AT91C_BASE_CAN1_MB0->CAN_MB_MDL ) {
            trace_LOG( trace_ERROR, "-E- Data Corrupted\n\r");
        }
        else if( AT91C_BASE_CAN0_MB0->CAN_MB_MDH != AT91C_BASE_CAN1_MB0->CAN_MB_MDH ) {
            trace_LOG( trace_ERROR, "-E- Data Corrupted\n\r");
        }
        else {
            trace_LOG( trace_INFO, "Test passed\n\r");
        }
    }

    CAN_ResetAllMailbox();

    trace_LOG( trace_INFO, "Without Interrupt ");
    trace_LOG( trace_INFO, "CAN0 Mailboxes 1 & 2 transmitting to CAN1 Mailbox 15\n\r");
    // Init CAN0 Mailbox 1, transmit
    CAN_ResetTransfer( pCAN0Transfer );
    pCAN0Transfer->can_number = 0;
    pCAN0Transfer->mailbox_number = 1;
    pCAN0Transfer->mode_reg = AT91C_CAN_MOT_TX | AT91C_CAN_PRIOR;
    pCAN0Transfer->acceptance_mask_reg = 0x00000000;
    pCAN0Transfer->identifier = AT91C_CAN_MIDvA & (0x09<<18);      // ID 9
    pCAN0Transfer->data_low_reg = 0xAABBCCDD;
    pCAN0Transfer->data_high_reg = 0xCAFEDECA;
    pCAN0Transfer->control_reg = (AT91C_CAN_MDLC & (0x8<<16)); // Mailbox Data Length Code
    CAN_InitMailboxRegisters( pCAN0Transfer );

    // Init CAN0 Mailbox 2, transmit
    pCAN0Transfer->can_number = 0;
    pCAN0Transfer->mailbox_number = 2;
    pCAN0Transfer->mode_reg = AT91C_CAN_MOT_TX | (AT91C_CAN_PRIOR-(1<<16));
    pCAN0Transfer->acceptance_mask_reg = 0x00000000;
    pCAN0Transfer->identifier = AT91C_CAN_MIDvA & (0x0A<<18);      // ID 10
    pCAN0Transfer->data_low_reg = 0x55667788;
    pCAN0Transfer->data_high_reg = 0x99AABBCC;
    pCAN0Transfer->control_reg = (AT91C_CAN_MDLC & (0x8<<16)); // Mailbox Data Length Code
    CAN_InitMailboxRegisters( pCAN0Transfer );

    // Init CAN1 Mailbox 15, reception with overwrite
    CAN_ResetTransfer( pCAN1Transfer );
    pCAN1Transfer->can_number = 1;
    pCAN1Transfer->mailbox_number = 15;
    pCAN1Transfer->mode_reg = AT91C_CAN_MOT_RXOVERWRITE;
    pCAN1Transfer->acceptance_mask_reg = 0;
    pCAN1Transfer->identifier = 0x0;
    pCAN1Transfer->data_low_reg = 0x00000000;
    pCAN1Transfer->data_high_reg = 0x00000000;
    pCAN1Transfer->control_reg = 0x00000000;
    CAN_InitMailboxRegisters( pCAN1Transfer );

    // Ask Transmissions on Mailbox 1 & 2 --> AT91C_CAN_MRDY & AT91C_CAN_MMI raises for Mailbox 15 CAN_MB_SR
    AT91C_BASE_CAN0->CAN_TCR = AT91C_CAN_MB1 | AT91C_CAN_MB2;
    
    // Wait for Last Transmit Mailbox
    tick = 0;
    do  {
        status = AT91C_BASE_CAN1_MB15->CAN_MB_MSR;
    }
    while( !(status & AT91C_CAN_MMI) && (++tick < AT91C_CAN_TIMEOUT) );

    if (tick == AT91C_CAN_TIMEOUT) {
    }
    else {
        trace_LOG( trace_DEBUG, "-I- Transfer completed: CAN1 Mailbox 15 MRDY and MMI flags have raised\n\r");
        if( AT91C_BASE_CAN0_MB1->CAN_MB_MDL != AT91C_BASE_CAN1_MB15->CAN_MB_MDL ) {
            trace_LOG( trace_ERROR, "-E- Data Corrupted\n\r");
        }
        else if( AT91C_BASE_CAN0_MB1->CAN_MB_MDH != AT91C_BASE_CAN1_MB15->CAN_MB_MDH ) {
            trace_LOG( trace_ERROR, "-E- Data Corrupted\n\r");
        }
        else {
            trace_LOG( trace_INFO, "Test passed\n\r");
        }
    }

    CAN_ResetAllMailbox();
    trace_LOG( trace_INFO, "Without Interrupt ");
    trace_LOG( trace_INFO, "CAN0 Mailboxes 1 & 2 transmitting to CAN1 Mailbox 15\n\r");
    // Init CAN0 Mailbox 1, transmit
    CAN_ResetTransfer( pCAN0Transfer );
    pCAN0Transfer->can_number = 0;
    pCAN0Transfer->mailbox_number = 1;
    pCAN0Transfer->mode_reg = AT91C_CAN_MOT_TX | AT91C_CAN_PRIOR;
    pCAN0Transfer->acceptance_mask_reg = 0x00000000;
    pCAN0Transfer->identifier = AT91C_CAN_MIDvA & (0x09<<18);      // ID 9
    pCAN0Transfer->data_low_reg = 0xAABBCCDD;
    pCAN0Transfer->data_high_reg = 0xCAFEDECA;
    pCAN0Transfer->control_reg = (AT91C_CAN_MDLC & (0x8<<16)); // Mailbox Data Length Code
    CAN_InitMailboxRegisters( pCAN0Transfer );

    // Init CAN0 Mailbox 2, transmit
    pCAN0Transfer->can_number = 0;
    pCAN0Transfer->mailbox_number = 2;
    pCAN0Transfer->mode_reg = AT91C_CAN_MOT_TX | (AT91C_CAN_PRIOR-(1<<16));
    pCAN0Transfer->acceptance_mask_reg = 0x00000000;
    pCAN0Transfer->identifier = AT91C_CAN_MIDvA & (0x0A<<18);      // ID 10
    pCAN0Transfer->data_low_reg = 0x55667788;
    pCAN0Transfer->data_high_reg = 0x99AABBCC;
    pCAN0Transfer->control_reg = (AT91C_CAN_MDLC & (0x8<<16)); // Mailbox Data Length Code
    CAN_InitMailboxRegisters( pCAN0Transfer );

    // Init CAN1 Mailbox 15, reception with overwrite
    CAN_ResetTransfer( pCAN1Transfer );
    pCAN1Transfer->can_number = 1;
    pCAN1Transfer->mailbox_number = 15;
    pCAN1Transfer->mode_reg = AT91C_CAN_MOT_RX;
    pCAN1Transfer->acceptance_mask_reg = 0;
    pCAN1Transfer->identifier = 0x0;
    pCAN1Transfer->data_low_reg = 0x00000000;
    pCAN1Transfer->data_high_reg = 0x00000000;
    pCAN1Transfer->control_reg = 0x00000000;
    CAN_InitMailboxRegisters( pCAN1Transfer );

    // Ask Transmissions on Mailbox 1 & 2 --> AT91C_CAN_MRDY & AT91C_CAN_MMI raises for Mailbox 15 CAN_MB_SR
    AT91C_BASE_CAN0->CAN_TCR = AT91C_CAN_MB1 | AT91C_CAN_MB2;
    
    // Wait for Last Transmit Mailbox
    tick = 0;
    do  {
        status = AT91C_BASE_CAN1_MB15->CAN_MB_MSR;
    }
    while( !(status & AT91C_CAN_MMI) && (++tick < AT91C_CAN_TIMEOUT) );

    if (tick == AT91C_CAN_TIMEOUT) {
    trace_LOG( trace_ERROR, "-E- Test FAILED\n\r");
    }
    else {
        trace_LOG( trace_DEBUG, "Transfer completed: CAN1 Mailbox 15 MRDY and MMI flags have raised\n\r");
        trace_LOG( trace_DEBUG, "MB_MDL: 0x%X\n\r", AT91C_BASE_CAN1_MB15->CAN_MB_MDL);
        trace_LOG( trace_DEBUG, "MB_MDLH: 0x%X\n\r", AT91C_BASE_CAN1_MB15->CAN_MB_MDH);
        if( AT91C_BASE_CAN0_MB2->CAN_MB_MDL != AT91C_BASE_CAN1_MB15->CAN_MB_MDL ) {
            trace_LOG( trace_ERROR, "-E- Data Corrupted\n\r");
        }
        else if( AT91C_BASE_CAN0_MB2->CAN_MB_MDH != AT91C_BASE_CAN1_MB15->CAN_MB_MDH ) {
            trace_LOG( trace_ERROR, "-E- Data Corrupted\n\r");
        }
        else {
            trace_LOG( trace_INFO, "Test passed\n\r");
        }
    }

    CAN_ResetAllMailbox();
    trace_LOG( trace_INFO, "Without Interrupt ");
    trace_LOG( trace_INFO, "CAN0 Mailbox 3 asking for CAN1 Mailbox 3 transmission\n\r");
    // Init CAN0 Mailbox 3, consumer mailbox
    // Sends a remote frame and waits for an answer
    CAN_ResetTransfer( pCAN0Transfer );
    pCAN0Transfer->can_number = 0;
    pCAN0Transfer->mailbox_number = 3;
    pCAN0Transfer->mode_reg = AT91C_CAN_MOT_CONSUMER | AT91C_CAN_PRIOR;
    pCAN0Transfer->acceptance_mask_reg = AT91C_CAN_MIDvA | AT91C_CAN_MIDvB;
    pCAN0Transfer->identifier = AT91C_CAN_MIDvA & (0x0B<<18);     // ID 11
    pCAN0Transfer->data_low_reg = 0x00000000;
    pCAN0Transfer->data_high_reg = 0x00000000;
    pCAN0Transfer->control_reg = 0x00000000;
    CAN_InitMailboxRegisters( pCAN0Transfer );

    // Init CAN1 Mailbox 3, porducer mailbox
    // Waits to receive a Remote Frame before sending its contents
    CAN_ResetTransfer( pCAN1Transfer );
    pCAN1Transfer->can_number = 1;
    pCAN1Transfer->mailbox_number = 3;
    pCAN1Transfer->mode_reg = AT91C_CAN_MOT_PRODUCER | AT91C_CAN_PRIOR;
    pCAN1Transfer->acceptance_mask_reg = 0;
    pCAN1Transfer->identifier = AT91C_CAN_MIDvA & (0x0B<<18);     // ID 11
    pCAN1Transfer->data_low_reg = 0xEEDDFF00;
    pCAN1Transfer->data_high_reg = 0x34560022;
    pCAN1Transfer->control_reg = (AT91C_CAN_MDLC & (0x8<<16));
    CAN_InitMailboxRegisters( pCAN1Transfer );

    // Ask Transmissions on Mailbox 3 --> AT91C_CAN_MRDY raises for Mailbox 3 CAN_MB_SR
    AT91C_BASE_CAN1->CAN_TCR = AT91C_CAN_MB3;
    AT91C_BASE_CAN0->CAN_TCR = AT91C_CAN_MB3;

    // Wait for Last Transmit Mailbox
    tick = 0;
    do  {
        status = AT91C_BASE_CAN0_MB3->CAN_MB_MSR;
    }
    while( !(status & AT91C_CAN_MRDY) && (++tick < AT91C_CAN_TIMEOUT) );

    if (tick == AT91C_CAN_TIMEOUT) {
        trace_LOG( trace_ERROR, "-E- Test FAILED\n\r");
    }
    else {
        trace_LOG( trace_DEBUG, "-I- Transfer Completed: CAN0 & CAN1 Mailboxes 3 MRDY flags have raised\n\r");
        if( AT91C_BASE_CAN0_MB3->CAN_MB_MDL != AT91C_BASE_CAN1_MB3->CAN_MB_MDL ) {
            trace_LOG( trace_ERROR, "-E- Data Corrupted\n\r");
        }
        else if( AT91C_BASE_CAN0_MB3->CAN_MB_MDH != AT91C_BASE_CAN1_MB3->CAN_MB_MDH ) {
            trace_LOG( trace_ERROR, "-E- Data Corrupted\n\r");
        }
        else {
            trace_LOG( trace_INFO, "Test passed\n\r");
        }
    }
#endif // AT91C_BASE_CAN1

  return;
}


//------------------------------------------------------------------------------
/// Disable CAN and enter in low power
//------------------------------------------------------------------------------
void CAN_disable( void )
{
    // Disable the interrupt on the interrupt controller
    AIC_DisableIT(AT91C_ID_CAN0);
    // disable all IT
    AT91C_BASE_CAN0->CAN_IDR = 0x1FFFFFFF;
#if defined AT91C_BASE_CAN1
    AIC_DisableIT(AT91C_ID_CAN1);
    // disable all IT
    AT91C_BASE_CAN1->CAN_IDR = 0x1FFFFFFF;
#endif

    // Enable Low Power mode
    AT91C_BASE_CAN0->CAN_MR |= AT91C_CAN_LPM;

    // Disable CANs Transceivers
    // Enter standby mode
    PIO_Set(&pin_can_transceiver_rs);
#if defined (PIN_CAN_TRANSCEIVER_RXEN)
    // Enable ultra Low Power mode
    PIO_Clear(&pin_can_transceiver_rxen);
#endif

    // Disable clock for CAN PIO
    AT91C_BASE_PMC->PMC_PCDR = (1 << AT91C_ID_PIOA);

    // Disable the CAN0 controller peripheral clock
    AT91C_BASE_PMC->PMC_PCDR = (1 << AT91C_ID_CAN0);

}

//------------------------------------------------------------------------------
/// baudrate calcul
/// \param base_CAN CAN base address
/// \param baudrate Baudrate value
///                 allowed values: 1000, 800, 500, 250, 125, 50, 25, 10
/// \return return 1 in success, otherwise return 0
//------------------------------------------------------------------------------
unsigned char CAN_BaudRateCalculate( AT91PS_CAN   base_CAN, 
                                     unsigned int baudrate )
{
    unsigned int BRP;
    unsigned int PROPAG;
    unsigned int PHASE1;
    unsigned int PHASE2;
    unsigned int SJW;
    unsigned int t1t2;

    base_CAN->CAN_BR = 0;

    BRP = (BOARD_MCK / (baudrate*1000*16))-1;
    //trace_LOG( trace_DEBUG, "BRP = 0x%X\n\r", BRP);
    // timing Delay:
    // Delay Bus Driver: 50 ns
    // Delay Receiver:   30 ns
    // Delay Bus Line:  110 ns
    if( (16*baudrate*2*(50+30+110)/1000000) >= 1) {
        PROPAG = (16*baudrate*2*(50+30+110)/1000000)-1;
    }
    else {
        PROPAG = 0;
    }
    //trace_LOG( trace_DEBUG, "PROPAG = 0x%X\n\r", PROPAG);

    t1t2 = 15-(PROPAG+1);
    //trace_LOG( trace_DEBUG, "t1t2 = 0x%X\n\r", t1t2);

    if( (t1t2 & 0x01) == 0x01 ) {
        // ODD
        //trace_LOG( trace_DEBUG, "ODD\n\r");
        PHASE1 = ((t1t2-1)/2)-1;
        PHASE2 = PHASE1+1;
    }
    else {
        // EVEN
        //trace_LOG( trace_DEBUG, "EVEN\n\r");
        PHASE1 = (t1t2/2)-1;
        PHASE2 = PHASE1;
    }
    //trace_LOG( trace_DEBUG, "PHASE1 = 0x%X\n\r", PHASE1);
    //trace_LOG( trace_DEBUG, "PHASE2 = 0x%X\n\r", PHASE2);

    if( 1 > (4/(PHASE1+1)) ) {
        //trace_LOG( trace_DEBUG, "4*Tcsc\n\r");
        SJW = 3;
    }
    else {
        //trace_LOG( trace_DEBUG, "Tphs1\n\r");
        SJW = PHASE1;
    }
    //trace_LOG( trace_DEBUG, "SJW = 0x%X\n\r", SJW);
    // Verif
    if( BRP == 0 ) {
        trace_LOG( trace_DEBUG, "BRP = 0 is not authorized\n\r");
        return 0;
    }
    if( (PROPAG + PHASE1 + PHASE2) != 12 ) {
        trace_LOG( trace_DEBUG, "(PROPAG + PHASE1 + PHASE2) != 12\n\r");
        return 0;
    }
    base_CAN->CAN_BR = (AT91C_CAN_PHASE2 & (PHASE2 <<  0))
                     + (AT91C_CAN_PHASE1 & (PHASE1 <<  4))
                     + (AT91C_CAN_PROPAG & (PROPAG <<  8))
                     + (AT91C_CAN_SYNC   & (SJW << 12))
                     + (AT91C_CAN_BRP    & (BRP << 16))
                     + (AT91C_CAN_SMP    & (0 << 24));
    return 1;

}

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
/// Init of the CAN peripheral
/// \param baudrate Baudrate value
///                 allowed values: 1000, 800, 500, 250, 125, 50, 25, 10
/// \param canTransfer0 CAN0 structure transfer
/// \param canTransfer1 CAN1 structure transfer
/// \return return 1 if CAN has good baudrate and CAN is synchronized, 
///         otherwise return 0
//------------------------------------------------------------------------------
unsigned char CAN_Init( unsigned int baudrate, 
                        CanTransfer *canTransfer0, 
                        CanTransfer *canTransfer1 ) 
{
    unsigned char ret;

    // CAN Transmit Serial Data
#if defined (PINS_CAN_TRANSCEIVER_TXD)
    PIO_Configure(pins_can_transceiver_txd, PIO_LISTSIZE(pins_can_transceiver_txd));
#endif
#if defined (PINS_CAN_TRANSCEIVER_RXD)
    // CAN Receive Serial Data
    PIO_Configure(pins_can_transceiver_rxd, PIO_LISTSIZE(pins_can_transceiver_rxd));
#endif
    // CAN RS
    PIO_Configure(&pin_can_transceiver_rs, PIO_LISTSIZE(pin_can_transceiver_rs));
#if defined (PIN_CAN_TRANSCEIVER_RXEN)
    // CAN RXEN
    PIO_Configure(&pin_can_transceiver_rxen, PIO_LISTSIZE(pin_can_transceiver_rxen));
#endif

    // Enable clock for CAN PIO
    AT91C_BASE_PMC->PMC_PCER = (1 << AT91C_ID_PIOA);

    // Enable the CAN0 controller peripheral clock
    AT91C_BASE_PMC->PMC_PCER = (1 << AT91C_ID_CAN0);

    // disable all IT
    AT91C_BASE_CAN0->CAN_IDR = 0x1FFFFFFF;

    // Enable CANs Transceivers
#if defined (PIN_CAN_TRANSCEIVER_RXEN)
    // Disable ultra Low Power mode
    PIO_Set(&pin_can_transceiver_rxen);
#endif
    // Normal Mode (versus Standby mode)
    PIO_Clear(&pin_can_transceiver_rs);

    // Configure the AIC for CAN interrupts
    AIC_ConfigureIT(AT91C_ID_CAN0, AT91C_AIC_PRIOR_HIGHEST, CAN0_Handler);

    // Enable the interrupt on the interrupt controller
    AIC_EnableIT(AT91C_ID_CAN0);

    if( CAN_BaudRateCalculate(AT91C_BASE_CAN0, baudrate) == 0 ) {
        // Baudrate problem
        trace_LOG( trace_DEBUG, "Baudrate CAN0 problem\n\r");
        return 0;
    }

    pCAN0Transfer = canTransfer0;

#if defined AT91C_BASE_CAN1
    if( canTransfer1 != NULL ) {
        pCAN1Transfer = canTransfer1;
        // Enable CAN1 Clocks
        AT91C_BASE_PMC->PMC_PCER = (1 << AT91C_ID_CAN1);

        // disable all IT
        AT91C_BASE_CAN1->CAN_IDR = 0x1FFFFFFF;

        // Configure the AIC for CAN interrupts
        AIC_ConfigureIT(AT91C_ID_CAN1, AT91C_AIC_PRIOR_HIGHEST, CAN1_Handler);

        // Enable the interrupt on the interrupt controller
        AIC_EnableIT(AT91C_ID_CAN1);

        if( CAN_BaudRateCalculate(AT91C_BASE_CAN1, baudrate) == 0 ) {
            // Baudrate problem
            trace_LOG( trace_DEBUG, "Baudrate CAN1 problem\n\r");
            return 0;
        }
    }
#endif
    // Reset all mailbox
    CAN_ResetAllMailbox();

    // Enable the interrupt with all error cases
    AT91C_BASE_CAN0->CAN_IER =  AT91C_CAN_CERR  // (CAN) CRC Error
                             |  AT91C_CAN_SERR  // (CAN) Stuffing Error
                             |  AT91C_CAN_BERR  // (CAN) Bit Error
                             |  AT91C_CAN_FERR  // (CAN) Form Error
                             |  AT91C_CAN_AERR; // (CAN) Acknowledgment Error

#if defined AT91C_BASE_CAN1
    if( canTransfer1 != NULL ) {
        AT91C_BASE_CAN1->CAN_IER =  AT91C_CAN_CERR  // (CAN) CRC Error
                                 |  AT91C_CAN_SERR  // (CAN) Stuffing Error
                                 |  AT91C_CAN_BERR  // (CAN) Bit Error
                                 |  AT91C_CAN_FERR  // (CAN) Form Error
                                 |  AT91C_CAN_AERR; // (CAN) Acknowledgment Error
    }
#endif

    // Wait for CAN synchronisation
    if( CAN_Synchronisation( ) == 1 ) {
        ret = 1;
    }
    else {
        ret = 0;
    }

    return ret;
}

