/** @file sci.c
 *   @brief SCI Driver Implementation File
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
#include <string.h>
/* USER CODE END */

#include "sci.h"
#include "sys_vim.h"
#include "math.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @struct g_sciTransfer
 *   @brief Interrupt mode globals
 *
 */
static volatile struct g_sciTransfer
{
    uint32 mode;      /* Used to check for TX interrupt Enable */
    uint32 tx_length; /* Transmit data length in number of Bytes */
    uint32 rx_length; /* Receive data length in number of Bytes */
    uint8 * tx_data;  /* Transmit data pointer */
    uint8 * rx_data;  /* Receive data pointer */
} g_sciTransfer_t[ 4U ];

/* SourceId : SCI_SourceId_001 */
/* DesignId : SCI_DesignId_001 */
/* Requirements : CONQ_SCI_SR5  */

/** @fn void sciInit(void)
 *   @brief Initializes the SCI Driver
 *
 *   This function initializes the SCI module.
 */
void sciInit( void )
{
    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    /** @b initialize @b SCI3 */

    /** - bring SCI3 out of reset */
    sciREG3->GCR0 = 0U;
    sciREG3->GCR0 = 1U;

    /** - Disable all interrupts */
    sciREG3->CLEARINT = 0xFFFFFFFFU;
    sciREG3->CLEARINTLVL = 0xFFFFFFFFU;

    /** - global control 1 */
    sciREG3->GCR1 = ( uint32 ) ( ( uint32 ) 1U << 25U ) /* enable transmit */
                  | ( uint32 ) ( ( uint32 ) 1U << 24U ) /* enable receive */
                  | ( uint32 ) ( ( uint32 ) 1U << 5U )  /* internal clock (device has no
                                                           clock pin) */
                  | ( uint32 ) ( ( uint32 ) ( 2U - 1U ) << 4U ) /* number of stop bits */
                  | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* even parity, otherwise odd */
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* enable parity */
                  | ( uint32 ) ( ( uint32 ) 1U << 1U ); /* asynchronous timing mode */

    /** - set baudrate */
    sciREG3->BRS = 40U; /* baudrate */

    /** - transmission length */
    sciREG3->FORMAT = 8U - 1U; /* length */

    /** - set SCI3 pins functional mode */
    sciREG3->PIO0 = ( uint32 ) ( ( uint32 ) 1U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 1U << 1U ); /* rx pin */

    /** - set SCI3 pins default output value */
    sciREG3->PIO3 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI3 pins output direction */
    sciREG3->PIO1 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI3 pins open drain enable */
    sciREG3->PIO6 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI3 pins pullup/pulldown enable */
    sciREG3->PIO7 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI3 pins pullup/pulldown select */
    sciREG3->PIO8 = ( uint32 ) ( ( uint32 ) 1U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 1U << 1U ); /* rx pin */

    /** - set interrupt level */
    sciREG3->SETINTLVL = ( uint32 ) ( ( uint32 ) 0U << 26U ) /* Framing error */
                       | ( uint32 ) ( ( uint32 ) 0U << 25U ) /* Overrun error */
                       | ( uint32 ) ( ( uint32 ) 0U << 24U ) /* Parity error */
                       | ( uint32 ) ( ( uint32 ) 0U << 9U )  /* Receive */
                       | ( uint32 ) ( ( uint32 ) 0U << 8U )  /* Transmit */
                       | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Wakeup */
                       | ( uint32 ) ( ( uint32 ) 0U << 0U ); /* Break detect */

    /** - set interrupt enable */
    sciREG3->SETINT = ( uint32 ) ( ( uint32 ) 0U << 26U ) /* Framing error */
                    | ( uint32 ) ( ( uint32 ) 0U << 25U ) /* Overrun error */
                    | ( uint32 ) ( ( uint32 ) 0U << 24U ) /* Parity error */
                    | ( uint32 ) ( ( uint32 ) 0U << 9U )  /* Receive */
                    | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Wakeup */
                    | ( uint32 ) ( ( uint32 ) 0U << 0U ); /* Break detect */

    /** - initialize global transfer variables */
    g_sciTransfer_t[ 2U ].mode = ( uint32 ) 0U << 8U;
    g_sciTransfer_t[ 2U ].tx_length = 0U;
    g_sciTransfer_t[ 2U ].rx_length = 0U;

    /** - Finaly start SCI3 */
    sciREG3->GCR1 |= 0x80U;

    /** @b initialize @b SCI4 */

    /** - bring SCI4 out of reset */
    sciREG4->GCR0 = 0U;
    sciREG4->GCR0 = 1U;

    /** - Disable all interrupts */
    sciREG4->CLEARINT = 0xFFFFFFFFU;
    sciREG4->CLEARINTLVL = 0xFFFFFFFFU;

    /** - global control 1 */
    sciREG4->GCR1 = ( uint32 ) ( ( uint32 ) 1U << 25U ) /* enable transmit */
                  | ( uint32 ) ( ( uint32 ) 1U << 24U ) /* enable receive */
                  | ( uint32 ) ( ( uint32 ) 1U << 5U )  /* internal clock (device has no
                                                           clock pin) */
                  | ( uint32 ) ( ( uint32 ) ( 2U - 1U ) << 4U ) /* number of stop bits */
                  | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* even parity, otherwise odd */
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* enable parity */
                  | ( uint32 ) ( ( uint32 ) 1U << 1U ); /* asynchronous timing mode */

    /** - set baudrate */
    sciREG4->BRS = 40U; /* baudrate */

    /** - transmission length */
    sciREG4->FORMAT = 8U - 1U; /* length */

    /** - set SCI4 pins functional mode */
    sciREG4->PIO0 = ( uint32 ) ( ( uint32 ) 1U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 1U << 1U ); /* rx pin */

    /** - set SCI4 pins default output value */
    sciREG4->PIO3 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI4 pins output direction */
    sciREG4->PIO1 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI4 pins open drain enable */
    sciREG4->PIO6 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI4 pins pullup/pulldown enable */
    sciREG4->PIO7 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI4 pins pullup/pulldown select */
    sciREG4->PIO8 = ( uint32 ) ( ( uint32 ) 1U << 2U )  /* tx pin */
                  | ( uint32 ) ( ( uint32 ) 1U << 1U ); /* rx pin */

    /** - set interrupt level */
    sciREG4->SETINTLVL = ( uint32 ) ( ( uint32 ) 0U << 26U ) /* Framing error */
                       | ( uint32 ) ( ( uint32 ) 0U << 25U ) /* Overrun error */
                       | ( uint32 ) ( ( uint32 ) 0U << 24U ) /* Parity error */
                       | ( uint32 ) ( ( uint32 ) 0U << 9U )  /* Receive */
                       | ( uint32 ) ( ( uint32 ) 0U << 8U )  /* Transmit */
                       | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Wakeup */
                       | ( uint32 ) ( ( uint32 ) 0U << 0U ); /* Break detect */

    /** - set interrupt enable */
    sciREG4->SETINT = ( uint32 ) ( ( uint32 ) 0U << 26U ) /* Framing error */
                    | ( uint32 ) ( ( uint32 ) 0U << 25U ) /* Overrun error */
                    | ( uint32 ) ( ( uint32 ) 0U << 24U ) /* Parity error */
                    | ( uint32 ) ( ( uint32 ) 0U << 9U )  /* Receive */
                    | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Wakeup */
                    | ( uint32 ) ( ( uint32 ) 0U << 0U ); /* Break detect */

    /** - initialize global transfer variables */
    g_sciTransfer_t[ 3U ].mode = ( uint32 ) 0U << 8U;
    g_sciTransfer_t[ 3U ].tx_length = 0U;
    g_sciTransfer_t[ 3U ].rx_length = 0U;

    /** - Finaly start SCI4 */
    sciREG4->GCR1 |= 0x80U;

    /* USER CODE BEGIN (3) */
    /** @b initialize @b SCILIN */

    /** - bring SCI out of reset */
    scilinREG->GCR0 = 0U;
    scilinREG->GCR0 = 1U;

    /** - Disable all interrupts */
    scilinREG->CLEARINT = 0xFFFFFFFFU;
    scilinREG->CLEARINTLVL = 0xFFFFFFFFU;

    /** - global control 1 */
    scilinREG->GCR1 = ( uint32 ) ( ( uint32 ) 1U << 25U ) /* enable transmit */
                    | ( uint32 ) ( ( uint32 ) 1U << 24U ) /* enable receive */
                    | ( uint32 ) ( ( uint32 ) 1U << 5U )  /* internal clock (device has
                                                             no clock pin) */
                    | ( uint32 ) ( ( uint32 ) ( 2U - 1U ) << 4U ) /* number of stop bits
                                                                   */
                    | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* even parity, otherwise odd */
                    | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* enable parity */
                    | ( uint32 ) ( ( uint32 ) 1U << 1U ); /* asynchronous timing mode */

    /** - set baudrate */
    scilinREG->BRS = 40U; /* baudrate */

    /** - transmission length */
    scilinREG->FORMAT = 8U - 1U; /* length */

    /** - set SCI pins functional mode */
    scilinREG->PIO0 = ( uint32 ) ( ( uint32 ) 1U << 2U )  /* tx pin */
                    | ( uint32 ) ( ( uint32 ) 1U << 1U ); /* rx pin */

    /** - set SCI pins default output value */
    scilinREG->PIO3 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                    | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI pins output direction */
    scilinREG->PIO1 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                    | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI pins open drain enable */
    scilinREG->PIO6 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                    | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI pins pullup/pulldown enable */
    scilinREG->PIO7 = ( uint32 ) ( ( uint32 ) 0U << 2U )  /* tx pin */
                    | ( uint32 ) ( ( uint32 ) 0U << 1U ); /* rx pin */

    /** - set SCI pins pullup/pulldown select */
    scilinREG->PIO8 = ( uint32 ) ( ( uint32 ) 1U << 2U )  /* tx pin */
                    | ( uint32 ) ( ( uint32 ) 1U << 1U ); /* rx pin */

    /** - set interrupt level */
    scilinREG->SETINTLVL = ( uint32 ) ( ( uint32 ) 0U << 26U ) /* Framing error */
                         | ( uint32 ) ( ( uint32 ) 0U << 25U ) /* Overrun error */
                         | ( uint32 ) ( ( uint32 ) 0U << 24U ) /* Parity error */
                         | ( uint32 ) ( ( uint32 ) 0U << 9U )  /* Receive */
                         | ( uint32 ) ( ( uint32 ) 0U << 8U )  /* Transmit */
                         | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Wakeup */
                         | ( uint32 ) ( ( uint32 ) 0U );       /* Break detect */

    /** - set interrupt enable */
    scilinREG->SETINT = ( uint32 ) ( ( uint32 ) 0U << 26U ) /* Framing error */
                      | ( uint32 ) ( ( uint32 ) 0U << 25U ) /* Overrun error */
                      | ( uint32 ) ( ( uint32 ) 0U << 24U ) /* Parity error */
                      | ( uint32 ) ( ( uint32 ) 0U << 9U )  /* Receive */
                      | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Wakeup */
                      | ( uint32 ) ( ( uint32 ) 0U );       /* Break detect */

    /** - initialize global transfer variables */
    g_sciTransfer_t[ 1U ].mode = ( uint32 ) 0U << 8U;
    g_sciTransfer_t[ 1U ].tx_length = 0U;
    g_sciTransfer_t[ 1U ].rx_length = 0U;

    /** - Finaly start SCILIN */
    scilinREG->GCR1 |= 0x80U;
    /* USER CODE END */
}

/* SourceId : SCI_SourceId_002 */
/* DesignId : SCI_DesignId_002 */
/* Requirements : CONQ_SCI_SR6 */

/** @fn void sciSetFunctional(sciBASE_t *sci, uint32 port)
 *   @brief Change functional behavior of pins at runtime.
 *   @param[in] sci   - sci module base address
 *   @param[in] port  - Value to write to PIO0 register
 *
 *   Change the value of the PCPIO0 register at runtime, this allows to
 *   dynamically change the functionality of the SCI pins between functional
 *   and GIO mode.
 */
void sciSetFunctional( sciBASE_t * sci, uint32 port )
{
    /* USER CODE BEGIN (4) */
    /* USER CODE END */

    sci->PIO0 = port;

    /* USER CODE BEGIN (5) */
    /* USER CODE END */
}

/* SourceId : SCI_SourceId_003 */
/* DesignId : SCI_DesignId_003 */
/* Requirements : CONQ_SCI_SR7 */

/** @fn void sciSetBaudrate(sciBASE_t *sci, uint32 baud)
 *   @brief Change baudrate at runtime.
 *   @param[in] sci  - sci module base address
 *   @param[in] baud - baudrate in Hz
 *
 *   Change the SCI baudrate at runtime.
 */
void sciSetBaudrate( sciBASE_t * sci, uint32 baud )
{
    float64 vclk = 75.000 * 1000000.0;
    uint32 f = ( ( sci->GCR1 & 2U ) == 2U ) ? 16U : 1U;
    uint32 temp;
    float64 temp2;

    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    /*SAFETYMCUSW 96 S MR:6.1 <APPROVED> "Calculations including int and float cannot be
     * avoided" */
    temp = ( f * ( baud ) );
    temp2 = ( ( vclk ) / ( ( float64 ) temp ) ) - 1U;
    temp2 = temp2 + 0.5;
    sci->BRS = ( uint32 ) ( ( uint32 ) temp2 & 0x00FFFFFFU );

    /* USER CODE BEGIN (7) */
    /* USER CODE END */
}

/* SourceId : SCI_SourceId_004 */
/* DesignId : SCI_DesignId_004 */
/* Requirements : CONQ_SCI_SR8 */

/** @fn uint32 sciIsTxReady(sciBASE_t *sci)
 *   @brief Check if Tx buffer empty
 *   @param[in] sci - sci module base address
 *
 *   @return The TX ready flag
 *
 *   Checks to see if the Tx buffer ready flag is set, returns
 *   0 is flags not set otherwise will return the Tx flag itself.
 */
uint32 sciIsTxReady( sciBASE_t * sci )
{
    /* USER CODE BEGIN (8) */
    /* USER CODE END */

    return sci->FLR & ( uint32 ) SCI_TX_INT;
}

/* SourceId : SCI_SourceId_005 */
/* DesignId : SCI_DesignId_005 */
/* Requirements : CONQ_SCI_SR9 */

/** @fn void sciSendByte(sciBASE_t *sci, uint8 byte)
 *   @brief Send Byte
 *   @param[in] sci  - sci module base address
 *   @param[in] byte - byte to transfer
 *
 *   Sends a single byte in polling mode, will wait in the
 *   routine until the transmit buffer is empty before sending
 *   the byte.  Use sciIsTxReady to check for Tx buffer empty
 *   before calling sciSendByte to avoid waiting.
 */
void sciSendByte( sciBASE_t * sci, uint8 byte )
{
    /* USER CODE BEGIN (9) */
    /* USER CODE END */

    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware Status
     * check for execution sequence" */
    while( ( sci->FLR & ( uint32 ) SCI_TX_INT ) == 0U )
    {
    } /* Wait */

    sci->TD = byte;

    /* USER CODE BEGIN (10) */
    /* USER CODE END */
}

/* SourceId : SCI_SourceId_006 */
/* DesignId : SCI_DesignId_006 */
/* Requirements : CONQ_SCI_SR10 */

/** @fn void sciSend(sciBASE_t *sci, uint32 length, uint8 * data)
 *   @brief Send Data
 *   @param[in] sci    - sci module base address
 *   @param[in] length - number of data words to transfer
 *   @param[in] data   - pointer to data to send
 *
 *   Send a block of data pointed to by 'data' and 'length' bytes
 *   long.  If interrupts have been enabled the data is sent using
 *   interrupt mode, otherwise polling mode is used.  In interrupt
 *   mode transmission of the first byte is started and the routine
 *   returns immediately, sciSend must not be called again until the
 *   transfer is complete, when the sciNotification callback will
 *   be called.  In polling mode, sciSend will not return  until
 *   the transfer is complete.
 *
 *   @note if data word is less than 8 bits, then the data must be left
 *         aligned in the data byte.
 */
void sciSend( sciBASE_t * sci, uint32 length, uint8 * data )
{
    uint32 index = ( sci == sciREG1 )
                     ? 0U
                     : ( ( sci == sciREG2 ) ? 1U : ( ( sci == sciREG3 ) ? 2U : 3U ) );
    uint8 txdata;

    /* USER CODE BEGIN (11) */
    /* USER CODE END */
    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Mode variable is configured in
     * sciEnableNotification()" */
    if( ( g_sciTransfer_t[ index ].mode & ( uint32 ) SCI_TX_INT ) != 0U )
    {
        /* we are in interrupt mode */

        g_sciTransfer_t[ index ].tx_length = length;
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        g_sciTransfer_t[ index ].tx_data = data;

        /* start transmit by sending first byte */
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        txdata = *g_sciTransfer_t[ index ].tx_data;
        sci->TD = ( uint32 ) ( txdata );
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
        g_sciTransfer_t[ index ].tx_data++;
        sci->SETINT = ( uint32 ) SCI_TX_INT;
    }
    else
    {
        /* send the data */
        /*SAFETYMCUSW 30 S MR:12.2,12.3 <APPROVED> "Used for data count in
         * Transmit/Receive polling and Interrupt mode" */
        while( length > 0U )
        {
            /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found -
             * Hardware Status check for execution sequence" */
            while( ( sci->FLR & ( uint32 ) SCI_TX_INT ) == 0U )
            {
            } /* Wait */

            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            txdata = *data;
            sci->TD = ( uint32 ) ( txdata );
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
            data++;
            length--;
        }
    }

    /* USER CODE BEGIN (12) */
    /* USER CODE END */
}

/* SourceId : SCI_SourceId_007 */
/* DesignId : SCI_DesignId_007 */
/* Requirements : CONQ_SCI_SR11 */

/** @fn uint32 sciIsRxReady(sciBASE_t *sci)
 *   @brief Check if Rx buffer full
 *   @param[in] sci - sci module base address
 *
 *   @return The Rx ready flag
 *
 *   Checks to see if the Rx buffer full flag is set, returns
 *   0 is flags not set otherwise will return the Rx flag itself.
 */
uint32 sciIsRxReady( sciBASE_t * sci )
{
    /* USER CODE BEGIN (13) */
    /* USER CODE END */

    return sci->FLR & ( uint32 ) SCI_RX_INT;
}

/* SourceId : SCI_SourceId_008 */
/* DesignId : SCI_DesignId_008 */
/* Requirements : CONQ_SCI_SR12 */

/** @fn uint32 sciIsIdleDetected(sciBASE_t *sci)
 *   @brief Check if Idle Period is Detected
 *   @param[in] sci - sci module base address
 *
 *   @return The Idle flag
 *
 *   Checks to see if the SCI Idle flag is set, returns 0 is flags
 *   not set otherwise will return the Ilde flag itself.
 */
uint32 sciIsIdleDetected( sciBASE_t * sci )
{
    /* USER CODE BEGIN (14) */
    /* USER CODE END */

    return sci->FLR & ( uint32 ) SCI_IDLE;
}

/* SourceId : SCI_SourceId_009 */
/* DesignId : SCI_DesignId_009 */
/* Requirements : CONQ_SCI_SR13 */

/** @fn uint32 sciRxError(sciBASE_t *sci)
 *   @brief Return Rx Error flags
 *   @param[in] sci - sci module base address
 *
 *   @return The Rx error flags
 *
 *   Returns the Rx framing, overrun and parity errors flags,
 *   also clears the error flags before returning.
 */
uint32 sciRxError( sciBASE_t * sci )
{
    uint32 status = ( sci->FLR
                      & ( ( uint32 ) SCI_FE_INT | ( uint32 ) SCI_OE_INT
                          | ( uint32 ) SCI_PE_INT ) );

    /* USER CODE BEGIN (15) */
    /* USER CODE END */

    sci->FLR = ( ( uint32 ) SCI_FE_INT | ( uint32 ) SCI_OE_INT | ( uint32 ) SCI_PE_INT );
    return status;
}

/* SourceId : SCI_SourceId_010 */
/* DesignId : SCI_DesignId_010 */
/* Requirements : CONQ_SCI_SR14 */

/** @fn uint32 sciReceiveByte(sciBASE_t *sci)
 *   @brief Receive Byte
 *   @param[in] sci - sci module base address
 *
 *   @return Received byte
 *
 *    Receives a single byte in polling mode.  If there is
 *    not a byte in the receive buffer the routine will wait
 *    until one is received.   Use sciIsRxReady to check to
 *    see if the buffer is full to avoid waiting.
 */
uint32 sciReceiveByte( sciBASE_t * sci )
{
    /* USER CODE BEGIN (16) */
    /* USER CODE END */

    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware Status
     * check for execution sequence" */
    while( ( sci->FLR & ( uint32 ) SCI_RX_INT ) == 0U )
    {
    } /* Wait */

    return ( sci->RD & ( uint32 ) 0x000000FFU );
}

/* SourceId : SCI_SourceId_011 */
/* DesignId : SCI_DesignId_011 */
/* Requirements : CONQ_SCI_SR15 */

/** @fn void sciReceive(sciBASE_t *sci, uint32 length, uint8 * data)
 *   @brief Receive Data
 *   @param[in] sci    - sci module base address
 *   @param[in] length - number of data words to transfer
 *   @param[in] data   - pointer to data buffer to receive data
 *
 *   Receive a block of 'length' bytes long and place it into the
 *   data buffer pointed to by 'data'.  If interrupts have been
 *   enabled the data is received using interrupt mode, otherwise
 *   polling mode is used.  In interrupt mode receive is setup and
 *   the routine returns immediately, sciReceive must not be called
 *   again until the transfer is complete, when the sciNotification
 *   callback will be called.  In polling mode, sciReceive will not
 *   return  until the transfer is complete.
 */
void sciReceive( sciBASE_t * sci, uint32 length, uint8 * data )
{
    /* USER CODE BEGIN (17) */
    /* USER CODE END */

    if( ( sci->SETINT & ( uint32 ) SCI_RX_INT ) == ( uint32 ) SCI_RX_INT )
    {
        /* we are in interrupt mode */
        uint32 index = ( sci == sciREG1 )
                         ? 0U
                         : ( ( sci == sciREG2 ) ? 1U : ( ( sci == sciREG3 ) ? 2U : 3U ) );

        /* clear error flags */
        sci->FLR = ( ( uint32 ) SCI_FE_INT | ( uint32 ) SCI_OE_INT
                     | ( uint32 ) SCI_PE_INT );

        g_sciTransfer_t[ index ].rx_length = length;
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        g_sciTransfer_t[ index ].rx_data = data;
    }
    else
    {
        while( length > 0U )
        {
            /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found -
             * Hardware Status check for execution sequence" */
            while( ( sci->FLR & ( uint32 ) SCI_RX_INT ) == 0U )
            {
            } /* Wait */

            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            *data = ( uint8 ) ( sci->RD & 0x000000FFU );
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
            data++;
            length--;
        }
    }

    /* USER CODE BEGIN (18) */
    /* USER CODE END */
}

/* SourceId : SCI_SourceId_012 */
/* DesignId : SCI_DesignId_014 */
/* Requirements : CONQ_SCI_SR18 */

/** @fn void sciEnableLoopback(sciBASE_t *sci, loopBackType_t Loopbacktype)
 *   @brief Enable Loopback mode for self test
 *   @param[in] sci        - sci module base address
 *   @param[in] Loopbacktype  - Digital or Analog
 *
 *   This function enables the Loopback mode for self test.
 */
void sciEnableLoopback( sciBASE_t * sci, loopBackType_t Loopbacktype )
{
    /* USER CODE BEGIN (19) */
    /* USER CODE END */

    /* Clear Loopback incase enabled already */
    sci->IODFTCTRL = 0U;

    /* Enable Loopback either in Analog or Digital Mode */
    sci->IODFTCTRL = ( uint32 ) 0x00000A00U
                   | ( uint32 ) ( ( uint32 ) Loopbacktype << 1U );

    /* USER CODE BEGIN (20) */
    /* USER CODE END */
}

/* SourceId : SCI_SourceId_013 */
/* DesignId : SCI_DesignId_015 */
/* Requirements : CONQ_SCI_SR19 */

/** @fn void sciDisableLoopback(sciBASE_t *sci)
 *   @brief Enable Loopback mode for self test
 *   @param[in] sci        - sci module base address
 *
 *   This function disable the Loopback mode.
 */
void sciDisableLoopback( sciBASE_t * sci )
{
    /* USER CODE BEGIN (21) */
    /* USER CODE END */

    /* Disable Loopback Mode */
    sci->IODFTCTRL = 0x00000500U;

    /* USER CODE BEGIN (22) */
    /* USER CODE END */
}

/* SourceId : SCI_SourceId_014 */
/* DesignId : SCI_DesignId_012 */
/* Requirements : CONQ_SCI_SR16 */

/** @fn sciEnableNotification(sciBASE_t *sci, uint32 flags)
 *   @brief Enable interrupts
 *   @param[in] sci   - sci module base address
 *   @param[in] flags - Interrupts to be enabled, can be ored value of:
 *                      SCI_FE_INT    - framing error,
 *                      SCI_OE_INT    - overrun error,
 *                      SCI_PE_INT    - parity error,
 *                      SCI_RX_INT    - receive buffer ready,
 *                      SCI_TX_INT    - transmit buffer ready,
 *                      SCI_WAKE_INT  - wakeup,
 *                      SCI_BREAK_INT - break detect
 */
void sciEnableNotification( sciBASE_t * sci, uint32 flags )
{
    uint32 index = ( sci == sciREG1 )
                     ? 0U
                     : ( ( sci == sciREG2 ) ? 1U : ( ( sci == sciREG3 ) ? 2U : 3U ) );

    /* USER CODE BEGIN (23) */
    /* USER CODE END */

    g_sciTransfer_t[ index ].mode |= ( flags & ( uint32 ) SCI_TX_INT );
    sci->SETINT = ( flags & ( uint32 ) ( ~( uint32 ) ( SCI_TX_INT ) ) );

    /* USER CODE BEGIN (24) */
    /* USER CODE END */
}

/* SourceId : SCI_SourceId_015 */
/* DesignId : SCI_DesignId_013 */
/* Requirements : CONQ_SCI_SR17 */

/** @fn sciDisableNotification(sciBASE_t *sci, uint32 flags)
 *   @brief Disable interrupts
 *   @param[in] sci   - sci module base address
 *   @param[in] flags - Interrupts to be disabled, can be ored value of:
 *                      SCI_FE_INT    - framing error,
 *                      SCI_OE_INT    - overrun error,
 *                      SCI_PE_INT    - parity error,
 *                      SCI_RX_INT    - receive buffer ready,
 *                      SCI_TX_INT    - transmit buffer ready,
 *                      SCI_WAKE_INT  - wakeup,
 *                      SCI_BREAK_INT - break detect
 */
void sciDisableNotification( sciBASE_t * sci, uint32 flags )
{
    uint32 index = ( sci == sciREG1 )
                     ? 0U
                     : ( ( sci == sciREG2 ) ? 1U : ( ( sci == sciREG3 ) ? 2U : 3U ) );

    /* USER CODE BEGIN (25) */
    /* USER CODE END */

    g_sciTransfer_t[ index ].mode &= ( uint32 ) ( ~( flags & ( uint32 ) SCI_TX_INT ) );
    sci->CLEARINT = ( flags & ( uint32 ) ( ~( uint32 ) ( SCI_TX_INT ) ) );

    /* USER CODE BEGIN (26) */
    /* USER CODE END */
}

/* SourceId : SCI_SourceId_016 */
/* DesignId : SCI_DesignId_001 */
/* Requirements :   */

/** @fn sciEnterResetState(sciBASE_t *sci)
 *   @brief Enter reset state
 *   @param[in] sci   - sci module base address
 *   @note The SCI should only be configured while in reset state
 */
void sciEnterResetState( sciBASE_t * sci )
{
    sci->GCR1 &= 0xFFFFFF7FU;
}

/* SourceId : SCI_SourceId_017 */
/* DesignId : SCI_DesignId_001 */
/* Requirements :   */

/** @fn scixitResetState(sciBASE_t *sci)
 *   @brief Exit reset state
 *   @param[in] sci   - sci module base address
 *   @note The SCI should only be configured while in reset state
 */
void sciExitResetState( sciBASE_t * sci )
{
    sci->GCR1 |= 0x00000080U;
}

/* SourceId : SCI_SourceId_020 */
/* DesignId : SCI_DesignId_016 */
/* Requirements : CONQ_SCI_SR25 */

/** @fn void sci3GetConfigValue(sci_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the SCI3 configuration registers
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

void sci3GetConfigValue( sci_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_GCR0 = SCI3_GCR0_CONFIGVALUE;
        config_reg->CONFIG_GCR1 = SCI3_GCR1_CONFIGVALUE;
        config_reg->CONFIG_SETINT = SCI3_SETINT_CONFIGVALUE;
        config_reg->CONFIG_SETINTLVL = SCI3_SETINTLVL_CONFIGVALUE;
        config_reg->CONFIG_FORMAT = SCI3_FORMAT_CONFIGVALUE;
        config_reg->CONFIG_BRS = SCI3_BRS_CONFIGVALUE;
        config_reg->CONFIG_PIO0 = SCI3_PIO0_CONFIGVALUE;
        config_reg->CONFIG_PIO1 = SCI3_PIO1_CONFIGVALUE;
        config_reg->CONFIG_PIO6 = SCI3_PIO6_CONFIGVALUE;
        config_reg->CONFIG_PIO7 = SCI3_PIO7_CONFIGVALUE;
        config_reg->CONFIG_PIO8 = SCI3_PIO8_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Register read back support" */
        config_reg->CONFIG_GCR0 = sciREG3->GCR0;
        config_reg->CONFIG_GCR1 = sciREG3->GCR1;
        config_reg->CONFIG_SETINT = sciREG3->SETINT;
        config_reg->CONFIG_SETINTLVL = sciREG3->SETINTLVL;
        config_reg->CONFIG_FORMAT = sciREG3->FORMAT;
        config_reg->CONFIG_BRS = sciREG3->BRS;
        config_reg->CONFIG_PIO0 = sciREG3->PIO0;
        config_reg->CONFIG_PIO1 = sciREG3->PIO1;
        config_reg->CONFIG_PIO6 = sciREG3->PIO6;
        config_reg->CONFIG_PIO7 = sciREG3->PIO7;
        config_reg->CONFIG_PIO8 = sciREG3->PIO8;
    }
}

/* SourceId : SCI_SourceId_021 */
/* DesignId : SCI_DesignId_016 */
/* Requirements : CONQ_SCI_SR26 */

/** @fn void sci4GetConfigValue(sci_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the SCI4 configuration registers
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

void sci4GetConfigValue( sci_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_GCR0 = SCI4_GCR0_CONFIGVALUE;
        config_reg->CONFIG_GCR1 = SCI4_GCR1_CONFIGVALUE;
        config_reg->CONFIG_SETINT = SCI4_SETINT_CONFIGVALUE;
        config_reg->CONFIG_SETINTLVL = SCI4_SETINTLVL_CONFIGVALUE;
        config_reg->CONFIG_FORMAT = SCI4_FORMAT_CONFIGVALUE;
        config_reg->CONFIG_BRS = SCI4_BRS_CONFIGVALUE;
        config_reg->CONFIG_PIO0 = SCI4_PIO0_CONFIGVALUE;
        config_reg->CONFIG_PIO1 = SCI4_PIO1_CONFIGVALUE;
        config_reg->CONFIG_PIO6 = SCI4_PIO6_CONFIGVALUE;
        config_reg->CONFIG_PIO7 = SCI4_PIO7_CONFIGVALUE;
        config_reg->CONFIG_PIO8 = SCI4_PIO8_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Register read back support" */
        config_reg->CONFIG_GCR0 = sciREG4->GCR0;
        config_reg->CONFIG_GCR1 = sciREG4->GCR1;
        config_reg->CONFIG_SETINT = sciREG4->SETINT;
        config_reg->CONFIG_SETINTLVL = sciREG4->SETINTLVL;
        config_reg->CONFIG_FORMAT = sciREG4->FORMAT;
        config_reg->CONFIG_BRS = sciREG4->BRS;
        config_reg->CONFIG_PIO0 = sciREG4->PIO0;
        config_reg->CONFIG_PIO1 = sciREG4->PIO1;
        config_reg->CONFIG_PIO6 = sciREG4->PIO6;
        config_reg->CONFIG_PIO7 = sciREG4->PIO7;
        config_reg->CONFIG_PIO8 = sciREG4->PIO8;
    }
}

void sci_print( char * str )
{
    sciDisplayText( scilinREG, str, strlen( str ) );
}

void sciDisplayText( sciBASE_t * sci, char * text, uint32_t length )
{
    while( length-- )
    {
        /* Wait until we hit an idle state */
        while( ( sci->FLR & ( uint32_t ) SCI_IDLE ) == 4U )
        {
            /* Wait */
        }

        /* Send out text   */
        sciSendByte( sci, *text++ );
    }
}

void sciDisplayData( sciBASE_t * sci, uint8_t * text, uint32_t length )
{
    uint8_t txt = 0;
    uint8_t txt1 = 0;

#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )
    text = text + ( length - 1 );
#endif

    while( length-- )
    {
#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )
        txt = *text--;
#else
        txt = *text++;
#endif

        txt1 = txt;

        txt &= ~( 0xF0 );
        txt1 &= ~( 0x0F );
        txt1 = txt1 >> 4;

        if( txt <= 0x9 )
        {
            txt += 0x30;
        }
        else if( ( txt > 0x9 ) && ( txt < 0xF ) )
        {
            txt += 0x37;
        }
        else
        {
            txt = 0x30;
        }

        if( txt1 <= 0x9 )
        {
            txt1 += 0x30;
        }
        else if( ( txt1 > 0x9 ) && ( txt1 <= 0xF ) )
        {
            txt1 += 0x37;
        }
        else
        {
            txt1 = 0x30;
        }

        while( ( scilinREG->FLR & 0x4 ) == 4 ) /* wait until busy */
        {
        }

        sciSendByte( scilinREG, txt1 ); /* send out text   */

        while( ( scilinREG->FLR & 0x4 ) == 4 ) /* wait until busy */
        {
        }

        sciSendByte( scilinREG, txt ); /* send out text   */
    }
}

/* USER CODE BEGIN (45) */
/* USER CODE END */
