/** @file i2c.c
 *   @brief I2C Driver Implementation File
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

#include "i2c.h"
#include "sys_vim.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @struct g_i2CTransfer
 *   @brief Interrupt mode globals
 *
 */
static struct g_i2cTransfer
{
    uint32 mode;
    uint32 length;
    uint8 * data;
} g_i2cTransfer_t[ 2U ];

/* USER CODE BEGIN (2) */
/* USER CODE END */

/* SourceId : I2C_SourceId_001 */
/* DesignId : I2C_DesignId_001 */
/* Requirements : CONQ_I2C_SR5 */
/** @fn void i2cInit(void)
 *   @brief Initializes the i2c Driver
 *
 *   This function initializes the i2c module.
 */
void i2cInit( void )
{
    /* USER CODE BEGIN (3) */
    /* USER CODE END */
    /** @b initialize @b I2C1 */

    /** - i2c Enter reset */
    i2cREG1->MDR = ( uint32 ) ( ( uint32 ) 0U << 5U );

    /** - set i2c mode */
    i2cREG1->MDR = ( uint32 ) ( ( uint32 ) 0U << 15U ) /* nack mode  */
                 | ( uint32 ) ( ( uint32 ) 0U << 14U ) /* free running */
                 | ( uint32 ) ( ( uint32 ) 0U << 13U ) /* start condition - master mode
                                                          only */
                 | ( uint32 ) ( ( uint32 ) 1U << 11U ) /* stop condition   */
                 | ( uint32 ) ( ( uint32 ) 1U << 10U ) /* Master/Slave mode  */
                 | ( uint32 ) ( ( uint32 ) I2C_TRANSMITTER ) /* Transmitter/receiver */
                 | ( uint32 ) ( ( uint32 ) I2C_7BIT_AMODE )  /* xpanded address */
                 | ( uint32 ) ( ( uint32 ) 0U << 7U )        /* repeat mode */
                 | ( uint32 ) ( ( uint32 ) 0U << 6U )        /* digital loopback */
                 | ( uint32 ) ( ( uint32 ) 0U << 4U )   /* start byte - master only */
                 | ( uint32 ) ( ( uint32 ) 0U << 3U )   /* free data format */
                 | ( uint32 ) ( ( uint32 ) I2C_8_BIT ); /* bit count */

    /** - set i2c extended mode */
    i2cREG1->EMDR = ( uint32 ) 0U << 1U; /* Ignore Nack Enable/Disable */

    /** - set i2c Backward Compatibility mode */
    i2cREG1->EMDR |= 0U;

    /** - Disable DMA */
    i2cREG1->DMACR = 0x00U;

    /** - set i2c data count */
    i2cREG1->CNT = 8U;

    /** - disable all interrupts */
    i2cREG1->IMR = 0x00U;

    /** - set prescale */
    i2cREG1->PSC = 8U;

    /** - set clock rate */
    i2cREG1->CKH = 37U;
    i2cREG1->CKL = 37U;

    /** - set i2c pins functional mode */
    i2cREG1->PFNC = ( 0U );

    /** - set i2c pins default output value */
    i2cREG1->DOUT = ( uint32 ) ( ( uint32 ) 0U << 1U ) /* sda pin */
                  | ( uint32 ) ( 0U );                 /* scl pin */

    /** - set i2c pins output direction */
    i2cREG1->DIR = ( uint32 ) ( ( uint32 ) 0U << 1U ) /* sda pin */
                 | ( uint32 ) ( 0U );                 /* scl pin */

    /** - set i2c pins open drain enable */
    i2cREG1->PDR = ( uint32 ) ( ( uint32 ) 0U << 1U ) /* sda pin */
                 | ( uint32 ) ( 0U );                 /* scl pin */

    /** - set i2c pins pullup/pulldown enable */
    i2cREG1->PDIS = ( uint32 ) ( ( uint32 ) 0U << 1U ) /* sda pin */
                  | ( uint32 ) ( 0U );                 /* scl pin */

    /** - set i2c pins pullup/pulldown select */
    i2cREG1->PSEL = ( uint32 ) ( ( uint32 ) 1U << 1U ) /* sda pin */
                  | ( uint32 ) ( 1U );                 /* scl pin */

    /** - set interrupt enable */
    i2cREG1->IMR = ( uint32 ) ( ( uint32 ) 0U << 6U ) /* Address as slave interrupt   */
                 | ( uint32 ) ( ( uint32 ) 0U << 5U ) /* Stop Condition detect interrupt
                                                       */
                 | ( uint32 ) ( ( uint32 ) 0U << 4U ) /* Transmit data ready interrupt */
                 | ( uint32 ) ( ( uint32 ) 0U << 3U ) /* Receive data ready interrupt */
                 | ( uint32 ) ( ( uint32 ) 0U << 2U ) /* Register Access ready interrupt
                                                       */
                 | ( uint32 ) ( ( uint32 ) 0U << 1U ) /* No Acknowledgment interrupt */
                 | ( uint32 ) ( ( uint32 ) 0U ); /* Arbitration Lost interrupt      */

    i2cREG1->MDR |= ( uint32 ) I2C_RESET_OUT; /* i2c out of reset */

    /** - initialize global transfer variables */
    g_i2cTransfer_t[ 0U ].mode = ( uint32 ) 0U << 4U;
    g_i2cTransfer_t[ 0U ].length = 0U;

    /** @b initialize @b I2C2 */

    /** - i2c Enter reset */
    i2cREG2->MDR = ( uint32 ) ( ( uint32 ) 0U << 5U );

    /** - set i2c mode */
    i2cREG2->MDR = ( uint32 ) ( ( uint32 ) 0U << 15U ) /* nack mode  */
                 | ( uint32 ) ( ( uint32 ) 0U << 14U ) /* free running */
                 | ( uint32 ) ( ( uint32 ) 0U << 13U ) /* start condition - master mode
                                                          only */
                 | ( uint32 ) ( ( uint32 ) 1U << 11U ) /* stop condition   */
                 | ( uint32 ) ( ( uint32 ) 1U << 10U ) /* Master/Slave mode  */
                 | ( uint32 ) ( ( uint32 ) I2C_TRANSMITTER ) /* Transmitter/receiver */
                 | ( uint32 ) ( ( uint32 ) I2C_7BIT_AMODE )  /* Expanded address */
                 | ( uint32 ) ( ( uint32 ) 0 << 7U )         /* repeat mode */
                 | ( uint32 ) ( ( uint32 ) 0U << 6U )        /* digital loopback */
                 | ( uint32 ) ( ( uint32 ) 0U << 4U ) /* start byte - master only */
                 | ( uint32 ) ( ( uint32 ) 0U << 3U ) /* free data format */
                 | ( uint32 ) ( I2C_2_BIT );          /* bit count */

    /** - set i2c extended mode */
    i2cREG2->EMDR = ( uint32 ) 0U << 1U; /* Ignore Nack Enable/Disable */

    /** - set i2c Backward Compatibility mode */
    i2cREG2->EMDR |= 0U;

    /** - Disable DMA */
    i2cREG2->DMACR = 0x00U;

    /** - set i2c data count */
    i2cREG2->CNT = 8U;

    /** - disable all interrupts */
    i2cREG2->IMR = 0x00U;

    /** - set prescale */
    i2cREG2->PSC = 8U;

    /** - set clock rate */
    i2cREG2->CKH = 37U;
    i2cREG2->CKL = 37U;

    /** - set i2c pins functional mode */
    i2cREG2->PFNC = ( 0U );

    /** - set i2c pins default output value */
    i2cREG2->DOUT = ( uint32 ) ( ( uint32 ) 0U << 1U ) /* sda pin */
                  | ( uint32 ) ( 0U );                 /* scl pin */

    /** - set i2c pins output direction */
    i2cREG2->DIR = ( uint32 ) ( ( uint32 ) 0U << 1U ) /* sda pin */
                 | ( uint32 ) ( 0U );                 /* scl pin */

    /** - set i2c pins open drain enable */
    i2cREG2->PDR = ( uint32 ) ( ( uint32 ) 0U << 1U ) /* sda pin */
                 | ( uint32 ) ( 0U );                 /* scl pin */

    /** - set i2c pins pullup/pulldown enable */
    i2cREG2->PDIS = ( uint32 ) ( ( uint32 ) 0U << 1U ) /* sda pin */
                  | ( uint32 ) ( 0U );                 /* scl pin */

    /** - set i2c pins pullup/pulldown select */
    i2cREG2->PSEL = ( uint32 ) ( ( uint32 ) 1U << 1U ) /* sda pin */
                  | ( uint32 ) ( 1U );                 /* scl pin */

    /** - set interrupt enable */
    i2cREG2->IMR = ( uint32 ) ( ( uint32 ) 0U << 6U ) /* Address as slave interrupt   */
                 | ( uint32 ) ( ( uint32 ) 0U << 5U ) /* Stop Condition detect interrupt
                                                       */
                 | ( uint32 ) ( ( uint32 ) 0U << 4U ) /* Transmit data ready interrupt */
                 | ( uint32 ) ( ( uint32 ) 0U << 3U ) /* Receive data ready interrupt */
                 | ( uint32 ) ( ( uint32 ) 0U << 2U ) /* Register Access ready interrupt
                                                       */
                 | ( uint32 ) ( ( uint32 ) 0U << 1U ) /* No Acknowledgment interrupt */
                 | ( uint32 ) ( 0U ); /* Arbitration Lost interrupt      */

    i2cREG2->MDR |= ( uint32 ) I2C_RESET_OUT; /* i2c out of reset */

    /** - initialize global transfer variables */
    g_i2cTransfer_t[ 1U ].mode = ( uint32 ) 0U << 4U;
    g_i2cTransfer_t[ 1U ].length = 0U;

    /* USER CODE BEGIN (4) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_002 */
/* DesignId : I2C_DesignId_002 */
/* Requirements : CONQ_I2C_SR6 */
/** @fn void i2cSetOwnAdd(i2cBASE_t *i2c, uint32 oadd)
 *   @brief Set I2C Own Address
 *   @param[in] oadd - I2C Own address (7-bit or 10 -bit address)
 *   @param[in] i2c  - i2c module base address
 *   Set the Own address of the I2C module.
 */
void i2cSetOwnAdd( i2cBASE_t * i2c, uint32 oadd )
{
    i2c->OAR = oadd; /* set own address */
}

/* SourceId : I2C_SourceId_003 */
/* DesignId : I2C_DesignId_003 */
/* Requirements : CONQ_I2C_SR7 */
/** @fn void i2cSetSlaveAdd(i2cBASE_t *i2c, uint32 sadd)
 *   @brief Set Port Direction
 *   @param[in] sadd - I2C Slave address
 *   @param[in] i2c  - i2c module base address
 *   Set the Slave address to communicate which is must in Master mode.
 */
void i2cSetSlaveAdd( i2cBASE_t * i2c, uint32 sadd )
{
    i2c->SAR = sadd; /* set slave address */
}

/* SourceId : I2C_SourceId_004 */
/* DesignId : I2C_DesignId_004 */
/* Requirements : CONQ_I2C_SR8 */
/** @fn void i2cSetBaudrate(i2cBASE_t *i2c, uint32 baud)
 *   @brief Change baudrate at runtime.
 *   @param[in] i2c  - i2c module base address
 *   @param[in] baud - baudrate in KHz
 *
 *   Change the i2c baudrate at runtime. The I2C module needs to be taken to reset( nIRS=0
 * in I2CMDR) in order to change baud rate.
 */
void i2cSetBaudrate( i2cBASE_t * i2c, uint32 baud )
{
    uint32 prescale;
    uint32 d;
    uint32 ck;
    float64 vclk = 75.000F * 1000000.0F;
    float64 divider = 0.0F;
    uint32 temp = 0U;

    /* USER CODE BEGIN (5) */
    /* USER CODE END */

    divider = vclk / 8000000.0F;
    prescale = ( uint32 ) divider - 1U;

    if( prescale >= 2U )
    {
        d = 5U;
    }
    else
    {
        d = ( prescale != 0U ) ? 6U : 7U;
    }

    temp = 2U * baud * 1000U * ( prescale + 1U );
    divider = vclk / ( ( float64 ) temp );
    ck = ( uint32 ) divider - d;

    i2c->PSC = prescale;
    i2c->CKH = ck;
    i2c->CKL = ck;

    /* USER CODE BEGIN (6) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_005 */
/* DesignId : I2C_DesignId_015 */
/* Requirements : CONQ_I2C_SR20 */
/** @fn void i2cSetStart(i2cBASE_t *i2c)
 *   @brief Set i2c start condition
 *   @param[in] i2c  - i2c module base address
 *   Set i2c to generate a start bit (Only in Master mode)
 */
void i2cSetStart( i2cBASE_t * i2c )
{
    /* USER CODE BEGIN (7) */
    /* USER CODE END */

    i2c->MDR |= ( uint32 ) I2C_START_COND; /* set start condition */

    /* USER CODE BEGIN (8) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_006 */
/* DesignId : I2C_DesignId_016 */
/* Requirements : CONQ_I2C_SR21 */
/** @fn void i2cSetStop(i2cBASE_t *i2c)
 *   @brief Set i2c stop condition
 *   @param[in] i2c  - i2c module base address
 *   Set i2c to generate a stop bit (Only in Master mode)
 */
void i2cSetStop( i2cBASE_t * i2c )
{
    /* USER CODE BEGIN (9) */
    /* USER CODE END */

    i2c->MDR |= ( uint32 ) I2C_STOP_COND; /* generate stop condition */

    /* USER CODE BEGIN (10) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_007 */
/* DesignId : I2C_DesignId_017 */
/* Requirements : CONQ_I2C_SR22 */
/** @fn void i2cSetCount(i2cBASE_t *i2c,uint32 cnt)
 *   @brief Set i2c data count
 *   @param[in] i2c  - i2c module base address
 *   @param[in] cnt  - data count
 *   Set i2c count to a transfer value after which the stop condition needs to be
 * generated. (Only in Master Mode)
 */
void i2cSetCount( i2cBASE_t * i2c, uint32 cnt )
{
    /* USER CODE BEGIN (11) */
    /* USER CODE END */

    i2c->CNT = cnt; /* set i2c count  */

    /* USER CODE BEGIN (12) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_008 */
/* DesignId : I2C_DesignId_005 */
/* Requirements : CONQ_I2C_SR9 */
/** @fn uint32 i2cIsTxReady(i2cBASE_t *i2c)
 *   @brief Check if Tx buffer empty
 *   @param[in] i2c - i2c module base address
 *
 *   @return The TX ready flag
 *
 *   Checks to see if the Tx buffer ready flag is set, returns
 *   0 is flags not set otherwise will return the Tx flag itself.
 */
uint32 i2cIsTxReady( i2cBASE_t * i2c )
{
    /* USER CODE BEGIN (13) */
    /* USER CODE END */

    return i2c->STR & ( uint32 ) I2C_TX_INT;

    /* USER CODE BEGIN (14) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_009 */
/* DesignId : I2C_DesignId_006 */
/* Requirements : CONQ_I2C_SR10 */
/** @fn void i2cSendByte(i2cBASE_t *i2c, uint8 byte)
 *   @brief Send Byte
 *   @param[in] i2c  - i2c module base address
 *   @param[in] byte - byte to transfer
 *
 *   Sends a single byte in polling mode, will wait in the
 *   routine until the transmit buffer is empty before sending
 *   the byte.  Use i2cIsTxReady to check for Tx buffer empty
 *   before calling i2cSendByte to avoid waiting.
 */
void i2cSendByte( i2cBASE_t * i2c, uint8 byte )
{
    /* USER CODE BEGIN (15) */
    /* USER CODE END */

    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware Status
     * check for execution sequence" */
    while( ( i2c->STR & ( uint32 ) I2C_TX_INT ) == 0U )
    {
    } /* Wait */
    i2c->DXR = ( uint32 ) byte;

    /* USER CODE BEGIN (16) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_010 */
/* DesignId : I2C_DesignId_007 */
/* Requirements : CONQ_I2C_SR11 */
/** @fn void i2cSend(i2cBASE_t *i2c, uint32 length, uint8 * data)
 *   @brief Send Data
 *   @param[in] i2c    - i2c module base address
 *   @param[in] length - number of data words to transfer
 *   @param[in] data   - pointer to data to send
 *
 *   Send a block of data pointed to by 'data' and 'length' bytes
 *   long.  If interrupts have been enabled the data is sent using
 *   interrupt mode, otherwise polling mode is used.  In interrupt
 *   mode transmission of the first byte is started and the routine
 *   returns immediately, i2cSend must not be called again until the
 *   transfer is complete, when the i2cNotification callback will
 *   be called.  In polling mode, i2cSend will not return  until
 *   the transfer is complete.
 *
 *   @note if data word is less than 8 bits, then the data must be left
 *         aligned in the data byte.
 */
void i2cSend( i2cBASE_t * i2c, uint32 length, uint8 * data )
{
    uint32 index = i2c == i2cREG1 ? 0U : 1U;

    /* USER CODE BEGIN (17) */
    /* USER CODE END */

    if( ( g_i2cTransfer_t[ index ].mode & ( uint32 ) I2C_TX_INT ) != 0U )
    {
        /* we are in interrupt mode */
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        g_i2cTransfer_t[ index ].data = data;

        /* start transmit by sending first byte */
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        i2c->DXR = ( uint32 ) *g_i2cTransfer_t[ index ].data;
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        g_i2cTransfer_t[ index ].data++;
        /* Length -1 since one data is written already */
        g_i2cTransfer_t[ index ].length = ( length - 1U );
        /* Enable Transmit Interrupt */
        i2c->IMR |= ( uint32 ) I2C_TX_INT;
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
            while( ( i2c->STR & ( uint32 ) I2C_TX_INT ) == 0U )
            {
            } /* Wait */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            i2c->DXR = ( uint32 ) *data;
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            data++;
            length--;
        }
    }
    /* USER CODE BEGIN (18) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_011 */
/* DesignId : I2C_DesignId_008 */
/* Requirements : CONQ_I2C_SR12 */
/** @fn uint32 i2cIsRxReady(i2cBASE_t *i2c)
 *   @brief Check if Rx buffer full
 *   @param[in] i2c - i2c module base address
 *
 *   @return The Rx ready flag
 *
 *   Checks to see if the Rx buffer full flag is set, returns
 *   0 is flags not set otherwise will return the Rx flag itself.
 */
uint32 i2cIsRxReady( i2cBASE_t * i2c )
{
    /* USER CODE BEGIN (19) */
    /* USER CODE END */

    return i2c->STR & ( uint32 ) I2C_RX_INT;

    /* USER CODE BEGIN (20) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_012 */
/* DesignId : I2C_DesignId_023 */
/* Requirements : CONQ_I2C_SR13 */
/** @fn uint32 i2cIsStopDetected(i2cBASE_t *i2c)
 *   @brief Check if Stop Condition Detected
 *   @param[in] i2c - i2c module base address
 *
 *   @return The Stop Condition Detected flag
 *
 *   Checks to see if the Stop Condition Detected flag is set,
 *   returns 0 if flags not set otherwise will return the Stop
 *   Condition Detected flag itself.
 */
uint32 i2cIsStopDetected( i2cBASE_t * i2c )
{
    return i2c->STR & ( uint32 ) I2C_SCD_INT;
}

/* SourceId : I2C_SourceId_013 */
/* DesignId : I2C_DesignId_010 */
/* Requirements : CONQ_I2C_SR15 */
/** @fn uint32 i2cRxError(i2cBASE_t *i2c)
 *   @brief Return Rx Error flags
 *   @param[in] i2c - i2c module base address
 *
 *   @return The Rx error flags
 *
 *   Returns the Rx framing, overrun and parity errors flags,
 *   also clears the error flags before returning.
 */
uint32 i2cRxError( i2cBASE_t * i2c )
{
    uint32 status = i2c->STR & ( ( uint32 ) I2C_AL_INT | ( uint32 ) I2C_NACK_INT );

    /* USER CODE BEGIN (21) */
    /* USER CODE END */

    i2c->STR = ( uint32 ) ( ( uint32 ) I2C_AL_INT | ( uint32 ) I2C_NACK_INT );

    /* USER CODE BEGIN (22) */
    /* USER CODE END */

    return status;
}

/* SourceId : I2C_SourceId_014 */
/* DesignId : I2C_DesignId_009 */
/* Requirements : CONQ_I2C_SR14 */
/** @fn void i2cClearSCD(i2cBASE_t *i2c)
 *   @brief Clears the Stop condition detect flags.
 *   @param[in] i2c - i2c module base address
 *
 *   This function is called to clear the Stop condition detect(SCD) flag
 */
void i2cClearSCD( i2cBASE_t * i2c )
{
    /* USER CODE BEGIN (23) */
    /* USER CODE END */

    i2c->STR = ( uint32 ) I2C_SCD_INT;

    /* USER CODE BEGIN (24) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_015 */
/* DesignId : I2C_DesignId_011 */
/* Requirements : CONQ_I2C_SR16 */
/** @fn uint8 i2cReceiveByte(i2cBASE_t *i2c)
 *   @brief Receive Byte
 *   @param[in] i2c - i2c module base address
 *
 *   @return Received byte
 *
 *    Receives a single byte in polling mode.  If there is
 *    not a byte in the receive buffer the routine will wait
 *    until one is received.   Use i2cIsRxReady to check to
 *    see if the buffer is full to avoid waiting.
 */
uint8 i2cReceiveByte( i2cBASE_t * i2c )
{
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found - Hardware Status
     * check for execution sequence" */
    while( ( i2c->STR & ( uint32 ) I2C_RX_INT ) == 0U )
    {
    } /* Wait */
      /* USER CODE BEGIN (25) */
      /* USER CODE END */

    return ( ( uint8 ) i2c->DRR );
}

/* SourceId : I2C_SourceId_016 */
/* DesignId : I2C_DesignId_012 */
/* Requirements : CONQ_I2C_SR17 */
/** @fn void i2cReceive(i2cBASE_t *i2c, uint32 length, uint8 * data)
 *   @brief Receive Data
 *   @param[in] i2c    - i2c module base address
 *   @param[in] length - number of data words to transfer
 *   @param[in] data   - pointer to data buffer
 *
 *   Receive a block of 'length' bytes long and place it into the
 *   data buffer pointed to by 'data'.  If interrupts have been
 *   enabled the data is received using interrupt mode, otherwise
 *   polling mode is used.  In interrupt mode receive is setup and
 *   the routine returns immediately, i2cReceive must not be called
 *   again until the transfer is complete, when the i2cNotification
 *   callback will be called.  In polling mode, i2cReceive will not
 *   return  until the transfer is complete.
 */
void i2cReceive( i2cBASE_t * i2c, uint32 length, uint8 * data )
{
    uint32 index = i2c == i2cREG1 ? 0U : 1U;

    /* USER CODE BEGIN (26) */
    /* USER CODE END */
    if( ( i2c->IMR & ( uint32 ) I2C_RX_INT ) != 0U )
    {
        /* we are in interrupt mode */
        /* clear error flags */
        i2c->STR = ( uint32 ) I2C_AL_INT | ( uint32 ) I2C_NACK_INT;

        g_i2cTransfer_t[ index ].length = length;
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
         * allowed in this driver" */
        g_i2cTransfer_t[ index ].data = data;
    }
    else
    { /*SAFETYMCUSW 30 S MR:12.2,12.3 <APPROVED> "Used for data count in Transmit/Receive
         polling and Interrupt mode" */
        while( length > 0U )
        {
            /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Potentially infinite loop found -
             * Hardware Status check for execution sequence" */
            while( ( i2c->STR & ( uint32 ) I2C_RX_INT ) == 0U )
            {
            } /* Wait */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            *data = ( ( uint8 ) i2c->DRR );
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            data++;
            length--;
        }
    }

    /* USER CODE BEGIN (27) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_017 */
/* DesignId : I2C_DesignId_018 */
/* Requirements : CONQ_I2C_SR24 */
/** @fn void i2cEnableLoopback(i2cBASE_t *i2c)
 *   @brief Enable Loopback mode for self test
 *   @param[in] i2c        - i2c module base address
 *
 *   This function enables the Loopback mode for self test.
 */
void i2cEnableLoopback( i2cBASE_t * i2c )
{
    /* USER CODE BEGIN (28) */
    /* USER CODE END */

    /* enable digital loopback    */
    i2c->MDR |= ( ( uint32 ) 1U << 6U );

    /* USER CODE BEGIN (29) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_018 */
/* DesignId : I2C_DesignId_019 */
/* Requirements : CONQ_I2C_SR25 */
/** @fn void i2cDisableLoopback(i2cBASE_t *i2c)
 *   @brief Enable Loopback mode for self test
 *   @param[in] i2c        - i2c module base address
 *
 *   This function disable the Loopback mode.
 */
void i2cDisableLoopback( i2cBASE_t * i2c )
{
    /* USER CODE BEGIN (30) */
    /* USER CODE END */

    /* Disable Loopback Mode */
    i2c->MDR &= 0xFFFFFFBFU;

    /* USER CODE BEGIN (31) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_019 */
/* DesignId : I2C_DesignId_013 */
/* Requirements : CONQ_I2C_SR18 */
/** @fn i2cEnableNotification(i2cBASE_t *i2c, uint32 flags)
 *   @brief Enable interrupts
 *   @param[in] i2c   - i2c module base address
 *   @param[in] flags - Interrupts to be enabled, can be ored value of:
 *                      i2c_FE_INT    - framing error,
 *                      i2c_OE_INT    - overrun error,
 *                      i2c_PE_INT    - parity error,
 *                      i2c_RX_INT    - receive buffer ready,
 *                      i2c_TX_INT    - transmit buffer ready,
 *                      i2c_WAKE_INT  - wakeup,
 *                      i2c_BREAK_INT - break detect
 */
void i2cEnableNotification( i2cBASE_t * i2c, uint32 flags )
{
    uint32 index = i2c == i2cREG1 ? 0U : 1U;

    /* USER CODE BEGIN (32) */
    /* USER CODE END */

    g_i2cTransfer_t[ index ].mode |= ( flags & ( uint32 ) I2C_TX_INT );
    i2c->IMR = ( flags & ( uint32 ) ( ~( uint32 ) I2C_TX_INT ) );
}

/* SourceId : I2C_SourceId_020 */
/* DesignId : I2C_DesignId_014 */
/* Requirements : CONQ_I2C_SR19 */
/** @fn i2cDisableNotification(i2cBASE_t *i2c, uint32 flags)
 *   @brief Disable interrupts
 *   @param[in] i2c   - i2c module base address
 *   @param[in] flags - Interrupts to be disabled, can be ored value of:
 *                      i2c_FE_INT    - framing error,
 *                      i2c_OE_INT    - overrun error,
 *                      i2c_PE_INT    - parity error,
 *                      i2c_RX_INT    - receive buffer ready,
 *                      i2c_TX_INT    - transmit buffer ready,
 *                      i2c_WAKE_INT  - wakeup,
 *                      i2c_BREAK_INT - break detect
 */
void i2cDisableNotification( i2cBASE_t * i2c, uint32 flags )
{
    uint32 index = i2c == i2cREG1 ? 0U : 1U;
    uint32 int_mask;

    /* USER CODE BEGIN (33) */
    /* USER CODE END */

    g_i2cTransfer_t[ index ].mode &= ( uint32 ) ~( flags & ( uint32 ) I2C_TX_INT );
    int_mask = i2c->IMR & ( uint32 ) ( ~( uint32 ) ( flags | ( uint32 ) I2C_TX_INT ) );
    i2c->IMR = int_mask;
}

/* SourceId : I2C_SourceId_021 */
/* DesignId : I2C_DesignId_020 */
/* Requirements : CONQ_I2C_SR23 */
/** @fn i2cSetMode(i2cBASE_t *i2c, uint32 mode)
 *   @brief Sets Master or Slave mode.
 *   @param[in] i2c   - i2c module base address
 *   @param[in] mode  - Mode can be either:
 *                      I2C_MASTER    - Master Mode,
 *                      I2C_SLAVE     - Slave Mode
 */
void i2cSetMode( i2cBASE_t * i2c, uint32 mode )
{
    uint32 temp_mdr;
    /* USER CODE BEGIN (34) */
    /* USER CODE END */

    /* set Master or Slave Mode */
    temp_mdr = ( i2c->MDR & ( ~I2C_MASTER ) );
    i2c->MDR = ( temp_mdr | mode );

    /* USER CODE BEGIN (35) */
    /* USER CODE END */
}

/* SourceId : I2C_SourceId_022 */
/* DesignId : I2C_DesignId_021 */
/* Requirements : CONQ_I2C_SR28 */
/** @fn void i2c1GetConfigValue(i2c_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the I2C1 configuration registers
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

void i2c1GetConfigValue( i2c_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_OAR = I2C1_OAR_CONFIGVALUE;
        config_reg->CONFIG_IMR = I2C1_IMR_CONFIGVALUE;
        config_reg->CONFIG_CLKL = I2C1_CLKL_CONFIGVALUE;
        config_reg->CONFIG_CLKH = I2C1_CLKH_CONFIGVALUE;
        config_reg->CONFIG_CNT = I2C1_CNT_CONFIGVALUE;
        config_reg->CONFIG_SAR = I2C1_SAR_CONFIGVALUE;
        config_reg->CONFIG_MDR = I2C1_MDR_CONFIGVALUE;
        config_reg->CONFIG_EMDR = I2C1_EMDR_CONFIGVALUE;
        config_reg->CONFIG_PSC = I2C1_PSC_CONFIGVALUE;
        config_reg->CONFIG_DMAC = I2C1_DMAC_CONFIGVALUE;
        config_reg->CONFIG_FUN = I2C1_FUN_CONFIGVALUE;
        config_reg->CONFIG_DIR = I2C1_DIR_CONFIGVALUE;
        config_reg->CONFIG_ODR = I2C1_ODR_CONFIGVALUE;
        config_reg->CONFIG_PD = I2C1_PD_CONFIGVALUE;
        config_reg->CONFIG_PSL = I2C1_PSL_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Register read back support" */
        config_reg->CONFIG_OAR = i2cREG1->OAR;
        config_reg->CONFIG_IMR = i2cREG1->IMR;
        config_reg->CONFIG_CLKL = i2cREG1->CKL;
        config_reg->CONFIG_CLKH = i2cREG1->CKH;
        config_reg->CONFIG_CNT = i2cREG1->CNT;
        config_reg->CONFIG_SAR = i2cREG1->SAR;
        config_reg->CONFIG_MDR = i2cREG1->MDR;
        config_reg->CONFIG_EMDR = i2cREG1->EMDR;
        config_reg->CONFIG_PSC = i2cREG1->PSC;
        config_reg->CONFIG_DMAC = i2cREG1->DMACR;
        config_reg->CONFIG_FUN = i2cREG1->PFNC;
        config_reg->CONFIG_DIR = i2cREG1->DIR;
        config_reg->CONFIG_ODR = i2cREG1->PDR;
        config_reg->CONFIG_PD = i2cREG1->PDIS;
        config_reg->CONFIG_PSL = i2cREG1->PSEL;
    }
}

/* SourceId : I2C_SourceId_023 */
/* DesignId : I2C_DesignId_021 */
/* Requirements : CONQ_I2C_SR29 */
/** @fn void i2c2GetConfigValue(i2c_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the I2C1 configuration registers
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

void i2c2GetConfigValue( i2c_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_OAR = I2C2_OAR_CONFIGVALUE;
        config_reg->CONFIG_IMR = I2C2_IMR_CONFIGVALUE;
        config_reg->CONFIG_CLKL = I2C2_CLKL_CONFIGVALUE;
        config_reg->CONFIG_CLKH = I2C2_CLKH_CONFIGVALUE;
        config_reg->CONFIG_CNT = I2C2_CNT_CONFIGVALUE;
        config_reg->CONFIG_SAR = I2C2_SAR_CONFIGVALUE;
        config_reg->CONFIG_MDR = I2C2_MDR_CONFIGVALUE;
        config_reg->CONFIG_EMDR = I2C2_EMDR_CONFIGVALUE;
        config_reg->CONFIG_PSC = I2C2_PSC_CONFIGVALUE;
        config_reg->CONFIG_DMAC = I2C2_DMAC_CONFIGVALUE;
        config_reg->CONFIG_FUN = I2C2_FUN_CONFIGVALUE;
        config_reg->CONFIG_DIR = I2C2_DIR_CONFIGVALUE;
        config_reg->CONFIG_ODR = I2C2_ODR_CONFIGVALUE;
        config_reg->CONFIG_PD = I2C2_PD_CONFIGVALUE;
        config_reg->CONFIG_PSL = I2C2_PSL_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Register read back support" */
        config_reg->CONFIG_OAR = i2cREG2->OAR;
        config_reg->CONFIG_IMR = i2cREG2->IMR;
        config_reg->CONFIG_CLKL = i2cREG2->CKL;
        config_reg->CONFIG_CLKH = i2cREG2->CKH;
        config_reg->CONFIG_CNT = i2cREG2->CNT;
        config_reg->CONFIG_SAR = i2cREG2->SAR;
        config_reg->CONFIG_MDR = i2cREG2->MDR;
        config_reg->CONFIG_EMDR = i2cREG2->EMDR;
        config_reg->CONFIG_PSC = i2cREG2->PSC;
        config_reg->CONFIG_DMAC = i2cREG2->DMACR;
        config_reg->CONFIG_FUN = i2cREG2->PFNC;
        config_reg->CONFIG_DIR = i2cREG2->DIR;
        config_reg->CONFIG_ODR = i2cREG2->PDR;
        config_reg->CONFIG_PD = i2cREG2->PDIS;
        config_reg->CONFIG_PSL = i2cREG2->PSEL;
    }
}

/** @fn i2cSetDirection(i2cBASE_t *i2c, uint32 dir)
 *   @brief Sets I2C as transmitter or receiver.
 *   @param[in] i2c   - i2c module base address
 *   @param[in] dir  - This can be one of the following:
 *                      I2C_TRANSMITTER  - Transmit Mode,
 *                      I2C_RECEIVER     - Receive Mode
 */
/* SourceId : I2C_SourceId_026 */
/* DesignId :  */
/* Requirements :  */
void i2cSetDirection( i2cBASE_t * i2c, uint32 dir )
{
    /* USER CODE BEGIN (58) */
    /* USER CODE END */

    /* set Transmit/Receive mode */
    i2c->MDR &= ~I2C_TRANSMITTER;
    i2c->MDR |= dir;

    /* USER CODE BEGIN (59) */
    /* USER CODE END */
}

/** @fn i2cIsMasterReady(i2cBASE_t *i2c)
 *   @brief Indicates whether MST bit is set or cleared to indicate that stop
 *   condition was generated. This API should be called after Master Tx or Rx
 *   to check if the transaction is complete.
 *   @param[in] i2c   - i2c module base address
 *   @return boolean value to indicate whether MST bit is cleared after STOP bit is
 * generated.
 *           - TRUE, if MST bit is cleared.
 *           - FALSE, if MST bit is set.
 */
/* SourceId : I2C_SourceId_027 */
/* DesignId :  */
/* Requirements :  */
bool i2cIsMasterReady( i2cBASE_t * i2c )
{
    bool retVal = 0U;
    /* USER CODE BEGIN (60) */
    /* USER CODE END */

    /* check if MST bit is cleared. */
    if( ( i2c->MDR & I2C_MASTER ) == 0 )
    {
        retVal = true;
    }
    else
    {
        retVal = false;
    }
    return retVal;

    /* USER CODE BEGIN (61) */
    /* USER CODE END */
}

/** @fn i2cIsBusBusy(i2cBASE_t *i2c)
 *   @brief Returns the state of the bus busy flag. True if it is set and false otherwise.
 *   @param[in] i2c   - i2c module base address
 *   @return boolean value to indicate whether BB bit is set in the status register.
 *           - TRUE, if BB bit is set.
 *           - FALSE, if BB bit is cleared.
 */
/* SourceId : I2C_SourceId_028 */
/* DesignId :  */
/* Requirements :  */
bool i2cIsBusBusy( i2cBASE_t * i2c )
{
    bool retVal = 0U;
    /* USER CODE BEGIN (62) */
    /* USER CODE END */

    /* check if BB bit is set. */
    if( ( i2c->STR & I2C_BUSBUSY ) == I2C_BUSBUSY )
    {
        retVal = true;
    }
    else
    {
        retVal = false;
    }
    return retVal;

    /* USER CODE BEGIN (63) */
    /* USER CODE END */
}
