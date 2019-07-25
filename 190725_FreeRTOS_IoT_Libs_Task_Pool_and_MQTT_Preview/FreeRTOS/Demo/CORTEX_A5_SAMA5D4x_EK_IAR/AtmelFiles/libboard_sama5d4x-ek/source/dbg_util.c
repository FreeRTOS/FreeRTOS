/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

/**
 *  \file
 *  Implement simple DBGU usage as stream receiver.
 */

/*-------------------------------
 *          Headers
 *-------------------------------*/

#include <board.h>

/*-------------------------------
 *          Defines
 *-------------------------------*/

/** Data RX timeout in binary start up */
#define TIMEOUT_RX_START        (1000*20)
/** Data RX timeout default value */
#define TIMEOUT_RX              (200)

/* ASCII Character Codes */
#define SOH             0x01
#define STX             0x02
#define EOT             0x04
#define CTRL_D          0x04 /**< Transfer Done */
#define ACK             0x06
#define NAK             0x15
#define CAN             0x18 /**< Cancel transfer */
#define CTRL_X          0x24

/* 1K XMODEM Parameters */
#define SOH_LENGTH      128
#define STX_LENGTH      1024
#define SOH_TIMEOUT     1000

/*-------------------------------
 *          Local functions
 *-------------------------------*/

/**
 * \brief Compute the CRC
 */
static uint16_t _GetCRC(uint8_t bByte, uint16_t wCrc)
{
    int32_t cnt;
    uint8_t  newBit;
    for (cnt = 7; cnt >= 0; cnt --)
    {
        newBit = ((wCrc >> 15) & 0x1) ^ ((bByte >> cnt) & 0x1);
        wCrc <<= 1;
        if (newBit) wCrc ^= (0x1021);
    }
    return wCrc;
    
}

/*-------------------------------
 *          Exported functions
 *-------------------------------*/

/**
 * \brief Receives byte with timeout.
 * \param pByte pointer to locate received byte, can be NULL
 *              to discard data.
 * \param timeOut timeout setting, in number of ticks.
 */
uint8_t DbgReceiveByte(uint8_t* pByte, uint32_t timeOut)
{
    uint32_t tick;
    uint32_t delay;
    tick = GetTickCount();
    while(1)
    {
        if (DBGU_IsRxReady())
        {
            uint8_t tmp = DBGU_GetChar();
            if (pByte) *pByte = tmp;
            return 1;
        }

        if (timeOut == 0)
        {   /* Never timeout */
        }
        else
        {
            delay = GetDelayInTicks(tick, GetTickCount());
            if (delay > timeOut)
            {
                return 0;
            }
        }
    }
}

/**
 * \brief Receives raw binary file through DBGU.
 * \param bStart 1 to start a new data stream.
 * \param address receiving data address
 * \param maxSize max receive data size in bytes
 * \return number of received bytes
 */
uint32_t DbgReceiveBinary(uint8_t bStart, uint32_t address, uint32_t maxSize)
{
    volatile uint32_t tick0;
    uint32_t delay;
    uint8_t  *pBuffer = (uint8_t*)address;
    uint8_t  xSign = 0;
    uint32_t rxCnt = 0;

    if (maxSize == 0) return 0;

    if (bStart)
    {
        printf("\n\r-- Please start binary data in %d seconds:\n\r",
            TIMEOUT_RX_START / 1000);
        tick0 = GetTickCount();
        while(1)
        {
            if (DBGU_IsRxReady())
            {
                pBuffer[rxCnt ++] = DBGU_GetChar();
                DBGU_PutChar(' ');
                break;
            }
            else
            {
                delay = GetDelayInTicks(tick0, GetTickCount());
                if ((delay % 1000) == 0)
                {
                    if (xSign == 0)
                    {
                        DBGU_PutChar('*');
                        xSign = 1;
                    }
                }
                else if (xSign)
                {
                    xSign = 0;
                }

                if (delay > TIMEOUT_RX_START)
                {
                    printf("\n\rRX timeout!\n\r");
                    return rxCnt;
                }
            }
        }
    }
    /* Get data */
    while(1)
    {
        tick0 = GetTickCount();
        while(1)
        {
            if (DBGU_IsRxReady())
            {
                pBuffer[rxCnt ++] = DBGU_GetChar();
                if ((rxCnt % (10*1024)) == 0)
                {
                    DBGU_PutChar('.');
                }
                if (rxCnt >= maxSize)
                {
                    /* Wait until file transfer finished */
                    return rxCnt;
                }
                break;
            }
            delay = GetDelayInTicks(tick0, GetTickCount());
            if (delay > TIMEOUT_RX)
            {
                return rxCnt;
            }
        }
    }
}

/**
 * \brief Receives raw binary file through DBGU.
 *
 * \note When "CCC..", uses Ctrl + D to exit.
 *
 * \param pktBuffer 1K size packet buffer
 * \param address   receiving data address
 * \param maxSize   max receive data size in bytes
 * \return number of received bytes
 */
uint32_t DbgReceive1KXModem(uint8_t* pktBuffer,
                            uint32_t address,
                            uint32_t maxSize)
{
    uint8_t inChar;
    uint32_t i, index = 0, pktLen = 0;
    uint8_t pktNum = 0, prevPktNum = 0;
    uint32_t error = 0;
    uint16_t inCrc, myCrc;
    uint8_t inCheckSum = 0xFF, checkSum = 0;
    uint8_t *pBuffer = (uint8_t*)address;
    uint32_t totalLen = 0;

    DBGU_PutChar('C');
    while (1)
    {
        if (!DbgReceiveByte(&inChar, SOH_TIMEOUT))
        {
            DBGU_PutChar('C');
            continue;
        }
        /* Done */
        if (EOT == inChar)
        {
            error = 0;
            DBGU_PutChar(ACK);
            break;
        }
        else if (CAN == inChar)
        {
            error = 2;
        }
        else if (CTRL_X == inChar)
        {
            error = 3;
        }
        else if (SOH == inChar)
        {
            pktLen = SOH_LENGTH;
        }
        else if (STX == inChar)
        {
            pktLen = STX_LENGTH;
        }
        else    continue;
        /* Get Packet Number */
        if (!DbgReceiveByte(&pktNum, SOH_TIMEOUT)) error = 4;
        /* Get 1's complement of packet number */
        if (!DbgReceiveByte(&inChar, SOH_TIMEOUT)) error = 5;
        /* Get 1 packet of information. */
        checkSum = 0; myCrc = 0; index = 0;
        for (i = 0; i < pktLen; i ++)
        {
            if (!DbgReceiveByte(&inChar, SOH_TIMEOUT)) error = 6;
            checkSum += inChar;
            myCrc = _GetCRC(inChar, myCrc);
            if (pktNum != prevPktNum)
            {
                pktBuffer[index ++] = inChar;
            }
        }
        /* Get CRC bytes */
        if (!DbgReceiveByte(&inCheckSum, SOH_TIMEOUT)) error = 7;
        inCrc  = inCheckSum << 8;
        if (!DbgReceiveByte(&inCheckSum, SOH_TIMEOUT)) error = 7;
        inCrc += inCheckSum;
        /* If CRC error, NAK */
        if (error || (inCrc != myCrc))
        {
            DBGU_PutChar(NAK);
            error = 0;
        }
        /* Save packet, ACK and next */
        else
        {
            prevPktNum = pktNum;

            /* Buffer full? */
            if (totalLen + pktLen > maxSize)
            {
                /* Copy until buffer full? */
                /* Stop transfer */
                DBGU_PutChar(CAN);
                return totalLen;
            }

            /* Copy the packet */
            for (i = 0; i < pktLen; i ++)
            {
                pBuffer[totalLen + i] = pktBuffer[i];
            }
            totalLen += pktLen;
            DBGU_PutChar(ACK);
        }
    }

    return totalLen;
}

