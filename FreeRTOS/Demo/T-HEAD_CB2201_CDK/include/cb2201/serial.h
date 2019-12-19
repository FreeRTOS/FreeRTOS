/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef __HOBBIT_UART_H__
#define __HOBBIT_UART_H__

#if defined  CONFIG_HOBBIT_NBIOT
//UART_1
#define HOBBIT_UART1_BASE                  0xB0004000

//UART_2
#define HOBBIT_UART2_BASE                  0xB0005000

//UART_3
#define HOBBIT_UART3_BASE                  0xB0015000

/* gpio setting */
#define HOBBIT_GPIO0_PORTCTR               0xB0006008
#else
//UART_1
#define HOBBIT_UART1_BASE                  0x50004000

//UART_2
#define HOBBIT_UART2_BASE                  0x50010400

//UART_3
#define HOBBIT_UART3_BASE                  0x50015000

/* gpio setting */
#define HOBBIT_GPIO0_PORTCTR               0x50006008
#endif

#define PA2_TXD0_SPI0MISO                  1<<2
#define PA3_RXD0_SPI0MOSI                  1<<3
#define PA16_RXD1_ADC8                     1<<16
#define PA17_TXD1_ADC9                     1<<17
#define PA24_TXD2_I2SMCLK_SPI1SSN0         1<<24
#define PA25_RXD2_I2SSCK_SPI1SSN1          1<<25


/* UART registers addr definition */
#define CK_UART_RBR            0x00    /* Receive Buffer Register (32 bits, R) */
#define CK_UART_THR            0x00    /* Transmit Holding Register (32 bits, W) */
#define CK_UART_DLL            0x00    /* Divisor Latch(Low)  (32 bits, R/W) */
#define CK_UART_IER            0x04    /* Interrupt Enable Register (32 bits, R/W) */
#define CK_UART_DLH            0x04    /* Divisor Latch(High) (32 bits, R/W) */
#define CK_UART_IIR            0x08    /* Interrupt Identity Register (32 bits, R) */
#define CK_UART_FCR            0x08    /* fifo Countrol Register (32 bits, W) */
#define CK_UART_LCR            0x0C    /* Line Control Register (32 bits, R/W) */
#define CK_UART_MCR            0x10    /* Modem Control Register (32 bits, W) */
#define CK_UART_LSR            0x14    /* Line Status Register (32 bits, R) */
#define CK_UART_MSR            0x18    /* Modem Status Register (32 bits, R/W) */
#define CK_UART_USR            0x7C    /* UART Status Register (32 bits, R/W) */


#define UART_BUSY_TIMEOUT      1000000
#define UART_RECEIVE_TIMEOUT   1000
#define UART_TRANSMIT_TIMEOUT  1000


/* UART register bit definitions */

#define USR_UART_BUSY           0x01
#define LSR_DATA_READY          0x01
#define LSR_THR_EMPTY           0x20
#define IER_RDA_INT_ENABLE      0x01
#define IER_THRE_INT_ENABLE     0x02
#define IIR_NO_ISQ_PEND         0x01
#define FCR_FIFO_ENAB           0x01

#define LCR_SET_DLAB            0x80   /* enable r/w DLR to set the baud rate */
#define LCR_PARITY_ENABLE   0x08   /* parity enabled */
#define LCR_PARITY_EVEN         0x10   /* Even parity enabled */
#define LCR_PARITY_ODD          0xef   /* Odd parity enabled */
#define LCR_WORD_SIZE_5         0xfc   /* the data length is 5 bits */
#define LCR_WORD_SIZE_6         0x01   /* the data length is 6 bits */
#define LCR_WORD_SIZE_7         0x02   /* the data length is 7 bits */
#define LCR_WORD_SIZE_8         0x03   /* the data length is 8 bits */
#define LCR_STOP_BIT1           0xfb   /* 1 stop bit */
#define LCR_STOP_BIT2           0x04   /* 1.5 stop bit */

#define CK_LSR_PFE              0x80
#define CK_LSR_TEMT             0x40
#define CK_LSR_THRE             0x40
#define CK_LSR_BI               0x10
#define CK_LSR_FE               0x08
#define CK_LSR_PE               0x04
#define CK_LSR_OE               0x02
#define CK_LSR_DR               0x01
#define CK_LSR_TRANS_EMPTY      0x20


/*config the uart */

#define CK_UART_TXBUFFERSIZE    128
#define CK_UART_RXBUFFERSIZE    128

typedef enum{
    LSR_IIR_MOD_STS  = 0,
    LSR_IIR_INT_PND  = 1,
    LSR_IIR_THR_EMP  = 2,
    LSR_IIR_RCV_AVAL = 4,
    LSR_IIR_RCV_STS  = 6,
    LSR_IIR_BS_DET   = 7,
    LSR_IIR_CHAR_TO  = 12
}LSR_IIR_IID;


typedef enum{
    B1200  = 1200,
    B2400  = 2400,
    B4800  = 4800,
    B9600  = 9600,
    B14400 = 14400,
    B19200 = 19200,
    B56000 = 56000,
    B38400 = 38400,
    B57600 = 57600,
    B115200= 115200
}UART_BAUDRATE;

typedef enum{
    ODD,
    EVEN,
    NONE
}UART_PARITY;

typedef enum{
    WORD_SIZE_5,
    WORD_SIZE_6,
    WORD_SIZE_7,
    WORD_SIZE_8
}UART_WORDSIZE;

typedef enum{
    LCR_STOP_BIT_1,
    LCR_STOP_BIT_2
}UART_STOPBIT;




#endif
