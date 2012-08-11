//*----------------------------------------------------------------------------
//*         ATMEL Microcontroller Software Support  -  ROUSSET  -
//*----------------------------------------------------------------------------
//* The software is delivered "AS IS" without warranty or condition of any
//* kind, either express, implied or statutory. This includes without
//* limitation any warranty or condition with respect to merchantability or
//* fitness for any particular purpose, or against the infringements of
//* intellectual property rights of others.
//*-----------------------------------------------------------------------------
//* File Name           : usart.h
//* Object              : USART Header File.
//*
//* 1.0 01/04/00 JCZ    : Creation
//*----------------------------------------------------------------------------

#ifndef usart_h
#define usart_h

//#include    "periph/stdc/std_c.h"
//#include    "periph/pio/lib_pio.h"

/*-------------------------------------------*/
/* USART User Interface Structure Definition */
/*-------------------------------------------*/

typedef struct
{
    at91_reg            US_CR ;         /* Control Register */
    at91_reg            US_MR ;         /* Mode Register */
    at91_reg            US_IER ;        /* Interrupt Enable Register */
    at91_reg            US_IDR ;        /* Interrupt Disable Register */
    at91_reg            US_IMR ;        /* Interrupt Mask Register */
    at91_reg            US_CSR ;        /* Channel Status Register */
    at91_reg            US_RHR ;        /* Receive Holding Register */
    at91_reg            US_THR ;        /* Transmit Holding Register */
    at91_reg            US_BRGR ;       /* Baud Rate Generator Register */
    at91_reg            US_RTOR ;       /* Receiver Timeout Register */
    at91_reg            US_TTGR ;       /* Transmitter Time-guard Register */
    at91_reg            Reserved ;
    at91_reg            US_RPR ;        /* Receiver Pointer Register */
    at91_reg            US_RCR ;        /* Receiver Counter Register */
    at91_reg            US_TPR ;        /* Transmitter Pointer Register */
    at91_reg            US_TCR ;        /* Transmitter Counter Register */
} StructUSART ;

/*--------------------------*/
/* US_CR : Control Register */
/*--------------------------*/

#define US_RSTRX                0x0004      /* Reset Receiver */
#define US_RSTTX                0x0008      /* Reset Transmitter */
#define US_RXEN                 0x0010      /* Receiver Enable */
#define US_RXDIS                0x0020      /* Receiver Disable */
#define US_TXEN                 0x0040      /* Transmitter Enable */
#define US_TXDIS                0x0080      /* Transmitter Disable */
#define US_RSTSTA               0x0100      /* Reset Status Bits */
#define US_STTBRK               0x0200      /* Start Break */
#define US_STPBRK               0x0400      /* Stop Break */
#define US_STTTO                0x0800      /* Start Time-out */
#define US_SENDA                0x1000      /* Send Address */

/*-----------------------*/
/* US_MR : Mode Register */
/*-----------------------*/

#define US_CLKS                 0x0030      /* Clock Selection */
#define US_CLKS_MCK             0x00        /* Master Clock */
#define US_CLKS_MCK8            0x10        /* Master Clock divided by 8 */
#define US_CLKS_SCK             0x20        /* External Clock */
#define US_CLKS_SLCK            0x30        /* Slow Clock */

#define US_CHRL                 0x00C0      /* Byte Length */
#define US_CHRL_5               0x00        /* 5 bits */
#define US_CHRL_6               0x40        /* 6 bits */
#define US_CHRL_7               0x80        /* 7 bits */
#define US_CHRL_8               0xC0        /* 8 bits */

#define US_SYNC                 0x0100      /* Synchronous Mode Enable */

#define US_PAR                  0x0E00      /* Parity Mode */
#define US_PAR_EVEN             0x00        /* Even Parity */
#define US_PAR_ODD              0x200       /* Odd Parity */
#define US_PAR_SPACE            0x400       /* Space Parity to 0 */
#define US_PAR_MARK             0x600       /* Marked Parity to 1 */
#define US_PAR_NO               0x800       /* No Parity */
#define US_PAR_MULTIDROP        0xC00       /* Multi-drop Mode */

#define US_NBSTOP               0x3000      /* Stop Bit Number */
#define US_NBSTOP_1             0x0000      /* 1 Stop Bit */
#define US_NBSTOP_1_5           0x1000      /* 1.5 Stop Bits */
#define US_NBSTOP_2             0x2000      /* 2 Stop Bits */

#define US_CHMODE                   0xC000  /* Channel Mode */
#define US_CHMODE_NORMAL            0x0000  /* Normal Mode */
#define US_CHMODE_AUTOMATIC_ECHO    0x4000  /* Automatic Echo */
#define US_CHMODE_LOCAL_LOOPBACK    0x8000  /* Local Loopback */
#define US_CHMODE_REMOTE_LOOPBACK   0xC000  /* Remote Loopback */

#define US_MODE9                0x20000     /* 9 Bit Mode */

#define US_CLKO                 0x40000     /* Baud Rate Output Enable */

/* Mode Register model */

/* Standard Asynchronous Mode : 8 bits , 1 stop , no parity */
#define US_ASYNC_MODE ( US_CHMODE_NORMAL + \
                        US_NBSTOP_1 + \
                        US_PAR_NO + \
                        US_CHRL_8 + \
                        US_CLKS_MCK )

/* Standard External Asynchronous Mode : 8 bits , 1 stop , no parity */
#define US_ASYNC_SCK_MODE ( US_CHMODE_NORMAL + \
                            US_NBSTOP_1 + \
                            US_PAR_NO + \
                            US_CHRL_8 + \
                            US_CLKS_SCK )

/* Standard Synchronous Mode : 8 bits , 1 stop , no parity */
#define US_SYNC_MODE ( US_SYNC + \
                       US_CHMODE_NORMAL + \
                       US_NBSTOP_1 + \
                       US_PAR_NO + \
                       US_CHRL_8 + \
                       US_CLKS_MCK )

/* SCK used Label */
#define SCK_USED (US_CLKO | US_CLKS_SCK)

/*---------------------------------------------------------------*/
/* US_IER, US_IDR, US_IMR, US_IMR: Status and Interrupt Register */
/*---------------------------------------------------------------*/

#define US_RXRDY            0x1       /* Receiver Ready */
#define US_TXRDY            0x2       /* Transmitter Ready */
#define US_RXBRK            0x4       /* Receiver Break */
#define US_ENDRX            0x8       /* End of Receiver PDC Transfer */
#define US_ENDTX            0x10       /* End of Transmitter PDC Transfer */
#define US_OVRE             0x20       /* Overrun Error */
#define US_FRAME            0x40       /* Framing Error */
#define US_PARE             0x80       /* Parity Error */
#define US_TIMEOUT          0x100       /* Receiver Timeout */
#define US_TXEMPTY          0x200       /* Transmitter Empty */

#define US_MASK_IRQ_TX      (US_TXRDY | US_ENDTX | US_TXEMPTY)
#define US_MASK_IRQ_RX      (US_RXRDY | US_ENDRX | US_TIMEOUT)
#define US_MASK_IRQ_ERROR   (US_PARE | US_FRAME | US_OVRE | US_RXBRK)



#endif /* usart_h */
