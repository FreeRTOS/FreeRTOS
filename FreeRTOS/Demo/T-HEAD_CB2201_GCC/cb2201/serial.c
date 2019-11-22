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
#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include <unistd.h>

#include <string.h>
#include <errno.h>

#include "irq.h"
#include "uart.h"
#include "chip.h"

#define CONFIG_SYSTEM_UARTS 3
#define CONFIG_USART_BAUD   115200
#define CONFIG_USART_BITS   8
#define CONFIG_USART_PARITY 0
#define CONFIG_USART_2STOP  0

//#define CONFIG_ARCH_HAVE_UART1
#define CONFIG_ARCH_HAVE_UART2
//#define CONFIG_ARCH_HAVE_UART3

#define OK 0
#define TRUE 0
#define FALSE 1

#define putreg32(v, x) (*(volatile uint32_t*)(x) = (v))
#define getreg32(x) (*(volatile uint32_t *)(x))

int  yunos_bsp_uart_setup(uint8_t id, int (*cb)(void *), void *arg);
int yunos_bsp_uart_set_format(uint8_t id, uint32_t baud, uint8_t bits, uint8_t parity, bool stopbits2);

/************************************************************************************
 * Private Types
 ************************************************************************************/

struct bsp_uart_s {
    uint8_t           onewire;   /* 0 = None, 1 = 1 wire */
    uint8_t           parity;    /* 0=none, 1=odd, 2=even */
    uint8_t           bits;      /* Number of bits (7 or 8) */
    bool              stopbits2; /* True: Configure with 2 stop bits instead of 1 */
    uint32_t        baud;      /* Configured baud */

    uint8_t     irq;       /* IRQ associated with this USART */
    uint32_t    apbclock;  /* PCLK 1 or 2 frequency */
    uint32_t    usartbase; /* Base address of USART registers */
    uint32_t    ioportctr; /* io port control registers */
    uint32_t    iomuxh;    /* io pinmux registers */
    bool        btxquery;  /* query mode or int mode   */
    bool        brxquery;  /* query mode or int mode   */

    int (*callback)(void *arg);  /* uart interrupt callback */
    void        *arg;            /* uart interrupt callback's argument */
};

/************************************************************************************
 * Private Function Prototypes
 ************************************************************************************/


/****************************************************************************
 * Private Variables
 ****************************************************************************/

#ifdef CONFIG_ARCH_HAVE_UART1
static struct bsp_uart_s g_hobbit_usart1priv;
#endif

#ifdef CONFIG_ARCH_HAVE_UART2
static struct bsp_uart_s g_hobbit_usart2priv;
#endif

#ifdef CONFIG_ARCH_HAVE_UART3
static struct bsp_uart_s g_hobbit_usart3priv;
#endif


/* This table lets us iterate over the configured USARTs */
static const uint8_t  g_uart_irqs[CONFIG_SYSTEM_UARTS] = {PIC_IRQ_UART1, PIC_IRQ_UART2, PIC_IRQ_UART3};
static const uint32_t  g_uart_base[CONFIG_SYSTEM_UARTS] = {HOBBIT_UART1_BASE, HOBBIT_UART2_BASE, HOBBIT_UART3_BASE};

static struct bsp_uart_s * const g_uart_devs[CONFIG_SYSTEM_UARTS] = {
#ifdef CONFIG_ARCH_HAVE_UART1
    [0] = &g_hobbit_usart1priv,
#else
    [0] = NULL,
#endif
#ifdef CONFIG_ARCH_HAVE_UART2
    [1] = &g_hobbit_usart2priv,
#else
    [1] = NULL,
#endif
#ifdef CONFIG_ARCH_HAVE_UART3
    [2] = &g_hobbit_usart3priv,
#else
    [2] = NULL,
#endif
};


/****************************************************************************
 * Private Functions
 ****************************************************************************/


/****************************************************************************
 * Name: up_serialin
 *
 * Description:
 *
 ****************************************************************************/
static inline uint32_t up_serialin(struct bsp_uart_s *priv, int offset)
{
    return (getreg32(priv->usartbase + offset));
}

/****************************************************************************
 * Name: up_serialout
 ****************************************************************************/
static inline void up_serialout(struct bsp_uart_s *priv, int offset, uint32_t value)
{
    putreg32(value, priv->usartbase + offset);
}

/****************************************************************************
 * Name: uart_interrupt_service
 ****************************************************************************/
#if 0
static int uart_interrupt_service(int irq, void *context)
{
    int i = 0;
    struct bsp_uart_s *priv;

    for (;i < sizeof(g_uart_irqs); i++) {
        if (irq == g_uart_irqs[i]) {
            break;
        }
    }

    if (i == sizeof(g_uart_irqs)) {
        /* error irq id */
        return -1;
    }

    priv = g_uart_devs[i];

    /* call interrupt's callback */
    if (priv->callback) {
        priv->callback(priv->arg);
    }
    return OK;
}
#endif

/****************************************************************************
 * Public Functions
 ****************************************************************************/


/****************************************************************************
 * Name: yunos_bsp_uart_init
 *
 * Description:
 *   init the uart module
 *
 ****************************************************************************/
int  yunos_bsp_uart_init(uint8_t * count)
{
    uint8_t id;
    *count = 0;

    for(id = 0; id < CONFIG_SYSTEM_UARTS; id++)
    {
        if(g_uart_devs[id] != NULL)
        {
            (*count) ++;
            yunos_bsp_uart_setup(id, NULL, NULL);
        }
    }

    return 0;
}


/****************************************************************************
 * Name: yunos_bsp_uart_setup
 *
 * Description:
 *   Configure the UART baud, bits, parity, fifos, etc. This
 *   method is called the first time that the serial port is
 *   opened.
 *
 ****************************************************************************/
int  yunos_bsp_uart_setup(uint8_t id, int (*cb)(void *), void *arg)
{
//    uint16_t uart_pins[2];
    struct bsp_uart_s *priv = g_uart_devs[id];
    int ret;

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return -1;
    }

    priv->irq = g_uart_irqs[id];
    priv->usartbase= g_uart_base[id];

    if (cb) {
        /* interrut callback */
        priv->callback = cb;
        priv->arg      = arg;
        /* attach irq */
//        ret = yunos_bsp_intc_attach_irq(priv->irq, uart_interrupt_service);
        if (ret == OK) {
//            yunos_bsp_intc_enable_irq(priv->irq);
        }
    }

    yunos_bsp_uart_set_format(id, CONFIG_USART_BAUD, CONFIG_USART_BITS, CONFIG_USART_PARITY, CONFIG_USART_2STOP);

    return 0;
}


/****************************************************************************
 * Name: uart_chargebaudrate
 *
 * Description:
 *  Set the serial baudrate.
 * Input parameters:
 *  uartid    - a base id, be one of UART1, UART2 or UART3
 *  baudrate  - baudrate that user typed in
 * Returned Value:
 *  0:success -1:fail
 *
 ****************************************************************************/
static uint8_t uart_changebaudrate(struct bsp_uart_s *priv, uint8_t uartid, UART_BAUDRATE baudrate,uint32_t apbfreq)
{
    int ret = 0;
    uint32_t tmp = 0;
    uint32_t divisor;

    /*the baudrates that uart surported as follows:*/
    if ((baudrate == B4800) || (baudrate == B9600) ||
       (baudrate == B14400) || (baudrate == B19200) ||
       (baudrate == B38400) || (baudrate == B56000) ||
       (baudrate == B57600) || (baudrate == B115200))
    {
        /*
        * DLH and DLL may be accessed when the UART is not
        * busy(USR[0]=0) and the DLAB bit(LCR[7]) is set.
        */
        /*baudrate=(seriak clock freq)/(16*divisor).*/
        divisor = ((apbfreq / baudrate) >> 4);
        tmp  = up_serialin(priv, CK_UART_LCR);
        tmp |= LCR_SET_DLAB;
    up_serialout(priv, CK_UART_LCR, tmp);

        /* DLL and DLH is lower 8-bits and higher 8-bits of divisor.*/
    if (baudrate == B115200)
    {
        divisor ++;
    }
        tmp = divisor & 0xff;
        up_serialout(priv, CK_UART_DLL, tmp);

        tmp = (divisor >> 8) & 0xff;
        up_serialout(priv, CK_UART_DLH, tmp);
        /*
        * The DLAB must be cleared after the baudrate is setted
        * to access other registers.
        */
        tmp  = up_serialin(priv, CK_UART_LCR);
        tmp &= (~LCR_SET_DLAB);
        up_serialout(priv, CK_UART_LCR, tmp);
        ret = 0;
    }
    return ret;
}


/****************************************************************************
 * Name: uart_setparity
 *
 * Description:
 *  Set the serial parity.
 * Input parameters:
 *  uartid    - a base id, be one of UART1, UART2 or UART3
 *  parity    - parity that user typed in
 * Returned Value:
 *  0:success -1:fail
 *
 ****************************************************************************/
static uint8_t uart_setparity(struct bsp_uart_s *priv, uint8_t uartid, UART_PARITY parity)
{
    int ret = 0;
    uint32_t tmp = 0;

    switch(parity)
    {
        case NONE:
        /*CLear the PEN bit(LCR[3]) to disable parity.*/
        tmp  = up_serialin(priv, CK_UART_LCR);
        tmp &= (~LCR_PARITY_ENABLE);
        up_serialout(priv, CK_UART_LCR, tmp);
        break;

        case ODD:
    /* Set PEN and clear EPS(LCR[4]) to set the ODD parity. */
        tmp  = up_serialin(priv, CK_UART_LCR);
    tmp |= LCR_PARITY_ENABLE;
    tmp &= LCR_PARITY_ODD;
        up_serialout(priv, CK_UART_LCR, tmp);
        break;

        case EVEN:
    /* Set PEN and EPS(LCR[4]) to set the EVEN parity.*/
        tmp  = up_serialin(priv, CK_UART_LCR);
    tmp |= LCR_PARITY_ENABLE;
    tmp |= LCR_PARITY_EVEN;
        up_serialout(priv, CK_UART_LCR, tmp);
        break;

        default:
    ret = -1;
    break;
    }
    return ret;
}


/****************************************************************************
 * Name: uart_setwordsize
 *
 * Description:
 *  Set the serial wordsize.
 * Input parameters:
 *  uartid    - a base id, be one of UART1, UART2 or UART3
 *  wordsize  - the data length that user decides
 * Returned Value:
 *  0:success -1:fail
 *
 ****************************************************************************/
static uint8_t uart_setwordsize(struct bsp_uart_s *priv, uint8_t uartid, UART_WORDSIZE wordsize)
{
    int ret = 0;
    uint32_t tmp = 0;

    /* DLS(LCR[1:0]) is writeable when the UART is not busy(USR[0]=0).*/

    /* The word size decides by the DLS bits(LCR[1:0]), and the
     * corresponding relationship between them is:
     *    DLS   word size
     *    00 -- 5 bits
     *    01 -- 6 bits
     *    10 -- 7 bits
     *    11 -- 8 bits
     */
    switch(wordsize)
    {
    case WORD_SIZE_5:
        tmp  = up_serialin(priv, CK_UART_LCR);
        tmp &= LCR_WORD_SIZE_5;
    up_serialout(priv, CK_UART_LCR, tmp);
        break;

    case WORD_SIZE_6:
        tmp  = up_serialin(priv, CK_UART_LCR);
        tmp &= 0xfd;
        tmp |= LCR_WORD_SIZE_6;
        up_serialout(priv, CK_UART_LCR, tmp);
        break;

    case WORD_SIZE_7:
        tmp  = up_serialin(priv, CK_UART_LCR);
        tmp &= 0xfe;
        tmp |= LCR_WORD_SIZE_7;
        up_serialout(priv, CK_UART_LCR, tmp);
        break;

    case WORD_SIZE_8:
        tmp  = up_serialin(priv, CK_UART_LCR);
        tmp |= LCR_WORD_SIZE_8;
        up_serialout(priv, CK_UART_LCR, tmp);
        break;

    default:
        ret = -1;
        break;
    }
    return ret;
}


/****************************************************************************
 * Name: uart_setstopbits
 *
 * Description:
 *  Set the serial stop bits.
 * Input parameters:
 *  uartid    - a base id, be one of UART1, UART2 or UART3
 *  stopbit   - it has two possible value: STOP_BIT_1 and STOP_BIT_2.
 * Returned Value:
 *  0:success -1:fail
 *
 ****************************************************************************/
static uint8_t uart_setstopbit(struct bsp_uart_s *priv, uint8_t uartid, UART_STOPBIT stopbit)
{
    int ret = 0;
    uint32_t tmp = 0;

    /* PEN bit(LCR[3]) is writeable when the UART is not busy(USR[0]=0).*/
    switch (stopbit)
    {
    case LCR_STOP_BIT_1:
        /* Clear the STOP bit to set 1 stop bit*/
        tmp  = up_serialin(priv, CK_UART_LCR);
        tmp &= LCR_STOP_BIT1;
        up_serialout(priv, CK_UART_LCR, tmp);
        break;

    case LCR_STOP_BIT_2:
        /*
        * If the STOP bit is set "1",we'd gotten 1.5 stop
        * bits when DLS(LCR[1:0]) is zero, else 2 stop bits.
        */
        tmp  = up_serialin(priv, CK_UART_LCR);
        tmp |= LCR_STOP_BIT2;
        up_serialout(priv, CK_UART_LCR, tmp);
        break;

    default:
        ret = -1;
        break;
    }
    return ret;
}


/****************************************************************************
 * Name: uart_settxmod
 *
 * Description:
 *  This function is used to set the transmit mode, interrupt mode or
 * Input parameters:
 *  uartid    - a base id, be one of UART1, UART2 or UART3
 *  bquery    - it indicates the transmit mode: TRUE - query mode, FALSE -
 * Returned Value:
 *  0:success -1:fail
 *
 ****************************************************************************/
static uint8_t uart_settxmode(struct bsp_uart_s *priv, uint8_t uartid, bool bquery)
{
    int ret = 0;
    uint32_t tmp = 0;

    if(bquery)
    {
        /* When query mode, disable the Transmit Holding Register Empty
        * Interrupt. To do this, we clear the ETBEI bit(IER[1]).
        */
        tmp  = up_serialin(priv, CK_UART_IER);
        tmp &= (~IER_THRE_INT_ENABLE);
        up_serialout(priv, CK_UART_IER, tmp);
        /* Refresh the uart info: transmit mode - query.*/
        priv->btxquery = TRUE;
    }
    else
    {
        /* When interrupt mode, inable the Transmit Holding Register
        * Empty Interrupt. To do this, we set the ETBEI bit(IER[1]).
        */
        tmp  = up_serialin(priv, CK_UART_IER);
        tmp |= IER_THRE_INT_ENABLE;
        up_serialout(priv, CK_UART_IER, tmp);
        /* Refresh the uart info: transmit mode - interrupt.*/
        priv->btxquery = FALSE;
    }
    return ret;
}


/****************************************************************************
 * Name: uart_setrxmod
 *
 * Description:
 *  This function is used to set the receive mode, interrupt mode or
 * Input parameters:
 *  uartid    - a base id, be one of UART1, UART2 or UART3
 *  bquery    - it indicates the transmit mode: TRUE - query mode, FALSE -
 * Returned Value:
 *  0:success -1:fail
 *
 ****************************************************************************/
static uint8_t uart_setrxmode(struct bsp_uart_s *priv, uint8_t uartid, bool bquery)
{
    int ret = 0;
    uint32_t tmp = 0;
    /* PEN bit(LCR[3]) is writeable when the UART is not busy(USR[0]=0).*/
    if(bquery)
    {
        /* When query mode, disable the Received Data Available
        * Interrupt. To do this, we clear the ERBFI bit(IER[0]).
        */
        tmp  = up_serialin(priv, CK_UART_IER);
        tmp &= (~IER_RDA_INT_ENABLE);
        up_serialout(priv, CK_UART_IER, tmp);
        /* Refresh the uart info: receive mode - query.*/
        priv->brxquery = TRUE;
    }
    else
    {
        /* When interrupt mode, inable the Received Data Available
        * Interrupt. To do this, we set the ERBFI bit(IER[0]).
        */
        tmp = up_serialin(priv, CK_UART_FCR);
        tmp |= FCR_FIFO_ENAB;
        up_serialout(priv, CK_UART_FCR, tmp);

        tmp  = up_serialin(priv, CK_UART_IER);
        tmp |= IER_RDA_INT_ENABLE;
        up_serialout(priv, CK_UART_IER, tmp);
        /* Refresh the uart info: receive mode - interrupt.*/
        priv->brxquery = FALSE;
    }
    return ret;
}


/****************************************************************************
 * Name: uart_reg_init
 *
 * Description:
 *   init the uart related registers
 *
 ****************************************************************************/
static int  uart_reg_init(struct bsp_uart_s *priv, uint8_t id)
{
    uint32_t tmp = 0;
    priv->ioportctr = HOBBIT_GPIO0_PORTCTR;

    tmp = 0x83;
    up_serialout(priv, CK_UART_LCR, tmp);
    tmp  = up_serialin(priv, CK_UART_LCR);
    tmp = 0x01;
    up_serialout(priv, CK_UART_DLL, tmp);
    tmp = 0x0;
    up_serialout(priv, CK_UART_DLH, tmp);

    return 0;
}

/****************************************************************************
 * Name: yunos_bsp_uart_set_format
 *
 * Description:
 *  Set the serial line format and speed.
 * Input parameters:
 *  parity    - 0=none, 1=odd, 2=even
 *  bits      - Number of bits (7 or 8)
 *  stopbits2 - True: Configure with 2 stop bits instead of 1
 *  baud      - Configured baud
 * Returned Value:
 *  NULL
 *
 ****************************************************************************/
int yunos_bsp_uart_set_format(uint8_t id, uint32_t baud, uint8_t bits, uint8_t parity, bool stopbits2)
{
//    unsigned int temp;
//    unsigned int remainder;
//    unsigned int fraction;
//    unsigned int divider;
    uint32_t timecount;
//    uint32_t tmp;
    struct bsp_uart_s *priv = g_uart_devs[id];

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return -1;
    }

    timecount = 0;
    while ((up_serialin(priv, CK_UART_USR) & USR_UART_BUSY)
        && (timecount < UART_BUSY_TIMEOUT))
    {
        timecount++;
    }
    if(timecount >= UART_BUSY_TIMEOUT)
    {
//        LOG("uart","uart %d is busy \n", id);
    return -1;
    }

    uart_reg_init(priv, id);
    uart_changebaudrate(priv, id, CONFIG_USART_BAUD, APB_DEFAULT_FREQ);
    uart_setparity(priv, id, NONE);
    uart_setwordsize(priv, id, CONFIG_USART_BITS);
    uart_setstopbit(priv, id, CONFIG_USART_2STOP);
    uart_setrxmode(priv, id, false);
    uart_settxmode(priv, id, true);

    priv->baud = baud;
    priv->bits = bits;
    priv->parity = parity;
    priv->stopbits2 = stopbits2;

    return 0;
}


/****************************************************************************
 *  * Name: yunos_bsp_uart_getc
 *  *
 *  * Description:
 *  * Called (usually) from the interrupt level to receive one character from
 *  * the UART.  Error bits associated with the receipt are provided in the
 *  * the return 'status'.
 *  *
 *  ****************************************************************************/
int yunos_bsp_uart_getc(uint8_t id)
{
    struct bsp_uart_s *priv = g_uart_devs[id];

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return -1;
    }

    if (priv->brxquery)
    {
    /* query mode */
    if (up_serialin(priv, CK_UART_LSR) & LSR_DATA_READY)
        {
            //*ch = up_serialin(priv, CK_UART_RBR);
        }

    } else {
        /* irq mode */

    }

    return up_serialin(priv, CK_UART_RBR) & 0xff;
}


/****************************************************************************
 *  * Name: yunos_bsp_uart_putc
 *  *
 *  * Description:
 *  *   This method will send one byte on the UART
 *  *
 *  ****************************************************************************/
void yunos_bsp_uart_putc(uint8_t id, int ch)
{
    struct bsp_uart_s *priv = g_uart_devs[id];

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return;
    }

    /* Wait until there is space in the FIFO */
    while (!(up_serialin(priv, CK_UART_LSR) & CK_LSR_TRANS_EMPTY));

    /* Send the character */
    up_serialout(priv, CK_UART_THR, ch);

    return;
}



/****************************************************************************
 * Name: yunos_bsp_uart_get_format
 *
 * Description:
 *  get the serial line format and speed.
 * Input parameters:
 *  parity    - 0=none, 1=odd, 2=even
 *  bits      - Number of bits (7 or 8)
 *  stopbits2 - True: Configure with 2 stop bits instead of 1
 *  baud      - Configured baud
 * Returned Value:
 *  Zero on success
 *  -1 on failed
 *
 ****************************************************************************/
int  yunos_bsp_uart_get_format(uint8_t id, uint32_t * baud, uint8_t * bits, uint8_t * parity, bool * stopbits2)
{
    struct bsp_uart_s *priv = g_uart_devs[id];

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return -1;
    }

    *baud = priv->baud;
    *bits = priv->bits;
    *parity = priv->parity;
    *stopbits2 = priv->stopbits2;

    return 0;
}

/****************************************************************************
 *  * Name: yunos_bsp_uart_get_irq
 *  *
 *  * Description:
 *  *   Call to get the uart irq number
 *  *
 *  ****************************************************************************/
int yunos_bsp_uart_get_irq(uint8_t id)
{
    struct bsp_uart_s *priv = g_uart_devs[id];

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return -1;
    }

    return priv->irq;
}

/****************************************************************************
 *  * Name: yunos_bsp_enable_txint
 *  *
 *  * Description:
 *  *   Call to enable or disable TX intterupt
 *  *
 *  ****************************************************************************/
void yunos_bsp_enable_txint(uint8_t id, bool enable)
{
    uint32_t cr;
    struct bsp_uart_s *priv = g_uart_devs[id];

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return ;
    }

    /* And restore the interrupt state (see the interrupt enable/usage table above) */
    cr = up_serialin(priv, CK_UART_IER);
    if(enable)
    {
        cr &= ~(IER_THRE_INT_ENABLE);
        cr |= (IER_THRE_INT_ENABLE);
    }
    else
    {
        cr &= ~(IER_THRE_INT_ENABLE);
    }

    //up_serialout(priv, CK_UART_IER, cr);
}


/****************************************************************************
 *  * Name: yunos_bsp_enable_rxint
 *  *
 *  * Description:
 *  *   Call to enable or disable RX intterupt
 *  *
 *  ****************************************************************************/
void yunos_bsp_enable_rxint(uint8_t id, bool enable)
{
    uint32_t cr;
    struct bsp_uart_s *priv = g_uart_devs[id];

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return;
    }

    /* And restore the interrupt state (see the interrupt enable/usage table above) */
    cr = up_serialin(priv, CK_UART_IER);
    if(enable)
    {
        cr &= ~(IER_RDA_INT_ENABLE);
        cr |= (IER_RDA_INT_ENABLE);
    }
    else
    {
        cr &= ~(IER_RDA_INT_ENABLE);
    }
    up_serialout(priv, CK_UART_IER, cr);
}


/****************************************************************************
 *  * Name: yunos_bsp_uart_shutdown
 *  *
 *  * Description:
 *  *   Disable the UART.  This method is called when the serial port is closed
 *  *
 *  ****************************************************************************/
void yunos_bsp_uart_shutdown(uint8_t id)
{
    struct bsp_uart_s *priv = g_uart_devs[id];
    unsigned int* addr = (unsigned int*)priv->usartbase;

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return;
    }

    /* Clear TX & RX circle buffer. */
    addr[CK_UART_IER] &= ~IER_RDA_INT_ENABLE;
//    yunos_bsp_intc_disable_irq(priv->irq);
//    irq_detach(priv->irq);

}


/****************************************************************************
 *  * Name: yunos_bsp_uart_txready
 *  *
 *  * Description:
 *  *   Return true if the transmit data register is empty
 *  *
 *  ****************************************************************************/
bool yunos_bsp_uart_txready(uint8_t id)
{
    bool ret = false;
    struct bsp_uart_s *priv = g_uart_devs[id];

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return 0;
    }

    //if ((up_serialin(priv, CK_UART_IIR) == LSR_IIR_THR_EMP) && (!priv->btxquery))
    {
        ret = true;
    }

    return ret;
}

/****************************************************************************
 *  * Name: yunos_bsp_uart_rxavailable
 *  *
 *  * Description:
 *  *   Return true if the receive register is not empty
 *  *
 *  ****************************************************************************/
bool yunos_bsp_uart_rxavailable(uint8_t id)
{
    bool ret = false;
    struct bsp_uart_s *priv = g_uart_devs[id];

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return false;
    }
    if ((up_serialin(priv, CK_UART_LSR) & LSR_DATA_READY) && (!priv->brxquery))
    {
        ret = true;
    }

    return ret;
}

/****************************************************************************
 * Name: yunos_bsp_uart_set_onewire
 *
 * Description:
 *  Set serial one wire mode or not.
 *
 * Input parameters:
 *  is_onewire    - is onw wire mode, 0 = no, 1 = one wire
 *
 * Returned Value:
 *  Zero on success
 *  -1 on failed
 *
 ****************************************************************************/
int yunos_bsp_uart_set_onewire(uint8_t id, uint8_t is_onewire)
{
    struct bsp_uart_s *priv = g_uart_devs[id];

    if(priv == NULL)
    {
//        LOG("uart","uart %d has not configed \n", id);
        return -1;
    }
    priv->onewire = is_onewire;

    return OK;
}

int fputc(int ch, FILE *stream)
{
    yunos_bsp_uart_putc(1, ch);

    return 0;
}
