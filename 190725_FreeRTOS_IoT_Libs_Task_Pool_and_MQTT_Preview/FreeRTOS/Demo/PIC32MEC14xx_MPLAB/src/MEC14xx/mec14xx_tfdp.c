/*****************************************************************************
* © 2014 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
*****************************************************************************/

/** @file mec14xx_tfdp.c
 *MEC14xx Trace FIFO Data Port hardware access
 */
/** @defgroup MEC14xx Peripherals TFDP
 *  @{
 */

#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_pcr.h"
#include "MEC14xx/mec14xx_gpio.h"
#include "MEC14xx/mec14xx_trace_func.h"


#ifdef ENABLE_TFDP_TRACE

#undef TFDP_PIN_1
#undef TFDP_PIN_2


#define TFDP_PIN_1 (GPIO_0116_ID)   // Func1 PullUp enabled
#define TFDP_PIN_2 (GPIO_0117_ID)   // Func1 PullUp enabled



static void tfdp_xmit_header(uint16_t nbr)
{
    TFDP->DATA = TFDP_FRAME_START;
    TFDP_DELAY();

    TFDP->DATA = (uint8_t)nbr;
    TFDP_DELAY();
    TFDP->DATA = (uint8_t)(nbr >> 8);
    TFDP_DELAY();
}


static void tfdp_xmit_hword(uint16_t hword)
{
    TFDP->DATA = (uint8_t)hword;
    TFDP_DELAY();
    TFDP->DATA = (uint8_t)(hword >> 8);
    TFDP_DELAY();
}


static void tfdp_xmit_word(uint32_t word)
{
    uint8_t i;

    for (i = 0u; i < 4; i++) {
        TFDP->DATA = (uint8_t)word;
        word >>= 8; 
        TFDP_DELAY();
    }
}


/**
 * tfdp_sleep_en - Gate clocks On/Off to TFDP block when idle
 * 
 * @author C21969 (2/4/2014)
 * 
 * @param sleep_en (1=Gate clocks when idle), (0=Do not gate 
 *                 clocks when idle)
 */
void tfdp_sleep_en(uint8_t sleep_en)
{
    if ( sleep_en ) {
        PCR->EC_SLEEP_EN |= (PCR_EC_TFDP_SLP_CLK);
    } else {
        PCR->EC_SLEEP_EN &= ~(PCR_EC_TFDP_SLP_CLK);
    }
}


/**
 * tfdp_enable - Init Trace FIFO Data Port
 * @param boolean true=enable TFDP, false=disable TFDP 
 * @param boolean true=change TFDP pin configuration. 
 * If TFDP is enabled then GPIO103/104 set to Alt. Func. 1 
 * Else GPIO103/104 set to GPIO input, internal PU enabled. 
 * @note - 
 */
void tfdp_enable(uint8_t en, uint8_t pin_cfg)
{
    uint32_t delay;

    if (en) {
        
        if (pin_cfg) {
            // Input with AltOut=1 to drive high when switched to output
            GPIO_CTRL->REG[TFDP_PIN_1].w = (1ul << 16);
            GPIO_CTRL->REG[TFDP_PIN_2].w = (1ul << 16);

            delay = 128;
            while ( delay-- )
            {
                CPU_NOP();
            }

            // GPIO Output enabled (drive based on above settings)
            GPIO_CTRL->REG[TFDP_PIN_1].w |= (1ul << 9);
            GPIO_CTRL->REG[TFDP_PIN_2].w |= (1ul << 9);

            delay = 128;
            while ( delay-- )
            {
                CPU_NOP();
            }

            // Switch to Function 1 (TFDP mode b[13:12]=01b)
            GPIO_CTRL->REG[TFDP_PIN_1].w = (1ul << 16) + (1ul << 12);
            GPIO_CTRL->REG[TFDP_PIN_2].w = (1ul << 16) + (1ul << 12);

        }
        /* b[0]=1(Enable)
         * b[1]=0(Shift data out on rising edge) 
         * b[3:2]=00b TFDP shift clocks = AHB_CLK/2
         * b[6:4]=000b 1 clock inter-packet delay
         */
        TFDP->CONTROL = 0x01u;

    } 
    else
    {
        TFDP->CONTROL = 0x00u;
        if (pin_cfg) 
        { /* Set to POR value (tri-stated input) */
            GPIO_CTRL->REG[TFDP_PIN_1].w = 0;
            GPIO_CTRL->REG[TFDP_PIN_2].w = 0;
        }
    }
} // end tfdp_enable()


/**
 * TFDPTrace0 - TRACE0: transmit 16-bit trace number lsb first 
 * over TFDP. 
 * 
 * @author sworley 
 * 
 * @param nbr 16-bit trace number 
 * @param b unused
 * 
 * @return uint8_t always TRUE 
 * @note Function implements critical section. 
 * Uses tool kit __disable_irq()/__enable_irq() pair which may use 
 * priviledged Cortex-Mx instructions. 
 */
void TFDPTrace0 ( uint16_t nbr, uint8_t b )
{
#ifdef ENABLE_TRACE_MASK_IRQ
    uint32_t isave;

    isave = mips32r2_dis_intr();
#endif

    (void)b;
    tfdp_xmit_header(nbr);

#ifdef ENABLE_TRACE_MASK_IRQ
     mips32r2_restore_intr(isave);
#endif
}


/**
 * TRDPTrace1 - TRACE1: transmit 16-bit trace number lsb first 
 * and 16-bit data lsb first over TFDP. 
 * 
 * @author sworley 
 * 
 * @param nbr 16-bit trace number 
 * @param b unused 
 * @param uint32_t p1 16-bit data1 in b[15:0]
 * 
 * @return uint8_t always TRUE 
 * @note Function implements critical section. 
 * Uses tool kit __disable_irq()/__enable_irq() pair which may use 
 * priviledged Cortex-Mx instructions. 
 */
void TFDPTrace1 ( uint16_t nbr, uint8_t b, uint32_t p1 )
{
#ifdef ENABLE_TRACE_MASK_IRQ
    uint32_t isave;
    
    isave = mips32r2_dis_intr();
#endif
    (void)b;
    tfdp_xmit_header(nbr);
    tfdp_xmit_hword(p1);

#ifdef ENABLE_TRACE_MASK_IRQ
    mips32r2_restore_intr(isave);
#endif
}


/**
 * TFDPTrace2 - TRACE2: transmit 16-bit trace number lsb first 
 * and two 16-bit data parameters lsb first over TFDP.
 * 
 * @author sworley 
 * 
 * @param nbr trace number
 * @param b unused
 * @param uint32_t p1 16-bit data1 in b[15:0]
 * @param uint32_t p2 16-bit data2 in b[15:0]
 * 
 * @return uint8_t always TRUE 
 * @note Uses tool kit functions to save/disable/restore 
 *       interrupts for critical section. These may use
 *       priviledged instructions.
 */
void TFDPTrace2 ( uint16_t nbr, uint8_t b, uint32_t p1, uint32_t p2 )
{
#ifdef ENABLE_TRACE_MASK_IRQ
    uint32_t isave;
    
    isave = mips32r2_dis_intr();
#endif
    (void)b;
    tfdp_xmit_header(nbr);
    tfdp_xmit_hword(p1);
    tfdp_xmit_hword(p2);

#ifdef ENABLE_TRACE_MASK_IRQ
    mips32r2_restore_intr(isave);
#endif
}


/**
 * TFDPTrace3 - TRACE3: transmit 16-bit trace number lsb first 
 * and three 16-bit data parameters lsb first over TFDP.
 * 
 * @author sworley 
 * 
 * @param nbr trace number
 * @param b unused
 * @param uint32_t p1 16-bit data1 in b[15:0]
 * @param uint32_t p2 16-bit data2 in b[15:0]
 * @param uint32_t p3 16-bit data3 in b[15:0]
 * 
 * @return uint8_t always TRUE 
 * @note Uses tool kit functions to save/disable/restore 
 *       interrupts for critical section. These may use
 *       priviledged instructions. 
 */
void TFDPTrace3 ( uint16_t nbr, uint8_t b, uint32_t p1, uint32_t p2, uint32_t p3)
{
#ifdef ENABLE_TRACE_MASK_IRQ
    uint32_t isave;
    
    isave = mips32r2_dis_intr();
#endif  
    (void)b;
    tfdp_xmit_header(nbr);
    tfdp_xmit_hword(p1);
    tfdp_xmit_hword(p2);
    tfdp_xmit_hword(p3);

#ifdef ENABLE_TRACE_MASK_IRQ
    if ( isave & (1ul<<0) )
    {
        mips32r2_en_intr();
    }
#endif
}


/**
 * TFDPTrace4 - TRACE3: transmit 16-bit trace number lsb first 
 * and four 16-bit data parameters lsb first over TFDP.
 * 
 * @author sworley 
 * 
 * @param nbr trace number
 * @param b unused
 * @param uint32_t p1 16-bit data1 in b[15:0]
 * @param uint32_t p2 16-bit data2 in b[15:0]
 * @param uint32_t p3 16-bit data3 in b[15:0]
 * @param uint32_t p4 16-bit data4 in b[15:0]
 * 
 * @return uint8_t always TRUE 
 * @note Uses tool kit functions to save/disable/restore 
 *       interrupts for critical section. These may use
 *       priviledged instructions. 
 */
void TFDPTrace4 ( uint16_t nbr, uint8_t b, uint32_t p1, uint32_t p2, uint32_t p3, uint32_t p4)
{
#ifdef ENABLE_TRACE_MASK_IRQ
    uint32_t isave;
    
    isave = mips32r2_dis_intr();
#endif
    (void)b;
    tfdp_xmit_header(nbr);
    tfdp_xmit_hword(p1);
    tfdp_xmit_hword(p2);
    tfdp_xmit_hword(p3);
    tfdp_xmit_hword(p4);
      
#ifdef ENABLE_TRACE_MASK_IRQ
    if ( isave & (1ul<<0) )
    {
        mips32r2_en_intr();
    }
#endif
}


/** 
 *  TFDPTrace11 - Transmit one 32-bit data item over TFDP 
 * 
 *  @param nbr trace number
 *  @param b unused 
 *  @param uint32_t p1 32-bit data to be transmitted
 * 
 */
void TFDPTrace11( uint16_t nbr, uint8_t b, uint32_t p1)
{
#ifdef ENABLE_TRACE_MASK_IRQ
    uint32_t isave;
    
    isave = mips32r2_dis_intr();
#endif  
    (void)b;
    tfdp_xmit_header(nbr);
    tfdp_xmit_word(p1);
    
#ifdef ENABLE_TRACE_MASK_IRQ
    if ( isave & (1ul<<0) )
    {
        mips32r2_en_intr();
    }
#endif
}


/** 
 *  TFDPTrace12 - Transmit two 32-bit data items over TFDP 
 * 
 *  @param nbr trace number
 *  @param b unused 
 *  @param uint32_t p1 32-bit data1 to be transmitted
 *  @param uint32_t p2 32-bit data2 to be transmitted
 * 
 */
void TFDPTrace12( uint16_t nbr, uint8_t b, uint32_t p1, uint32_t p2 )
{
#ifdef ENABLE_TRACE_MASK_IRQ
    uint32_t isave;
    
    isave = mips32r2_dis_intr();
#endif  
    (void)b;
    tfdp_xmit_header(nbr);
    tfdp_xmit_word(p1);
    tfdp_xmit_word(p2);

#ifdef ENABLE_TRACE_MASK_IRQ
    if ( isave & (1ul<<0) )
    {
        mips32r2_en_intr();
    }
#endif
}

#endif // #ifdef ENABLE_TFDP_TRACE


/* end mec14xx_tfdp.c */
/**   @}
 */
