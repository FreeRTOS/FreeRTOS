/****************************************************************************
* © 2013 Microchip Technology Inc. and its subsidiaries.
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
*/

/** @defgroup interrupt interrupt
 *  @{
 */
/** @file interrupt.h
 \brief This is the header file for interrupt.c
 This program is designed to allow the other C programs to be able to use this component

 There are entry points for all C wrapper API implementation

<b>Platform:</b> This is ARC-based component 

<b>Toolset:</b> Metaware IDE(8.5.1)
<b>Reference:</b> smsc_reusable_fw_requirement.doc */

/*******************************************************************************
 *  SMSC version control information (Perforce):
 *
 *  FILE:     $File: //depot_pcs/FWEng/Release/projects/CEC1302_CLIB/release2/Source/hw_blks/kernel/skern/source/interrupt/interrupt.h $
 *  REVISION: $Revision: #1 $
 *  DATETIME: $DateTime: 2015/12/23 15:37:58 $
 *  AUTHOR:   $Author: akrishnan $
 *
 *  Revision history (latest first):
 *      #xx
 ***********************************************************************************
 */

#ifndef _INTERRUPT_H_
#define _INTERRUPT_H_


/* public function prototypes */
void interrupt_block_init(void);
void null_handler(void);

/* macro for interrupt control */
/* 16-bit timers interrupt control */
#define sbit_TIMER0				( 1UL << 0UL )
#define sbit_TIMER1				( 1UL << 1UL )
#define sbit_TIMER2				( 1UL << 2UL )
#define sbit_TIMER3				( 1UL << 3Ul )

#define disable_timer0_irq()	mCLR_BIT(sbit_TIMER0, MMCR_EC_GIRQ23_ENABLE_SET)
#define enable_timer0_irq()		mSET_BIT(sbit_TIMER0, MMCR_EC_GIRQ23_ENABLE_SET)
#define clear_timer0_source()	mCLR_SRC_BIT(sbit_TIMER0, MMCR_EC_GIRQ23_SOURCE)
#define get_timer0_source()	    mGET_BIT(sbit_TIMER0, MMCR_EC_GIRQ23_SOURCE)

#define disable_timer1_irq()	mCLR_BIT(sbit_TIMER1, MMCR_EC_GIRQ23_ENABLE_SET)
#define enable_timer1_irq()		mSET_BIT(sbit_TIMER1, MMCR_EC_GIRQ23_ENABLE_SET)
#define clear_timer1_source()	mCLR_SRC_BIT(sbit_TIMER1, MMCR_EC_GIRQ23_SOURCE)
#define get_timer1_source()	    mGET_BIT(sbit_TIMER1, MMCR_EC_GIRQ23_SOURCE)

#define disable_timer2_irq()	mCLR_BIT(sbit_TIMER2, MMCR_EC_GIRQ23_ENABLE_SET)
#define enable_timer2_irq()		mSET_BIT(sbit_TIMER2, MMCR_EC_GIRQ23_ENABLE_SET)
#define clear_timer2_source()	mCLR_SRC_BIT(sbit_TIMER2, MMCR_EC_GIRQ23_SOURCE)
#define get_timer2_source()	    mGET_BIT(sbit_TIMER2, MMCR_EC_GIRQ23_SOURCE)

#define disable_timer3_irq()	mCLR_BIT(sbit_TIMER3, MMCR_EC_GIRQ23_ENABLE_SET)
#define enable_timer3_irq()		mSET_BIT(sbit_TIMER3, MMCR_EC_GIRQ23_ENABLE_SET)
#define clear_timer3_source()	mCLR_SRC_BIT(sbit_TIMER3, MMCR_EC_GIRQ23_SOURCE)
#define get_timer3_source()	    mGET_BIT(sbit_TIMER3, MMCR_EC_GIRQ23_SOURCE)


/* hibernation timers interrupt control */
#define sbit_HTIMER0			( 1UL << 20 )
#define sbit_HTIMER1			b_bit14

#define disable_htimer0_irq()	mCLR_BIT(sbit_HTIMER0, MMCR_EC_GIRQ17_ENABLE_SET)
#define enable_htimer0_irq()	mSET_BIT(sbit_HTIMER0, MMCR_EC_GIRQ17_ENABLE_SET)
#define clear_htimer0_source()	mCLR_SRC_BIT(sbit_HTIMER0, MMCR_EC_GIRQ17_SOURCE)
#define get_htimer0_source()	mGET_BIT(sbit_HTIMER0, MMCR_EC_GIRQ17_SOURCE)

#define disable_htimer1_irq()	mCLR_BIT(sbit_HTIMER1, MMCR_EC_GIRQ23_ENABLE_SET)
#define enable_htimer1_irq()	mSET_BIT(sbit_HTIMER1, MMCR_EC_GIRQ23_ENABLE_SET)
#define clear_htimer1_source()	mCLR_SRC_BIT(sbit_HTIMER1, MMCR_EC_GIRQ23_SOURCE)
#define get_htimer1_source()	mGET_BIT(sbit_HTIMER1, MMCR_EC_GIRQ23_SOURCE)

/* RTC  interrupt control */
#define b_bit18 (1 << 18)
#define b_bit19 (1 << 19)
#define sbit_RTC_INT                   b_bit18
#define disable_rtc_irq()              mCLR_BIT(sbit_RTC_INT, MMCR_EC_GIRQ17_ENABLE_SET)
#define enable_rtc_irq()               mSET_BIT(sbit_RTC_INT, MMCR_EC_GIRQ17_ENABLE_SET)
#define clear_rtc_irq_source()         mCLR_SRC_BIT(sbit_RTC_INT, MMCR_EC_GIRQ17_ENABLE_SET)
#define get_rtc_irq_source()           mGET_BIT(sbit_RTC_INT, MMCR_EC_GIRQ17_ENABLE_SET)
/* RTC  alarm interrupt control */
#define sbit_RTC_ALM_INT               b_bit19
#define disable_rtc_alm_irq()          mCLR_BIT(sbit_RTC_ALM_INT, MMCR_EC_GIRQ17_ENABLE_SET)
#define enable_rtc_alm_irq()           mSET_BIT(sbit_RTC_ALM_INT, MMCR_EC_GIRQ17_ENABLE_SET)
#define clear_rtc_irq_alm_source()     mCLR_SRC_BIT(sbit_RTC_ALM_INT, MMCR_EC_GIRQ17_ENABLE_SET)
#define get_rtc_irq_alm_source()       mGET_BIT(sbit_RTC_ALM_INT, MMCR_EC_GIRQ17_ENABLE_SET)

/* week timer interrupt control */
#define sbit_WKTIMER			b_bit7

#define disable_wktimer_irq()	mCLR_BIT(sbit_WKTIMER, MMCR_EC_GIRQ23_ENABLE_SET)
#define enable_wktimer_irq()	mSET_BIT(sbit_WKTIMER, MMCR_EC_GIRQ23_ENABLE_SET)
#define clear_wktimer_source()	mCLR_SRC_BIT(sbit_WKTIMER, MMCR_EC_GIRQ23_SOURCE)
#define get_wktimer_source()	mGET_BIT(sbit_WKTIMER, MMCR_EC_GIRQ23_SOURCE)


/* scan matrix interrupt control */
#define sbit_SCANNER			b_bit16
#define disable_scanner_irq()	mCLR_BIT(sbit_SCANNER, MMCR_EC_GIRQ18_ENABLE_SET)
#define enable_scanner_irq()	mSET_BIT(sbit_SCANNER, MMCR_EC_GIRQ18_ENABLE_SET)
#define clear_scanner_source()	mCLR_SRC_BIT(sbit_SCANNER, MMCR_EC_GIRQ18_SOURCE)
#define get_scanner_source()	mGET_BIT(sbit_SCANNER, MMCR_EC_GIRQ18_SOURCE)


/* PS2 interrupt control */
/* PS2 activity interrupt */
#define sbit_PS2_ACT_0			  b_bit13
#define sbit_PS2_ACT_1			  b_bit14
#define sbit_PS2_ACT_2			  b_bit15
/* PS2 wakeup interrupt: detect start bit */
#define sbit_PS2_WK_0A			  b_bit17
#define sbit_PS2_WK_1B			  b_bit20
#define sbit_PS2_WK_2			  b_bit21

/* PS2 activity interrupt control */
#define disable_ps2_act_0_irq()	  mCLR_BIT(sbit_PS2_ACT_0, MMCR_EC_GIRQ19_ENABLE_SET)
#define enable_ps2_act_0_irq()	  mSET_BIT(sbit_PS2_ACT_0, MMCR_EC_GIRQ19_ENABLE_SET)
#define clear_ps2_act_0_source()  mCLR_SRC_BIT(sbit_PS2_ACT_0, MMCR_EC_GIRQ19_SOURCE)
#define get_ps2_act_0_source()    mGET_BIT(sbit_PS2_ACT_0, MMCR_EC_GIRQ19_SOURCE)

#define disable_ps2_act_1_irq()	  mCLR_BIT(sbit_PS2_ACT_1, MMCR_EC_GIRQ19_ENABLE_SET)
#define enable_ps2_act_1_irq()	  mSET_BIT(sbit_PS2_ACT_1, MMCR_EC_GIRQ19_ENABLE_SET)
#define clear_ps2_act_1_source()  mCLR_SRC_BIT(sbit_PS2_ACT_1, MMCR_EC_GIRQ19_SOURCE)
#define get_ps2_act_1_source()    mGET_BIT(sbit_PS2_ACT_1, MMCR_EC_GIRQ19_SOURCE)

#define disable_ps2_act_2_irq()	  mCLR_BIT(sbit_PS2_ACT_2, MMCR_EC_GIRQ19_ENABLE_SET)
#define enable_ps2_act_2_irq()	  mSET_BIT(sbit_PS2_ACT_2, MMCR_EC_GIRQ19_ENABLE_SET)
#define clear_ps2_act_2_source()  mCLR_SRC_BIT(sbit_PS2_ACT_2, MMCR_EC_GIRQ19_SOURCE)
#define get_ps2_act_2_source()    mGET_BIT(sbit_PS2_ACT_2, MMCR_EC_GIRQ19_SOURCE)

/* PS2 wakeup interrupt control */
#define disable_ps2_wk_0_irq()	  mCLR_BIT(sbit_PS2_WK_0A, MMCR_EC_GIRQ19_ENABLE_SET)
#define enable_ps2_wk_0_irq()	  mSET_BIT(sbit_PS2_WK_0A, MMCR_EC_GIRQ19_ENABLE_SET)
#define clear_ps2_wk_0_source()   mCLR_SRC_BIT(sbit_PS2_WK_0A, MMCR_EC_GIRQ19_SOURCE)
#define get_ps2_wk_0_source()     mGET_BIT(sbit_PS2_WK_0A, MMCR_EC_GIRQ19_SOURCE)

#define disable_ps2_wk_1_irq()	  mCLR_BIT(sbit_PS2_WK_1B, MMCR_EC_GIRQ19_ENABLE_SET)
#define enable_ps2_wk_1_irq()	  mSET_BIT(sbit_PS2_WK_1B, MMCR_EC_GIRQ19_ENABLE_SET)
#define clear_ps2_wk_1_source()   mCLR_SRC_BIT(sbit_PS2_WK_1B, MMCR_EC_GIRQ19_SOURCE)
#define get_ps2_wk_1_source()     mGET_BIT(sbit_PS2_WK_1B, MMCR_EC_GIRQ19_SOURCE)

#define disable_ps2_wk_2_irq()	  mCLR_BIT(sbit_PS2_WK_2, MMCR_EC_GIRQ19_ENABLE_SET)
#define enable_ps2_wk_2_irq()	  mSET_BIT(sbit_PS2_WK_2, MMCR_EC_GIRQ19_ENABLE_SET)
#define clear_ps2_wk_2_source()   mCLR_SRC_BIT(sbit_PS2_WK_2, MMCR_EC_GIRQ19_SOURCE)
#define get_ps2_wk_2_source()     mGET_BIT(sbit_PS2_WK_2, MMCR_EC_GIRQ19_SOURCE)


/* ICT interrupt control */
/* capture 0~5 interrupt */
#define sbit_ICT_CAPTURE0		  b_bit17
#define sbit_ICT_CAPTURE1		  b_bit18
#define sbit_ICT_CAPTURE2		  b_bit19
#define sbit_ICT_CAPTURE3		  b_bit20
#define sbit_ICT_CAPTURE4		  b_bit21
#define sbit_ICT_CAPTURE5		  b_bit22

/* capture 0 interrupt control */
#define disable_capture0_irq()	  mCLR_BIT(sbit_ICT_CAPTURE0, MMCR_EC_GIRQ23_ENABLE_SET)
#define enable_capture0_irq()	  mSET_BIT(sbit_ICT_CAPTURE0, MMCR_EC_GIRQ23_ENABLE_SET)
#define clear_capture0_source()	  mCLR_SRC_BIT(sbit_ICT_CAPTURE0, MMCR_EC_GIRQ23_SOURCE)
#define get_capture0_source()	  mGET_BIT(sbit_ICT_CAPTURE0, MMCR_EC_GIRQ23_SOURCE)


/* SMBus interrupt control */


/* GPIO interrupt control */


/* BC link interrupt control */
/* bclink A~D interrupt */
#define sbit_BCLINK_A_BUSY		  b_bit0
#define sbit_BCLINK_A_ERR		  b_bit1
#define sbit_BCLINK_A_INT		  b_bit2
#define sbit_BCLINK_B_BUSY		  b_bit3
#define sbit_BCLINK_B_ERR		  b_bit4
#define sbit_BCLINK_B_INT		  b_bit5
#define sbit_BCLINK_C_BUSY		  b_bit6
#define sbit_BCLINK_C_ERR		  b_bit7
#define sbit_BCLINK_C_INT		  b_bit8
#define sbit_BCLINK_D_BUSY		  b_bit9
#define sbit_BCLINK_D_ERR		  b_bit10
#define sbit_BCLINK_D_INT		  b_bit11

/* bclink B interrupt control */
#define disable_bclink_b_busy_irq()		mCLR_BIT(sbit_BCLINK_B_BUSY, MMCR_EC_GIRQ18_ENABLE_SET)
#define enable_bclink_b_busy_irq()		mSET_BIT(sbit_BCLINK_B_BUSY, MMCR_EC_GIRQ18_ENABLE_SET)
#define clear_bclink_b_busy_source()    mCLR_SRC_BIT(sbit_BCLINK_B_BUSY, MMCR_EC_GIRQ18_SOURCE)
#define get_bclink_b_busy_source()      mGET_BIT(sbit_BCLINK_B_BUSY, MMCR_EC_GIRQ18_SOURCE)

#define disable_bclink_b_err_irq()		mCLR_BIT(sbit_BCLINK_B_ERR, MMCR_EC_GIRQ18_ENABLE_SET)
#define enable_bclink_b_err_irq()		mSET_BIT(sbit_BCLINK_B_ERR, MMCR_EC_GIRQ18_ENABLE_SET)
#define clear_bclink_b_err_source()     mCLR_SRC_BIT(sbit_BCLINK_B_ERR, MMCR_EC_GIRQ18_SOURCE)
#define get_bclink_b_err_source()       mGET_BIT(sbit_BCLINK_B_ERR, MMCR_EC_GIRQ18_SOURCE)

#define disable_bclink_b_int_irq()		mCLR_BIT(sbit_BCLINK_B_INT, MMCR_EC_GIRQ18_ENABLE_SET)
#define enable_bclink_b_int_irq()		mSET_BIT(sbit_BCLINK_B_INT, MMCR_EC_GIRQ18_ENABLE_SET)
#define clear_bclink_b_int_source()     mCLR_SRC_BIT(sbit_BCLINK_B_INT, MMCR_EC_GIRQ18_SOURCE)
#define get_bclink_b_int_source()       mGET_BIT(sbit_BCLINK_B_INT, MMCR_EC_GIRQ18_SOURCE)

/* UART interrupt control */
#define sbit_UART_INT                   b_bit0

#define disable_uart_irq()              mCLR_BIT(sbit_UART_INT, MMCR_EC_GIRQ15_ENABLE_SET)
#define enable_uart_irq()               mSET_BIT(sbit_UART_INT, MMCR_EC_GIRQ15_ENABLE_SET)
#define clear_uart_irq_source()         mCLR_SRC_BIT(sbit_UART_INT, MMCR_EC_GIRQ15_SOURCE)
#define get_uart_irq_source()           mGET_BIT(sbit_UART_INT, MMCR_EC_GIRQ15_SOURCE)

// GIRQ IDs for EC Interrupt Aggregator
enum MEC_GIRQ_IDS
{
    MEC_GIRQ08_ID = 0,
    MEC_GIRQ09_ID,                  
    MEC_GIRQ10_ID,                  
    MEC_GIRQ11_ID,                  
    MEC_GIRQ12_ID,                  
    MEC_GIRQ13_ID,                  
    MEC_GIRQ14_ID,                  
    MEC_GIRQ15_ID,                  
    MEC_GIRQ16_ID,                  
    MEC_GIRQ17_ID,                  
    MEC_GIRQ18_ID,                  
    MEC_GIRQ19_ID,                  
    MEC_GIRQ20_ID,                  
    MEC_GIRQ21_ID,                  
    MEC_GIRQ22_ID,                  
    MEC_GIRQ23_ID,                                   
    MEC_GIRQ_ID_MAX
};

//Bitmask of GIRQ in ECIA Block Registers
#define MEC_GIRQ08_BITMASK          (1UL << (MEC_GIRQ08_ID + 8))
#define MEC_GIRQ09_BITMASK          (1UL << (MEC_GIRQ09_ID + 8))  
#define MEC_GIRQ10_BITMASK          (1UL << (MEC_GIRQ10_ID + 8))  
#define MEC_GIRQ11_BITMASK          (1UL << (MEC_GIRQ11_ID + 8)) 
#define MEC_GIRQ12_BITMASK          (1UL << (MEC_GIRQ12_ID + 8)) 
#define MEC_GIRQ13_BITMASK          (1UL << (MEC_GIRQ13_ID + 8)) 
#define MEC_GIRQ14_BITMASK          (1UL << (MEC_GIRQ14_ID + 8)) 
#define MEC_GIRQ15_BITMASK          (1UL << (MEC_GIRQ15_ID + 8)) 
#define MEC_GIRQ16_BITMASK          (1UL << (MEC_GIRQ16_ID + 8)) 
#define MEC_GIRQ17_BITMASK          (1UL << (MEC_GIRQ17_ID + 8)) 
#define MEC_GIRQ18_BITMASK          (1UL << (MEC_GIRQ18_ID + 8)) 
#define MEC_GIRQ19_BITMASK          (1UL << (MEC_GIRQ19_ID + 8)) 
#define MEC_GIRQ20_BITMASK          (1UL << (MEC_GIRQ20_ID + 8)) 
#define MEC_GIRQ21_BITMASK          (1UL << (MEC_GIRQ21_ID + 8)) 
#define MEC_GIRQ22_BITMASK          (1UL << (MEC_GIRQ22_ID + 8)) 
#define MEC_GIRQ23_BITMASK          (1UL << (MEC_GIRQ23_ID + 8)) 

#define INTERRUPT_MODE_ALL_AGGREGATED        (0u)
#define INTERRUPT_MODE_DIRECT                (1u)

// Bit map of GIRQs whose sources can be directly connected to the NVIC
// GIRQs 12 - 18, 23
#define ECIA_GIRQ_DIRECT_BITMAP     (0x0087F000ul)

/*
 *  n = b[7:0]   = zero-based direct mapped NVIC ID
 *  m = b[15:8]  = zero-based aggregated NVIC ID
 *  a = b[23:16] = block Aggregator register block ID
 *  b = b[31:24] = block bit position in Aggregator registers
*/
#define IROUTE(b,a,m,n) 	(((uint32_t)(n)&0xFFul) + \
                            (((uint32_t)(m)&0xFFul)<<8u) + \
                            ((((uint32_t)(a)-8ul)&0x0F)<<16u) + \
                            (((uint32_t)(b)&0x1Ful)<<24))

#define ECIA_NVIC_ID_BITPOS             (0u)
#define ECIA_IA_NVIC_ID_BITPOS          (8u)
#define ECIA_GIRQ_ID_BITPOS             (16u)
#define ECIA_GIRQ_BIT_BITPOS            (24u)

//
// GIRQ08
//
#define GPIO_0140_IROUTE                IROUTE(0,8,57,57)
#define GPIO_0141_IROUTE                IROUTE(1,8,57,57)
#define GPIO_0142_IROUTE                IROUTE(2,8,57,57)
#define GPIO_0143_IROUTE                IROUTE(3,8,57,57)
#define GPIO_0144_IROUTE                IROUTE(4,8,57,57)
#define GPIO_0145_IROUTE                IROUTE(5,8,57,57)
#define GPIO_0147_IROUTE                IROUTE(7,8,57,57)
//
#define GPIO_0150_IROUTE                IROUTE(8,8,57,57)
#define GPIO_0151_IROUTE                IROUTE(9,8,57,57)
#define GPIO_0152_IROUTE                IROUTE(10,8,57,57)
#define GPIO_0153_IROUTE                IROUTE(11,8,57,57)
#define GPIO_0154_IROUTE                IROUTE(12,8,57,57)
#define GPIO_0155_IROUTE                IROUTE(13,8,57,57)
#define GPIO_0156_IROUTE                IROUTE(14,8,57,57)
#define GPIO_0157_IROUTE                IROUTE(15,8,57,57)
//
#define GPIO_0160_IROUTE                IROUTE(16,8,57,57)
#define GPIO_0161_IROUTE                IROUTE(17,8,57,57)
#define GPIO_0162_IROUTE                IROUTE(18,8,57,57)
#define GPIO_0163_IROUTE                IROUTE(19,8,57,57)
#define GPIO_0164_IROUTE                IROUTE(20,8,57,57)
#define GPIO_0165_IROUTE                IROUTE(21,8,57,57)
#define GPIO_0166_IROUTE                IROUTE(22,8,57,57)
#define GPIO_0167_IROUTE                IROUTE(23,8,57,57)

//
// GIRQ09
//
#define GPIO_0100_IROUTE                IROUTE(0,9,58,58)
#define GPIO_0101_IROUTE                IROUTE(1,9,58,58)
#define GPIO_0102_IROUTE                IROUTE(2,9,58,58)
#define GPIO_0103_IROUTE                IROUTE(3,9,58,58)
#define GPIO_0104_IROUTE                IROUTE(4,9,58,58)
#define GPIO_0105_IROUTE                IROUTE(5,9,58,58)
#define GPIO_0105_IROUTE                IROUTE(5,9,58,58)
#define GPIO_0107_IROUTE                IROUTE(7,9,58,58)
//
#define GPIO_0110_IROUTE                IROUTE(8,9,58,58)
#define GPIO_0111_IROUTE                IROUTE(9,9,58,58)
#define GPIO_0112_IROUTE                IROUTE(10,9,58,58)
#define GPIO_0113_IROUTE                IROUTE(11,9,58,58)
#define GPIO_0114_IROUTE                IROUTE(12,9,58,58)
#define GPIO_0115_IROUTE                IROUTE(13,9,58,58)
#define GPIO_0116_IROUTE                IROUTE(14,9,58,58)
#define GPIO_0117_IROUTE                IROUTE(15,9,58,58)
//
#define GPIO_0120_IROUTE                IROUTE(16,9,58,58)
#define GPIO_0121_IROUTE                IROUTE(17,9,58,58)
#define GPIO_0122_IROUTE                IROUTE(18,9,58,58)
#define GPIO_0124_IROUTE                IROUTE(20,9,58,58)
#define GPIO_0125_IROUTE                IROUTE(21,9,58,58)
#define GPIO_0126_IROUTE                IROUTE(22,9,58,58)
#define GPIO_0127_IROUTE                IROUTE(23,9,58,58)
//
#define GPIO_0130_IROUTE                IROUTE(24,9,58,58)
#define GPIO_0131_IROUTE                IROUTE(25,9,58,58)
#define GPIO_0132_IROUTE                IROUTE(26,9,58,58)
#define GPIO_0133_IROUTE                IROUTE(27,9,58,58)
#define GPIO_0134_IROUTE                IROUTE(28,9,58,58)
#define GPIO_0135_IROUTE                IROUTE(29,9,58,58)
#define GPIO_0136_IROUTE                IROUTE(30,9,58,58)

//
// GIRQ10
//
#define GPIO_0040_IROUTE                IROUTE(0,10,59,59)
#define GPIO_0041_IROUTE                IROUTE(1,10,59,59)
#define GPIO_0042_IROUTE                IROUTE(2,10,59,59)
#define GPIO_0043_IROUTE                IROUTE(3,10,59,59)
#define GPIO_0044_IROUTE                IROUTE(4,10,59,59)
#define GPIO_0045_IROUTE                IROUTE(5,10,59,59)
#define GPIO_0045_IROUTE                IROUTE(5,10,59,59)
#define GPIO_0047_IROUTE                IROUTE(7,10,59,59)
//
#define GPIO_0050_IROUTE                IROUTE(8,10,59,59)
#define GPIO_0051_IROUTE                IROUTE(9,10,59,59)
#define GPIO_0052_IROUTE                IROUTE(10,10,59,59)
#define GPIO_0053_IROUTE                IROUTE(11,10,59,59)
#define GPIO_0054_IROUTE                IROUTE(12,10,59,59)
#define GPIO_0055_IROUTE                IROUTE(13,10,59,59)
#define GPIO_0056_IROUTE                IROUTE(14,10,59,59)
#define GPIO_0057_IROUTE                IROUTE(15,10,59,59)
//
#define GPIO_0060_IROUTE                IROUTE(16,10,59,59)
#define GPIO_0061_IROUTE                IROUTE(17,10,59,59)
#define GPIO_0062_IROUTE                IROUTE(18,10,59,59)
#define GPIO_0063_IROUTE                IROUTE(19,10,59,59)
#define GPIO_0064_IROUTE                IROUTE(20,10,59,59)
#define GPIO_0065_IROUTE                IROUTE(21,10,59,59)
#define GPIO_0066_IROUTE                IROUTE(22,10,59,59)
#define GPIO_0067_IROUTE                IROUTE(23,10,59,59)
//
#define GPIO_0070_IROUTE                IROUTE(24,10,59,59)
#define GPIO_0071_IROUTE                IROUTE(25,10,59,59)
#define GPIO_0072_IROUTE                IROUTE(26,10,59,59)
#define GPIO_0073_IROUTE                IROUTE(27,10,59,59)
#define GPIO_0074_IROUTE                IROUTE(28,10,59,59)
#define GPIO_0075_IROUTE                IROUTE(29,10,59,59)
#define GPIO_0076_IROUTE                IROUTE(30,10,59,59)

//
// GIRQ11
//
#define GPIO_0000_IROUTE                IROUTE(0,11,60,60)
#define GPIO_0001_IROUTE                IROUTE(1,11,60,60)
#define GPIO_0002_IROUTE                IROUTE(2,11,60,60)
#define GPIO_0003_IROUTE                IROUTE(3,11,60,60)
#define GPIO_0004_IROUTE                IROUTE(4,11,60,60)
#define GPIO_0005_IROUTE                IROUTE(5,11,60,60)
#define GPIO_0006_IROUTE                IROUTE(6,11,60,60)
#define GPIO_0007_IROUTE                IROUTE(7,11,60,60)
//
#define GPIO_0010_IROUTE                IROUTE(8,11,60,60)
#define GPIO_0011_IROUTE                IROUTE(9,11,60,60)
#define GPIO_0012_IROUTE                IROUTE(10,11,60,60)
#define GPIO_0013_IROUTE                IROUTE(11,11,60,60)
#define GPIO_0014_IROUTE                IROUTE(12,11,60,60)
#define GPIO_0015_IROUTE                IROUTE(13,11,60,60)
#define GPIO_0016_IROUTE                IROUTE(14,11,60,60)
#define GPIO_0017_IROUTE                IROUTE(15,11,60,60)
//
#define GPIO_0020_IROUTE                IROUTE(16,11,60,60)
#define GPIO_0021_IROUTE                IROUTE(17,11,60,60)
#define GPIO_0022_IROUTE                IROUTE(18,11,60,60)
#define GPIO_0023_IROUTE                IROUTE(19,11,60,60)
#define GPIO_0024_IROUTE                IROUTE(20,11,60,60)
#define GPIO_0025_IROUTE                IROUTE(21,11,60,60)
#define GPIO_0026_IROUTE                IROUTE(22,11,60,60)
#define GPIO_0027_IROUTE                IROUTE(23,11,60,60)
//
#define GPIO_0030_IROUTE                IROUTE(24,11,60,60)
#define GPIO_0031_IROUTE                IROUTE(25,11,60,60)
#define GPIO_0032_IROUTE                IROUTE(26,11,60,60)
#define GPIO_0033_IROUTE                IROUTE(27,11,60,60)
#define GPIO_0034_IROUTE                IROUTE(28,11,60,60)
#define GPIO_0035_IROUTE                IROUTE(29,11,60,60)
#define GPIO_0036_IROUTE                IROUTE(30,11,60,60)

//
// GIRQ12
//
#define SMB0_IROUTE                     IROUTE(0,12,61,0)
#define SMB1_IROUTE                     IROUTE(1,12,61,1)
#define SMB2_IROUTE                     IROUTE(2,12,61,2)
#define SMB3_IROUTE                     IROUTE(3,12,61,3)
// SMB wakes have no direct connection to NVIC, always aggregated
#define SMB0_WAKE_IROUTE                IROUTE(4,12,61,61)
#define SMB1_WAKE_IROUTE                IROUTE(5,12,61,61)
#define SMB2_WAKE_IROUTE                IROUTE(6,12,61,61)
#define SMB3_WAKE_IROUTE                IROUTE(7,12,61,61)
#define SMB4_WAKE_IROUTE                IROUTE(8,12,61,61)

//
// GIRQ13
//
#define DMA0_IROUTE                     IROUTE(16,13,62,4)
#define DMA1_IROUTE                     IROUTE(17,13,62,5)
#define DMA2_IROUTE                     IROUTE(18,13,62,6)
#define DMA3_IROUTE                     IROUTE(19,13,62,7)
#define DMA4_IROUTE                     IROUTE(20,13,62,8)
#define DMA5_IROUTE                     IROUTE(21,13,62,9)
#define DMA6_IROUTE                     IROUTE(22,13,62,10)
#define DMA7_IROUTE                     IROUTE(23,13,62,11)
#define DMA8_IROUTE                     IROUTE(24,13,62,81)
#define DMA9_IROUTE                     IROUTE(25,13,62,82)
#define DMA10_IROUTE                    IROUTE(26,13,62,83)
#define DMA11_IROUTE                    IROUTE(27,13,62,84)

//
// GIRQ14
//
#define LPC_BERR_IROUTE                 IROUTE(2,14,63,12)

//
// GIRQ15
//
#define UART0_IROUTE                    IROUTE(0,15,64,13)
#define EMI0_IROUTE                     IROUTE(2,15,64,14)
#define ACPI_EC0_IBF_IROUTE             IROUTE(6,15,64,15)
#define ACPI_EC0_OBF_IROUTE             IROUTE(7,15,64,16)
#define ACPI_EC1_IBF_IROUTE             IROUTE(8,15,64,17)
#define ACPI_EC1_OBF_IROUTE             IROUTE(9,15,64,18)
#define ACPI_PM1_CTL_IROUTE             IROUTE(10,15,64,19)
#define ACPI_PM1_EN_IROUTE              IROUTE(11,15,64,20)
#define ACPI_PM1_STS_IROUTE             IROUTE(12,15,64,21)
#define EM8042_OBF_IROUTE               IROUTE(13,15,64,22)
#define EM8042_IBF_IROUTE               IROUTE(14,15,64,23)
#define MBOX_IROUTE                     IROUTE(15,15,64,24)
#define MBOX_DATA_IROUTE                IROUTE(16,15,64,40) 

//
// GIRQ16
//
#define PECI_IROUTE                     IROUTE(3,16,65,25)

//
// GIRQ17
//
#define TACH0_IROUTE                    IROUTE(0,17,66,26)
#define TACH1_IROUTE                    IROUTE(1,17,66,27)
#define PS2_0_WAKE_IROUTE               IROUTE(2,17,66,66)
#define PS2_1_WAKE_IROUTE               IROUTE(3,17,66,66)
#define PS2_2_WAKE_IROUTE               IROUTE(4,17,66,66)
#define PS2_3_WAKE_IROUTE               IROUTE(5,17,66,66)
#define BC_WAKE_IROUTE                  IROUTE(6,17,66,66)
#define ADC_SNGL_IROUTE                 IROUTE(10,17,66,28)
#define ADC_RPT_IROUTE                  IROUTE(11,17,66,29)
#define ADC2PWM1_IROUTE                 IROUTE(12,17,66,30)
#define ADC2PWM2_IROUTE                 IROUTE(13,17,66,31)
#define PS2_0_IROUTE                    IROUTE(14,17,66,32)
#define PS2_1_IROUTE                    IROUTE(15,17,66,33)
#define PS2_2_IROUTE                    IROUTE(16,17,66,34)
#define PS2_3_IROUTE                    IROUTE(17,17,66,35)
#define RTC_IROUTE                      IROUTE(18,17,66,91)
#define RTC_ALARM_IROUTE                IROUTE(19,17,66,92)
#define HTIMER_IROUTE                   IROUTE(20,17,66,38)
#define KSC_IROUTE                      IROUTE(21,17,66,39)
#define KSC_WAKE_IROUTE                 IROUTE(22,17,66,66)
#define RPM_STALL_IROUTE                IROUTE(23,17,66,41)
#define RPM_SPIN_IROUTE                 IROUTE(24,17,66,42)
#define PFR_IROUTE                      IROUTE(25,17,66,43)
#define LED0_IROUTE                     IROUTE(26,17,66,44)
#define LED1_IROUTE                     IROUTE(27,17,66,45)
#define LED2_IROUTE                     IROUTE(28,17,66,46)
#define BCM_ERR_IROUTE                  IROUTE(29,17,66,47)
#define BCM_BUSY_IROUTE                 IROUTE(30,17,66,48)

//
// GIRQ18
//
#define SPI0_TX_IROUTE                  IROUTE(0,18,67,36)
#define SPI0_RX_IROUTE                  IROUTE(1,18,67,37)
#define SPI1_TX_IROUTE                  IROUTE(2,18,67,55)
#define SPI1_RX_IROUTE                  IROUTE(3,18,67,56)
#define LED3_IROUTE                     IROUTE(4,18,67,85)
#define PKE_ERR_IROUTE                  IROUTE(5,18,67,86)
#define PKE_END_IROUTE                  IROUTE(6,18,67,87)
#define NDRNG_IROUTE                    IROUTE(7,18,67,88)
#define AES_IROUTE                      IROUTE(8,18,67,89)
#define HASH_IROUTE                     IROUTE(9,18,67,90)

//
// GIRQ19, Aggregated only
//
#define LRESET_IROUTE                   IROUTE(0,19,68,68)
#define VCC_PWRGD_IROUTE                IROUTE(1,19,68,68)

//
// GIRQ20, Aggregated only
//
#define GPIO_0200_IROUTE                IROUTE(0,20,69,69)
#define GPIO_0201_IROUTE                IROUTE(1,20,69,69)
#define GPIO_0202_IROUTE                IROUTE(2,20,69,69)
#define GPIO_0203_IROUTE                IROUTE(3,20,69,69)
#define GPIO_0204_IROUTE                IROUTE(4,20,69,69)
#define GPIO_0206_IROUTE                IROUTE(6,20,69,69)
//
#define GPIO_0210_IROUTE                IROUTE(8,20,69,69)
#define GPIO_0211_IROUTE                IROUTE(9,20,69,69)
#define GPIO_0212_IROUTE                IROUTE(10,20,69,69)
#define GPIO_0213_IROUTE                IROUTE(11,20,69,69)

//
// GIRQ21
//
// No sources

//
// GIRQ22
//
// No sources

//
// GIRQ23
//
#define BTMR0_IROUTE                    IROUTE(0,23,72,49)
#define BTMR1_IROUTE                    IROUTE(1,23,72,50)
#define BTMR2_IROUTE                    IROUTE(2,23,72,51)
#define BTMR3_IROUTE                    IROUTE(3,23,72,52)
#define BTMR4_IROUTE                    IROUTE(4,23,72,53)
#define BTMR5_IROUTE                    IROUTE(5,23,72,54)

// GIRQ08 Bit Positions 
#define GIRQ08_GPIO_0140_BITPOS         (0)
#define GIRQ08_GPIO_0141_BITPOS         (1)
#define GIRQ08_GPIO_0142_BITPOS         (2)
#define GIRQ08_GPIO_0143_BITPOS         (3)
#define GIRQ08_GPIO_0144_BITPOS         (4)
#define GIRQ08_GPIO_0145_BITPOS         (5)
//#define GIRQ08_GPIO_0146_BITPOS       (6) RESERVED
#define GIRQ08_GPIO_0147_BITPOS         (7)
//
#define GIRQ08_GPIO_0150_BITPOS         (8)
#define GIRQ08_GPIO_0151_BITPOS         (9)
#define GIRQ08_GPIO_0152_BITPOS         (10)
#define GIRQ08_GPIO_0153_BITPOS         (11)
#define GIRQ08_GPIO_0154_BITPOS         (12)
#define GIRQ08_GPIO_0155_BITPOS         (13)
#define GIRQ08_GPIO_0156_BITPOS         (14) 
#define GIRQ08_GPIO_0157_BITPOS         (15)
//
#define GIRQ08_GPIO_0160_BITPOS         (16)
#define GIRQ08_GPIO_0161_BITPOS         (17)
#define GIRQ08_GPIO_0162_BITPOS         (18)
#define GIRQ08_GPIO_0163_BITPOS         (19)
#define GIRQ08_GPIO_0164_BITPOS         (20)
#define GIRQ08_GPIO_0165_BITPOS         (21)
#define GIRQ08_GPIO_0166_BITPOS         (22) 
#define GIRQ08_GPIO_0167_BITPOS         (23)
//
#define GIRQ08_MASK                     (0x00FFFFBFul)
#define GIRQ08_WAKE_CAPABLE_MASK        (0x00FFFFBFul)
//

// GIRQ09 Bit Positions 
#define GIRQ09_GPIO_0100_BITPOS         (0)
#define GIRQ09_GPIO_0101_BITPOS         (1)
#define GIRQ09_GPIO_0102_BITPOS         (2)
#define GIRQ09_GPIO_0103_BITPOS         (3)
#define GIRQ09_GPIO_0104_BITPOS         (4)
#define GIRQ09_GPIO_0105_BITPOS         (5)
#define GIRQ09_GPIO_0106_BITPOS         (6) 
#define GIRQ09_GPIO_0107_BITPOS         (7)
//
#define GIRQ09_GPIO_0110_BITPOS         (8)
#define GIRQ09_GPIO_0111_BITPOS         (9)
#define GIRQ09_GPIO_0112_BITPOS         (10)
#define GIRQ09_GPIO_0113_BITPOS         (11)
#define GIRQ09_GPIO_0114_BITPOS         (12)
#define GIRQ09_GPIO_0115_BITPOS         (13)
#define GIRQ09_GPIO_0116_BITPOS         (14) 
#define GIRQ09_GPIO_0117_BITPOS         (15)
//
#define GIRQ09_GPIO_0120_BITPOS         (16)
#define GIRQ09_GPIO_0121_BITPOS         (17)
#define GIRQ09_GPIO_0122_BITPOS         (18)
//#define GIRQ09_GPIO_0123_BITPOS       (19) RESERVED
#define GIRQ09_GPIO_0124_BITPOS         (20)
#define GIRQ09_GPIO_0125_BITPOS         (21)
#define GIRQ09_GPIO_0126_BITPOS         (22) 
#define GIRQ09_GPIO_0127_BITPOS         (23)
//
#define GIRQ09_GPIO_0130_BITPOS         (24)
#define GIRQ09_GPIO_0131_BITPOS         (25)
#define GIRQ09_GPIO_0132_BITPOS         (26)
#define GIRQ09_GPIO_0133_BITPOS         (27)
#define GIRQ09_GPIO_0134_BITPOS         (28)
#define GIRQ09_GPIO_0135_BITPOS         (29)
#define GIRQ09_GPIO_0136_BITPOS         (30) 
//#define GIRQ09_GPIO_0137_BITPOS       (31) RESERVED
//
#define GIRQ09_MASK                     (0x7FF7FFFFul)
#define GIRQ09_WAKE_CAPABLE_MASK        (0x7FF7FFFFul)
//

// GIRQ10 Bit Positions 
#define GIRQ10_GPIO_0040_BITPOS         (0)
#define GIRQ10_GPIO_0041_BITPOS         (1)
#define GIRQ10_GPIO_0042_BITPOS         (2)
#define GIRQ10_GPIO_0043_BITPOS         (3)
#define GIRQ10_GPIO_0044_BITPOS         (4)
#define GIRQ10_GPIO_0045_BITPOS         (5)
#define GIRQ10_GPIO_0046_BITPOS         (6) 
#define GIRQ10_GPIO_0047_BITPOS         (7)
//
#define GIRQ10_GPIO_0050_BITPOS         (8)
#define GIRQ10_GPIO_0051_BITPOS         (9)
#define GIRQ10_GPIO_0052_BITPOS         (10)
#define GIRQ10_GPIO_0053_BITPOS         (11)
#define GIRQ10_GPIO_0054_BITPOS         (12)
#define GIRQ10_GPIO_0055_BITPOS         (13)
#define GIRQ10_GPIO_0056_BITPOS         (14) 
#define GIRQ10_GPIO_0057_BITPOS         (15)
//
#define GIRQ10_GPIO_0060_BITPOS         (16)
#define GIRQ10_GPIO_0061_BITPOS         (17)
#define GIRQ10_GPIO_0062_BITPOS         (18)
#define GIRQ10_GPIO_0063_BITPOS         (19)
#define GIRQ10_GPIO_0064_BITPOS         (20)
#define GIRQ10_GPIO_0065_BITPOS         (21)
#define GIRQ10_GPIO_0066_BITPOS         (22) 
#define GIRQ10_GPIO_0067_BITPOS         (23)
//
#define GIRQ10_GPIO_0070_BITPOS         (24)
#define GIRQ10_GPIO_0071_BITPOS         (25)
#define GIRQ10_GPIO_0072_BITPOS         (26)
#define GIRQ10_GPIO_0073_BITPOS         (27)
#define GIRQ10_GPIO_0074_BITPOS         (28)
#define GIRQ10_GPIO_0075_BITPOS         (29)
#define GIRQ10_GPIO_0076_BITPOS         (30) 
//#define GIRQ10_GPIO_0077_BITPOS       (31) RESERVED
//
#define GIRQ10_MASK                     (0x7FFFFFFFul)
#define GIRQ10_WAKE_CAPABLE_MASK        (0x7FFFFFFFul)
//

// GIRQ11 Bit Positions 
#define GIRQ11_GPIO_0000_BITPOS         (0)
#define GIRQ11_GPIO_0001_BITPOS         (1)
#define GIRQ11_GPIO_0002_BITPOS         (2)
#define GIRQ11_GPIO_0003_BITPOS         (3)
#define GIRQ11_GPIO_0004_BITPOS         (4)
#define GIRQ11_GPIO_0005_BITPOS         (5)
#define GIRQ11_GPIO_0006_BITPOS         (6) 
#define GIRQ11_GPIO_0007_BITPOS         (7)
//
#define GIRQ11_GPIO_0010_BITPOS         (8)
#define GIRQ11_GPIO_0011_BITPOS         (9)
#define GIRQ11_GPIO_0012_BITPOS         (10)
#define GIRQ11_GPIO_0013_BITPOS         (11)
#define GIRQ11_GPIO_0014_BITPOS         (12)
#define GIRQ11_GPIO_0015_BITPOS         (13)
#define GIRQ11_GPIO_0016_BITPOS         (14) 
#define GIRQ11_GPIO_0017_BITPOS         (15)
//
#define GIRQ11_GPIO_0020_BITPOS         (16)
#define GIRQ11_GPIO_0021_BITPOS         (17)
#define GIRQ11_GPIO_0022_BITPOS         (18)
#define GIRQ11_GPIO_0023_BITPOS         (19)
#define GIRQ11_GPIO_0024_BITPOS         (20)
#define GIRQ11_GPIO_0025_BITPOS         (21)
#define GIRQ11_GPIO_0026_BITPOS         (22) 
#define GIRQ11_GPIO_0027_BITPOS         (23)
//
#define GIRQ11_GPIO_0030_BITPOS         (24)
#define GIRQ11_GPIO_0031_BITPOS         (25)
#define GIRQ11_GPIO_0032_BITPOS         (26)
#define GIRQ11_GPIO_0033_BITPOS         (27)
#define GIRQ11_GPIO_0034_BITPOS         (28)
#define GIRQ11_GPIO_0035_BITPOS         (29)
#define GIRQ11_GPIO_0036_BITPOS         (30) 
//#define GIRQ11_GPIO_0037_BITPOS       (31) RESERVED
//
#define GIRQ11_MASK                     (0x7FFFFFFFul)
#define GIRQ11_WAKE_CAPABLE_MASK        (0x7FFFFFFFul)
//

// GIRQ12 Bit Positions 
#define GIRQ12_SMBUS0_BITPOS            (0)
#define GIRQ12_SMBUS1_BITPOS            (1)
#define GIRQ12_SMBUS2_BITPOS            (2)
#define GIRQ12_SMBUS3_BITPOS            (3)
#define GIRQ12_SMBUS0_WAKE_BITPOS       (4)
#define GIRQ12_SMBUS1_WAKE_BITPOS       (5)
#define GIRQ12_SMBUS2_WAKE_BITPOS       (6)
#define GIRQ12_SMBUS3_WAKE_BITPOS       (7)
#define GIRQ12_SMBUS4_WAKE_BITPOS       (8)
// RESERVED bits[31:9]
#define GIRQ12_MASK                     (0x01FFul)
#define GIRQ12_WAKE_CAPABLE_MASK        (0x01F0ul)
//

// GIRQ13 Bit Positions 
#define GIRQ13_DMA0_BITPOS              (16)
#define GIRQ13_DMA1_BITPOS              (17)
#define GIRQ13_DMA2_BITPOS              (18)
#define GIRQ13_DMA3_BITPOS              (19)
#define GIRQ13_DMA4_BITPOS              (20)
#define GIRQ13_DMA5_BITPOS              (21)
#define GIRQ13_DMA6_BITPOS              (22)
#define GIRQ13_DMA7_BITPOS              (23)
#define GIRQ13_DMA8_BITPOS              (24)
#define GIRQ13_DMA9_BITPOS              (25)
#define GIRQ13_DMA10_BITPOS             (26)
#define GIRQ13_DMA11_BITPOS             (27)
//
#define GIRQ13_MASK                     (0x0FFF0000ul)
#define GIRQ13_WAKE_CAPABLE_MASK        (0x00000000ul)
//

// GIRQ14 Bit Positions 
#define GIRQ14_LPC_BITPOS               (2)
//
#define GIRQ14_MASK                     (0x04ul)
#define GIRQ14_WAKE_CAPABLE_MASK        (0x00ul)
//

// GIRQ15 Bit Positions 
#define GIRQ15_UART0_BITPOS             (0)
#define GIRQ15_IMAP_BITPOS              (2)
#define GIRQ15_KBD_K_BITPOS             (3)
#define GIRQ15_KBD_M_BITPOS             (4)
#define GIRQ15_ACPI0_IBF_BITPOS         (6)
#define GIRQ15_ACPI0_OBF_BITPOS         (7)
#define GIRQ15_ACPI1_IBF_BITPOS         (8)
#define GIRQ15_ACPI1_OBF_BITPOS         (9)
#define GIRQ15_ACPI_PM1CTL_BITPOS       (10)
#define GIRQ15_ACPI_PM1EN_BITPOS        (11)
#define GIRQ15_ACPI_PM1STS_BITPOS       (12)
#define GIRQ15_MF8042_OBF_BITPOS        (13)
#define GIRQ15_MF8042_IBF_BITPOS        (14)
#define GIRQ15_MAILBOX_BITPOS           (15)
#define GIRQ15_MAILBOX_DATA_BITPOS      (16)
//
#define GIRQ15_MASK                     (0x01FFDDul)
#define GIRQ15_WAKE_CAPABLE_MASK        (0x000000ul)
//

// GIRQ16 Bit Positions 
#define GIRQ16_PECI_BITPOS              (3)
//
#define GIRQ16_MASK                     (0x08ul)
#define GIRQ16_WAKE_CAPABLE_MASK        (0x00ul)
//

// GIRQ17 Bit Positions 
#define GIRQ17_TACH0_BITPOS             (0)
#define GIRQ17_TACH1_BITPOS             (1)
#define GIRQ17_PS2_0_WAKE_BITPOS        (2)
#define GIRQ17_PS2_1_WAKE_BITPOS        (3)
#define GIRQ17_PS2_2_WAKE_BITPOS        (4)
#define GIRQ17_PS2_3_WAKE_BITPOS        (5)
#define GIRQ17_BC_WAKE_BITPOS           (6)
// RESERVED b[9:7]
#define GIRQ17_ADC_INT0_BITPOS          (10)
#define GIRQ17_ADC_INT1_BITPOS          (11)
#define GIRQ17_V2P_INT0_BITPOS          (12)
#define GIRQ17_V2P_INT1_BITPOS          (13)
#define GIRQ17_PS2_0_BITPOS             (14)
#define GIRQ17_PS2_1_BITPOS             (15)
#define GIRQ17_PS2_2_BITPOS             (16)
#define GIRQ17_PS2_3_BITPOS             (17)
// RESERVED b[19:18]
#define GIRQ17_HIBTMR_BITPOS            (20)
#define GIRQ17_KEY_INT_BITPOS           (21)
#define GIRQ17_KEY_INT_WAKE_BITPOS      (22)
#define GIRQ17_RPM_STALL_BITPOS         (23)
#define GIRQ17_RPM_SPIN_BITPOS          (24)
#define GIRQ17_VBAT_BITPOS              (25)
#define GIRQ17_LED0_BITPOS              (26)
#define GIRQ17_LED1_BITPOS              (27)
#define GIRQ17_LED2_BITPOS              (28)
#define GIRQ17_MBC_ERR_BITPOS           (29)
#define GIRQ17_MBC_BUSY_BITPOS          (30)
//
#define GIRQ17_MASK                     (0x7FF3FC7Ful)
#define GIRQ17_WAKE_CAPABLE_MASK        (0x0230007Cul)
//

// GIRQ18 Bit Positions 
#define GIRQ18_SPI0_TX_BITPOS           (0)
#define GIRQ18_SPI0_RX_BITPOS           (1)
#define GIRQ18_SPI1_TX_BITPOS           (2)
#define GIRQ18_SPI1_RX_BITPOS           (3)
#define GIRQ18_LED3_BITPOS              (4)  // NVIC 85
#define GIRQ18_PKE_ERR_BITPOS           (5)  // NVIC 86
#define GIRQ18_PKE_END_BITPOS           (6)  // NVIC 87
#define GIRQ18_TRNG_BITPOS              (7)  // NVIC 88
#define GIRQ18_AES_BITPOS               (8)  // NVIC 89
#define GIRQ18_HASH_BITPOS              (9)  // NVIC 90
//
#define GIRQ18_MASK                     (0x0FFul)
#define GIRQ18_WAKE_CAPABLE_MASK        (0x000ul)
//

// GIRQ19 Bit Positions 
#define GIRQ19_LRESET_BITPOS            (0)
#define GIRQ19_VCC_PWRGD_BITPOS         (1)
//
#define GIRQ19_MASK                     (0x03ul)
#define GIRQ19_WAKE_CAPABLE_MASK        (0x03ul)
//

// GIRQ20 Bit Positions 
#define GIRQ20_GPIO_0200_BITPOS         (0)
#define GIRQ20_GPIO_0201_BITPOS         (1)
#define GIRQ20_GPIO_0202_BITPOS         (2)
#define GIRQ20_GPIO_0203_BITPOS         (3)
#define GIRQ20_GPIO_0204_BITPOS         (4)
//#define GIRQ20_GPIO_0205_BITPOS       (5)
#define GIRQ20_GPIO_0206_BITPOS         (6)
//#define GIRQ20_GPIO_0207_BITPOS       (7)
//
#define GIRQ20_GPIO_0210_BITPOS         (8)
#define GIRQ20_GPIO_0211_BITPOS         (9)
#define GIRQ20_GPIO_0212_BITPOS         (10)
#define GIRQ20_GPIO_0213_BITPOS         (11)
// 
#define GIRQ20_MASK                     (0x0F5Ful)
#define GIRQ20_WAKE_CAPABLE_MASK        (0x0F5Ful)
//

// GIRQ21 Bit Positions 
#define GIRQ21_MASK                     (0x00ul)
#define GIRQ21_WAKE_CAPABLE_MASK        (0x00ul)

// GIRQ22 Bit Positions 
#define GIRQ22_MASK                     (0x00ul)
#define GIRQ22_WAKE_CAPABLE_MASK        (0x00ul)

// GIRQ23 Bit Positions 
#define GIRQ23_TMR0_BITPOS              (0)
#define GIRQ23_TMR1_BITPOS              (1)
#define GIRQ23_TMR2_BITPOS              (2)
#define GIRQ23_TMR3_BITPOS              (3)
#define GIRQ23_TMR4_BITPOS              (4)
#define GIRQ23_TMR5_BITPOS              (5)
//
#define GIRQ23_MASK                     (0x03Ful)
#define GIRQ23_WAKE_CAPABLE_MASK        (0x000ul)
//

/* ------------------------------------------------------------------------------- */
/*                  NVIC,ECIA Routing Policy for Direct Mode                       */
/* ------------------------------------------------------------------------------- */
/* In Direct Mode, some interrupts could be configured to be used as aggregated.
 * Configuration:
 *      1. Always set ECS Interrupt Direct enable bit.         
 *      2. If GIRQn aggregated set Block Enable bit.
 *      3. If GIRQn direct then clear Block Enable bit and enable individual NVIC inputs.
 *  Switching issues:
 *  Aggregate enable/disable requires set/clear single GIRQn bit in GIRQ Block En/Clr registers.
 *  Also requires set/clear of individual NVIC Enables.
 *  
 * Note: interrupt_is_girq_direct() internal function uses this policy to detect 
 * if any interrupt is configured as direct or aggregated
*/

/** Initialize EC Interrupt Aggregator
 * @param mode 1 - Direct Map mode, 0 - Fully Aggregated Mode 
 * @param girq_bitmask - BitMask of GIRQ to be configured as aggregated 
 *                     This parameter is only applicable in direct mode.
 * @note All GPIO's and wake capable sources are always 
 * aggregated! GPIO's interrupts will still work in direct mode.
 * Block wakes are not be routed to the processor in direct 
 * mode. 
 * Note2: This function disables and enables global interrupt  
 */
void interrupt_init(uint8_t mode, uint32_t girq_bitmask);

/** Set interrupt routing mode to aggregated or direct. 
 * @param mode 1 = Direct (except GPIO & wake), 0 = All Aggregated 
 * @note In direct mode, one could enable certain GIRQs as aggregated using 
 * p_interrupt_ecia_block_enable_set function
 */
void interrupt_mode_set(uint8_t mode);

/** Clears all individual interrupts Enables and Source in ECIA,
 *  and Clears all NVIC external enables and pending bits  
 */
void interrupt_reset(void);

/** Enables interrupt for a device 
 * @param dev_iroute - source IROUTING information 
 * @note This function disables and enables global interrupt 
 */
void interrupt_device_enable(uint32_t dev_iroute);

/** Disables interrupt for a device
 * @param dev_iroute - source IROUTING information  
 * @note This function disables and enables global interrupt 
 */
void interrupt_device_disable(uint32_t dev_iroute);

/* ------------------------------------------------------------------------------- */
/*                  ECIA APIs using device IROUTE() as input                       */ 
/* ------------------------------------------------------------------------------- */

/** Clear Source in the ECIA for the device  
 * @param devi - device IROUTING value  
 */
void interrupt_device_ecia_source_clear(const uint32_t dev_iroute);

/** Get the Source bit in the ECIA for the device  
 * @param devi - device IROUTING value  
 * @return 0 if source bit not set; else non-zero value
 */
uint32_t interrupt_device_ecia_source_get(const uint32_t dev_iroute);

/** Get the Result bit in the ECIA for the device  
 * @param devi - device IROUTING value  
 * @return 0 if result bit not set; else non-zero value
 */
uint32_t interrupt_device_ecia_result_get(const uint32_t dev_iroute);

/* ------------------------------------------------------------------------------- */
/*                  NVIC APIs using device IROUTE() as input                       */ 
/* ------------------------------------------------------------------------------- */
/* Note that if the device interrupt is aggregated, then these APIs would affect the 
 * NVIC corresponding to the aggregated GIRQ 
 */

/**  Enable/Disable the NVIC (in the NVIC controller) for the device
 * @param dev_iroute : source IROUTING information (encoded in a uint32_t)
 * @param en_flag : 1 = Enable the NVIC IRQ, 0 = Disable the NVIC IRQ 
 * @note Recommended to use interrupt_device_enable, interrupt_device_disable
 * to enable/disable interrupts for the device, since those APIs configure ECIA as well
 */
void interrupt_device_nvic_enable(uint32_t dev_iroute, uint8_t en_flag);

/** Set NVIC priority for specified peripheral interrupt source
 * @param dev_iroute - source IROUTING information (encoded in a uint32_t)
 * @param nvic_pri - NVIC Priority
 * @note 1. If ECIA is in aggregated mode, the priority affects all interrupt 
 * sources in the GIRQ. 
 * 2. This function disables and enables global interrupt    
 */
void interrupt_device_nvic_priority_set(const uint32_t dev_iroute, const uint8_t nvic_pri);

/** Return NVIC priority for interrupt source
 * @param dev_iroute - source IROUTING information 
 * @return uint32_t  NVIC priority 
 */
uint32_t interrupt_device_nvic_priority_get(const uint32_t dev_iroute);

/** Return NVIC pending for interrupt source
 * @param dev_iroute - source IROUTING information 
 * @return uint8_t 0(not pending), 1 (pending in NVIC) 
 *  
 */
uint8_t interrupt_device_nvic_pending_get(const uint32_t dev_iroute);

/** Set NVIC pending for interrupt source
 * @param dev_iroute - source IROUTING information   
 */
void interrupt_device_nvic_pending_set(const uint32_t dev_iroute);

/** Clears NVIC pending for interrupt source
 * @param dev_iroute - source IROUTING information 
 * @return uint8_t 0(not pending), 1 (pending in NVIC) - before clear 
 * @note This function disables and enables global interrupt    
 */
uint8_t interrupt_device_nvic_pending_clear(const uint32_t dev_iroute);
    
/* ------------------------------------------------------------------------------- */
/* Peripheral Functions - Operations on GIRQ Block Enable Set, Enable Clear        *
 * and Status Register                                                             */
/* ------------------------------------------------------------------------------- */

/** Enable specified GIRQ in ECIA block
 * @param girq_id - enum MEC_GIRQ_IDS 
 */
 void p_interrupt_ecia_block_enable_set(uint8_t girq_id);
  
 /** Enable GIRQs in ECIA Block 
 * @param girq_bitmask - Bitmask of GIRQs to be enabled in ECIA Block  
 */
void p_interrupt_ecia_block_enable_bitmask_set(uint32_t girq_bitmask);

/** Check if specified GIRQ block enabled or not
 * @param girq_id - enum MEC_GIRQ_IDS 
 * @return retVal - 1 if the particular GIRQ block enabled, else 0
 */
uint8_t p_interrupt_ecia_block_enable_get(uint8_t girq_id);

/** Set all GIRQ block enables */
void p_interrupt_ecia_block_enable_all_set(void);

/** Clear specified GIRQ in ECIA Block 
 * @param girq_id - enum MEC_GIRQ_IDS 
 */
void p_interrupt_ecia_block_enable_clr(uint8_t girq_id);

/** Clear GIRQs in ECIA Block 
 * @param girq_bitmask - Bitmask of GIRQs to be cleared in ECIA Block  
 */
void p_interrupt_ecia_block_enable_bitmask_clr(uint32_t girq_bitmask);

/** p_interrupt_ecia_block_enable_all_clr - Clears all GIRQ block enables */
void p_interrupt_ecia_block_enable_all_clr(void);
 
 /** Get status of GIRQ in ECIA Block
 * @param girq_id - enum MEC_GIRQ_IDS  
 * @return 0 if status bit not set; else non-zero value
 */
uint32_t p_interrupt_ecia_block_irq_status_get(uint8_t girq_id);

/** Reads the Block IRQ Vector Register
  * @return 32-bit value
 */
uint32_t p_interrupt_ecia_block_irq_all_status_get(void);

/* ---------------------------------------------------------------------------- */
/* Peripheral Functions - Operations on GIRQx Source, Enable, Result            *
 * and Enable Registers                                                         */
/* ---------------------------------------------------------------------------- */

/** Clear specified interrupt source bit in GIRQx
 * @param girq_id - enum MEC_GIRQ_IDS
 * @param bitnum -[0, 31]
 */
void p_interrupt_ecia_girq_source_clr(int16_t girq_id, uint8_t bitnum);

/** Read the specified interrupt source bit in GIRQx
 * @param girq_id - enum MEC_GIRQ_IDS
 * @param bitnum -[0, 31]
 * @return 0 if source bit not set; else non-zero value
 */
uint32_t p_interrupt_ecia_girq_source_get(int16_t girq_id, uint8_t bitnum);

/** Enable the specified interrupt in GIRQx
 * girq_id - enum MEC_GIRQ_IDS
 * bitnum = [0, 31]
 */
void p_interrupt_ecia_girq_enable_set(uint16_t girq_id, uint8_t bitnum);

/** Disable the specified interrupt in GIRQx
 * girq_id - enum MEC_GIRQ_IDS
 * bitnum = [0, 31]
 */
void p_interrupt_ecia_girq_enable_clr(uint16_t girq_id, uint8_t bitnum);

/** Read the status of the specified interrupt in GIRQx
 * girq_id - enum MEC_GIRQ_IDS
 * bitnum = [0, 31]
 * @return 0 if enable bit not set; else non-zero value
 */
uint32_t p_interrupt_ecia_girq_enable_get(uint16_t girq_id, uint8_t bitnum);

/** Read the result bit of the interrupt in GIRQx
 * @param girq_id - enum MEC_GIRQ_IDS
 * @param bitnum -[0, 31]
 * @return 0 if enable bit not set; else non-zero value
 */
uint32_t p_interrupt_ecia_girq_result_get(int16_t girq_id, uint8_t bitnum);

/* ------------------------------------------------------------------------------- */
/* Peripheral Function - Operations on all GIRQs                                   */
/* ------------------------------------------------------------------------------- */

/** Clear all aggregator GIRQn status registers */
void p_interrupt_ecia_girqs_source_reset(void);

/** Clear all aggregator GIRQn enables */
 void p_interrupt_ecia_girqs_enable_reset(void);
 
/* ------------------------------------------------------------------------------- */
/* Peripheral Function - Function to set interrupt control                         */
/* ------------------------------------------------------------------------------- */

/** Set interrupt control 
 * @param nvic_en_flag : 0 = Alternate NVIC disabled, 1 = Alternate NVIC enabled
 */
 void p_interrupt_control_set(uint8_t nvic_en_flag);
     
 /** Read interrupt control 
 * @return uint8_t - 0 = Alternate NVIC disabled, 1 = Alternate NVIC enabled
 */
uint8_t p_interrupt_control_get(void);

/* ------------------------------------------------------------------------------- */
/* Peripheral Functions - NVIC                                                     */
/* ------------------------------------------------------------------------------- */

/**  Enable/Disable the NVIC IRQ in the NVIC interrupt controller
 * @param nvic_num : NVIC number (see enum IRQn_Type)
 * @param en_flag : 1 = Enable the NVIC IRQ, 0 = Disable the NVIC IRQ
 * @note Application should perform this operation
 */
 void p_interrupt_nvic_enable(IRQn_Type nvic_num, uint8_t en_flag);
     
 /**  ecia_nvic_clr_en - Clear all NVIC external enables */ 
void p_interrupt_nvic_extEnables_clr(void);

/** Clear all NVIC external enables and pending bits */
void p_interrupt_nvic_enpend_clr(void);

/** Set NVIC external priorities to POR value */
void p_interrupt_nvic_priorities_default_set(void);

/** Set NVIC external priorities to specified priority (0 - 7)
 * @param zero-based 3-bit priority value: 0=highest, 7=lowest.
 * @note NVIC highest priority is the value 0, lowest is all 1's.
 * Each external interrupt has an 8-bit register and the priority 
 * is left justified in the registers. MECxxx implements 8 priority 
 * levels or bits [7:5] in the register. Lowest priority = 0xE0
 */
void p_interrupt_nvic_priorities_set(uint8_t new_pri);

#endif /*_INTERRUPT_H_*/

/**   @}
 */



