//*****************************************************************************
//
// hw_adc.h - Macros used when accessing the ADC hardware.
//
// Copyright (c) 2005-2007 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
// 
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  Any use in violation
// of the foregoing restrictions may subject the user to criminal sanctions
// under applicable laws, as well as to civil liability for the breach of the
// terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
// This is part of revision 1582 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __HW_ADC_H__
#define __HW_ADC_H__

//*****************************************************************************
//
// The following define the offsets of the ADC registers.
//
//*****************************************************************************
#define ADC_O_ACTSS             0x00000000  // Active sample register
#define ADC_O_RIS               0x00000004  // Raw interrupt status register
#define ADC_O_IM                0x00000008  // Interrupt mask register
#define ADC_O_ISC               0x0000000C  // Interrupt status/clear register
#define ADC_O_OSTAT             0x00000010  // Overflow status register
#define ADC_O_EMUX              0x00000014  // Event multiplexer select reg.
#define ADC_O_USTAT             0x00000018  // Underflow status register
#define ADC_O_SSPRI             0x00000020  // Channel priority register
#define ADC_O_PSSI              0x00000028  // Processor sample initiate reg.
#define ADC_O_SAC               0x00000030  // Sample Averaging Control reg.
#define ADC_O_SSMUX0            0x00000040  // Multiplexer select 0 register
#define ADC_O_SSCTL0            0x00000044  // Sample sequence control 0 reg.
#define ADC_O_SSFIFO0           0x00000048  // Result FIFO 0 register
#define ADC_O_SSFSTAT0          0x0000004C  // FIFO 0 status register
#define ADC_O_SSMUX1            0x00000060  // Multiplexer select 1 register
#define ADC_O_SSCTL1            0x00000064  // Sample sequence control 1 reg.
#define ADC_O_SSFIFO1           0x00000068  // Result FIFO 1 register
#define ADC_O_SSFSTAT1          0x0000006C  // FIFO 1 status register
#define ADC_O_SSMUX2            0x00000080  // Multiplexer select 2 register
#define ADC_O_SSCTL2            0x00000084  // Sample sequence control 2 reg.
#define ADC_O_SSFIFO2           0x00000088  // Result FIFO 2 register
#define ADC_O_SSFSTAT2          0x0000008C  // FIFO 2 status register
#define ADC_O_SSMUX3            0x000000A0  // Multiplexer select 3 register
#define ADC_O_SSCTL3            0x000000A4  // Sample sequence control 3 reg.
#define ADC_O_SSFIFO3           0x000000A8  // Result FIFO 3 register
#define ADC_O_SSFSTAT3          0x000000AC  // FIFO 3 status register
#define ADC_O_TMLB              0x00000100  // Test mode loopback register

//*****************************************************************************
//
// The following define the offsets of the ADC sequence registers.
//
//*****************************************************************************
#define ADC_O_SEQ               0x00000040  // Offset to the first sequence
#define ADC_O_SEQ_STEP          0x00000020  // Increment to the next sequence
#define ADC_O_X_SSMUX           0x00000000  // Multiplexer select register
#define ADC_O_X_SSCTL           0x00000004  // Sample sequence control register
#define ADC_O_X_SSFIFO          0x00000008  // Result FIFO register
#define ADC_O_X_SSFSTAT         0x0000000C  // FIFO status register

//*****************************************************************************
//
// The following define the bit fields in the ADC_ACTSS register.
//
//*****************************************************************************
#define ADC_ACTSS_ASEN3         0x00000008  // Sample sequence 3 enable
#define ADC_ACTSS_ASEN2         0x00000004  // Sample sequence 2 enable
#define ADC_ACTSS_ASEN1         0x00000002  // Sample sequence 1 enable
#define ADC_ACTSS_ASEN0         0x00000001  // Sample sequence 0 enable

//*****************************************************************************
//
// The following define the bit fields in the ADC_RIS register.
//
//*****************************************************************************
#define ADC_RIS_INR3            0x00000008  // Sample sequence 3 interrupt
#define ADC_RIS_INR2            0x00000004  // Sample sequence 2 interrupt
#define ADC_RIS_INR1            0x00000002  // Sample sequence 1 interrupt
#define ADC_RIS_INR0            0x00000001  // Sample sequence 0 interrupt

//*****************************************************************************
//
// The following define the bit fields in the ADC_IM register.
//
//*****************************************************************************
#define ADC_IM_MASK3            0x00000008  // Sample sequence 3 mask
#define ADC_IM_MASK2            0x00000004  // Sample sequence 2 mask
#define ADC_IM_MASK1            0x00000002  // Sample sequence 1 mask
#define ADC_IM_MASK0            0x00000001  // Sample sequence 0 mask

//*****************************************************************************
//
// The following define the bit fields in the ADC_ISC register.
//
//*****************************************************************************
#define ADC_ISC_IN3             0x00000008 // Sample sequence 3 interrupt
#define ADC_ISC_IN2             0x00000004 // Sample sequence 2 interrupt
#define ADC_ISC_IN1             0x00000002 // Sample sequence 1 interrupt
#define ADC_ISC_IN0             0x00000001 // Sample sequence 0 interrupt

//*****************************************************************************
//
// The following define the bit fields in the ADC_OSTAT register.
//
//*****************************************************************************
#define ADC_OSTAT_OV3           0x00000008  // Sample sequence 3 overflow
#define ADC_OSTAT_OV2           0x00000004  // Sample sequence 2 overflow
#define ADC_OSTAT_OV1           0x00000002  // Sample sequence 1 overflow
#define ADC_OSTAT_OV0           0x00000001  // Sample sequence 0 overflow

//*****************************************************************************
//
// The following define the bit fields in the ADC_EMUX register.
//
//*****************************************************************************
#define ADC_EMUX_EM3_MASK       0x0000F000  // Event mux 3 mask
#define ADC_EMUX_EM3_PROCESSOR  0x00000000  // Processor event
#define ADC_EMUX_EM3_COMP0      0x00001000  // Analog comparator 0 event
#define ADC_EMUX_EM3_COMP1      0x00002000  // Analog comparator 1 event
#define ADC_EMUX_EM3_COMP2      0x00003000  // Analog comparator 2 event
#define ADC_EMUX_EM3_EXTERNAL   0x00004000  // External event
#define ADC_EMUX_EM3_TIMER      0x00005000  // Timer event
#define ADC_EMUX_EM3_PWM0       0x00006000  // PWM0 event
#define ADC_EMUX_EM3_PWM1       0x00007000  // PWM1 event
#define ADC_EMUX_EM3_PWM2       0x00008000  // PWM2 event
#define ADC_EMUX_EM3_ALWAYS     0x0000F000  // Always event
#define ADC_EMUX_EM2_MASK       0x00000F00  // Event mux 2 mask
#define ADC_EMUX_EM2_PROCESSOR  0x00000000  // Processor event
#define ADC_EMUX_EM2_COMP0      0x00000100  // Analog comparator 0 event
#define ADC_EMUX_EM2_COMP1      0x00000200  // Analog comparator 1 event
#define ADC_EMUX_EM2_COMP2      0x00000300  // Analog comparator 2 event
#define ADC_EMUX_EM2_EXTERNAL   0x00000400  // External event
#define ADC_EMUX_EM2_TIMER      0x00000500  // Timer event
#define ADC_EMUX_EM2_PWM0       0x00000600  // PWM0 event
#define ADC_EMUX_EM2_PWM1       0x00000700  // PWM1 event
#define ADC_EMUX_EM2_PWM2       0x00000800  // PWM2 event
#define ADC_EMUX_EM2_ALWAYS     0x00000F00  // Always event
#define ADC_EMUX_EM1_MASK       0x000000F0  // Event mux 1 mask
#define ADC_EMUX_EM1_PROCESSOR  0x00000000  // Processor event
#define ADC_EMUX_EM1_COMP0      0x00000010  // Analog comparator 0 event
#define ADC_EMUX_EM1_COMP1      0x00000020  // Analog comparator 1 event
#define ADC_EMUX_EM1_COMP2      0x00000030  // Analog comparator 2 event
#define ADC_EMUX_EM1_EXTERNAL   0x00000040  // External event
#define ADC_EMUX_EM1_TIMER      0x00000050  // Timer event
#define ADC_EMUX_EM1_PWM0       0x00000060  // PWM0 event
#define ADC_EMUX_EM1_PWM1       0x00000070  // PWM1 event
#define ADC_EMUX_EM1_PWM2       0x00000080  // PWM2 event
#define ADC_EMUX_EM1_ALWAYS     0x000000F0  // Always event
#define ADC_EMUX_EM0_MASK       0x0000000F  // Event mux 0 mask
#define ADC_EMUX_EM0_PROCESSOR  0x00000000  // Processor event
#define ADC_EMUX_EM0_COMP0      0x00000001  // Analog comparator 0 event
#define ADC_EMUX_EM0_COMP1      0x00000002  // Analog comparator 1 event
#define ADC_EMUX_EM0_COMP2      0x00000003  // Analog comparator 2 event
#define ADC_EMUX_EM0_EXTERNAL   0x00000004  // External event
#define ADC_EMUX_EM0_TIMER      0x00000005  // Timer event
#define ADC_EMUX_EM0_PWM0       0x00000006  // PWM0 event
#define ADC_EMUX_EM0_PWM1       0x00000007  // PWM1 event
#define ADC_EMUX_EM0_PWM2       0x00000008  // PWM2 event
#define ADC_EMUX_EM0_ALWAYS     0x0000000F  // Always event
#define ADC_EMUX_EM0_SHIFT               0  // The shift for the first event
#define ADC_EMUX_EM1_SHIFT               4  // The shift for the second event
#define ADC_EMUX_EM2_SHIFT               8  // The shift for the third event
#define ADC_EMUX_EM3_SHIFT              12  // The shift for the fourth event

//*****************************************************************************
//
// The following define the bit fields in the ADC_USTAT register.
//
//*****************************************************************************
#define ADC_USTAT_UV3           0x00000008  // Sample sequence 3 underflow
#define ADC_USTAT_UV2           0x00000004  // Sample sequence 2 underflow
#define ADC_USTAT_UV1           0x00000002  // Sample sequence 1 underflow
#define ADC_USTAT_UV0           0x00000001  // Sample sequence 0 underflow

//*****************************************************************************
//
// The following define the bit fields in the ADC_SSPRI register.
//
//*****************************************************************************
#define ADC_SSPRI_SS3_MASK      0x00003000  // Sequencer 3 priority mask
#define ADC_SSPRI_SS3_1ST       0x00000000  // First priority
#define ADC_SSPRI_SS3_2ND       0x00001000  // Second priority
#define ADC_SSPRI_SS3_3RD       0x00002000  // Third priority
#define ADC_SSPRI_SS3_4TH       0x00003000  // Fourth priority
#define ADC_SSPRI_SS2_MASK      0x00000300  // Sequencer 2 priority mask
#define ADC_SSPRI_SS2_1ST       0x00000000  // First priority
#define ADC_SSPRI_SS2_2ND       0x00000100  // Second priority
#define ADC_SSPRI_SS2_3RD       0x00000200  // Third priority
#define ADC_SSPRI_SS2_4TH       0x00000300  // Fourth priority
#define ADC_SSPRI_SS1_MASK      0x00000030  // Sequencer 1 priority mask
#define ADC_SSPRI_SS1_1ST       0x00000000  // First priority
#define ADC_SSPRI_SS1_2ND       0x00000010  // Second priority
#define ADC_SSPRI_SS1_3RD       0x00000020  // Third priority
#define ADC_SSPRI_SS1_4TH       0x00000030  // Fourth priority
#define ADC_SSPRI_SS0_MASK      0x00000003  // Sequencer 0 priority mask
#define ADC_SSPRI_SS0_1ST       0x00000000  // First priority
#define ADC_SSPRI_SS0_2ND       0x00000001  // Second priority
#define ADC_SSPRI_SS0_3RD       0x00000002  // Third priority
#define ADC_SSPRI_SS0_4TH       0x00000003  // Fourth priority

//*****************************************************************************
//
// The following define the bit fields in the ADC_PSSI register.
//
//*****************************************************************************
#define ADC_PSSI_SS3            0x00000008  // Trigger sample sequencer 3
#define ADC_PSSI_SS2            0x00000004  // Trigger sample sequencer 2
#define ADC_PSSI_SS1            0x00000002  // Trigger sample sequencer 1
#define ADC_PSSI_SS0            0x00000001  // Trigger sample sequencer 0

//*****************************************************************************
//
// The following define the bit fields in the ADC_SAC register.
//
//*****************************************************************************
#define ADC_SAC_AVG_OFF         0x00000000  // No hardware oversampling
#define ADC_SAC_AVG_2X          0x00000001  // 2x hardware oversampling
#define ADC_SAC_AVG_4X          0x00000002  // 4x hardware oversampling
#define ADC_SAC_AVG_8X          0x00000003  // 8x hardware oversampling
#define ADC_SAC_AVG_16X         0x00000004  // 16x hardware oversampling
#define ADC_SAC_AVG_32X         0x00000005  // 32x hardware oversampling
#define ADC_SAC_AVG_64X         0x00000006  // 64x hardware oversampling

//*****************************************************************************
//
// The following define the bit fields in the ADC_SSMUX0, ADC_SSMUX1,
// ADC_SSMUX2, and ADC_SSMUX3 registers.  Not all fields are present in all
// registers.
//
//*****************************************************************************
#define ADC_SSMUX_MUX7_MASK     0x70000000  // 8th mux select mask
#define ADC_SSMUX_MUX6_MASK     0x07000000  // 7th mux select mask
#define ADC_SSMUX_MUX5_MASK     0x00700000  // 6th mux select mask
#define ADC_SSMUX_MUX4_MASK     0x00070000  // 5th mux select mask
#define ADC_SSMUX_MUX3_MASK     0x00007000  // 4th mux select mask
#define ADC_SSMUX_MUX2_MASK     0x00000700  // 3rd mux select mask
#define ADC_SSMUX_MUX1_MASK     0x00000070  // 2nd mux select mask
#define ADC_SSMUX_MUX0_MASK     0x00000007  // 1st mux select mask
#define ADC_SSMUX_MUX7_SHIFT    28
#define ADC_SSMUX_MUX6_SHIFT    24
#define ADC_SSMUX_MUX5_SHIFT    20
#define ADC_SSMUX_MUX4_SHIFT    16
#define ADC_SSMUX_MUX3_SHIFT    12
#define ADC_SSMUX_MUX2_SHIFT    8
#define ADC_SSMUX_MUX1_SHIFT    4
#define ADC_SSMUX_MUX0_SHIFT    0

//*****************************************************************************
//
// The following define the bit fields in the ADC_SSCTL0, ADC_SSCTL1,
// ADC_SSCTL2, and ADC_SSCTL3 registers.  Not all fields are present in all
// registers.
//
//*****************************************************************************
#define ADC_SSCTL_TS7           0x80000000  // 8th temperature sensor select
#define ADC_SSCTL_IE7           0x40000000  // 8th interrupt enable
#define ADC_SSCTL_END7          0x20000000  // 8th sequence end select
#define ADC_SSCTL_D7            0x10000000  // 8th differential select
#define ADC_SSCTL_TS6           0x08000000  // 7th temperature sensor select
#define ADC_SSCTL_IE6           0x04000000  // 7th interrupt enable
#define ADC_SSCTL_END6          0x02000000  // 7th sequence end select
#define ADC_SSCTL_D6            0x01000000  // 7th differential select
#define ADC_SSCTL_TS5           0x00800000  // 6th temperature sensor select
#define ADC_SSCTL_IE5           0x00400000  // 6th interrupt enable
#define ADC_SSCTL_END5          0x00200000  // 6th sequence end select
#define ADC_SSCTL_D5            0x00100000  // 6th differential select
#define ADC_SSCTL_TS4           0x00080000  // 5th temperature sensor select
#define ADC_SSCTL_IE4           0x00040000  // 5th interrupt enable
#define ADC_SSCTL_END4          0x00020000  // 5th sequence end select
#define ADC_SSCTL_D4            0x00010000  // 5th differential select
#define ADC_SSCTL_TS3           0x00008000  // 4th temperature sensor select
#define ADC_SSCTL_IE3           0x00004000  // 4th interrupt enable
#define ADC_SSCTL_END3          0x00002000  // 4th sequence end select
#define ADC_SSCTL_D3            0x00001000  // 4th differential select
#define ADC_SSCTL_TS2           0x00000800  // 3rd temperature sensor select
#define ADC_SSCTL_IE2           0x00000400  // 3rd interrupt enable
#define ADC_SSCTL_END2          0x00000200  // 3rd sequence end select
#define ADC_SSCTL_D2            0x00000100  // 3rd differential select
#define ADC_SSCTL_TS1           0x00000080  // 2nd temperature sensor select
#define ADC_SSCTL_IE1           0x00000040  // 2nd interrupt enable
#define ADC_SSCTL_END1          0x00000020  // 2nd sequence end select
#define ADC_SSCTL_D1            0x00000010  // 2nd differential select
#define ADC_SSCTL_TS0           0x00000008  // 1st temperature sensor select
#define ADC_SSCTL_IE0           0x00000004  // 1st interrupt enable
#define ADC_SSCTL_END0          0x00000002  // 1st sequence end select
#define ADC_SSCTL_D0            0x00000001  // 1st differential select

//*****************************************************************************
//
// The following define the bit fields in the ADC_SSFIFO0, ADC_SSFIFO1,
// ADC_SSFIFO2, and ADC_SSFIFO3 registers.
//
//*****************************************************************************
#define ADC_SSFIFO_DATA_MASK    0x000003FF  // Sample data
#define ADC_SSFIFO_DATA_SHIFT   0

//*****************************************************************************
//
// The following define the bit fields in the ADC_SSFSTAT0, ADC_SSFSTAT1,
// ADC_SSFSTAT2, and ADC_SSFSTAT3 registers.
//
//*****************************************************************************
#define ADC_SSFSTAT_FULL        0x00001000  // FIFO is full
#define ADC_SSFSTAT_EMPTY       0x00000100  // FIFO is empty
#define ADC_SSFSTAT_HPTR        0x000000F0  // FIFO head pointer
#define ADC_SSFSTAT_TPTR        0x0000000F  // FIFO tail pointer

//*****************************************************************************
//
// The following define the bit fields in the ADC_TMLB register.
//
//*****************************************************************************
#define ADC_TMLB_LB             0x00000001  // Loopback control signals

//*****************************************************************************
//
// The following define the bit fields in the loopback ADC data.
//
//*****************************************************************************
#define ADC_LB_CNT_MASK         0x000003C0  // Sample counter mask
#define ADC_LB_CONT             0x00000020  // Continuation sample
#define ADC_LB_DIFF             0x00000010  // Differential sample
#define ADC_LB_TS               0x00000008  // Temperature sensor sample
#define ADC_LB_MUX_MASK         0x00000007  // Input channel number mask
#define ADC_LB_CNT_SHIFT        6           // Sample counter shift
#define ADC_LB_MUX_SHIFT        0           // Input channel number shift

#endif // __HW_ADC_H__
