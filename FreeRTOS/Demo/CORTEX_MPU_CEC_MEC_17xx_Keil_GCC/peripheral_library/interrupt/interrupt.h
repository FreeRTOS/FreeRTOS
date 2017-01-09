/*****************************************************************************
* © 2015 Microchip Technology Inc. and its subsidiaries.
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
******************************************************************************

Version Control Information (Perforce)
******************************************************************************
$Revision: #1 $ 
$DateTime: 2016/09/22 08:03:49 $ 
$Author: pramans $
Last Change: Renamed ecia_init to interrupt_init
******************************************************************************/
/** @file interrupt.h
* \brief Interrupt Header File
* \author jvasanth
* 
* This file implements the Interrupt Module Header file  
******************************************************************************/

/** @defgroup Interrupt
 *  @{
 */

#ifndef _INTERRUPT_H
#define _INTERRUPT_H

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
// GIRQs 13 - 19, 21, 23, 24-26
#define ECIA_GIRQ_DIRECT_BITMAP     (0x07AFE000ul)

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
#define GPIO_0140_IROUTE                IROUTE(0,8,0,0)
#define GPIO_0141_IROUTE                IROUTE(1,8,0,0)
#define GPIO_0142_IROUTE                IROUTE(2,8,0,0)
#define GPIO_0143_IROUTE                IROUTE(3,8,0,0)
#define GPIO_0144_IROUTE                IROUTE(4,8,0,0)
#define GPIO_0145_IROUTE                IROUTE(5,8,0,0)
#define GPIO_0147_IROUTE                IROUTE(7,8,0,0)
//
#define GPIO_0150_IROUTE                IROUTE(8,8,0,0)
#define GPIO_0151_IROUTE                IROUTE(9,8,0,0)
#define GPIO_0152_IROUTE                IROUTE(10,8,0,0)
#define GPIO_0153_IROUTE                IROUTE(11,8,0,0)
#define GPIO_0154_IROUTE                IROUTE(12,8,0,0)
#define GPIO_0155_IROUTE                IROUTE(13,8,0,0)
#define GPIO_0156_IROUTE                IROUTE(14,8,0,0)
#define GPIO_0157_IROUTE                IROUTE(15,8,0,0)
//
#define GPIO_0160_IROUTE                IROUTE(16,8,0,0)
#define GPIO_0161_IROUTE                IROUTE(17,8,0,0)
#define GPIO_0162_IROUTE                IROUTE(18,8,0,0)
#define GPIO_0163_IROUTE                IROUTE(19,8,0,0)
#define GPIO_0164_IROUTE                IROUTE(20,8,0,0)
#define GPIO_0165_IROUTE                IROUTE(21,8,0,0)
#define GPIO_0166_IROUTE                IROUTE(22,8,0,0)
#define GPIO_0167_IROUTE                IROUTE(23,8,0,0)

#define GPIO_0170_IROUTE                IROUTE(24,8,0,0)
#define GPIO_0171_IROUTE                IROUTE(25,8,0,0)
#define GPIO_0172_IROUTE                IROUTE(26,8,0,0)
#define GPIO_0173_IROUTE                IROUTE(27,8,0,0)
#define GPIO_0174_IROUTE                IROUTE(28,8,0,0)
#define GPIO_0175_IROUTE                IROUTE(29,8,0,0)
#define GPIO_0176_IROUTE                IROUTE(30,8,0,0)

//
// GIRQ09
//
#define GPIO_0100_IROUTE                IROUTE(0,9,1,1)
#define GPIO_0101_IROUTE                IROUTE(1,9,1,1)
#define GPIO_0102_IROUTE                IROUTE(2,9,1,1)
#define GPIO_0103_IROUTE                IROUTE(3,9,1,1)
#define GPIO_0104_IROUTE                IROUTE(4,9,1,1)
#define GPIO_0105_IROUTE                IROUTE(5,9,1,1)
#define GPIO_0105_IROUTE                IROUTE(5,9,1,1)
#define GPIO_0107_IROUTE                IROUTE(7,9,1,1)
//
#define GPIO_0110_IROUTE                IROUTE(8,9,1,1)
#define GPIO_0111_IROUTE                IROUTE(9,9,1,1)
#define GPIO_0112_IROUTE                IROUTE(10,9,1,1)
#define GPIO_0113_IROUTE                IROUTE(11,9,1,1)
#define GPIO_0114_IROUTE                IROUTE(12,9,1,1)
#define GPIO_0115_IROUTE                IROUTE(13,9,1,1)
#define GPIO_0116_IROUTE                IROUTE(14,9,1,1)
#define GPIO_0117_IROUTE                IROUTE(15,9,1,1)
//
#define GPIO_0120_IROUTE                IROUTE(16,9,1,1)
#define GPIO_0121_IROUTE                IROUTE(17,9,1,1)
#define GPIO_0122_IROUTE                IROUTE(18,9,1,1)
#define GPIO_0124_IROUTE                IROUTE(20,9,1,1)
#define GPIO_0125_IROUTE                IROUTE(21,9,1,1)
#define GPIO_0126_IROUTE                IROUTE(22,9,1,1)
#define GPIO_0127_IROUTE                IROUTE(23,9,1,1)
//
#define GPIO_0130_IROUTE                IROUTE(24,9,1,1)
#define GPIO_0131_IROUTE                IROUTE(25,9,1,1)
#define GPIO_0132_IROUTE                IROUTE(26,9,1,1)
#define GPIO_0133_IROUTE                IROUTE(27,9,1,1)
#define GPIO_0134_IROUTE                IROUTE(28,9,1,1)
#define GPIO_0135_IROUTE                IROUTE(29,9,1,1)
#define GPIO_0136_IROUTE                IROUTE(30,9,1,1)

//
// GIRQ10
//
#define GPIO_0040_IROUTE                IROUTE(0,10,2,2)
#define GPIO_0041_IROUTE                IROUTE(1,10,2,2)
#define GPIO_0042_IROUTE                IROUTE(2,10,2,2)
#define GPIO_0043_IROUTE                IROUTE(3,10,2,2)
#define GPIO_0044_IROUTE                IROUTE(4,10,2,2)
#define GPIO_0045_IROUTE                IROUTE(5,10,2,2)
#define GPIO_0045_IROUTE                IROUTE(5,10,2,2)
#define GPIO_0047_IROUTE                IROUTE(7,10,2,2)
//
#define GPIO_0050_IROUTE                IROUTE(8,10,2,2)
#define GPIO_0051_IROUTE                IROUTE(9,10,2,2)
#define GPIO_0052_IROUTE                IROUTE(10,10,2,2)
#define GPIO_0053_IROUTE                IROUTE(11,10,2,2)
#define GPIO_0054_IROUTE                IROUTE(12,10,2,2)
#define GPIO_0055_IROUTE                IROUTE(13,10,2,2)
#define GPIO_0056_IROUTE                IROUTE(14,10,2,2)
#define GPIO_0057_IROUTE                IROUTE(15,10,2,2)
//
#define GPIO_0060_IROUTE                IROUTE(16,10,2,2)
#define GPIO_0061_IROUTE                IROUTE(17,10,2,2)
#define GPIO_0062_IROUTE                IROUTE(18,10,2,2)
#define GPIO_0063_IROUTE                IROUTE(19,10,2,2)
#define GPIO_0064_IROUTE                IROUTE(20,10,2,2)
#define GPIO_0065_IROUTE                IROUTE(21,10,2,2)
#define GPIO_0066_IROUTE                IROUTE(22,10,2,2)
#define GPIO_0067_IROUTE                IROUTE(23,10,2,2)
//
#define GPIO_0070_IROUTE                IROUTE(24,10,2,2)
#define GPIO_0071_IROUTE                IROUTE(25,10,2,2)
#define GPIO_0072_IROUTE                IROUTE(26,10,2,2)
#define GPIO_0073_IROUTE                IROUTE(27,10,2,2)
#define GPIO_0074_IROUTE                IROUTE(28,10,2,2)
#define GPIO_0075_IROUTE                IROUTE(29,10,2,2)
#define GPIO_0076_IROUTE                IROUTE(30,10,2,2)

//
// GIRQ11
//
#define GPIO_0000_IROUTE                IROUTE(0,11,3,3)
#define GPIO_0001_IROUTE                IROUTE(1,11,3,3)
#define GPIO_0002_IROUTE                IROUTE(2,11,3,3)
#define GPIO_0003_IROUTE                IROUTE(3,11,3,3)
#define GPIO_0004_IROUTE                IROUTE(4,11,3,3)
#define GPIO_0005_IROUTE                IROUTE(5,11,3,3)
#define GPIO_0006_IROUTE                IROUTE(6,11,3,3)
#define GPIO_0007_IROUTE                IROUTE(7,11,3,3)
//
#define GPIO_0010_IROUTE                IROUTE(8,11,3,3)
#define GPIO_0011_IROUTE                IROUTE(9,11,3,3)
#define GPIO_0012_IROUTE                IROUTE(10,11,3,3)
#define GPIO_0013_IROUTE                IROUTE(11,11,3,3)
#define GPIO_0014_IROUTE                IROUTE(12,11,3,3)
#define GPIO_0015_IROUTE                IROUTE(13,11,3,3)
#define GPIO_0016_IROUTE                IROUTE(14,11,3,3)
#define GPIO_0017_IROUTE                IROUTE(15,11,3,3)
//
#define GPIO_0020_IROUTE                IROUTE(16,11,3,3)
#define GPIO_0021_IROUTE                IROUTE(17,11,3,3)
#define GPIO_0022_IROUTE                IROUTE(18,11,3,3)
#define GPIO_0023_IROUTE                IROUTE(19,11,3,3)
#define GPIO_0024_IROUTE                IROUTE(20,11,3,3)
#define GPIO_0025_IROUTE                IROUTE(21,11,3,3)
#define GPIO_0026_IROUTE                IROUTE(22,11,3,3)
#define GPIO_0027_IROUTE                IROUTE(23,11,3,3)
//
#define GPIO_0030_IROUTE                IROUTE(24,11,3,3)
#define GPIO_0031_IROUTE                IROUTE(25,11,3,3)
#define GPIO_0032_IROUTE                IROUTE(26,11,3,3)
#define GPIO_0033_IROUTE                IROUTE(27,11,3,3)
#define GPIO_0034_IROUTE                IROUTE(28,11,3,3)
#define GPIO_0035_IROUTE                IROUTE(29,11,3,3)
#define GPIO_0036_IROUTE                IROUTE(30,11,3,3)


// GIRQ12
//
#define GPIO_0200_IROUTE                IROUTE(0,12,4,4)
#define GPIO_0201_IROUTE                IROUTE(1,12,4,4)
#define GPIO_0202_IROUTE                IROUTE(2,12,4,4)
#define GPIO_0203_IROUTE                IROUTE(3,12,4,4)
#define GPIO_0204_IROUTE                IROUTE(4,12,4,4)
#define GPIO_0205_IROUTE                IROUTE(5,12,4,4)
#define GPIO_0206_IROUTE                IROUTE(6,12,4,4)
#define GPIO_0207_IROUTE                IROUTE(7,12,4,4)
//
#define GPIO_0210_IROUTE                IROUTE(8,12,4,4)
#define GPIO_0211_IROUTE                IROUTE(9,12,4,4)
#define GPIO_0212_IROUTE                IROUTE(10,12,4,4)
#define GPIO_0213_IROUTE                IROUTE(11,12,4,4)
#define GPIO_0214_IROUTE                IROUTE(12,12,4,4)
#define GPIO_0215_IROUTE                IROUTE(13,12,4,4)
#define GPIO_0216_IROUTE                IROUTE(14,12,4,4)
#define GPIO_0217_IROUTE                IROUTE(15,12,4,4)
//
#define GPIO_0220_IROUTE                IROUTE(16,12,4,4)
#define GPIO_0221_IROUTE                IROUTE(17,12,4,4)
#define GPIO_0222_IROUTE                IROUTE(18,12,4,4)
#define GPIO_0223_IROUTE                IROUTE(19,12,4,4)
#define GPIO_0224_IROUTE                IROUTE(20,12,4,4)
#define GPIO_0225_IROUTE                IROUTE(21,12,4,4)
#define GPIO_0226_IROUTE                IROUTE(22,12,4,4)
#define GPIO_0227_IROUTE                IROUTE(23,12,4,4)
//
#define GPIO_0230_IROUTE                IROUTE(24,12,4,4)
#define GPIO_0231_IROUTE                IROUTE(25,12,4,4)
#define GPIO_0232_IROUTE                IROUTE(26,12,4,4)
#define GPIO_0233_IROUTE                IROUTE(27,12,4,4)
#define GPIO_0234_IROUTE                IROUTE(28,12,4,4)
#define GPIO_0235_IROUTE                IROUTE(29,12,4,4)
#define GPIO_0236_IROUTE                IROUTE(30,12,4,4)



//
// GIRQ13
//
#define SMB0_IROUTE                     IROUTE(0,13,5,20)
#define SMB1_IROUTE                     IROUTE(1,13,5,21)
#define SMB2_IROUTE                     IROUTE(2,13,5,22)
#define SMB3_IROUTE                     IROUTE(3,13,5,23)

//
// GIRQ14
//
#define DMA0_IROUTE                     IROUTE(0,14,6,24)
#define DMA1_IROUTE                     IROUTE(1,14,6,25)
#define DMA2_IROUTE                     IROUTE(2,14,6,26)
#define DMA3_IROUTE                     IROUTE(3,14,6,27)
#define DMA4_IROUTE                     IROUTE(4,14,6,28)
#define DMA5_IROUTE                     IROUTE(5,14,6,29)
#define DMA6_IROUTE                     IROUTE(6,14,6,30)
#define DMA7_IROUTE                     IROUTE(7,14,6,31)
#define DMA8_IROUTE                     IROUTE(8,14,6,33)
#define DMA9_IROUTE                     IROUTE(9,14,6,33)
#define DMA10_IROUTE                    IROUTE(10,14,6,34)
#define DMA11_IROUTE                    IROUTE(11,14,6,35)
#define DMA12_IROUTE                    IROUTE(12,14,6,36)
#define DMA13_IROUTE                    IROUTE(13,14,6,37)


//
// GIRQ15
//
#define UART0_IROUTE                    IROUTE(0,15,7,40)
#define UART1_IROUTE                    IROUTE(1,15,7,41)
#define EMI0_IROUTE                     IROUTE(2,15,7,42)
#define EMI1_IROUTE                     IROUTE(3,15,7,43)
#define EMI2_IROUTE                     IROUTE(4,15,7,44)
#define ACPI_EC0_IBF_IROUTE             IROUTE(5,15,7,45)
#define ACPI_EC0_OBF_IROUTE             IROUTE(6,15,7,46)
#define ACPI_EC1_IBF_IROUTE             IROUTE(7,15,7,47)
#define ACPI_EC1_OBF_IROUTE             IROUTE(8,15,7,48)
#define ACPI_EC2_IBF_IROUTE             IROUTE(9,15,7,49)
#define ACPI_EC2_OBF_IROUTE             IROUTE(10,15,7,50)
#define ACPI_EC3_IBF_IROUTE             IROUTE(11,15,7,51)
#define ACPI_EC3_OBF_IROUTE             IROUTE(12,15,7,52)
#define ACPI_EC4_IBF_IROUTE             IROUTE(13,15,7,53)
#define ACPI_EC4_OBF_IROUTE             IROUTE(14,15,7,54)
#define ACPI_PM1_CTL_IROUTE             IROUTE(15,15,7,55)
#define ACPI_PM1_EN_IROUTE              IROUTE(16,15,7,56)
#define ACPI_PM1_STS_IROUTE             IROUTE(17,15,7,57)
#define EM8042_OBF_IROUTE               IROUTE(18,15,7,58)
#define EM8042_IBF_IROUTE               IROUTE(19,15,7,59)
#define MBOX_IROUTE                     IROUTE(20,15,7,60)
#define PORT80_DBG0_BDPINT_IROUTE       IROUTE(22,15,7,62)
#define PORT80_DBG1_BDPINT_IROUTE       IROUTE(23,15,7,63)
#define TEST_IROUTE                     IROUTE(24,15,7,64)

//
// GIRQ16
//
#define PKE_ERROR_IROUTE                IROUTE(0,16,8,65)
#define PKE_END_IROUTE                  IROUTE(1,16,8,66)
#define RNG_IROUTE                      IROUTE(2,16,8,67)
#define AES_IROUTE                      IROUTE(3,16,8,68)
#define HASH_IROUTE                     IROUTE(4,16,8,69)

//
// GIRQ17
//
#define PECI_IROUTE                     IROUTE(0,17,9,70)
#define TACH0_IROUTE                    IROUTE(1,17,9,71)
#define TACH1_IROUTE                    IROUTE(2,17,9,72)
#define TACH2_IROUTE                    IROUTE(3,17,9,73)
#define RPM2PWM0_FAIL_IROUTE            IROUTE(4,17,9,74)
#define RPM2PWM0_STALL_IROUTE           IROUTE(5,17,9,75)
#define RPM2PWM1_FAIL_IROUTE            IROUTE(6,17,9,76)
#define RPM2PWM1_STALL_IROUTE           IROUTE(7,17,9,77)
#define ADC_SNGL_IROUTE                 IROUTE(8,17,9,78)
#define ADC_RPT_IROUTE                  IROUTE(9,17,9,79)
#define RC_ID0_IROUTE                   IROUTE(10,17,9,80)
#define RC_ID1_IROUTE                   IROUTE(11,17,9,81)
#define RC_ID2_IROUTE                   IROUTE(12,17,9,82)
#define LED0_IROUTE                     IROUTE(13,17,9,83)
#define LED1_IROUTE                     IROUTE(14,17,9,84)
#define LED2_IROUTE                     IROUTE(15,17,9,85)
#define LED3_IROUTE                     IROUTE(16,17,9,86)
#define PHOT_IROUTE                     IROUTE(17,17,9,87)
#define POWER_GUARD0_IROUTE             IROUTE(18,17,9,88)
#define POWER_GUARD1_IROUTE             IROUTE(19,17,9,89)
#define RTOS_SWI0_IROUTE                IROUTE(25,17,9,9)
#define RTOS_SWI1_IROUTE                IROUTE(26,17,9,9)
#define RTOS_SWI2_IROUTE                IROUTE(27,17,9,9)
#define RTOS_SWI3_IROUTE                IROUTE(28,17,9,9)

//
// GIRQ18 
//
#define LPC_INT_ERR_IROUTE              IROUTE(0,18,10,90)
#define QMSPI_INT_IROUTE                IROUTE(1,18,10,91)
#define GP_SPI0_TXBE_STS_IROUTE         IROUTE(2,18,10,92)
#define GP_SPI0_RXBF_STS_IROUTE         IROUTE(3,18,10,93)
#define GP_SPI1_TXBE_STS_IROUTE         IROUTE(4,18,10,94)
#define GP_SPI1_RXBF_STS_IROUTE         IROUTE(5,18,10,95)
#define BCLINK0_BCM_ERR_IROUTE          IROUTE(6,18,10,96)
#define BCLINK0_BUSY_CLR_IROUTE         IROUTE(7,18,10,97)
#define BCLINK1_BCM_ERR_IROUTE          IROUTE(8,18,10,98)
#define BCLINK1_BUSY_CLR_IROUTE         IROUTE(9,18,10,99)
#define PS2_IFACE0_ACT_IROUTE           IROUTE(10,18,10,100)
#define PS2_IFACE1_ACT_IROUTE           IROUTE(11,18,10,101)
#define PS2_IFACE2_ACT_IROUTE           IROUTE(12,18,10,102)
#define EEPROM_IROUTE                   IROUTE(13,18,10,155)


//
// GIRQ19
//
#define ESPI_SLAVE_INTR_PC_IROUTE       IROUTE(0,19,11,103)
#define ESPI_SLAVE_INTR_BM1_IROUTE      IROUTE(1,19,11,104)
#define ESPI_SLAVE_INTR_BM2_IROUTE      IROUTE(2,19,11,105)
#define ESPI_SLAVE_INTR_LTR_IROUTE      IROUTE(3,19,11,106)
#define ESPI_SLAVE_INTR_OOB_UP_IROUTE   IROUTE(4,19,11,107)
#define ESPI_SLAVE_INTR_OOB_DN_IROUTE   IROUTE(5,19,11,108)
#define ESPI_SLAVE_INTR_FLASH_IROUTE    IROUTE(6,19,11,109)
#define ESPI_SLAVE_ESPI_RESET_IROUTE    IROUTE(7,19,11,110)
#define ESPI_SLAVE_VW_ENABLE_IROUTE     IROUTE(8,19,11,156)

//
// GIRQ20
//


//
// GIRQ21
//
#define RTOS_TIMER_IROUTE               IROUTE(0,21,13,111)
#define HTIMER0_IROUTE                  IROUTE(1,21,13,112)
#define HTIMER1_IROUTE                  IROUTE(2,21,13,113)
#define WEEK_ALARM_INT_IROUTE           IROUTE(3,21,13,114)
#define SUB_WEEK_ALARM_IN_IROUTE        IROUTE(4,21,13,115)
#define WEEK_ALARM_ONE_SECOND_IROUTE    IROUTE(5,21,13,116)
#define WEEK_ALARM_SUB_SECOND_IROUTE    IROUTE(6,21,13,117)
#define WEEK_ALARM_SYSPWR_PRES_IROUTE   IROUTE(7,21,13,118)
#define RTC_IROUTE                      IROUTE(8,21,13,119)
#define RTC_ALARM_IROUTE                IROUTE(9,21,13,120)
#define VBAT_VCI_OVRD_IN_IROUTE         IROUTE(10,21,13,121)
#define VBAT_VCI_IN0_IROUTE             IROUTE(11,21,13,122)
#define VBAT_VCI_IN1_IROUTE             IROUTE(12,21,13,123)
#define VBAT_VCI_IN2_IROUTE             IROUTE(13,21,13,124)
#define VBAT_VCI_IN3_IROUTE             IROUTE(14,21,13,125)
#define VBAT_VCI_IN4_IROUTE             IROUTE(15,21,13,126)
#define VBAT_VCI_IN5_IROUTE             IROUTE(16,21,13,127)
#define VBAT_VCI_IN6_IROUTE             IROUTE(17,21,13,128)
#define PS2_0A_WK_IROUTE                IROUTE(18,21,13,129)
#define PS2_0B_WK_IROUTE                IROUTE(19,21,13,130)
#define PS2_1A_WK_IROUTE                IROUTE(20,21,13,131)
#define PS2_1B_WK_IROUTE                IROUTE(21,21,13,132)
#define PS2_2_WK_IROUTE                 IROUTE(22,21,13,133)
#define ENVMON_IROUTE                   IROUTE(24,21,13,134)
#define KSC_INT_IROUTE                  IROUTE(25,21,13,135)


//
// GIRQ22 (No Aggregated & No direct source, WAKE ONLY EVENTS)
//
#define LPC_WAKE_ONLY_IROUTE            IROUTE(0,22,22,22)
#define SMB0_WAKE_ONLY_IROUTE           IROUTE(1,22,22,22)
#define SMB1_WAKE_ONLY_IROUTE           IROUTE(2,22,22,22)
#define SMB2_WAKE_ONLY_IROUTE           IROUTE(3,22,22,22)
#define SMB3_WAKE_ONLY_IROUTE           IROUTE(4,22,22,22)
#define ESPI_WAKE_ONLY_IROUTE           IROUTE(9,22,22,22)

//
// GIRQ23
//
#define BTMR0_IROUTE                    IROUTE(0,23,14,136)
#define BTMR1_IROUTE                    IROUTE(1,23,14,137)
#define BTMR2_IROUTE                    IROUTE(2,23,14,138)
#define BTMR3_IROUTE                    IROUTE(3,23,14,139)
#define BTMR4_IROUTE                    IROUTE(4,23,14,140)
#define BTMR5_IROUTE                    IROUTE(5,23,14,141)
#define CTIMER0_IROUTE                  IROUTE(6,23,14,142)
#define CTIMER1_IROUTE                  IROUTE(7,23,14,143)
#define CTIMER2_IROUTE                  IROUTE(8,23,14,144)
#define CTIMER3_IROUTE                  IROUTE(9,23,14,145)
#define CAP_TIMER_IROUTE                IROUTE(10,23,14,146)
#define CC_TIMER0_IROUTE                IROUTE(11,23,14,147)
#define CC_TIMER1_IROUTE                IROUTE(12,23,14,148)
#define CC_TIMER2_IROUTE                IROUTE(13,23,14,149)
#define CC_TIMER3_IROUTE                IROUTE(14,23,14,150)
#define CC_TIMER4_IROUTE                IROUTE(15,23,14,151)
#define CC_TIMER5_IROUTE                IROUTE(16,23,14,152)
#define CC_TIMER_CMP0_IROUTE            IROUTE(17,23,14,153)
#define CC_TIMER_CMP1_IROUTE            IROUTE(18,23,14,154)

//
// GIRQ23
//
#define ESPI_SLAVE_VW00_SRC0_IROUTE     IROUTE(0,24,15,15)
#define ESPI_SLAVE_VW00_SRC1_IROUTE     IROUTE(1,24,15,15)
#define ESPI_SLAVE_VW00_SRC2_IROUTE     IROUTE(2,24,15,15)
#define ESPI_SLAVE_VW00_SRC3_IROUTE     IROUTE(3,24,15,15)
#define ESPI_SLAVE_VW01_SRC0_IROUTE     IROUTE(4,24,15,15)
#define ESPI_SLAVE_VW01_SRC1_IROUTE     IROUTE(5,24,15,15)
#define ESPI_SLAVE_VW01_SRC2_IROUTE     IROUTE(6,24,15,15)
#define ESPI_SLAVE_VW01_SRC3_IROUTE     IROUTE(7,24,15,15)
#define ESPI_SLAVE_VW02_SRC0_IROUTE     IROUTE(8,24,15,15)
#define ESPI_SLAVE_VW02_SRC1_IROUTE     IROUTE(9,24,15,15)
#define ESPI_SLAVE_VW02_SRC2_IROUTE     IROUTE(10,24,15,15)
#define ESPI_SLAVE_VW02_SRC3_IROUTE     IROUTE(11,24,15,15)
#define ESPI_SLAVE_VW03_SRC0_IROUTE     IROUTE(12,24,15,15)
#define ESPI_SLAVE_VW03_SRC1_IROUTE     IROUTE(13,24,15,15)
#define ESPI_SLAVE_VW03_SRC2_IROUTE     IROUTE(14,24,15,15)
#define ESPI_SLAVE_VW03_SRC3_IROUTE     IROUTE(15,24,15,15)
#define ESPI_SLAVE_VW04_SRC0_IROUTE     IROUTE(16,24,15,15)
#define ESPI_SLAVE_VW04_SRC1_IROUTE     IROUTE(17,24,15,15)
#define ESPI_SLAVE_VW04_SRC2_IROUTE     IROUTE(18,24,15,15)
#define ESPI_SLAVE_VW04_SRC3_IROUTE     IROUTE(19,24,15,15)
#define ESPI_SLAVE_VW05_SRC0_IROUTE     IROUTE(20,24,15,15)
#define ESPI_SLAVE_VW05_SRC1_IROUTE     IROUTE(21,24,15,15)
#define ESPI_SLAVE_VW05_SRC2_IROUTE     IROUTE(22,24,15,15)
#define ESPI_SLAVE_VW05_SRC3_IROUTE     IROUTE(23,24,15,15)
#define ESPI_SLAVE_VW06_SRC0_IROUTE     IROUTE(24,24,15,15)
#define ESPI_SLAVE_VW06_SRC1_IROUTE     IROUTE(25,24,15,15)
#define ESPI_SLAVE_VW06_SRC2_IROUTE     IROUTE(26,24,15,15)
#define ESPI_SLAVE_VW06_SRC3_IROUTE     IROUTE(27,24,15,15)


//
// GIRQ25
//
#define ESPI_SLAVE_VW07_SRC0_IROUTE     IROUTE(0,25,15,15)
#define ESPI_SLAVE_VW07_SRC1_IROUTE     IROUTE(1,25,15,15)
#define ESPI_SLAVE_VW07_SRC2_IROUTE     IROUTE(2,25,15,15)
#define ESPI_SLAVE_VW07_SRC3_IROUTE     IROUTE(3,25,15,15)
#define ESPI_SLAVE_VW08_SRC0_IROUTE     IROUTE(4,25,15,15)
#define ESPI_SLAVE_VW08_SRC1_IROUTE     IROUTE(5,25,15,15)
#define ESPI_SLAVE_VW08_SRC2_IROUTE     IROUTE(6,25,15,15)
#define ESPI_SLAVE_VW08_SRC3_IROUTE     IROUTE(7,25,15,15)
#define ESPI_SLAVE_VW09_SRC0_IROUTE     IROUTE(8,25,15,15)
#define ESPI_SLAVE_VW09_SRC1_IROUTE     IROUTE(9,25,15,15)
#define ESPI_SLAVE_VW09_SRC2_IROUTE     IROUTE(10,25,15,15)
#define ESPI_SLAVE_VW09_SRC3_IROUTE     IROUTE(11,25,15,15)
#define ESPI_SLAVE_VW10_SRC0_IROUTE     IROUTE(12,25,15,15)
#define ESPI_SLAVE_VW10_SRC1_IROUTE     IROUTE(13,25,15,15)
#define ESPI_SLAVE_VW10_SRC2_IROUTE     IROUTE(14,25,15,15)
#define ESPI_SLAVE_VW10_SRC3_IROUTE     IROUTE(15,25,15,15)

//
// GIRQ26
//
#define GPIO_0240_IROUTE                IROUTE(0,26,17,17)
#define GPIO_0241_IROUTE                IROUTE(1,26,17,17)
#define GPIO_0242_IROUTE                IROUTE(2,26,17,17)
#define GPIO_0243_IROUTE                IROUTE(3,26,17,17)
#define GPIO_0244_IROUTE                IROUTE(4,26,17,17)
#define GPIO_0245_IROUTE                IROUTE(5,26,17,17)
#define GPIO_0246_IROUTE                IROUTE(6,26,17,17)
#define GPIO_0247_IROUTE                IROUTE(7,26,17,17)
//
#define GPIO_0250_IROUTE                IROUTE(8,26,17,17)
#define GPIO_0251_IROUTE                IROUTE(9,26,17,17)
#define GPIO_0252_IROUTE                IROUTE(10,26,17,17)
#define GPIO_0253_IROUTE                IROUTE(11,26,17,17)
#define GPIO_0254_IROUTE                IROUTE(12,26,17,17)
#define GPIO_0255_IROUTE                IROUTE(13,26,17,17)
#define GPIO_0256_IROUTE                IROUTE(14,26,17,17)
#define GPIO_0257_IROUTE                IROUTE(15,26,17,17)
//
#define GPIO_0260_IROUTE                IROUTE(16,26,17,17)
#define GPIO_0261_IROUTE                IROUTE(17,26,17,17)
#define GPIO_0262_IROUTE                IROUTE(18,26,17,17)
#define GPIO_0263_IROUTE                IROUTE(19,26,17,17)
#define GPIO_0264_IROUTE                IROUTE(20,26,17,17)
#define GPIO_0265_IROUTE                IROUTE(21,26,17,17)
#define GPIO_0266_IROUTE                IROUTE(22,26,17,17)
#define GPIO_0267_IROUTE                IROUTE(23,26,17,17)
//
#define GPIO_0270_IROUTE                IROUTE(24,26,17,17)
#define GPIO_0271_IROUTE                IROUTE(25,26,17,17)
#define GPIO_0272_IROUTE                IROUTE(26,26,17,17)
#define GPIO_0273_IROUTE                IROUTE(27,26,17,17)
#define GPIO_0274_IROUTE                IROUTE(28,26,17,17)
#define GPIO_0275_IROUTE                IROUTE(29,26,17,17)
#define GPIO_0276_IROUTE                IROUTE(30,26,17,17)


// GIRQ08 Bit Positions 
#define GIRQ08_GPIO_0140_BITPOS         (0)
#define GIRQ08_GPIO_0141_BITPOS         (1)
#define GIRQ08_GPIO_0142_BITPOS         (2)
#define GIRQ08_GPIO_0143_BITPOS         (3)
#define GIRQ08_GPIO_0144_BITPOS         (4)
#define GIRQ08_GPIO_0145_BITPOS         (5)
#define GIRQ08_GPIO_0146_BITPOS         (6)
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

#define GIRQ08_GPIO_0170_BITPOS         (24)
#define GIRQ08_GPIO_0171_BITPOS         (25)
#define GIRQ08_GPIO_0172_BITPOS         (26)
#define GIRQ08_GPIO_0173_BITPOS         (27)
#define GIRQ08_GPIO_0174_BITPOS         (28)
#define GIRQ08_GPIO_0175_BITPOS         (29)
#define GIRQ08_GPIO_0176_BITPOS         (30) 

//
#define GIRQ08_MASK                     (0x7FFFFFFFul)
#define GIRQ08_WAKE_CAPABLE_MASK        (0x7FFFFFFFul)
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
#define GIRQ09_GPIO_0123_BITPOS         (19)
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

//
#define GIRQ09_MASK                     (0x7FFFFFFFul)
#define GIRQ09_WAKE_CAPABLE_MASK        (0x7FFFFFFFul)
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

//
#define GIRQ11_MASK                     (0x7FFFFFFFul)
#define GIRQ11_WAKE_CAPABLE_MASK        (0x7FFFFFFFul)
//

// GIRQ12 Bit Positions 
#define GIRQ12_GPIO_0200_BITPOS         (0)
#define GIRQ12_GPIO_0201_BITPOS         (1)
#define GIRQ12_GPIO_0202_BITPOS         (2)
#define GIRQ12_GPIO_0203_BITPOS         (3)
#define GIRQ12_GPIO_0204_BITPOS         (4)
#define GIRQ12_GPIO_0205_BITPOS         (5)
#define GIRQ12_GPIO_0206_BITPOS         (6) 
#define GIRQ12_GPIO_0207_BITPOS         (7)
//
#define GIRQ12_GPIO_0210_BITPOS         (8)
#define GIRQ12_GPIO_0211_BITPOS         (9)
#define GIRQ12_GPIO_0212_BITPOS         (10)
#define GIRQ12_GPIO_0213_BITPOS         (11)
#define GIRQ12_GPIO_0214_BITPOS         (12)
#define GIRQ12_GPIO_0215_BITPOS         (13)
#define GIRQ12_GPIO_0216_BITPOS         (14) 
#define GIRQ12_GPIO_0217_BITPOS         (15)
//
#define GIRQ12_GPIO_0220_BITPOS         (16)
#define GIRQ12_GPIO_0221_BITPOS         (17)
#define GIRQ12_GPIO_0222_BITPOS         (18)
#define GIRQ12_GPIO_0223_BITPOS         (19)
#define GIRQ12_GPIO_0224_BITPOS         (20)
#define GIRQ12_GPIO_0225_BITPOS         (21)
#define GIRQ12_GPIO_0226_BITPOS         (22) 
#define GIRQ12_GPIO_0227_BITPOS         (23)
//
#define GIRQ12_GPIO_0230_BITPOS         (24)
#define GIRQ12_GPIO_0231_BITPOS         (25)
#define GIRQ12_GPIO_0232_BITPOS         (26)
#define GIRQ12_GPIO_0233_BITPOS         (27)
#define GIRQ12_GPIO_0234_BITPOS         (28)
#define GIRQ12_GPIO_0235_BITPOS         (29)
#define GIRQ12_GPIO_0236_BITPOS         (30) 

//
#define GIRQ12_MASK                     (0x7FFFFFFFul)
#define GIRQ12_WAKE_CAPABLE_MASK        (0x7FFFFFFFul)

// GIRQ13 Bit Positions 
#define GIRQ13_SMBUS0_BITPOS            (0)
#define GIRQ13_SMBUS1_BITPOS            (1)
#define GIRQ13_SMBUS2_BITPOS            (2)
#define GIRQ13_SMBUS3_BITPOS            (3)

#define GIRQ13_MASK                     (0xFul)
#define GIRQ13_WAKE_CAPABLE_MASK        (0x0ul)
//

// GIRQ14 Bit Positions 
#define GIRQ14_DMA0_BITPOS              (0)
#define GIRQ14_DMA1_BITPOS              (1)
#define GIRQ14_DMA2_BITPOS              (2)
#define GIRQ14_DMA3_BITPOS              (3)
#define GIRQ14_DMA4_BITPOS              (4)
#define GIRQ14_DMA5_BITPOS              (5)
#define GIRQ14_DMA6_BITPOS              (6)
#define GIRQ14_DMA7_BITPOS              (7)
#define GIRQ14_DMA8_BITPOS              (8)
#define GIRQ14_DMA9_BITPOS              (9)
#define GIRQ14_DMA10_BITPOS             (10)
#define GIRQ14_DMA11_BITPOS             (11)
#define GIRQ14_DMA12_BITPOS             (12)
#define GIRQ14_DMA13_BITPOS             (13)
//
#define GIRQ14_MASK                     (0x3FFFul)
#define GIRQ14_WAKE_CAPABLE_MASK        (0x00000000ul)
//


// GIRQ15 Bit Positions 
#define GIRQ15_UART0_BITPOS             (0)
#define GIRQ15_UART1_BITPOS             (1)
#define GIRQ15_EMI0_BITPOS              (2)
#define GIRQ15_EMI1_BITPOS              (3)
#define GIRQ15_EMI2_BITPOS              (4)
#define GIRQ15_ACPI0_IBF_BITPOS         (5)
#define GIRQ15_ACPI0_OBF_BITPOS         (6)
#define GIRQ15_ACPI1_IBF_BITPOS         (7)
#define GIRQ15_ACPI1_OBF_BITPOS         (8)
#define GIRQ15_ACPI2_IBF_BITPOS         (9)
#define GIRQ15_ACPI2_OBF_BITPOS         (10)
#define GIRQ15_ACPI3_IBF_BITPOS         (11)
#define GIRQ15_ACPI3_OBF_BITPOS         (12)
#define GIRQ15_ACPI4_IBF_BITPOS         (13)
#define GIRQ15_ACPI4_OBF_BITPOS         (14)
#define GIRQ15_ACPI_PM1CTL_BITPOS       (15)
#define GIRQ15_ACPI_PM1EN_BITPOS        (16)
#define GIRQ15_ACPI_PM1STS_BITPOS       (17)
#define GIRQ15_MF8042_OBF_BITPOS        (18)
#define GIRQ15_MF8042_IBF_BITPOS        (19)
#define GIRQ15_MAILBOX_BITPOS           (20)
#define GIRQ15_PORT80_DBG0_BITPOS       (22)
#define GIRQ15_PORT80_DBG1_BITPOS       (23)
#define GIRQ15_TEST_BITPOS              (24)

//
#define GIRQ15_MASK                     (0x1FFFFFFul)
#define GIRQ15_WAKE_CAPABLE_MASK        (0x000000ul)
//

// GIRQ16 Bit Positions 
#define PKE_ERROR_BITPOS                (0)
#define PKE_END_BITPOS                  (1)
#define RNG_BITPOS                      (2)
#define AES_BITPOS                      (3)
#define HASH_BITPOS                     (4)

//
#define GIRQ16_MASK                     (0x1Ful)
#define GIRQ16_WAKE_CAPABLE_MASK        (0x00ul)
//

// GIRQ17 Bit Positions 
#define GIRQ17_PECI_BITPOS              (0)
#define GIRQ17_TACH0_BITPOS             (1)
#define GIRQ17_TACH1_BITPOS             (2)
#define GIRQ17_TACH2_BITPOS             (3)
#define GIRQ17_RPM2PWM0_FAIL_BITPOS     (4)
#define GIRQ17_RPM2PWM0_STALL_BITPOS    (5)
#define GIRQ17_RPM2PWM1_FAIL_BITPOS     (6)
#define GIRQ17_RPM2PWM1_STALL_BITPOS    (7)
#define GIRQ17_ADC_INT0_BITPOS          (8)
#define GIRQ17_ADC_INT1_BITPOS          (9)
#define GIRQ17_RC_ID0_BITPOS            (10)
#define GIRQ17_RC_ID1_BITPOS            (11)
#define GIRQ17_RC_ID2_BITPOS            (12)
#define GIRQ17_LED0_BITPOS              (13)
#define GIRQ17_LED1_BITPOS              (14)
#define GIRQ17_LED2_BITPOS              (15)
#define GIRQ17_LED3_BITPOS              (16)
#define GIRQ17_PHOT_BITPOS              (17)
#define GIRQ17_PWRGUARD0_BITPOS         (18)
#define GIRQ17_PWRGUARD1_BITPOS         (19)
#define GIRQ17_RTOS_SWI0_BITPOS         (25)
#define GIRQ17_RTOS_SWI1_BITPOS         (26)
#define GIRQ17_RTOS_SWI2_BITPOS         (27)
#define GIRQ17_RTOS_SWI3_BITPOS         (28)

//
#define GIRQ17_MASK                     (0x1E0FFFFFul)
#define GIRQ17_WAKE_CAPABLE_MASK        (0x0ul)
//

// GIRQ18 Bit Positions
#define GIRQ18_LPC_ERROR_BITPOS         (0)
#define GIRQ18_QMSPI_INT_BITPOS         (1)
#define GIRQ18_SPI0_TX_BITPOS           (2)
#define GIRQ18_SPI0_RX_BITPOS           (3)
#define GIRQ18_SPI1_TX_BITPOS           (4)
#define GIRQ18_SPI1_RX_BITPOS           (5)
#define GIRQ18_BCM0_BUSY_CLR_BITPOS     (6)
#define GIRQ18_BCM0_ERROR_BITPOS        (7)
#define GIRQ18_BCM1_BUSY_CLR_BITPOS     (8)
#define GIRQ18_BCM1_ERROR_BITPOS        (9)
#define GIRQ18_PS2_ACT0_BITPOS          (10)
#define GIRQ18_PS2_ACT1_BITPOS          (11)
#define GIRQ18_PS2_ACT2_BITPOS          (12)
#define GIRQ18_EEPROM_BITPOS            (13)

//
#define GIRQ18_MASK                     (0x3FFFul)
#define GIRQ18_WAKE_CAPABLE_MASK        (0x0ul)
//

// GIRQ19 Bit Positions 
#define GIRQ19_ESPI_INTR_PC_BITPOS       (0)
#define GIRQ19_ESPI_INTR_BM1_BITPOS      (1)
#define GIRQ19_ESPI_INTR_BM2_BITPOS      (2)
#define GIRQ19_ESPI_INTR_LTR_BITPOS      (3)
#define GIRQ19_ESPI_INTR_OOB_UP_BITPOS   (4)
#define GIRQ19_ESPI_INTR_OOB_DN_BITPOS   (5)
#define GIRQ19_ESPI_INTR_FLASH_BITPOS    (6)
#define GIRQ19_ESPI_RESET_BITPOS         (7)
#define GIRQ19_ESPI_VW_ENABLE_BITPOS     (8)

//
#define GIRQ19_MASK                     (0x01FFul)
#define GIRQ19_WAKE_CAPABLE_MASK        (0x0ul)
//

// GIRQ20 Bit Positions 

// 
#define GIRQ20_MASK                     (0x0ul)
#define GIRQ20_WAKE_CAPABLE_MASK        (0x0ul)
//

// GIRQ21 Bit Positions 
#define GIRQ21_RTOS_TIMER_BITPOS        (0)
#define GIRQ21_HTIMER0_BITPOS           (1)
#define GIRQ21_HTIMER1_BITPOS           (2)
#define GIRQ21_WEEK_ALRM_INT_BITPOS     (3)
#define GIRQ21_SUB_WEEK_ALRM_INT_BITPOS (4)
#define GIRQ21_ONE_SECOND_BITPOS        (5)
#define GIRQ21_SUB_SECOND_BITPOS        (6)
#define GIRQ21_SYSPWR_PRES_BITPOS       (7)
#define GIRQ21_RTC_BITPOS               (8)
#define GIRQ21_RTC_ALARM_BITPOS         (9)
#define GIRQ21_VBAT_VCI_OVRD_IN_BITPOS  (10)
#define GIRQ21_VBAT_VCI_IN0_BITPOS      (11)
#define GIRQ21_VBAT_VCI_IN1_BITPOS      (12)
#define GIRQ21_VBAT_VCI_IN2_BITPOS      (13)
#define GIRQ21_VBAT_VCI_IN3_BITPOS      (14)
#define GIRQ21_VBAT_VCI_IN4_BITPOS      (15)
#define GIRQ21_VBAT_VCI_IN5_BITPOS      (16)
#define GIRQ21_VBAT_VCI_IN6_BITPOS      (17)
#define GIRQ21_PS2_0A_WK_BITPOS         (18)
#define GIRQ21_PS2_0B_WK_BITPOS         (19)
#define GIRQ21_PS2_1A_WK_BITPOS         (20)
#define GIRQ21_PS2_1B_WK_BITPOS         (21)
#define GIRQ21_PS2_2_WK_BITPOS          (22)
#define GIRQ21_ENVMON_BITPOS            (24)
#define GIRQ21_KSC_INT_BITPOS           (25)

//
#define GIRQ21_MASK                     (0x37FFFFFul)
#define GIRQ21_WAKE_CAPABLE_MASK        (0x37FFFFFul)
//

// GIRQ22 Bit Positions 
#define GIRQ22_LPC_WAKE_ONLY_BITPOS     (0)
#define GIRQ22_SMB0_WAKE_ONLY_BITPOS    (1)
#define GIRQ22_SMB1_WAKE_ONLY_BITPOS    (2)
#define GIRQ22_SMB2_WAKE_ONLY_BITPOS    (3)
#define GIRQ22_SMB3_WAKE_ONLY_BITPOS    (4)
#define GIRQ22_ESPI_WAKE_ONLY_BITPOS    (9)

#define GIRQ22_MASK                     (0x021Ful)
#define GIRQ22_WAKE_CAPABLE_MASK        (0x021Ful)

// GIRQ23 Bit Positions 
#define GIRQ23_TMR0_BITPOS              (0)
#define GIRQ23_TMR1_BITPOS              (1)
#define GIRQ23_TMR2_BITPOS              (2)
#define GIRQ23_TMR3_BITPOS              (3)
#define GIRQ23_TMR4_BITPOS              (4)
#define GIRQ23_TMR5_BITPOS              (5)
#define GIRQ23_CTIMER0_BITPOS           (6)
#define GIRQ23_CTIMER1_BITPOS           (7)
#define GIRQ23_CTIMER2_BITPOS           (8)
#define GIRQ23_CTIMER3_BITPOS           (9)
#define GIRQ23_CAP_TIMER_BITPOS         (10)
#define GIRQ23_CCTIMER0_BITPOS          (11)
#define GIRQ23_CCTIMER1_BITPOS          (12)
#define GIRQ23_CCTIMER2_BITPOS          (13)
#define GIRQ23_CCTIMER3_BITPOS          (14)
#define GIRQ23_CCTIMER4_BITPOS          (15)
#define GIRQ23_CCTIMER5_BITPOS          (16)
#define GIRQ23_CCTIMER6_BITPOS          (17)
#define GIRQ23_CCTIMER7_BITPOS          (18)

//
#define GIRQ23_MASK                     (0x07FFFFul)
#define GIRQ23_WAKE_CAPABLE_MASK        (0x0ul)
//

// GIRQ24 Bit Positions
#define GIRQ24_ESPI_VW00_SRC0_BITPOS     (0)
#define GIRQ24_ESPI_VW00_SRC1_BITPOS     (1)
#define GIRQ24_ESPI_VW00_SRC2_BITPOS     (2)
#define GIRQ24_ESPI_VW00_SRC3_BITPOS     (3)
#define GIRQ24_ESPI_VW01_SRC0_BITPOS     (4)
#define GIRQ24_ESPI_VW01_SRC1_BITPOS     (5)
#define GIRQ24_ESPI_VW01_SRC2_BITPOS     (6)
#define GIRQ24_ESPI_VW01_SRC3_BITPOS     (7)
#define GIRQ24_ESPI_VW02_SRC0_BITPOS     (8)
#define GIRQ24_ESPI_VW02_SRC1_BITPOS     (9)
#define GIRQ24_ESPI_VW02_SRC2_BITPOS     (10)
#define GIRQ24_ESPI_VW02_SRC3_BITPOS     (11)
#define GIRQ24_ESPI_VW03_SRC0_BITPOS     (12)
#define GIRQ24_ESPI_VW03_SRC1_BITPOS     (13)
#define GIRQ24_ESPI_VW03_SRC2_BITPOS     (14)
#define GIRQ24_ESPI_VW03_SRC3_BITPOS     (15)
#define GIRQ24_ESPI_VW04_SRC0_BITPOS     (16)
#define GIRQ24_ESPI_VW04_SRC1_BITPOS     (17)
#define GIRQ24_ESPI_VW04_SRC2_BITPOS     (18)
#define GIRQ24_ESPI_VW04_SRC3_BITPOS     (19)
#define GIRQ24_ESPI_VW05_SRC0_BITPOS     (20)
#define GIRQ24_ESPI_VW05_SRC1_BITPOS     (21)
#define GIRQ24_ESPI_VW05_SRC2_BITPOS     (22)
#define GIRQ24_ESPI_VW05_SRC3_BITPOS     (23)
#define GIRQ24_ESPI_VW06_SRC0_BITPOS     (24)
#define GIRQ24_ESPI_VW06_SRC1_BITPOS     (25)
#define GIRQ24_ESPI_VW06_SRC2_BITPOS     (26)
#define GIRQ24_ESPI_VW06_SRC3_BITPOS     (27)

//
#define GIRQ24_MASK                      (0x0FFFFFFFul)
#define GIRQ24_WAKE_CAPABLE_MASK         (0x0FFFFFFFul)
//

// GIRQ25 Bit Positions
#define GIRQ25_ESPI_VW07_SRC0_BITPOS     (0)
#define GIRQ25_ESPI_VW07_SRC1_BITPOS     (1)
#define GIRQ25_ESPI_VW07_SRC2_BITPOS     (2)
#define GIRQ25_ESPI_VW07_SRC3_BITPOS     (3)
#define GIRQ25_ESPI_VW08_SRC0_BITPOS     (4)
#define GIRQ25_ESPI_VW08_SRC1_BITPOS     (5)
#define GIRQ25_ESPI_VW08_SRC2_BITPOS     (6)
#define GIRQ25_ESPI_VW08_SRC3_BITPOS     (7)
#define GIRQ25_ESPI_VW09_SRC0_BITPOS     (8)
#define GIRQ25_ESPI_VW09_SRC1_BITPOS     (9)
#define GIRQ25_ESPI_VW09_SRC2_BITPOS     (10)
#define GIRQ25_ESPI_VW09_SRC3_BITPOS     (11)
#define GIRQ25_ESPI_VW10_SRC0_BITPOS     (12)
#define GIRQ25_ESPI_VW10_SRC1_BITPOS     (13)
#define GIRQ25_ESPI_VW10_SRC2_BITPOS     (14)
#define GIRQ25_ESPI_VW10_SRC3_BITPOS     (15)

//
#define GIRQ25_MASK                      (0x0FFFFul)
#define GIRQ25_WAKE_CAPABLE_MASK         (0x0FFFFul)
//

// GIRQ26 bit positions
#define GIRQ26_GPIO240_BITPOS            (0)
#define GIRQ26_GPIO241_BITPOS            (1)
#define GIRQ26_GPIO242_BITPOS            (2)
#define GIRQ26_GPIO243_BITPOS            (3)
#define GIRQ26_GPIO244_BITPOS            (4)
#define GIRQ26_GPIO245_BITPOS            (5)
#define GIRQ26_GPIO246_BITPOS            (6)
#define GIRQ26_GPIO247_BITPOS            (7)

#define GIRQ26_GPIO250_BITPOS            (8)
#define GIRQ26_GPIO251_BITPOS            (9)
#define GIRQ26_GPIO252_BITPOS            (10)
#define GIRQ26_GPIO253_BITPOS            (11)
#define GIRQ26_GPIO254_BITPOS            (12)
#define GIRQ26_GPIO255_BITPOS            (13)
#define GIRQ26_GPIO256_BITPOS            (14)
#define GIRQ26_GPIO257_BITPOS            (15)

#define GIRQ26_GPIO260_BITPOS            (16)
#define GIRQ26_GPIO261_BITPOS            (17)
#define GIRQ26_GPIO262_BITPOS            (18)
#define GIRQ26_GPIO263_BITPOS            (19)
#define GIRQ26_GPIO264_BITPOS            (20)
#define GIRQ26_GPIO265_BITPOS            (21)
#define GIRQ26_GPIO266_BITPOS            (22)
#define GIRQ26_GPIO267_BITPOS            (23)

#define GIRQ26_GPIO270_BITPOS            (24)
#define GIRQ26_GPIO271_BITPOS            (25)
#define GIRQ26_GPIO272_BITPOS            (26)
#define GIRQ26_GPIO273_BITPOS            (27)
#define GIRQ26_GPIO274_BITPOS            (28)
#define GIRQ26_GPIO275_BITPOS            (29)
#define GIRQ26_GPIO276_BITPOS            (30)

#define GIRQ26_MASK                      (0x7FFFFFFFul)
#define GIRQ26_WAKE_CAPABLE_MASK         (0x7FFFFFFFul)

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

#endif // #ifndef _INTERRUPT_H
/* end interrupt.h */
/**   @}
 */



