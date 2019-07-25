/*****************************************************************************
* Copyright 2014 Microchip Technology Inc. and its subsidiaries.
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

/** @file mec14xx_pcr.h
 *MEC14xx Power Control Reset definitions
 */
/** @defgroup MEC14xx Peripherals PCR
 */

#ifndef _MEC14XX_PCR_H
#define _MEC14XX_PCR_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define PCR_SLEEP_EN    (1u)
#define PCR_SLEEP_DIS   (0u)

//
// VTR Powered PCR registers
//

//
// Chip Sleep Enable Reg (Offset +00h) 
// Chip Clock Required Status Reg (Offset +04h)
//
#define PCR_CHIP_SLP_EN_OFFSET          (0ul)
#define PCR_CHIP_SLP_EN_MASK            (0x03ul)
#define PCR_CHIP_STAP_BITPOS            (0)
#define PCR_CHIP_EFUSE_BITPOS           (1)
#define PCR_CHIP_CLK_REQ_OFFSET         (0x04ul)
#define PCR_CHIP_CLK_REQ_MASK           (0x03ul)
//
#define PCR_CHIP_STAP_SLP_CLK           (1ul << (PCR_CHIP_STAP_BITPOS))
#define PCR_CHIP_EFUSE_SLP_CLK          (1ul << (PCR_CHIP_EFUSE_BITPOS))
//
#define PCR_CHIP_STAP_NOSLP_CLK         (0ul)
#define PCR_CHIP_EFUSE_NOSLP_CLK        (0ul)


//
// EC Sleep Enable Reg (Offset +08h)
// EC Clock Required Status Reg (Offset +0Ch)
//
#define PCR_EC_SLP_EN_OFFSET            (0x08ul)
#define PCR_EC_SLP_EN_MASK              (0xE7F00FF7ul)
#define PCR_EC_CLK_REQ_OFFSET           (0x0Cul)
#define PCR_EC_CLK_REQ_MASK             (0xE7F00FF7ul)
//
#define PCR_EC_INT_SLP_BITPOS           (0)
#define PCR_EC_PECI_SLP_BITPOS          (1)
#define PCR_EC_TACH0_SLP_BITPOS         (2)
// bit[3] Reserved
#define PCR_EC_PWM0_SLP_BITPOS          (4)
#define PCR_EC_PMC_SLP_BITPOS           (5)
#define PCR_EC_DMA_SLP_BITPOS           (6)
#define PCR_EC_TFDP_SLP_BITPOS          (7)
#define PCR_EC_CPU_SLP_BITPOS           (8)
#define PCR_EC_WDT_SLP_BITPOS           (9)
#define PCR_EC_SMB0_SLP_BITPOS          (10)
#define PCR_EC_TACH1_SLP_BITPOS         (11)
// bits[19:12] Rerserved
#define PCR_EC_PWM1_SLP_BITPOS          (20)
#define PCR_EC_PWM2_SLP_BITPOS          (21)
#define PCR_EC_PWM3_SLP_BITPOS          (22)
#define PCR_EC_PWM4_SLP_BITPOS          (23)
#define PCR_EC_PWM5_SLP_BITPOS          (24)
#define PCR_EC_PWM6_SLP_BITPOS          (25)
#define PCR_EC_PWM7_SLP_BITPOS          (26)
// bits[28:17] Reserved
#define PCR_EC_REG_SLP_BITPOS           (29)
#define PCR_EC_TIMER0_SLP_BITPOS        (30)
#define PCR_EC_TIMER1_SLP_BITPOS        (31)
//

#define PCR_EC_INT_SLP_CLK          (1ul << (PCR_EC_INT_SLP_BITPOS))
#define PCR_EC_PECI_SLP_CLK         (1ul << (PCR_EC_PECI_SLP_BITPOS))
#define PCR_EC_TACH0_SLP_CLK        (1ul << PCR_EC_TACH0_SLP_BITPOS))
// bit[3] Reserved
#define PCR_EC_PWM0_SLP_CLK         (1ul << (PCR_EC_PWM0_SLP_BITPOS))
#define PCR_EC_PMC_SLP_CLK          (1ul << (PCR_EC_PMC_SLP_BITPOS))
#define PCR_EC_DMA_SLP_CLK          (1ul << (PCR_EC_DMA_SLP_BITPOS))
#define PCR_EC_TFDP_SLP_CLK         (1ul << (PCR_EC_TFDP_SLP_BITPOS))
#define PCR_EC_CPU_SLP_CLK          (1ul << (PCR_EC_CPU_SLP_BITPOS))
#define PCR_EC_WDT_SLP_CLK          (1ul << (PCR_EC_WDT_SLP_BITPOS))
#define PCR_EC_SMB0_SLP_CLK         (1ul << (PCR_EC_SMB0_SLP_BITPOS))
#define PCR_EC_TACH1_SLP_CLK        (1ul << (PCR_EC_TACH1_SLP_BITPOS))
// bits[19:12] Rerserved
#define PCR_EC_PWM1_SLP_CLK         (1ul << (PCR_EC_PWM1_SLP_BITPOS))
#define PCR_EC_PWM2_SLP_CLK         (1ul << (PCR_EC_PWM2_SLP_BITPOS))
#define PCR_EC_PWM3_SLP_CLK         (1ul << (PCR_EC_PWM3_SLP_BITPOS))
#define PCR_EC_PWM4_SLP_CLK         (1ul << (PCR_EC_PWM4_SLP_BITPOS))
#define PCR_EC_PWM5_SLP_CLK         (1ul << (PCR_EC_PWM5_SLP_BITPOS))
#define PCR_EC_PWM6_SLP_CLK         (1ul << (PCR_EC_PWM6_SLP_BITPOS))
#define PCR_EC_PWM7_SLP_CLK         (1ul << (PCR_EC_PWM7_SLP_BITPOS))
// bits[28:17] Reserved
#define PCR_EC_REG_SLP_CLK          (1ul << (PCR_EC_REG_SLP_BITPOS))
#define PCR_EC_TIMER0_SLP_CLK       (1ul << (PCR_EC_TIMER0_SLP_BITPOS))
#define PCR_EC_TIMER1_SLP_CLK       (1ul << (PCR_EC_TIMER1_SLP_BITPOS))


//
// Host Sleep Enable Reg (Offset +10h)
// Host Clock Required Status Reg (Offset +14h)
//
#define PCR_HOST_SLP_EN_OFFSET          (0x10UL)
#define PCR_HOST_SLP_EN_MASK            (0x001BFC0Ful)
#define PCR_HOST_CLK_REQ_OFFSET         (0x14UL)
#define PCR_HOST_CLK_REQ_MASK           (0x001BFC0Ful)
//
#define PCR_HOST_LPC_SLP_BITPOS         (0)
#define PCR_HOST_UART0_SLP_BITPOS       (1)
#define PCR_HOST_P80A_SLP_BITPOS        (2)
#define PCR_HOST_P80B_SLP_BITPOS        (3)
// b[9:4] Reserved
#define PCR_HOST_ACPI_EC2_SLP_BITPOS    (10)
#define PCR_HOST_ACPI_EC3_SLP_BITPOS    (11)
#define PCR_HOST_GLBL_CFG_SLP_BITPOS    (12)
#define PCR_HOST_APCI_EC0_SLP_BITPOS    (13)
#define PCR_HOST_APCI_EC1_SLP_BITPOS    (14)
#define PCR_HOST_APCI_PM1_SLP_BITPOS    (15)
#define PCR_HOST_MIF8042_SLP_BITPOS     (16)
#define PCR_HOST_MBOX_SLP_BITPOS        (17)
// b[18] Reserved
#define PCR_HOST_ESPI_SLP_BITPOS        (19)
#define PCR_HOST_TSCR_SLP_BITPOS        (20)
// b[31:12] Reserved

//
#define PCR_HOST_LPC_SLP_CLK            (1UL<<(PCR_HOST_LPC_SLP_BITPOS))
#define PCR_HOST_UART0_SLP_CLK          (1UL<<(PCR_HOST_UART0_SLP_BITPOS))
#define PCR_HOST_P80A_SLP_CLK           (1UL<<(PCR_HOST_P80A_SLP_BITPOS))
#define PCR_HOST_P80B_SLP_CLK           (1UL<<(PCR_HOST_P80B_SLP_BITPOS))
#define PCR_HOST_ACPI_EC2_SLP_CLK       (1UL<<(PCR_HOST_ACPI_EC2_SLP_BITPOS))
#define PCR_HOST_ACPI_EC3_SLP_CLK       (1UL<<(PCR_HOST_ACPI_EC3_SLP_BITPOS))
#define PCR_HOST_GLBL_CFG_SLP_CLK       (1UL<<(PCR_HOST_GLBL_CFG_SLP_BITPOS))
#define PCR_HOST_APCI_EC0_SLP_CLK       (1UL<<(PCR_HOST_APCI_EC0_SLP_BITPOS))
#define PCR_HOST_APCI_EC1_SLP_CLK       (1UL<<(PCR_HOST_APCI_EC1_SLP_BITPOS))
#define PCR_HOST_APCI_PM1_SLP_CLK       (1UL<<(PCR_HOST_APCI_PM1_SLP_BITPOS))
#define PCR_HOST_MIF8042_SLP_CLK        (1UL<<(PCR_HOST_MIF8042_SLP_BITPOS))
#define PCR_HOST_MBOX_SLP_CLK           (1UL<<(PCR_HOST_MBOX_SLP_BITPOS))
#define PCR_HOST_ESPI_SLP_CLK           (1UL<<(PCR_HOST_ESPI_SLP_BITPOS))
#define PCR_HOST_TSCR_SLP_CLK           (1UL<<(PCR_HOST_TSCR_SLP_BITPOS))

//
#define PCR_HOST_LPC_NOSLP_CLK            (0)
#define PCR_HOST_UART0_NOSLP_CLK          (0)
#define PCR_HOST_P80A_NOSLP_CLK           (0)
#define PCR_HOST_P80B_NOSLP_CLK           (0)
#define PCR_HOST_ACPI_EC2_NOSLP_CLK       (0)
#define PCR_HOST_ACPI_EC3_NOSLP_CLK       (0)
#define PCR_HOST_GLBL_CFG_NOSLP_CLK       (0)
#define PCR_HOST_APIC_EC0_NOSLP_CLK       (0)
#define PCR_HOST_APIC_EC1_NOSLP_CLK       (0)
#define PCR_HOST_APIC_PM1_NOSLP_CLK       (0)
#define PCR_HOST_MIF8042_NOSLP_CLK        (0)
#define PCR_HOST_MBOX_NOSLP_CLK           (0)
#define PCR_HOST_ESPI_NOSLP_CLK           (0)
#define PCR_HOST_TSCR_NOSLP_CLK           (0)



//
// System Sleep Control Reg (Offset +18h)
//
#define PCR_SYS_SLP_CTRL_OFFSET             (0x18ul)
#define PCR_SYS_SLP_CTRL_MASK               (0x77ul)
#define PCR_SYS_SLP_ROSC_PD_BITPOS          (0u)
#define PCR_SYS_SLP_ROSC_GATE_BITPOS        (1u)
#define PCR_SYS_SLP_CORE_VREG_STDBY_BITPOS  (2u)
#define PCR_SYS_SLP_ALL_BITPOS              (4u)
#define PCR_SYS_SLP_DBG_BITPOS              (5u)
#define PCR_SYS_SLP_AUTO_CLR_BITPOS         (6u)

#define PCR_SYS_SLP_ROSC_PD             (1ul<<(PCR_SYS_SLP_ROSC_PD_BITPOS))
#define PCR_SYS_SLP_ROSC_GATE           (1ul<<(PCR_SYS_SLP_ROSC_GATE_BITPOS))
#define PCR_SYS_SLP_CORE_VREG_STDBY     (1ul<<(PCR_SYS_SLP_CORE_VREG_STDBY_BITPOS))
#define PCR_SYS_SLP_ALL                 (1ul<<(PCR_SYS_SLP_ALL_BITPOS))
#define PCR_SYS_SLP_DBG                 (1ul<<(PCR_SYS_SLP_DBG_BITPOS))
#define PCR_SYS_SLP_AUTO_CLR            (1ul<<(PCR_SYS_SLP_AUTO_CLR_BITPOS))



//
// Reserved (Offset +1Ch)
//

//
// Processor Clock Control Reg (Offset +20h)
//
#define PCR_CLK_CTRL_OFFSET             (0x20UL)
#define PCR_CLK_CTRL_MASK               (0xFFUL)
#define PCR_CLK_CTRL_48M                (0x01UL)
#define PCR_CLK_CTRL_24M                (0x02UL)
#define PCR_CLK_CTRL_16M                (0x03UL)
#define PCR_CLK_CTRL_12M                (0x04UL)
#define PCR_CLK_CTRL_9P6M               (0x05UL)
#define PCR_CLK_CTRL_8M                 (0x06UL)
#define PCR_CLK_CTRL_6P9M               (0x07UL)
#define PCR_CLK_CTRL_6M                 (0x08UL)
#define PCR_CLK_CTRL_4M                 (0x0CUL)
#define PCR_CLK_CTRL_1M                 (0x30UL)

//
// EC Sleep Enable 2 Reg (Offset +24h)
// EC Clock Required 2 Reg (Offset +28h)
//
#define PCR_SLP_EN2_OFFSET              (0x24UL)
#define PCR_SLP_EN2_MASK                (0x00FF7E6Eul)
#define PCR_CLK_REQ2_OFFSET             (0x28UL)
#define PCR_CLK_REQ2_MASK               (0x00FF7E6EUL)
//
#define PCR_EC2_DAC0_SLP_BITPOS         (1)
#define PCR_EC2_DAC1_SLP_BITPOS         (2)
#define PCR_EC2_ADC_SLP_BITPOS          (3)
// bit[4] Reserved
#define PCR_EC2_PS2_0_SLP_BITPOS        (5)
#define PCR_EC2_PS2_1_SLP_BITPOS        (6)
// bits[8:7] Reserved
#define PCR_EC2_SPI0_SLP_BITPOS         (9)
#define PCR_EC2_HIB_SLP_BITPOS          (10)
#define PCR_EC2_KEY_SLP_BITPOS          (11)
#define PCR_EC2_RTOS_TMR_SLP_BITPOS     (12)
#define PCR_EC2_SMB1_SLP_BITPOS         (13)
#define PCR_EC2_SMB2_SLP_BITPOS         (14)
// bit[15] Reserved
#define PCR_EC2_LED0_SLP_BITPOS         (16)
#define PCR_EC2_LED1_SLP_BITPOS         (17)
#define PCR_EC2_LED2_SLP_BITPOS         (18)
#define PCR_EC2_BCM0_SLP_BITPOS         (19)
#define PCR_EC2_BCM1_SLP_BITPOS         (20)
#define PCR_EC2_TIMER2_SLP_BITPOS       (21)
#define PCR_EC2_TIMER3_SLP_BITPOS       (22)
#define PCR_EC2_SUBDEC_SLP_BITPOS       (23)

//
#define PCR_EC2_DAC0_SLP_CLK        (1ul << (PCR_EC2_DAC0_SLP_BITPOS))
#define PCR_EC2_DAC1_SLP_CLK        (1ul << (PCR_EC2_DAC1_SLP_BITPOS))
#define PCR_EC2_ADC_SLP_CLK         (1ul << (PCR_EC2_ADC_SLP_BITPOS))
#define PCR_EC2_PS2_0_SLP_CLK       (1ul << (PCR_EC2_PS2_0_SLP_BITPOS))
#define PCR_EC2_PS2_1_SLP_CLK       (1ul << (PCR_EC2_PS2_1_SLP_BITPOS))
#define PCR_EC2_SPI0_SLP_CLK        (1ul << (PCR_EC2_SPI0_SLP_BITPOS))
#define PCR_EC2_HIB_SLP_CLK         (1ul << (PCR_EC2_SPI0_SLP_BITPOS))
#define PCR_EC2_KEY_SLP_CLK         (1ul << (PCR_EC2_KEY_SLP_BITPOS))
#define PCR_EC2_RTOS_TMR_SLP_CLK    (1ul << (PCR_EC2_RTOS_TMR_SLP_BITPOS))
#define PCR_EC2_SMB1_SLP_CLK        (1ul << (PCR_EC2_SMB1_SLP_BITPOS))
#define PCR_EC2_SMB2_SLP_CLK        (1ul << (PCR_EC2_SMB2_SLP_BITPOS))
#define PCR_EC2_LED0_SLP_CLK        (1ul << (PCR_EC2_LED0_SLP_BITPOS))
#define PCR_EC2_LED1_SLP_CLK        (1ul << (PCR_EC2_LED1_SLP_BITPOS))
#define PCR_EC2_LED2_SLP_CLK        (1ul << (PCR_EC2_LED2_SLP_BITPOS))
#define PCR_EC2_BCM0_SLP_CLK        (1ul << (PCR_EC2_BCM0_SLP_BITPOS))
#define PCR_EC2_BCM1_SLP_CLK        (1ul << (PCR_EC2_BCM1_SLP_BITPOS))
#define PCR_EC2_TIMER2_SLP_CLK      (1ul << (PCR_EC2_TIMER2_SLP_BITPOS))
#define PCR_EC2_TIMER3_SLP_CLK      (1ul << (PCR_EC2_TIMER3_SLP_BITPOS))
#define PCR_EC2_SUBDEC_SLP_CLK      (1ul << (PCR_EC2_SUBDEC_SLP_BITPOS))

//
#define PCR_EC2_DAC0_NOSLP_CLK      (0)
#define PCR_EC2_DAC1_NOSLP_CLK      (0)
#define PCR_EC2_ADC_NOSLP_CLK       (0)
#define PCR_EC2_PS2_0_NOSLP_CLK     (0)
#define PCR_EC2_PS2_1_NOSLP_CLK     (0)
#define PCR_EC2_SPI0_NOSLP_CLK      (0)
#define PCR_EC2_HIB_NOSLP_CLK       (0)
#define PCR_EC2_KEY_NOSLP_CLK       (0)
#define PCR_EC2_RTOS_TMR_NOSLP_CLK  (0)
#define PCR_EC2_SMB1_NOSLP_CLK      (0)
#define PCR_EC2_SMB2_NOSLP_CLK      (0)
#define PCR_EC2_LED0_NOSLP_CLK      (0)
#define PCR_EC2_LED1_NOSLP_CLK      (0)
#define PCR_EC2_LED2_NOSLP_CLK      (0)
#define PCR_EC2_BCM0_NOSLP_CLK      (0)
#define PCR_EC2_BCM1_NOSLP_CLK      (0)
#define PCR_EC2_TIMER2_NOSLP_CLK    (0)
#define PCR_EC2_TIMER3_NOSLP_CLK    (0)
#define PCR_EC2_SUBDEC_NOSLP_CLK    (0)



//
// Slow Clock Control Reg (Offset +2Ch)
//
#define PCR_SLOW_CLK_CTRL_OFFSET        (0x2Cul)
#define PCR_SLOW_CLK_CTRL_MASK          (0x03FFul)
#define PCR_SLOW_CLK_OFF                (0ul)
#define PCR_SLOW_CLK_48M                (1ul)
#define PCR_SLOW_CLK_24M                (2ul)
#define PCR_SLOW_CLK_16M                (3ul)
#define PCR_SLOW_CLK_12M                (4ul)
#define PCR_SLOW_CLK_9P6M               (5ul)
#define PCR_SLOW_CLK_8M                 (6ul)
#define PCR_SLOW_CLK_6M                 (8ul)
#define PCR_SLOW_CLK_4M                 (12ul)
#define PCR_SLOW_CLK_3M                 (16ul)
#define PCR_SLOW_CLK_2M                 (24ul)
#define PCR_SLOW_CLK_1M                 (48ul)

//
// Oscillator ID Reg (Offset +30h)
//
#define PCR_OSC_ID_OFFSET               (0x30ul)
#define PCR_OSC_LOCK                    (1ul<<8)

//
// Chip Sub-system Power Reset Status (Offset +34h)
//
#define PCR_CHIP_PRS_OFFSET             (0x34ul)
#define PCR_CHIP_PRS_MASK               (0x0E6Cul)
#define PCR_CHIP_PRS_VCC_PWRGD_RO       (1ul << 2)
#define PCR_CHIP_PRS_SIO_RSTN_RO        (1ul << 3)
#define PCR_CHIP_PRS_VBAT_RST_RW1C      (1ul << 5)
#define PCR_CHIP_PRS_VTR_RST_RW1C       (1ul << 6)
#define PCR_CHIP_PRS_VBAT_LOW_RO        (1ul << 9)
#define PCR_CHIP_PRS_32K_ACT_RO         (1ul << 10)
#define PCR_CHIP_PRS_PCICLK_ACT_RO      (1ul << 11)

//
// Chip Reset Enable Reg (Offset +38h)
//
#define PCR_CHIP_RST_EN_OFFSET          (0x38ul)
#define PCR_CHIP_RST_EN_STAP            (1ul << 0)
#define PCR_CHIP_RST_EN_EFUSE           (1ul << 1)

//
// Host Reset Enable Reg (Offset +3Ch)
//
#define PCR_HOST_RST_EN_OFFSET          (0x3Cul)
#define PCR_HOST_RST_EN_MASK            (0x0001F003ul)
#define PCR_HOST_RST_EN_LPC             (1ul << 0)
#define PCR_HOST_RST_EN_UART0           (1ul << 1)
#define PCR_HOST_RST_EN_GLBL_CFG        (1ul << 12)
#define PCR_HOST_RST_EN_ACPI_EC0        (1ul << 13)
#define PCR_HOST_RST_EN_ACPI_EC1        (1ul << 14)
#define PCR_HOST_RST_EN_ACPI_PM1        (1ul << 15)
#define PCR_HOST_RST_EN_MIF8042         (1ul << 16)


//
// EC Reset Enable Register (Offset +40h)
//
#define PCR_EC_RST_EN_OFFSET            (0x40ul)
#define PCR_EC_RST_EN_MASK              (0xE7F00FF7ul)
#define PCR_EC_RST_EN_INT               (1ul << 0)
#define PCR_EC_RST_EN_PECI              (1ul << 1)
#define PCR_EC_RST_EN_TACH0             (1ul << 2)
// bit[3] Reserved
#define PCR_EC_RST_EN_PWM0              (1ul << 4)
#define PCR_EC_RST_EN_PMC               (1ul << 5)
#define PCR_EC_RST_EN_DMA               (1ul << 6)
#define PCR_EC_RST_EN_TFDP              (1ul << 7)
#define PCR_EC_RST_EN_CPU               (1ul << 8)
#define PCR_EC_RST_EN_WDT               (1ul << 9)
#define PCR_EC_RST_EN_SMB0              (1ul << 10)
#define PCR_EC_RST_EN_TACH1             (1ul << 11)
// bits[19:12] Reserved
#define PCR_EC_RST_EN_PWM1              (1ul << 20)
#define PCR_EC_RST_EN_PWM2              (1ul << 21)
#define PCR_EC_RST_EN_PWM3              (1ul << 22)
#define PCR_EC_RST_EN_PWM4              (1ul << 23)
#define PCR_EC_RST_EN_PWM5              (1ul << 24)
#define PCR_EC_RST_EN_PWM6              (1ul << 25)
#define PCR_EC_RST_EN_PWM7              (1ul << 26)
// bits[28:27] Reserved
#define PCR_EC_RST_EN_REG               (1ul << 29)
#define PCR_EC_RST_EN_TIMER0            (1ul << 30)
#define PCR_EC_RST_EN_TIMER1            (1ul << 31)

//
// EC Reset Enable 2 Register (Offset +44h)
//
#define PCR_EC_RST_EN2_OFFSET           (0x44ul)
#define PCR_EC_RST_EN2_MASK             (0x007FEE68ul)
#define PCR_EC2_RST_EN_ADC              (1ul << 3)
#define PCR_EC2_RST_EN_PS2_0            (1ul << 5)
#define PCR_EC2_RST_EN_PS2_1            (1ul << 6)
#define PCR_EC2_RST_EN_SPI0             (1ul << 9)
#define PCR_EC2_RST_EN_HIB              (1ul << 10)
#define PCR_EC2_RST_EN_KEY              (1ul << 11)
#define PCR_EC2_RST_EN_SMB1             (1ul << 13)
#define PCR_EC2_RST_EN_SMB2             (1ul << 14)
#define PCR_EC2_RST_EN_SMB3             (1ul << 15)
#define PCR_EC2_RST_EN_LED0             (1ul << 16)
#define PCR_EC2_RST_EN_LED1             (1ul << 17)
#define PCR_EC2_RST_EN_LED2             (1ul << 18)
#define PCR_EC2_RST_EN_BCM0             (1ul << 19)
#define PCR_EC2_RST_EN_BCM1             (1ul << 20)
#define PCR_EC2_RST_EN_TIMER2           (1ul << 21)
#define PCR_EC2_RST_EN_TIMER3           (1ul << 22)

//
// Host Reset 
//
// Power Reset Control Reg (Offset +48h)
//
#define PCR_HOST_OFFSET                 (0x48ul)
#define PCR_HOST_MASK                   (0x03ul)
#define PCR_HOST_IRESET_OUT_BITPOS      (0)
#define PCR_HOST_IRESET_OUT_ASSERT      (1ul << (PCR_HOST_IRESET_OUT_BITPOS))
#define PCR_HOST_RESET_SEL_BITPOS       (1)
#define PCR_HOST_RESET_SEL_LPC          (0ul << (PCR_HOST_RESET_SEL_BITPOS))
#define PCR_HOST_RESET_SEL_ESPI         (1ul << (PCR_HOST_RESET_SEL_BITPOS))

//
// ------------------------------------------------------------------
//

//
// VBAT Powered Register Bank
//
#define VBATR_PWR_FAIL_RESET_OFS        (0)
#define VBATR_ATE_REG_CTRL_OFS			(4)
#define VBATR_CLOCK_ENABLE_OFS          (8)
#define VBATR_ATE_TEST_OFS				(0x10)
#define VBATR_OSC_32K_TRIM_OFS			(0x14)
#define VBATR_VTR_ALT_CTRL_OFS			(0x18)
#define VBATR_OSC_TRIM_CTRL_OFS			(0x1C)


//
// Power Fail Reset Status Reg
//
#define VBATR_PFR_MASK                      (0xA1)
#define VBATR_PFR_RESERVED_MASK             ~(VBATR_PFR_MASK)
#define VBATR_PFR_DET32K_BITPOS             (0)
#define VBATR_PFR_DET32K                    (1U << (VBATR_PFR_DET32K_BITPOS))
#define VBATR_PFR_WDT_STS_BITPOS            (5)
#define VBATR_PFR_WDT_STS                   (1U << (VBATR_PFR_WDT_STS_BITPOS))
#define VBATR_PFR_VBAT_RST_STS_BITPOS       (7)
#define VBATR_PFR_VBAT_RST_STS              (1U << (VBATR_PFR_VBAT_RST_STS_BITPOS))

//
// ATE Regulator Control, offset 0x04

//
// Clock Enable Reg, offset 0x08
//
#define PCRVB_CLKEN_XOSEL_BITPOS            (0)
#define PCRVB_CLKEN_XOSEL                   (1U<<0)
#define PCRVB_CLKEN_EN_32K_BITPOS           (1)
#define PCRVB_CLKEN_EN_32K                  (1U<<1)

//
// 32KHz Oscillator Trim, offset 0x14
//
#define PCRVB_OSC_32K_TRIM_MASK				(0x1Ful)



#ifdef __cplusplus
}
#endif

#endif // #ifndef _MEC14XX_PCR_H
/* end mec14xx_pcr.h */
/**   @}
 */

