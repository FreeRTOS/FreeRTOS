/**************************************************************************//**
 * @file     scu_reg.h
 * @version  V1.00
 * @brief    SCU register definition header file
 *
 * @copyright (C) 2017 Nuvoton Technology Corp. All rights reserved.
 *****************************************************************************/
#ifndef __SCU_REG_H__
#define __SCU_REG_H__

/** @addtogroup REGISTER Control Register

  @{

*/


/*---------------------- Secure configuration Unit -------------------------*/
/**
    @addtogroup SCU Secure configuration Unit(SCU)
    Memory Mapped Structure for SCU Controller
@{ */

typedef struct
{


    /**
     * @var SCU_T::PNSSET[0]
     * Offset: 0x00  Peripheral Non-secure Attribution Set Register0 (0x4000_0000~0x4001_FFFF)
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[9]     |USBH      |Set USBH to Non-secure State
     * |        |          |Write 1 to set USBH to non-secure state. Write 0 has no effect.
     * |        |          |0 = USBH is a secure module (default).
     * |        |          |1 = USBH is a non-secure module.
     * |[13]    |SDH0      |Set SDH0 to Non-secure State
     * |        |          |Write 1 to set SDH0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = SDH0 is a secure module (default).
     * |        |          |1 = SDH0 is a non-secure module.
     * |[16]    |EBI       |Set EBI to Non-secure State
     * |        |          |Write 1 to set EBI to non-secure state. Write 0 has no effect.
     * |        |          |0 = EBI is a secure module (default).
     * |        |          |1 = EBI is a non-secure module.
     * |[24]    |PDMA1     |Set PDMA1 to Non-secure State
     * |        |          |Write 1 to set PDMA1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = PDMA1 is a secure module (default).
     * |        |          |1 = PDMA1 is a non-secure module.
     * @var SCU_T::PNSSET[1]
     * Offset: 0x04  Peripheral Non-secure Attribution Set Register1 (0x4002_0000~0x4003_FFFF)
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[17]    |CRC       |Set CRC to Non-secure State
     * |        |          |Write 1 to set CRC to non-secure state. Write 0 has no effect.
     * |        |          |0 = CRC is a secure module (default).
     * |        |          |1 = CRC is a non-secure module.
     * |[18]    |CRPT      |Set CRPT to Non-secure State
     * |        |          |Write 1 to set CRPT to non-secure state. Write 0 has no effect.
     * |        |          |0 = CRPT is a secure module (default).
     * |        |          |1 = CRPT is a non-secure module.
     * @var SCU_T::PNSSET[2]
     * Offset: 0x08  Peripheral Non-secure Attribution Set Register2 (0x4004_0000~0x4005_FFFF)
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[1]     |RTC       |Set RTC to Non-secure State
     * |        |          |Write 1 to set RTC to non-secure state. Write 0 has no effect.
     * |        |          |0 = RTC is a secure module (default).
     * |        |          |1 = RTC is a non-secure module.
     * |[3]     |EADC      |Set EADC to Non-secure State
     * |        |          |Write 1 to set EADC to non-secure state. Write 0 has no effect.
     * |        |          |0 = EADC is a secure module (default).
     * |        |          |1 = EADC is a non-secure module.
     * |[5]     |ACMP01    |Set ACMP01 to Non-secure State
     * |        |          |Write 1 to set ACMP0, ACMP1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = ACMP0, ACMP1 are secure modules (default).
     * |        |          |1 = ACMP0, ACMP1 are non-secure modules.
     * |[7]     |DAC       |Set DAC to Non-secure State
     * |        |          |Write 1 to set DAC to non-secure state. Write 0 has no effect.
     * |        |          |0 = DAC is a secure module (default).
     * |        |          |1 = DAC is a non-secure module.
     * |[8]     |I2S0      |Set I2S0 to Non-secure State
     * |        |          |Write 1 to set I2S0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = I2S0 is a secure module (default).
     * |        |          |1 = I2S0 is a non-secure module.
     * |[13]    |OTG       |Set OTG to Non-secure State
     * |        |          |Write 1 to set OTG to non-secure state. Write 0 has no effect.
     * |        |          |0 = OTG is a secure module (default).
     * |        |          |1 = OTG is a non-secure module.
     * |[17]    |TMR23     |Set TMR23 to Non-secure State
     * |        |          |Write 1 to set TMR23 to non-secure state. Write 0 has no effect.
     * |        |          |0 = TMR23 is a secure module (default).
     * |        |          |1 = TMR23 is a non-secure module.
     * |[24]    |EPWM0     |Set EPWM0 to Non-secure State
     * |        |          |Write 1 to set EPWM0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = EPWM0 is a secure module (default).
     * |        |          |1 = EPWM0 is a non-secure module.
     * |[25]    |EPWM1     |Set EPWM1 to Non-secure State
     * |        |          |Write 1 to set EPWM1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = EPWM1 is a secure module (default).
     * |        |          |1 = EPWM1 is a non-secure module.
     * |[26]    |BPWM0     |Set BPWM0 to Non-secure State
     * |        |          |Write 1 to set BPWM0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = BPWM0 is a secure module (default).
     * |        |          |1 = BPWM0 is a non-secure module.
     * |[27]    |BPWM1     |Set BPWM1 to Non-secure State
     * |        |          |Write 1 to set BPWM1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = BPWM1 is a secure module (default).
     * |        |          |1 = BPWM1 is a non-secure module.
     * @var SCU_T::PNSSET[3]
     * Offset: 0x0C  Peripheral Non-secure Attribution Set Register3 (0x4006_0000~0x4007_FFFF)
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[0]     |QSPI0     |Set QSPI0 to Non-secure State
     * |        |          |Write 1 to set QSPI0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = QSPI0 is a secure module (default).
     * |        |          |1 = QSPI0 is a non-secure module.
     * |[1]     |SPI0      |Set SPI0 to Non-secure State
     * |        |          |Write 1 to set SPI0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = SPI0 is a secure module (default).
     * |        |          |1 = SPI0 is a non-secure module.
     * |[2]     |SPI1      |Set SPI1 to Non-secure State
     * |        |          |Write 1 to set SPI1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = SPI1 is a secure module (default).
     * |        |          |1 = SPI1 is a non-secure module.
     * |[3]     |SPI2      |Set SPI2 to Non-secure State
     * |        |          |Write 1 to set SPI2 to non-secure state. Write 0 has no effect.
     * |        |          |0 = SPI2 is a secure module (default).
     * |        |          |1 = SPI2 is a non-secure module.
     * |[4]     |SPI3      |Set SPI3 to Non-secure State
     * |        |          |Write 1 to set SPI3 to non-secure state. Write 0 has no effect.
     * |        |          |0 = SPI3 is a secure module (default).
     * |        |          |1 = SPI3 is a non-secure module.
     * |[16]    |UART0     |Set UART0 to Non-secure State
     * |        |          |Write 1 to set UART0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = UART0 is a secure module (default).
     * |        |          |1 = UART0 is a non-secure module.
     * |[17]    |UART1     |Set UART1 to Non-secure State
     * |        |          |Write 1 to set UART1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = UART1 is a secure module (default).
     * |        |          |1 = UART1 is a non-secure module.
     * |[18]    |UART2     |Set UART2 to Non-secure State
     * |        |          |Write 1 to set UART2 to non-secure state. Write 0 has no effect.
     * |        |          |0 = UART2 is a secure module (default).
     * |        |          |1 = UART2 is a non-secure module.
     * |[19]    |UART3     |Set UART3 to Non-secure State
     * |        |          |Write 1 to set UART3 to non-secure state. Write 0 has no effect.
     * |        |          |0 = UART3 is a secure module (default).
     * |        |          |1 = UART3 is a non-secure module.
     * |[20]    |UART4     |Set UART4 to Non-secure State
     * |        |          |Write 1 to set UART4 to non-secure state. Write 0 has no effect.
     * |        |          |0 = UART4 is a secure module (default).
     * |        |          |1 = UART4 is a non-secure module.
     * |[21]    |UART5     |Set UART5 to Non-secure State
     * |        |          |Write 1 to set UART5 to non-secure state. Write 0 has no effect.
     * |        |          |0 = UART5 is a secure module (default).
     * |        |          |1 = UART5 is a non-secure module.
     * @var SCU_T::PNSSET[4]
     * Offset: 0x10  Peripheral Non-secure Attribution Set Register4 (0x4008_0000~0x4009_FFFF)
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[0]     |I2C0      |Set I2C0 to Non-secure State
     * |        |          |Write 1 to set I2C0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = I2C0 is a secure module (default).
     * |        |          |1 = I2C0 is a non-secure module.
     * |[1]     |I2C1      |Set I2C1 to Non-secure State
     * |        |          |Write 1 to set I2C1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = I2C1 is a secure module (default).
     * |        |          |1 = I2C1 is a non-secure module.
     * |[2]     |I2C2      |Set I2C2 to Non-secure State
     * |        |          |Write 1 to set I2C2 to non-secure state. Write 0 has no effect.
     * |        |          |0 = I2C2 is a secure module (default).
     * |        |          |1 = I2C2 is a non-secure module.
     * |[16]    |SC0       |Set SC0 to Non-secure State
     * |        |          |Write 1 to set SC0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = SC0 is a secure module (default).
     * |        |          |1 = SC0 is a non-secure module.
     * |[17]    |SC1       |Set SC1 to Non-secure State
     * |        |          |Write 1 to set SC1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = SC1 is a secure module (default).
     * |        |          |1 = SC1 is a non-secure module.
     * |[18]    |SC2       |Set SC2 to Non-secure State
     * |        |          |Write 1 to set SC2 to non-secure state. Write 0 has no effect.
     * |        |          |0 = SC2 is a secure module (default).
     * |        |          |1 = SC2 is a non-secure module.
     * @var SCU_T::PNSSET[5]
     * Offset: 0x14  Peripheral Non-secure Attribution Set Register5 (0x400A_0000~0x400B_FFFF)
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[0]     |CAN0      |Set CAN0 to Non-secure State
     * |        |          |Write 1 to set CAN0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = CAN0 is a secure module (default).
     * |        |          |1 = CAN0 is a non-secure module.
     * |[16]    |QEI0      |Set QEI0 to Non-secure State
     * |        |          |Write 1 to set QEI0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = QEI0 is a secure module (default).
     * |        |          |1 = QEI0 is a non-secure module.
     * |[17]    |QEI1      |Set QEI1 to Non-secure State
     * |        |          |Write 1 to set QEI1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = QEI1 is a secure module (default).
     * |        |          |1 = QEI1 is a non-secure module.
     * |[20]    |ECAP0     |Set ECAP0 to Non-secure State
     * |        |          |Write 1 to set ECAP0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = ECAP0 is a secure module (default).
     * |        |          |1 = ECAP0 is a non-secure module.
     * |[21]    |ECAP1     |Set ECAP1 to Non-secure State
     * |        |          |Write 1 to set ECAP1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = ECAP1 is a secure module (default).
     * |        |          |1 = ECAP1 is a non-secure module.
     * |[25]    |TRNG      |Set TRNG to Non-secure State
     * |        |          |Write 1 to set TRNG to non-secure state. Write 0 has no effect.
     * |        |          |0 = TRNG is a secure module (default).
     * |        |          |1 = TRNG is a non-secure module.
     * @var SCU_T::PNSSET[6]
     * Offset: 0x18  Peripheral Non-secure Attribution Set Register6 (0x400C_0000~0x400D_FFFF)
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[0]     |USBD      |Set USBD to Non-secure State
     * |        |          |Write 1 to set USBD to non-secure state. Write 0 has no effect.
     * |        |          |0 = USBD is a secure module (default).
     * |        |          |1 = USBD is a non-secure module.
     * |[16]    |USCI0     |Set USCI0 to Non-secure State
     * |        |          |Write 1 to set USCI0 to non-secure state. Write 0 has no effect.
     * |        |          |0 = USCI0 is a secure module (default).
     * |        |          |1 = USCI0 is a non-secure module.
     * |[17]    |USCI1     |Set USCI1 to Non-secure State
     * |        |          |Write 1 to set USCI1 to non-secure state. Write 0 has no effect.
     * |        |          |0 = USCI1 is a secure module (default).
     * |        |          |1 = USCI1 is a non-secure module.
     * @var SCU_T::IONSSET
     * Offset: 0x20  IO Non-secure Attribution Set Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[0]     |PA        |Set GPIO Port a to Non-scecure State
     * |        |          |Write 1 to set PA to non-secure state. Write 0 has no effect.
     * |        |          |0 = GPIO port A is secure (default).
     * |        |          |1 = GPIO port A is non-secure.
     * |[1]     |PB        |Set GPIO Port B to Non-scecure State
     * |        |          |Write 1 to set PB to non-secure state. Write 0 has no effect.
     * |        |          |0 = GPIO port B is secure (default).
     * |        |          |1 = GPIO port B is non-secure.
     * |[2]     |PC        |Set GPIO Port C to Non-scecure State
     * |        |          |Write 1 to set PC to non-secure state. Write 0 has no effect.
     * |        |          |0 = GPIO port C is secure (default).
     * |        |          |1 = GPIO port C is non-secure.
     * |[3]     |PD        |Set GPIO Port D to Non-scecure State
     * |        |          |Write 1 to set PD to non-secure state. Write 0 has no effect.
     * |        |          |0 = GPIO port D is secure (default).
     * |        |          |1 = GPIO port D is non-secure.
     * |[4]     |PE        |Set GPIO Port E to Non-scecure State
     * |        |          |Write 1 to set PE to non-secure state. Write 0 has no effect.
     * |        |          |0 = GPIO port E is secure (default).
     * |        |          |1 = GPIO port E is non-secure.
     * |[5]     |PF        |Set GPIO Port F to Non-scecure State
     * |        |          |Write 1 to set PF to non-secure state. Write 0 has no effect.
     * |        |          |0 = GPIO port F is secure (default).
     * |        |          |1 = GPIO port F is non-secure.
     * |[6]     |PG        |Set GPIO Port G to Non-scecure State
     * |        |          |Write 1 to set PG to non-secure state. Write 0 has no effect.
     * |        |          |0 = GPIO port G is secure (default).
     * |        |          |1 = GPIO port G is non-secure.
     * |[7]     |PH        |Set GPIO Port H to Non-scecure State
     * |        |          |Write 1 to set PH to non-secure state. Write 0 has no effect.
     * |        |          |0 = GPIO port H is secure (default).
     * |        |          |1 = GPIO port H is non-secure.
     * @var SCU_T::SRAMNSSET
     * Offset: 0x24  SRAM Non-secure Attribution Set Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[11:0]  |SECn      |Set SRAM Section N to Non-scecure State
     * |        |          |Write 1 to set SRAM section n to non-secure state. Write 0 is ignored.
     * |        |          |0 = SRAM Section n is secure (default).
     * |        |          |1 = SRAM Section n is non-secure.
     * |        |          |Secure SRAM section n is 0x2000_0000+0x2000*n to 0x2000_0000+0x2000*(n+1)-0x1
     * |        |          |Non-secure SRAM section n is 0x3000_0000+0x2000*n to 0x3000_0000+0x2000*(n+1)-0x1
     * @var SCU_T::FNSADDR
     * Offset: 0x28  Flash Non-secure Boundary Address Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |FNSADDR   |Flash Non-secure Boundary Address
     * |        |          |Indicate the base address of Non-secure region set in user configuration
     * |        |          |Refer to FMC section for more details.
     * @var SCU_T::SVIOIEN
     * Offset: 0x2C  Security Violation Interrupt Enable Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[0]     |APB0IEN   |APB0 Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of APB0 Disabled.
     * |        |          |1 = Interrupt triggered from security violation of APB0 Enabled.
     * |[1]     |APB1IEN   |APB1 Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of APB1 Disabled.
     * |        |          |1 = Interrupt triggered from security violation of APB1 Enabled.
     * |[4]     |GPIOIEN   |GPIO Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of GPIO Disabled.
     * |        |          |1 = Interrupt triggered from security violation of GPIO Enabled.
     * |[5]     |EBIIEN    |EBI Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of EBI Disabled.
     * |        |          |1 = Interrupt triggered from security violation of EBI Enabled.
     * |[6]     |USBHIEN   |USBH Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of USB host Disabled.
     * |        |          |1 = Interrupt triggered from security violation of USB host Enabled.
     * |[7]     |CRCIEN    |CRC Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of CRC Disabled.
     * |        |          |1 = Interrupt triggered from security violation of CRC Enabled.
     * |[8]     |SDH0IEN   |SDH0 Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of SD host 0 Disabled.
     * |        |          |1 = Interrupt triggered from security violation of SD host 0 Enabled.
     * |[10]    |PDMA0IEN  |PDMA0 Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of PDMA0 Disabled.
     * |        |          |1 = Interrupt triggered from security violation of PDMA0 Enabled.
     * |[11]    |PDMA1IEN  |PDMA1 Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of PDMA1 Disabled.
     * |        |          |1 = Interrupt triggered from security violation of PDMA1 Enabled.
     * |[12]    |SRAM0IEN  |SRAM Bank 0 Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of SRAM bank0 Disabled.
     * |        |          |1 = Interrupt triggered from security violation of SRAM bank0 Enabled.
     * |[13]    |SRAM1IEN  |SRAM Bank 1 Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of SRAM bank1 Disabled.
     * |        |          |1 = Interrupt triggered from security violation of SRAM bank1 Enabled.
     * |[14]    |FMCIEN    |FMC Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of FMC Disabled.
     * |        |          |1 = Interrupt triggered from security violation of FMC Enabled.
     * |[15]    |FLASHIEN  |FLASH Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of Flash data Disabled.
     * |        |          |1 = Interrupt triggered from security violation of Flash data Enabled.
     * |[16]    |SCUIEN    |SCU Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of SCU Disabled.
     * |        |          |1 = Interrupt triggered from security violation of SCU Enabled.
     * |[17]    |SYSIEN    |SYS Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of system manager Disabled.
     * |        |          |1 = Interrupt triggered from security violation of system manager Enabled.
     * |[18]    |CRPTIEN   |CRPT Security Violation Interrupt Enable Bit
     * |        |          |0 = Interrupt triggered from security violation of crypto Disabled.
     * |        |          |1 = Interrupt triggered from security violation of crypto Enabled.
     * @var SCU_T::SVINTSTS
     * Offset: 0x30  Security Violation Interrupt Status Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[0]     |APB0IF    |APB0 Security Violation Interrupt Status
     * |        |          |0 = No APB0 violation interrupt event.
     * |        |          |1 = There is APB0 violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[1]     |APB1IF    |APB1 Security Violation Interrupt Status
     * |        |          |0 = No APB1 violation interrupt event.
     * |        |          |1 = There is APB1 violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[4]     |GPIOIF    |GPIO Security Violation Interrupt Status
     * |        |          |0 = No GPIO violation interrupt event.
     * |        |          |1 = There is GPIO violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[5]     |EBIIF     |EBI Security Violation Interrupt Status
     * |        |          |0 = No EBI violation interrupt event.
     * |        |          |1 = There is EBI violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[6]     |USBHIF    |USBH Security Violation Interrupt Status
     * |        |          |0 = No USBH violation interrupt event.
     * |        |          |1 = There is USBH violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[7]     |CRCIF     |CRC Security Violation Interrupt Status
     * |        |          |0 = No CRC violation interrupt event.
     * |        |          |1 = There is CRC violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[8]     |SDH0IF    |SDH0 Security Violation Interrupt Status
     * |        |          |0 = No SDH0 violation interrupt event.
     * |        |          |1 = There is SDH0 violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[10]    |PDMA0IF   |PDMA0 Security Violation Interrupt Status
     * |        |          |0 = No PDMA0 violation interrupt event.
     * |        |          |1 = There is PDMA0 violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[11]    |PDMA1IF   |PDMA1 Security Violation Interrupt Status
     * |        |          |0 = No PDMA1 violation interrupt event.
     * |        |          |1 = There is PDMA1 violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[12]    |SRAM0IF   |SRAM0 Security Violation Interrupt Status
     * |        |          |0 = No SRAM0 violation interrupt event.
     * |        |          |1 = There is SRAM0 violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[13]    |SRAM1IF   |SRAM Bank 1 Security Violation Interrupt Status
     * |        |          |0 = No SRAM1 violation interrupt event.
     * |        |          |1 = There is SRAM1 violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[14]    |FMCIF     |FMC Security Violation Interrupt Status
     * |        |          |0 = No FMC violation interrupt event.
     * |        |          |1 = There is FMC violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[15]    |FLASHIF   |FLASH Security Violation Interrupt Status
     * |        |          |0 = No FLASH violation interrupt event.
     * |        |          |1 = There is FLASH violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[16]    |SCUIF     |SCU Security Violation Interrupt Status
     * |        |          |0 = No SCU violation interrupt event.
     * |        |          |1 = There is SCU violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[17]    |SYSIF     |SYS Security Violation Interrupt Status
     * |        |          |0 = No SYS violation interrupt event.
     * |        |          |1 = There is SYS violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * |[18]    |CRPTIF    |CRPT Security Violation Interrupt Status
     * |        |          |0 = No CRPT violation interrupt event.
     * |        |          |1 = There is CRPT violation interrupt event.
     * |        |          |Note: Write 1 to clear the interrupt flag.
     * @var SCU_T::APB0VSRC
     * Offset: 0x34  APB0 Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::APB0VA
     * Offset: 0x38  APB0 Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::APB1VSRC
     * Offset: 0x3C  APB1 Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::APB1VA
     * Offset: 0x40  APB1 Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::GPIOVSRC
     * Offset: 0x44  GPIO Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::GPIOVA
     * Offset: 0x48  GPIO Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::EBIVSRC
     * Offset: 0x4C  EBI Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::EBIVA
     * Offset: 0x50  EBI Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::USBHVSRC
     * Offset: 0x54  USBH Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::USBHVA
     * Offset: 0x58  USBH Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::CRCVSRC
     * Offset: 0x5C  CRC Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::CRCVA
     * Offset: 0x60  CRC Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::SD0VSRC
     * Offset: 0x64  SDH0 Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::SD0VA
     * Offset: 0x68  SDH0 Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::PDMA0VSRC
     * Offset: 0x74  PDMA0 Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::PDMA0VA
     * Offset: 0x78  PDMA0 Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::PDMA1VSRC
     * Offset: 0x7C  PDMA1 Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::PDMA1VA
     * Offset: 0x80  PDMA1 Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::SRAM0VSRC
     * Offset: 0x84  SRAM0 Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::SRAM0VA
     * Offset: 0x88  SRAM0 Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::SRAM1VSRC
     * Offset: 0x8C  SRAM1 Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::SRAM1VA
     * Offset: 0x90  SRAM1 Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::FMCVSRC
     * Offset: 0x94  FMC Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::FMCVA
     * Offset: 0x98  FMC Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::FLASHVSRC
     * Offset: 0x9C  Flash Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::FLASHVA
     * Offset: 0xA0  Flash Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::SCUVSRC
     * Offset: 0xA4  SCU Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::SCUVA
     * Offset: 0xA8  SCU Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::SYSVSRC
     * Offset: 0xAC  System Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::SYSVA
     * Offset: 0xB0  System Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::CRPTVSRC
     * Offset: 0xB4  Crypto Security Policy Violation Source
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[3:0]   |MASTER    |Master Violating Security Policy
     * |        |          |Indicate which master invokes the security violation.
     * |        |          |0x0 = core processor.
     * |        |          |0x3 = PDMA0.
     * |        |          |0x4 = SDH0.
     * |        |          |0x5 = CRYPTO.
     * |        |          |0x6 = USH.
     * |        |          |0xB = PDMA1.
     * |        |          |Others is undefined.
     * @var SCU_T::CRPTVA
     * Offset: 0xB8  Crypto Violation Address
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |VIOADDR   |Violation Address
     * |        |          |Indicate the target address of the access, which invokes the security violation.
     * @var SCU_T::NSMCTL
     * Offset: 0x200  Non-secure State Monitor Control Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[7:0]   |PRESCALE  |Pre-scale Value of Non-secure State Monitor Counter
     * |        |          |0 = Counter Disabled.
     * |        |          |Others = Counter Enabled and the counter clock source = HCLK/PRESCALE.
     * |[8]     |NSMIEN    |Non-secure State Monitor Interrupt Enable Bit
     * |        |          |0 = Non-secure state monitor interrupt Disabled.
     * |        |          |1 = Non-secure state monitor interrupt Enabled.
     * |[9]     |AUTORLD   |Auto Reload Non-secure State Monitor Counter When CURRNS Changing to 1
     * |        |          |0 = Disable clearing non-secure state monitor counter automtically. (default)
     * |        |          |1 = Enable clearing non-secure state monitor counter automatically when the core processor changes from secure state to non-secure state
     * |[10]    |TMRMOD    |Non-secure Monitor Mode Enable Bit
     * |        |          |0 = Monitor mode. The counter will count down when the core processor is in non-secure state. (default)
     * |        |          |1 = Free-counting mode
     * |        |          |The counter will keep counting no mater the core processor is in secure or non-secure state.
     * |[12]    |IDLEON    |Monitor Counter Keep Counting When the Chip is in Idle Mode Enable Bit
     * |        |          |0 = The counter will be halted when the chip is in idle mode.
     * |        |          |1 = The counter will keep counting when the chip is in idle mode. (default)
     * |        |          |Note: In monitor mode, the counter is always halted when the core processor is in secure state.
     * |[13]    |DBGON     |Monitor Counter Keep Counting When the Chip is in Debug Mode Enable Bit
     * |        |          |0 = The counter will be halted when the core processor is halted by ICE. (default)
     * |        |          |1 = The counter will keep counting when the core processor is halted by ICE.
     * @var SCU_T::NSMLOAD
     * Offset: 0x204  Non-secure State Monitor Reload Value Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[23:0]  |RELOAD    |Reload Value for Non-secure State Monitor Counter
     * |        |          |The RELOAD value will be reloaded to the counter whenever the counter counts down to 0.
     * @var SCU_T::NSMVAL
     * Offset: 0x208  Non-secure State Monitor Counter Value Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[23:0]  |VALUE     |Counter Value of Non-secure State Monitor Counter
     * |        |          |Current value of non-secure state monitor counter
     * |        |          |This is down counter and counts down only when CURRNS = 1
     * |        |          |When counting down to 0, VALUE will automatically be reloaded from NSMLOAD register.
     * |        |          |A write of any value clears the VALUE to 0 and also clears NSMIF.
     * @var SCU_T::NSMSTS
     * Offset: 0x20C  Non-secure State Monitor Status Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[0]     |CURRNS    |Current Core Processor Secure/Non-secure State
     * |        |          |0 = Core processor is in secure state.
     * |        |          |1 = Core processor is in non-secure state.
     * |        |          |Note: This bit can be used to monitor the current secure/non-secure state of the core processor, even if the non-secure state monitor counter is disabled.
     * |[1]     |NSMIF     |Non-secure State Monitor Interrupt Flag
     * |        |          |0 = Counter doesnu2019t count down to 0 since the last NSMIF has been cleared.
     * |        |          |1 = Counter counts down to 0.
     * |        |          |Note: This bit is cleared by writing 1.
     */
    __IO uint32_t PNSSET[7];             /*!< [0x0000~0X0018] Peripheral Non-secure Attribution Set Register0 (0x4000_0000~0x4001_FFFF) */
    __I  uint32_t RESERVE0[1];
    __IO uint32_t IONSSET;               /*!< [0x0020] IO Non-secure Attribution Set Register                           */
    __IO uint32_t SRAMNSSET;             /*!< [0x0024] SRAM Non-secure Attribution Set Register                         */
    __I  uint32_t FNSADDR;               /*!< [0x0028] Flash Non-secure Boundary Address Register                       */
    __IO uint32_t SVIOIEN;               /*!< [0x002c] Security Violation Interrupt Enable Register                     */
    __IO uint32_t SVINTSTS;              /*!< [0x0030] Security Violation Interrupt Status Register                     */
    __I  uint32_t APB0VSRC;              /*!< [0x0034] APB0 Security Policy Violation Source                            */
    __I  uint32_t APB0VA;                /*!< [0x0038] APB0 Violation Address                                           */
    __I  uint32_t APB1VSRC;              /*!< [0x003c] APB1 Security Policy Violation Source                            */
    __I  uint32_t APB1VA;                /*!< [0x0040] APB1 Violation Address                                           */
    __I  uint32_t GPIOVSRC;              /*!< [0x0044] GPIO Security Policy Violation Source                            */
    __I  uint32_t GPIOVA;                /*!< [0x0048] GPIO Violation Address                                           */
    __I  uint32_t EBIVSRC;               /*!< [0x004c] EBI Security Policy Violation Source                             */
    __I  uint32_t EBIVA;                 /*!< [0x0050] EBI Violation Address                                            */
    __I  uint32_t USBHVSRC;              /*!< [0x0054] USBH Security Policy Violation Source                            */
    __I  uint32_t USBHVA;                /*!< [0x0058] USBH Violation Address                                           */
    __I  uint32_t CRCVSRC;               /*!< [0x005c] CRC Security Policy Violation Source                             */
    __I  uint32_t CRCVA;                 /*!< [0x0060] CRC Violation Address                                            */
    __I  uint32_t SD0VSRC;               /*!< [0x0064] SDH0 Security Policy Violation Source                            */
    __I  uint32_t SD0VA;                 /*!< [0x0068] SDH0 Violation Address                                           */
    __I  uint32_t RESERVE1[2];
    __I  uint32_t PDMA0VSRC;             /*!< [0x0074] PDMA0 Security Policy Violation Source                           */
    __I  uint32_t PDMA0VA;               /*!< [0x0078] PDMA0 Violation Address                                          */
    __I  uint32_t PDMA1VSRC;             /*!< [0x007c] PDMA1 Security Policy Violation Source                           */
    __I  uint32_t PDMA1VA;               /*!< [0x0080] PDMA1 Violation Address                                          */
    __I  uint32_t SRAM0VSRC;             /*!< [0x0084] SRAM0 Security Policy Violation Source                           */
    __I  uint32_t SRAM0VA;               /*!< [0x0088] SRAM0 Violation Address                                          */
    __I  uint32_t SRAM1VSRC;             /*!< [0x008c] SRAM1 Security Policy Violation Source                           */
    __I  uint32_t SRAM1VA;               /*!< [0x0090] SRAM1 Violation Address                                          */
    __I  uint32_t FMCVSRC;               /*!< [0x0094] FMC Security Policy Violation Source                             */
    __I  uint32_t FMCVA;                 /*!< [0x0098] FMC Violation Address                                            */
    __I  uint32_t FLASHVSRC;             /*!< [0x009c] Flash Security Policy Violation Source                           */
    __I  uint32_t FLASHVA;               /*!< [0x00a0] Flash Violation Address                                          */
    __I  uint32_t SCUVSRC;               /*!< [0x00a4] SCU Security Policy Violation Source                             */
    __I  uint32_t SCUVA;                 /*!< [0x00a8] SCU Violation Address                                            */
    __I  uint32_t SYSVSRC;               /*!< [0x00ac] System Security Policy Violation Source                          */
    __I  uint32_t SYSVA;                 /*!< [0x00b0] System Violation Address                                         */
    __I  uint32_t CRPTVSRC;              /*!< [0x00b4] Crypto Security Policy Violation Source                          */
    __I  uint32_t CRPTVA;                /*!< [0x00b8] Crypto Violation Address                                         */
    __I  uint32_t RESERVE2[81];
    __IO uint32_t NSMCTL;                /*!< [0x0200] Non-secure State Monitor Control Register                        */
    __IO uint32_t NSMLOAD;               /*!< [0x0204] Non-secure State Monitor Reload Value Register                   */
    __IO uint32_t NSMVAL;                /*!< [0x0208] Non-secure State Monitor Counter Value Register                  */
    __IO uint32_t NSMSTS;                /*!< [0x020c] Non-secure State Monitor Status Register                         */

} SCU_T;

/**
    @addtogroup SCU_CONST SCU Bit Field Definition
    Constant Definitions for SCU Controller
@{ */

#define SCU_PNSSET0_USBH_Pos             (9)                                               /*!< SCU_T::PNSSET0: USBH Position          */
#define SCU_PNSSET0_USBH_Msk             (0x1ul << SCU_PNSSET0_USBH_Pos)                   /*!< SCU_T::PNSSET0: USBH Mask              */

#define SCU_PNSSET0_SDH0_Pos             (13)                                              /*!< SCU_T::PNSSET0: SDH0 Position          */
#define SCU_PNSSET0_SDH0_Msk             (0x1ul << SCU_PNSSET0_SDH0_Pos)                   /*!< SCU_T::PNSSET0: SDH0 Mask              */

#define SCU_PNSSET0_EBI_Pos              (16)                                              /*!< SCU_T::PNSSET0: EBI Position           */
#define SCU_PNSSET0_EBI_Msk              (0x1ul << SCU_PNSSET0_EBI_Pos)                    /*!< SCU_T::PNSSET0: EBI Mask               */

#define SCU_PNSSET0_PDMA1_Pos            (24)                                              /*!< SCU_T::PNSSET0: PDMA1 Position         */
#define SCU_PNSSET0_PDMA1_Msk            (0x1ul << SCU_PNSSET0_PDMA1_Pos)                  /*!< SCU_T::PNSSET0: PDMA1 Mask             */

#define SCU_PNSSET1_CRC_Pos              (17)                                              /*!< SCU_T::PNSSET1: CRC Position           */
#define SCU_PNSSET1_CRC_Msk              (0x1ul << SCU_PNSSET1_CRC_Pos)                    /*!< SCU_T::PNSSET1: CRC Mask               */

#define SCU_PNSSET1_CRPT_Pos             (18)                                              /*!< SCU_T::PNSSET1: CRPT Position          */
#define SCU_PNSSET1_CRPT_Msk             (0x1ul << SCU_PNSSET1_CRPT_Pos)                   /*!< SCU_T::PNSSET1: CRPT Mask              */

#define SCU_PNSSET2_RTC_Pos              (1)                                               /*!< SCU_T::PNSSET2: RTC Position           */
#define SCU_PNSSET2_RTC_Msk              (0x1ul << SCU_PNSSET2_RTC_Pos)                    /*!< SCU_T::PNSSET2: RTC Mask               */

#define SCU_PNSSET2_EADC_Pos             (3)                                               /*!< SCU_T::PNSSET2: EADC Position          */
#define SCU_PNSSET2_EADC_Msk             (0x1ul << SCU_PNSSET2_EADC_Pos)                   /*!< SCU_T::PNSSET2: EADC Mask              */

#define SCU_PNSSET2_ACMP01_Pos           (5)                                               /*!< SCU_T::PNSSET2: ACMP01 Position        */
#define SCU_PNSSET2_ACMP01_Msk           (0x1ul << SCU_PNSSET2_ACMP01_Pos)                 /*!< SCU_T::PNSSET2: ACMP01 Mask            */

#define SCU_PNSSET2_DAC_Pos              (7)                                               /*!< SCU_T::PNSSET2: DAC Position           */
#define SCU_PNSSET2_DAC_Msk              (0x1ul << SCU_PNSSET2_DAC_Pos)                    /*!< SCU_T::PNSSET2: DAC Mask               */

#define SCU_PNSSET2_I2S0_Pos             (8)                                               /*!< SCU_T::PNSSET2: I2S0 Position          */
#define SCU_PNSSET2_I2S0_Msk             (0x1ul << SCU_PNSSET2_I2S0_Pos)                   /*!< SCU_T::PNSSET2: I2S0 Mask              */

#define SCU_PNSSET2_OTG_Pos              (13)                                              /*!< SCU_T::PNSSET2: OTG Position           */
#define SCU_PNSSET2_OTG_Msk              (0x1ul << SCU_PNSSET2_OTG_Pos)                    /*!< SCU_T::PNSSET2: OTG Mask               */

#define SCU_PNSSET2_TMR23_Pos            (17)                                              /*!< SCU_T::PNSSET2: TMR23 Position         */
#define SCU_PNSSET2_TMR23_Msk            (0x1ul << SCU_PNSSET2_TMR23_Pos)                  /*!< SCU_T::PNSSET2: TMR23 Mask             */

#define SCU_PNSSET2_EPWM0_Pos            (24)                                              /*!< SCU_T::PNSSET2: EPWM0 Position         */
#define SCU_PNSSET2_EPWM0_Msk            (0x1ul << SCU_PNSSET2_EPWM0_Pos)                  /*!< SCU_T::PNSSET2: EPWM0 Mask             */

#define SCU_PNSSET2_EPWM1_Pos            (25)                                              /*!< SCU_T::PNSSET2: EPWM1 Position         */
#define SCU_PNSSET2_EPWM1_Msk            (0x1ul << SCU_PNSSET2_EPWM1_Pos)                  /*!< SCU_T::PNSSET2: EPWM1 Mask             */

#define SCU_PNSSET2_BPWM0_Pos            (26)                                              /*!< SCU_T::PNSSET2: BPWM0 Position         */
#define SCU_PNSSET2_BPWM0_Msk            (0x1ul << SCU_PNSSET2_BPWM0_Pos)                  /*!< SCU_T::PNSSET2: BPWM0 Mask             */

#define SCU_PNSSET2_BPWM1_Pos            (27)                                              /*!< SCU_T::PNSSET2: BPWM1 Position         */
#define SCU_PNSSET2_BPWM1_Msk            (0x1ul << SCU_PNSSET2_BPWM1_Pos)                  /*!< SCU_T::PNSSET2: BPWM1 Mask             */

#define SCU_PNSSET3_QSPI0_Pos            (0)                                               /*!< SCU_T::PNSSET3: QSPI0 Position         */
#define SCU_PNSSET3_QSPI0_Msk            (0x1ul << SCU_PNSSET3_QSPI0_Pos)                  /*!< SCU_T::PNSSET3: QSPI0 Mask             */

#define SCU_PNSSET3_SPI0_Pos             (1)                                               /*!< SCU_T::PNSSET3: SPI0 Position          */
#define SCU_PNSSET3_SPI0_Msk             (0x1ul << SCU_PNSSET3_SPI0_Pos)                   /*!< SCU_T::PNSSET3: SPI0 Mask              */

#define SCU_PNSSET3_SPI1_Pos             (2)                                               /*!< SCU_T::PNSSET3: SPI1 Position          */
#define SCU_PNSSET3_SPI1_Msk             (0x1ul << SCU_PNSSET3_SPI1_Pos)                   /*!< SCU_T::PNSSET3: SPI1 Mask              */

#define SCU_PNSSET3_SPI2_Pos             (3)                                               /*!< SCU_T::PNSSET3: SPI2 Position          */
#define SCU_PNSSET3_SPI2_Msk             (0x1ul << SCU_PNSSET3_SPI2_Pos)                   /*!< SCU_T::PNSSET3: SPI2 Mask              */

#define SCU_PNSSET3_SPI3_Pos             (4)                                               /*!< SCU_T::PNSSET3: SPI3 Position          */
#define SCU_PNSSET3_SPI3_Msk             (0x1ul << SCU_PNSSET3_SPI3_Pos)                   /*!< SCU_T::PNSSET3: SPI3 Mask              */

#define SCU_PNSSET3_UART0_Pos            (16)                                              /*!< SCU_T::PNSSET3: UART0 Position         */
#define SCU_PNSSET3_UART0_Msk            (0x1ul << SCU_PNSSET3_UART0_Pos)                  /*!< SCU_T::PNSSET3: UART0 Mask             */

#define SCU_PNSSET3_UART1_Pos            (17)                                              /*!< SCU_T::PNSSET3: UART1 Position         */
#define SCU_PNSSET3_UART1_Msk            (0x1ul << SCU_PNSSET3_UART1_Pos)                  /*!< SCU_T::PNSSET3: UART1 Mask             */

#define SCU_PNSSET3_UART2_Pos            (18)                                              /*!< SCU_T::PNSSET3: UART2 Position         */
#define SCU_PNSSET3_UART2_Msk            (0x1ul << SCU_PNSSET3_UART2_Pos)                  /*!< SCU_T::PNSSET3: UART2 Mask             */

#define SCU_PNSSET3_UART3_Pos            (19)                                              /*!< SCU_T::PNSSET3: UART3 Position         */
#define SCU_PNSSET3_UART3_Msk            (0x1ul << SCU_PNSSET3_UART3_Pos)                  /*!< SCU_T::PNSSET3: UART3 Mask             */

#define SCU_PNSSET3_UART4_Pos            (20)                                              /*!< SCU_T::PNSSET3: UART4 Position         */
#define SCU_PNSSET3_UART4_Msk            (0x1ul << SCU_PNSSET3_UART4_Pos)                  /*!< SCU_T::PNSSET3: UART4 Mask             */

#define SCU_PNSSET3_UART5_Pos            (21)                                              /*!< SCU_T::PNSSET3: UART5 Position         */
#define SCU_PNSSET3_UART5_Msk            (0x1ul << SCU_PNSSET3_UART5_Pos)                  /*!< SCU_T::PNSSET3: UART5 Mask             */

#define SCU_PNSSET4_I2C0_Pos             (0)                                               /*!< SCU_T::PNSSET4: I2C0 Position          */
#define SCU_PNSSET4_I2C0_Msk             (0x1ul << SCU_PNSSET4_I2C0_Pos)                   /*!< SCU_T::PNSSET4: I2C0 Mask              */

#define SCU_PNSSET4_I2C1_Pos             (1)                                               /*!< SCU_T::PNSSET4: I2C1 Position          */
#define SCU_PNSSET4_I2C1_Msk             (0x1ul << SCU_PNSSET4_I2C1_Pos)                   /*!< SCU_T::PNSSET4: I2C1 Mask              */

#define SCU_PNSSET4_I2C2_Pos             (2)                                               /*!< SCU_T::PNSSET4: I2C2 Position          */
#define SCU_PNSSET4_I2C2_Msk             (0x1ul << SCU_PNSSET4_I2C2_Pos)                   /*!< SCU_T::PNSSET4: I2C2 Mask              */

#define SCU_PNSSET4_SC0_Pos              (16)                                              /*!< SCU_T::PNSSET4: SC0 Position           */
#define SCU_PNSSET4_SC0_Msk              (0x1ul << SCU_PNSSET4_SC0_Pos)                    /*!< SCU_T::PNSSET4: SC0 Mask               */

#define SCU_PNSSET4_SC1_Pos              (17)                                              /*!< SCU_T::PNSSET4: SC1 Position           */
#define SCU_PNSSET4_SC1_Msk              (0x1ul << SCU_PNSSET4_SC1_Pos)                    /*!< SCU_T::PNSSET4: SC1 Mask               */

#define SCU_PNSSET4_SC2_Pos              (18)                                              /*!< SCU_T::PNSSET4: SC2 Position           */
#define SCU_PNSSET4_SC2_Msk              (0x1ul << SCU_PNSSET4_SC2_Pos)                    /*!< SCU_T::PNSSET4: SC2 Mask               */

#define SCU_PNSSET5_CAN0_Pos             (0)                                               /*!< SCU_T::PNSSET5: CAN0 Position          */
#define SCU_PNSSET5_CAN0_Msk             (0x1ul << SCU_PNSSET5_CAN0_Pos)                   /*!< SCU_T::PNSSET5: CAN0 Mask              */

#define SCU_PNSSET5_QEI0_Pos             (16)                                              /*!< SCU_T::PNSSET5: QEI0 Position          */
#define SCU_PNSSET5_QEI0_Msk             (0x1ul << SCU_PNSSET5_QEI0_Pos)                   /*!< SCU_T::PNSSET5: QEI0 Mask              */

#define SCU_PNSSET5_QEI1_Pos             (17)                                              /*!< SCU_T::PNSSET5: QEI1 Position          */
#define SCU_PNSSET5_QEI1_Msk             (0x1ul << SCU_PNSSET5_QEI1_Pos)                   /*!< SCU_T::PNSSET5: QEI1 Mask              */

#define SCU_PNSSET5_ECAP0_Pos            (20)                                              /*!< SCU_T::PNSSET5: ECAP0 Position         */
#define SCU_PNSSET5_ECAP0_Msk            (0x1ul << SCU_PNSSET5_ECAP0_Pos)                  /*!< SCU_T::PNSSET5: ECAP0 Mask             */

#define SCU_PNSSET5_ECAP1_Pos            (21)                                              /*!< SCU_T::PNSSET5: ECAP1 Position         */
#define SCU_PNSSET5_ECAP1_Msk            (0x1ul << SCU_PNSSET5_ECAP1_Pos)                  /*!< SCU_T::PNSSET5: ECAP1 Mask             */

#define SCU_PNSSET5_TRNG_Pos             (25)                                              /*!< SCU_T::PNSSET5: TRNG Position          */
#define SCU_PNSSET5_TRNG_Msk             (0x1ul << SCU_PNSSET5_TRNG_Pos)                   /*!< SCU_T::PNSSET5: TRNG Mask              */

#define SCU_PNSSET6_USBD_Pos             (0)                                               /*!< SCU_T::PNSSET6: USBD Position          */
#define SCU_PNSSET6_USBD_Msk             (0x1ul << SCU_PNSSET6_USBD_Pos)                   /*!< SCU_T::PNSSET6: USBD Mask              */

#define SCU_PNSSET6_USCI0_Pos            (16)                                              /*!< SCU_T::PNSSET6: USCI0 Position         */
#define SCU_PNSSET6_USCI0_Msk            (0x1ul << SCU_PNSSET6_USCI0_Pos)                  /*!< SCU_T::PNSSET6: USCI0 Mask             */

#define SCU_PNSSET6_USCI1_Pos            (17)                                              /*!< SCU_T::PNSSET6: USCI1 Position         */
#define SCU_PNSSET6_USCI1_Msk            (0x1ul << SCU_PNSSET6_USCI1_Pos)                  /*!< SCU_T::PNSSET6: USCI1 Mask             */

#define SCU_IONSSET_PA_Pos               (0)                                               /*!< SCU_T::IONSSET: PA Position            */
#define SCU_IONSSET_PA_Msk               (0x1ul << SCU_IONSSET_PA_Pos)                     /*!< SCU_T::IONSSET: PA Mask                */

#define SCU_IONSSET_PB_Pos               (1)                                               /*!< SCU_T::IONSSET: PB Position            */
#define SCU_IONSSET_PB_Msk               (0x1ul << SCU_IONSSET_PB_Pos)                     /*!< SCU_T::IONSSET: PB Mask                */

#define SCU_IONSSET_PC_Pos               (2)                                               /*!< SCU_T::IONSSET: PC Position            */
#define SCU_IONSSET_PC_Msk               (0x1ul << SCU_IONSSET_PC_Pos)                     /*!< SCU_T::IONSSET: PC Mask                */

#define SCU_IONSSET_PD_Pos               (3)                                               /*!< SCU_T::IONSSET: PD Position            */
#define SCU_IONSSET_PD_Msk               (0x1ul << SCU_IONSSET_PD_Pos)                     /*!< SCU_T::IONSSET: PD Mask                */

#define SCU_IONSSET_PE_Pos               (4)                                               /*!< SCU_T::IONSSET: PE Position            */
#define SCU_IONSSET_PE_Msk               (0x1ul << SCU_IONSSET_PE_Pos)                     /*!< SCU_T::IONSSET: PE Mask                */

#define SCU_IONSSET_PF_Pos               (5)                                               /*!< SCU_T::IONSSET: PF Position            */
#define SCU_IONSSET_PF_Msk               (0x1ul << SCU_IONSSET_PF_Pos)                     /*!< SCU_T::IONSSET: PF Mask                */

#define SCU_IONSSET_PG_Pos               (6)                                               /*!< SCU_T::IONSSET: PG Position            */
#define SCU_IONSSET_PG_Msk               (0x1ul << SCU_IONSSET_PG_Pos)                     /*!< SCU_T::IONSSET: PG Mask                */

#define SCU_IONSSET_PH_Pos               (7)                                               /*!< SCU_T::IONSSET: PH Position            */
#define SCU_IONSSET_PH_Msk               (0x1ul << SCU_IONSSET_PH_Pos)                     /*!< SCU_T::IONSSET: PH Mask                */

#define SCU_SRAMNSSET_SECn_Pos           (0)                                               /*!< SCU_T::SRAMNSSET: SECn Position        */
#define SCU_SRAMNSSET_SECn_Msk           (0xffful << SCU_SRAMNSSET_SECn_Pos)               /*!< SCU_T::SRAMNSSET: SECn Mask            */

#define SCU_FNSADDR_FNSADDR_Pos          (0)                                               /*!< SCU_T::FNSADDR: FNSADDR Position       */
#define SCU_FNSADDR_FNSADDR_Msk          (0xfffffffful << SCU_FNSADDR_FNSADDR_Pos)         /*!< SCU_T::FNSADDR: FNSADDR Mask           */

#define SCU_SVIOIEN_APB0IEN_Pos          (0)                                               /*!< SCU_T::SVIOIEN: APB0IEN Position       */
#define SCU_SVIOIEN_APB0IEN_Msk          (0x1ul << SCU_SVIOIEN_APB0IEN_Pos)                /*!< SCU_T::SVIOIEN: APB0IEN Mask           */

#define SCU_SVIOIEN_APB1IEN_Pos          (1)                                               /*!< SCU_T::SVIOIEN: APB1IEN Position       */
#define SCU_SVIOIEN_APB1IEN_Msk          (0x1ul << SCU_SVIOIEN_APB1IEN_Pos)                /*!< SCU_T::SVIOIEN: APB1IEN Mask           */

#define SCU_SVIOIEN_GPIOIEN_Pos          (4)                                               /*!< SCU_T::SVIOIEN: GPIOIEN Position       */
#define SCU_SVIOIEN_GPIOIEN_Msk          (0x1ul << SCU_SVIOIEN_GPIOIEN_Pos)                /*!< SCU_T::SVIOIEN: GPIOIEN Mask           */

#define SCU_SVIOIEN_EBIIEN_Pos           (5)                                               /*!< SCU_T::SVIOIEN: EBIIEN Position        */
#define SCU_SVIOIEN_EBIIEN_Msk           (0x1ul << SCU_SVIOIEN_EBIIEN_Pos)                 /*!< SCU_T::SVIOIEN: EBIIEN Mask            */

#define SCU_SVIOIEN_USBHIEN_Pos          (6)                                               /*!< SCU_T::SVIOIEN: USBHIEN Position       */
#define SCU_SVIOIEN_USBHIEN_Msk          (0x1ul << SCU_SVIOIEN_USBHIEN_Pos)                /*!< SCU_T::SVIOIEN: USBHIEN Mask           */

#define SCU_SVIOIEN_CRCIEN_Pos           (7)                                               /*!< SCU_T::SVIOIEN: CRCIEN Position        */
#define SCU_SVIOIEN_CRCIEN_Msk           (0x1ul << SCU_SVIOIEN_CRCIEN_Pos)                 /*!< SCU_T::SVIOIEN: CRCIEN Mask            */

#define SCU_SVIOIEN_SDH0IEN_Pos          (8)                                               /*!< SCU_T::SVIOIEN: SDH0IEN Position       */
#define SCU_SVIOIEN_SDH0IEN_Msk          (0x1ul << SCU_SVIOIEN_SDH0IEN_Pos)                /*!< SCU_T::SVIOIEN: SDH0IEN Mask           */

#define SCU_SVIOIEN_PDMA0IEN_Pos         (10)                                              /*!< SCU_T::SVIOIEN: PDMA0IEN Position      */
#define SCU_SVIOIEN_PDMA0IEN_Msk         (0x1ul << SCU_SVIOIEN_PDMA0IEN_Pos)               /*!< SCU_T::SVIOIEN: PDMA0IEN Mask          */

#define SCU_SVIOIEN_PDMA1IEN_Pos         (11)                                              /*!< SCU_T::SVIOIEN: PDMA1IEN Position      */
#define SCU_SVIOIEN_PDMA1IEN_Msk         (0x1ul << SCU_SVIOIEN_PDMA1IEN_Pos)               /*!< SCU_T::SVIOIEN: PDMA1IEN Mask          */

#define SCU_SVIOIEN_SRAM0IEN_Pos         (12)                                              /*!< SCU_T::SVIOIEN: SRAM0IEN Position      */
#define SCU_SVIOIEN_SRAM0IEN_Msk         (0x1ul << SCU_SVIOIEN_SRAM0IEN_Pos)               /*!< SCU_T::SVIOIEN: SRAM0IEN Mask          */

#define SCU_SVIOIEN_SRAM1IEN_Pos         (13)                                              /*!< SCU_T::SVIOIEN: SRAM1IEN Position      */
#define SCU_SVIOIEN_SRAM1IEN_Msk         (0x1ul << SCU_SVIOIEN_SRAM1IEN_Pos)               /*!< SCU_T::SVIOIEN: SRAM1IEN Mask          */

#define SCU_SVIOIEN_FMCIEN_Pos           (14)                                              /*!< SCU_T::SVIOIEN: FMCIEN Position        */
#define SCU_SVIOIEN_FMCIEN_Msk           (0x1ul << SCU_SVIOIEN_FMCIEN_Pos)                 /*!< SCU_T::SVIOIEN: FMCIEN Mask            */

#define SCU_SVIOIEN_FLASHIEN_Pos         (15)                                              /*!< SCU_T::SVIOIEN: FLASHIEN Position      */
#define SCU_SVIOIEN_FLASHIEN_Msk         (0x1ul << SCU_SVIOIEN_FLASHIEN_Pos)               /*!< SCU_T::SVIOIEN: FLASHIEN Mask          */

#define SCU_SVIOIEN_SCUIEN_Pos           (16)                                              /*!< SCU_T::SVIOIEN: SCUIEN Position        */
#define SCU_SVIOIEN_SCUIEN_Msk           (0x1ul << SCU_SVIOIEN_SCUIEN_Pos)                 /*!< SCU_T::SVIOIEN: SCUIEN Mask            */

#define SCU_SVIOIEN_SYSIEN_Pos           (17)                                              /*!< SCU_T::SVIOIEN: SYSIEN Position        */
#define SCU_SVIOIEN_SYSIEN_Msk           (0x1ul << SCU_SVIOIEN_SYSIEN_Pos)                 /*!< SCU_T::SVIOIEN: SYSIEN Mask            */

#define SCU_SVIOIEN_CRPTIEN_Pos          (18)                                              /*!< SCU_T::SVIOIEN: CRPTIEN Position       */
#define SCU_SVIOIEN_CRPTIEN_Msk          (0x1ul << SCU_SVIOIEN_CRPTIEN_Pos)                /*!< SCU_T::SVIOIEN: CRPTIEN Mask           */

#define SCU_SVINTSTS_APB0IF_Pos          (0)                                               /*!< SCU_T::SVINTSTS: APB0IF Position       */
#define SCU_SVINTSTS_APB0IF_Msk          (0x1ul << SCU_SVINTSTS_APB0IF_Pos)                /*!< SCU_T::SVINTSTS: APB0IF Mask           */

#define SCU_SVINTSTS_APB1IF_Pos          (1)                                               /*!< SCU_T::SVINTSTS: APB1IF Position       */
#define SCU_SVINTSTS_APB1IF_Msk          (0x1ul << SCU_SVINTSTS_APB1IF_Pos)                /*!< SCU_T::SVINTSTS: APB1IF Mask           */

#define SCU_SVINTSTS_GPIOIF_Pos          (4)                                               /*!< SCU_T::SVINTSTS: GPIOIF Position       */
#define SCU_SVINTSTS_GPIOIF_Msk          (0x1ul << SCU_SVINTSTS_GPIOIF_Pos)                /*!< SCU_T::SVINTSTS: GPIOIF Mask           */

#define SCU_SVINTSTS_EBIIF_Pos           (5)                                               /*!< SCU_T::SVINTSTS: EBIIF Position        */
#define SCU_SVINTSTS_EBIIF_Msk           (0x1ul << SCU_SVINTSTS_EBIIF_Pos)                 /*!< SCU_T::SVINTSTS: EBIIF Mask            */

#define SCU_SVINTSTS_USBHIF_Pos          (6)                                               /*!< SCU_T::SVINTSTS: USBHIF Position       */
#define SCU_SVINTSTS_USBHIF_Msk          (0x1ul << SCU_SVINTSTS_USBHIF_Pos)                /*!< SCU_T::SVINTSTS: USBHIF Mask           */

#define SCU_SVINTSTS_CRCIF_Pos           (7)                                               /*!< SCU_T::SVINTSTS: CRCIF Position        */
#define SCU_SVINTSTS_CRCIF_Msk           (0x1ul << SCU_SVINTSTS_CRCIF_Pos)                 /*!< SCU_T::SVINTSTS: CRCIF Mask            */

#define SCU_SVINTSTS_SDH0IF_Pos          (8)                                               /*!< SCU_T::SVINTSTS: SDH0IF Position       */
#define SCU_SVINTSTS_SDH0IF_Msk          (0x1ul << SCU_SVINTSTS_SDH0IF_Pos)                /*!< SCU_T::SVINTSTS: SDH0IF Mask           */

#define SCU_SVINTSTS_PDMA0IF_Pos         (10)                                              /*!< SCU_T::SVINTSTS: PDMA0IF Position      */
#define SCU_SVINTSTS_PDMA0IF_Msk         (0x1ul << SCU_SVINTSTS_PDMA0IF_Pos)               /*!< SCU_T::SVINTSTS: PDMA0IF Mask          */

#define SCU_SVINTSTS_PDMA1IF_Pos         (11)                                              /*!< SCU_T::SVINTSTS: PDMA1IF Position      */
#define SCU_SVINTSTS_PDMA1IF_Msk         (0x1ul << SCU_SVINTSTS_PDMA1IF_Pos)               /*!< SCU_T::SVINTSTS: PDMA1IF Mask          */

#define SCU_SVINTSTS_SRAM0IF_Pos         (12)                                              /*!< SCU_T::SVINTSTS: SRAM0IF Position      */
#define SCU_SVINTSTS_SRAM0IF_Msk         (0x1ul << SCU_SVINTSTS_SRAM0IF_Pos)               /*!< SCU_T::SVINTSTS: SRAM0IF Mask          */

#define SCU_SVINTSTS_SRAM1IF_Pos         (13)                                              /*!< SCU_T::SVINTSTS: SRAM1IF Position      */
#define SCU_SVINTSTS_SRAM1IF_Msk         (0x1ul << SCU_SVINTSTS_SRAM1IF_Pos)               /*!< SCU_T::SVINTSTS: SRAM1IF Mask          */

#define SCU_SVINTSTS_FMCIF_Pos           (14)                                              /*!< SCU_T::SVINTSTS: FMCIF Position        */
#define SCU_SVINTSTS_FMCIF_Msk           (0x1ul << SCU_SVINTSTS_FMCIF_Pos)                 /*!< SCU_T::SVINTSTS: FMCIF Mask            */

#define SCU_SVINTSTS_FLASHIF_Pos         (15)                                              /*!< SCU_T::SVINTSTS: FLASHIF Position      */
#define SCU_SVINTSTS_FLASHIF_Msk         (0x1ul << SCU_SVINTSTS_FLASHIF_Pos)               /*!< SCU_T::SVINTSTS: FLASHIF Mask          */

#define SCU_SVINTSTS_SCUIF_Pos           (16)                                              /*!< SCU_T::SVINTSTS: SCUIF Position        */
#define SCU_SVINTSTS_SCUIF_Msk           (0x1ul << SCU_SVINTSTS_SCUIF_Pos)                 /*!< SCU_T::SVINTSTS: SCUIF Mask            */

#define SCU_SVINTSTS_SYSIF_Pos           (17)                                              /*!< SCU_T::SVINTSTS: SYSIF Position        */
#define SCU_SVINTSTS_SYSIF_Msk           (0x1ul << SCU_SVINTSTS_SYSIF_Pos)                 /*!< SCU_T::SVINTSTS: SYSIF Mask            */

#define SCU_SVINTSTS_CRPTIF_Pos          (18)                                              /*!< SCU_T::SVINTSTS: CRPTIF Position       */
#define SCU_SVINTSTS_CRPTIF_Msk          (0x1ul << SCU_SVINTSTS_CRPTIF_Pos)                /*!< SCU_T::SVINTSTS: CRPTIF Mask           */

#define SCU_APB0VSRC_MASTER_Pos          (0)                                               /*!< SCU_T::APB0VSRC: MASTER Position       */
#define SCU_APB0VSRC_MASTER_Msk          (0xful << SCU_APB0VSRC_MASTER_Pos)                /*!< SCU_T::APB0VSRC: MASTER Mask           */

#define SCU_APB0VA_VIOADDR_Pos           (0)                                               /*!< SCU_T::APB0VA: VIOADDR Position        */
#define SCU_APB0VA_VIOADDR_Msk           (0xfffffffful << SCU_APB0VA_VIOADDR_Pos)          /*!< SCU_T::APB0VA: VIOADDR Mask            */

#define SCU_APB1VSRC_MASTER_Pos          (0)                                               /*!< SCU_T::APB1VSRC: MASTER Position       */
#define SCU_APB1VSRC_MASTER_Msk          (0xful << SCU_APB1VSRC_MASTER_Pos)                /*!< SCU_T::APB1VSRC: MASTER Mask           */

#define SCU_APB1VA_VIOADDR_Pos           (0)                                               /*!< SCU_T::APB1VA: VIOADDR Position        */
#define SCU_APB1VA_VIOADDR_Msk           (0xfffffffful << SCU_APB1VA_VIOADDR_Pos)          /*!< SCU_T::APB1VA: VIOADDR Mask            */

#define SCU_GPIOVSRC_MASTER_Pos          (0)                                               /*!< SCU_T::GPIOVSRC: MASTER Position       */
#define SCU_GPIOVSRC_MASTER_Msk          (0xful << SCU_GPIOVSRC_MASTER_Pos)                /*!< SCU_T::GPIOVSRC: MASTER Mask           */

#define SCU_GPIOVA_VIOADDR_Pos           (0)                                               /*!< SCU_T::GPIOVA: VIOADDR Position        */
#define SCU_GPIOVA_VIOADDR_Msk           (0xfffffffful << SCU_GPIOVA_VIOADDR_Pos)          /*!< SCU_T::GPIOVA: VIOADDR Mask            */

#define SCU_EBIVSRC_MASTER_Pos           (0)                                               /*!< SCU_T::EBIVSRC: MASTER Position        */
#define SCU_EBIVSRC_MASTER_Msk           (0xful << SCU_EBIVSRC_MASTER_Pos)                 /*!< SCU_T::EBIVSRC: MASTER Mask            */

#define SCU_EBIVA_VIOADDR_Pos            (0)                                               /*!< SCU_T::EBIVA: VIOADDR Position         */
#define SCU_EBIVA_VIOADDR_Msk            (0xfffffffful << SCU_EBIVA_VIOADDR_Pos)           /*!< SCU_T::EBIVA: VIOADDR Mask             */

#define SCU_USBHVSRC_MASTER_Pos          (0)                                               /*!< SCU_T::USBHVSRC: MASTER Position       */
#define SCU_USBHVSRC_MASTER_Msk          (0xful << SCU_USBHVSRC_MASTER_Pos)                /*!< SCU_T::USBHVSRC: MASTER Mask           */

#define SCU_USBHVA_VIOADDR_Pos           (0)                                               /*!< SCU_T::USBHVA: VIOADDR Position        */
#define SCU_USBHVA_VIOADDR_Msk           (0xfffffffful << SCU_USBHVA_VIOADDR_Pos)          /*!< SCU_T::USBHVA: VIOADDR Mask            */

#define SCU_CRCVSRC_MASTER_Pos           (0)                                               /*!< SCU_T::CRCVSRC: MASTER Position        */
#define SCU_CRCVSRC_MASTER_Msk           (0xful << SCU_CRCVSRC_MASTER_Pos)                 /*!< SCU_T::CRCVSRC: MASTER Mask            */

#define SCU_CRCVA_VIOADDR_Pos            (0)                                               /*!< SCU_T::CRCVA: VIOADDR Position         */
#define SCU_CRCVA_VIOADDR_Msk            (0xfffffffful << SCU_CRCVA_VIOADDR_Pos)           /*!< SCU_T::CRCVA: VIOADDR Mask             */

#define SCU_SD0VSRC_MASTER_Pos           (0)                                               /*!< SCU_T::SD0VSRC: MASTER Position        */
#define SCU_SD0VSRC_MASTER_Msk           (0xful << SCU_SD0VSRC_MASTER_Pos)                 /*!< SCU_T::SD0VSRC: MASTER Mask            */

#define SCU_SD0VA_VIOADDR_Pos            (0)                                               /*!< SCU_T::SD0VA: VIOADDR Position         */
#define SCU_SD0VA_VIOADDR_Msk            (0xfffffffful << SCU_SD0VA_VIOADDR_Pos)           /*!< SCU_T::SD0VA: VIOADDR Mask             */

#define SCU_PDMA0VSRC_MASTER_Pos         (0)                                               /*!< SCU_T::PDMA0VSRC: MASTER Position      */
#define SCU_PDMA0VSRC_MASTER_Msk         (0xful << SCU_PDMA0VSRC_MASTER_Pos)               /*!< SCU_T::PDMA0VSRC: MASTER Mask          */

#define SCU_PDMA0VA_VIOADDR_Pos          (0)                                               /*!< SCU_T::PDMA0VA: VIOADDR Position       */
#define SCU_PDMA0VA_VIOADDR_Msk          (0xfffffffful << SCU_PDMA0VA_VIOADDR_Pos)         /*!< SCU_T::PDMA0VA: VIOADDR Mask           */

#define SCU_PDMA1VSRC_MASTER_Pos         (0)                                               /*!< SCU_T::PDMA1VSRC: MASTER Position      */
#define SCU_PDMA1VSRC_MASTER_Msk         (0xful << SCU_PDMA1VSRC_MASTER_Pos)               /*!< SCU_T::PDMA1VSRC: MASTER Mask          */

#define SCU_PDMA1VA_VIOADDR_Pos          (0)                                               /*!< SCU_T::PDMA1VA: VIOADDR Position       */
#define SCU_PDMA1VA_VIOADDR_Msk          (0xfffffffful << SCU_PDMA1VA_VIOADDR_Pos)         /*!< SCU_T::PDMA1VA: VIOADDR Mask           */

#define SCU_SRAM0VSRC_MASTER_Pos         (0)                                               /*!< SCU_T::SRAM0VSRC: MASTER Position      */
#define SCU_SRAM0VSRC_MASTER_Msk         (0xful << SCU_SRAM0VSRC_MASTER_Pos)               /*!< SCU_T::SRAM0VSRC: MASTER Mask          */

#define SCU_SRAM0VA_VIOADDR_Pos          (0)                                               /*!< SCU_T::SRAM0VA: VIOADDR Position       */
#define SCU_SRAM0VA_VIOADDR_Msk          (0xfffffffful << SCU_SRAM0VA_VIOADDR_Pos)         /*!< SCU_T::SRAM0VA: VIOADDR Mask           */

#define SCU_SRAM1VSRC_MASTER_Pos         (0)                                               /*!< SCU_T::SRAM1VSRC: MASTER Position      */
#define SCU_SRAM1VSRC_MASTER_Msk         (0xful << SCU_SRAM1VSRC_MASTER_Pos)               /*!< SCU_T::SRAM1VSRC: MASTER Mask          */

#define SCU_SRAM1VA_VIOADDR_Pos          (0)                                               /*!< SCU_T::SRAM1VA: VIOADDR Position       */
#define SCU_SRAM1VA_VIOADDR_Msk          (0xfffffffful << SCU_SRAM1VA_VIOADDR_Pos)         /*!< SCU_T::SRAM1VA: VIOADDR Mask           */

#define SCU_FMCVSRC_MASTER_Pos           (0)                                               /*!< SCU_T::FMCVSRC: MASTER Position        */
#define SCU_FMCVSRC_MASTER_Msk           (0xful << SCU_FMCVSRC_MASTER_Pos)                 /*!< SCU_T::FMCVSRC: MASTER Mask            */

#define SCU_FMCVA_VIOADDR_Pos            (0)                                               /*!< SCU_T::FMCVA: VIOADDR Position         */
#define SCU_FMCVA_VIOADDR_Msk            (0xfffffffful << SCU_FMCVA_VIOADDR_Pos)           /*!< SCU_T::FMCVA: VIOADDR Mask             */

#define SCU_FLASHVSRC_MASTER_Pos         (0)                                               /*!< SCU_T::FLASHVSRC: MASTER Position      */
#define SCU_FLASHVSRC_MASTER_Msk         (0xful << SCU_FLASHVSRC_MASTER_Pos)               /*!< SCU_T::FLASHVSRC: MASTER Mask          */

#define SCU_FLASHVA_VIOADDR_Pos          (0)                                               /*!< SCU_T::FLASHVA: VIOADDR Position       */
#define SCU_FLASHVA_VIOADDR_Msk          (0xfffffffful << SCU_FLASHVA_VIOADDR_Pos)         /*!< SCU_T::FLASHVA: VIOADDR Mask           */

#define SCU_SCUVSRC_MASTER_Pos           (0)                                               /*!< SCU_T::SCUVSRC: MASTER Position        */
#define SCU_SCUVSRC_MASTER_Msk           (0xful << SCU_SCUVSRC_MASTER_Pos)                 /*!< SCU_T::SCUVSRC: MASTER Mask            */

#define SCU_SCUVA_VIOADDR_Pos            (0)                                               /*!< SCU_T::SCUVA: VIOADDR Position         */
#define SCU_SCUVA_VIOADDR_Msk            (0xfffffffful << SCU_SCUVA_VIOADDR_Pos)           /*!< SCU_T::SCUVA: VIOADDR Mask             */

#define SCU_SYSVSRC_MASTER_Pos           (0)                                               /*!< SCU_T::SYSVSRC: MASTER Position        */
#define SCU_SYSVSRC_MASTER_Msk           (0xful << SCU_SYSVSRC_MASTER_Pos)                 /*!< SCU_T::SYSVSRC: MASTER Mask            */

#define SCU_SYSVA_VIOADDR_Pos            (0)                                               /*!< SCU_T::SYSVA: VIOADDR Position         */
#define SCU_SYSVA_VIOADDR_Msk            (0xfffffffful << SCU_SYSVA_VIOADDR_Pos)           /*!< SCU_T::SYSVA: VIOADDR Mask             */

#define SCU_CRPTVSRC_MASTER_Pos          (0)                                               /*!< SCU_T::CRPTVSRC: MASTER Position       */
#define SCU_CRPTVSRC_MASTER_Msk          (0xful << SCU_CRPTVSRC_MASTER_Pos)                /*!< SCU_T::CRPTVSRC: MASTER Mask           */

#define SCU_CRPTVA_VIOADDR_Pos           (0)                                               /*!< SCU_T::CRPTVA: VIOADDR Position        */
#define SCU_CRPTVA_VIOADDR_Msk           (0xfffffffful << SCU_CRPTVA_VIOADDR_Pos)          /*!< SCU_T::CRPTVA: VIOADDR Mask            */

#define SCU_NSMCTL_PRESCALE_Pos          (0)                                               /*!< SCU_T::NSMCTL: PRESCALE Position       */
#define SCU_NSMCTL_PRESCALE_Msk          (0xfful << SCU_NSMCTL_PRESCALE_Pos)               /*!< SCU_T::NSMCTL: PRESCALE Mask           */

#define SCU_NSMCTL_NSMIEN_Pos            (8)                                               /*!< SCU_T::NSMCTL: NSMIEN Position         */
#define SCU_NSMCTL_NSMIEN_Msk            (0x1ul << SCU_NSMCTL_NSMIEN_Pos)                  /*!< SCU_T::NSMCTL: NSMIEN Mask             */

#define SCU_NSMCTL_AUTORLD_Pos           (9)                                               /*!< SCU_T::NSMCTL: AUTORLD Position        */
#define SCU_NSMCTL_AUTORLD_Msk           (0x1ul << SCU_NSMCTL_AUTORLD_Pos)                 /*!< SCU_T::NSMCTL: AUTORLD Mask            */

#define SCU_NSMCTL_TMRMOD_Pos            (10)                                              /*!< SCU_T::NSMCTL: TMRMOD Position         */
#define SCU_NSMCTL_TMRMOD_Msk            (0x1ul << SCU_NSMCTL_TMRMOD_Pos)                  /*!< SCU_T::NSMCTL: TMRMOD Mask             */

#define SCU_NSMCTL_IDLEON_Pos            (12)                                              /*!< SCU_T::NSMCTL: IDLEON Position         */
#define SCU_NSMCTL_IDLEON_Msk            (0x1ul << SCU_NSMCTL_IDLEON_Pos)                  /*!< SCU_T::NSMCTL: IDLEON Mask             */

#define SCU_NSMCTL_DBGON_Pos             (13)                                              /*!< SCU_T::NSMCTL: DBGON Position          */
#define SCU_NSMCTL_DBGON_Msk             (0x1ul << SCU_NSMCTL_DBGON_Pos)                   /*!< SCU_T::NSMCTL: DBGON Mask              */

#define SCU_NSMLOAD_RELOAD_Pos           (0)                                               /*!< SCU_T::NSMLOAD: RELOAD Position        */
#define SCU_NSMLOAD_RELOAD_Msk           (0xfffffful << SCU_NSMLOAD_RELOAD_Pos)            /*!< SCU_T::NSMLOAD: RELOAD Mask            */

#define SCU_NSMVAL_VALUE_Pos             (0)                                               /*!< SCU_T::NSMVAL: VALUE Position          */
#define SCU_NSMVAL_VALUE_Msk             (0xfffffful << SCU_NSMVAL_VALUE_Pos)              /*!< SCU_T::NSMVAL: VALUE Mask              */

#define SCU_NSMSTS_CURRNS_Pos            (0)                                               /*!< SCU_T::NSMSTS: CURRNS Position         */
#define SCU_NSMSTS_CURRNS_Msk            (0x1ul << SCU_NSMSTS_CURRNS_Pos)                  /*!< SCU_T::NSMSTS: CURRNS Mask             */

#define SCU_NSMSTS_NSMIF_Pos             (1)                                               /*!< SCU_T::NSMSTS: NSMIF Position          */
#define SCU_NSMSTS_NSMIF_Msk             (0x1ul << SCU_NSMSTS_NSMIF_Pos)                   /*!< SCU_T::NSMSTS: NSMIF Mask              */

/**@}*/ /* SCU_CONST */
/**@}*/ /* end of SCU register group */
/**@}*/ /* end of REGISTER group */


#endif /* __SCU_REG_H__ */
