/**************************************************************************//**
 * @file     SYS.h
 * @version  V3
 * @brief    M2351 series System Manager (SYS) driver header file
 *
 * @note
 * Copyright (C) 2016 Nuvoton Technology Corp. All rights reserved.
 *
 ******************************************************************************/
#ifndef __SYS_H__
#define __SYS_H__


#ifdef __cplusplus
extern "C"
{
#endif

/** @addtogroup Standard_Driver Standard Driver
  @{
*/

/** @addtogroup SYS_Driver SYS Driver
  @{
*/

/** @addtogroup SYS_EXPORTED_CONSTANTS SYS Exported Constants
  @{
*/

/*---------------------------------------------------------------------------------------------------------*/
/*  Module Reset Control Resister constant definitions.                                                    */
/*---------------------------------------------------------------------------------------------------------*/
#define PDMA0_RST   ((0x0UL<<24)|(uint32_t)SYS_IPRST0_PDMA0RST_Pos)     /*!< PDMA0 reset is one of the SYS_ResetModule parameter */
#define EBI_RST     ((0x0UL<<24)|(uint32_t)SYS_IPRST0_EBIRST_Pos)       /*!< EBI reset is one of the SYS_ResetModule parameter */
#define USBH_RST    ((0x0UL<<24)|(uint32_t)SYS_IPRST0_USBHRST_Pos)      /*!< USBH reset is one of the SYS_ResetModule parameter */
#define SDH0_RST    ((0x0UL<<24)|(uint32_t)SYS_IPRST0_SDH0RST_Pos)      /*!< SDH0 reset is one of the SYS_ResetModule parameter */
#define CRC_RST     ((0x0UL<<24)|(uint32_t)SYS_IPRST0_CRCRST_Pos)       /*!< CRC reset is one of the SYS_ResetModule parameter */
#define CRPT_RST    ((0x0UL<<24)|(uint32_t)SYS_IPRST0_CRPTRST_Pos)      /*!< CRPT reset is one of the SYS_ResetModule parameter */
#define PDMA1_RST   ((0x0UL<<24)|(uint32_t)SYS_IPRST0_PDMA1RST_Pos)     /*!< PDMA1 reset is one of the SYS_ResetModule parameter */

#define GPIO_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_GPIORST_Pos)      /*!< GPIO reset is one of the SYS_ResetModule parameter */
#define TMR0_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_TMR0RST_Pos)      /*!< TMR0 reset is one of the SYS_ResetModule parameter */
#define TMR1_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_TMR1RST_Pos)      /*!< TMR1 reset is one of the SYS_ResetModule parameter */
#define TMR2_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_TMR2RST_Pos)      /*!< TMR2 reset is one of the SYS_ResetModule parameter */
#define TMR3_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_TMR3RST_Pos)      /*!< TMR3 reset is one of the SYS_ResetModule parameter */
#define ACMP01_RST  ((0x4UL<<24)|(uint32_t)SYS_IPRST1_ACMP01RST_Pos)    /*!< ACMP01 reset is one of the SYS_ResetModule parameter */
#define I2C0_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_I2C0RST_Pos)      /*!< I2C0 reset is one of the SYS_ResetModule parameter */
#define I2C1_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_I2C1RST_Pos)      /*!< I2C1 reset is one of the SYS_ResetModule parameter */
#define I2C2_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_I2C2RST_Pos)      /*!< I2C2 reset is one of the SYS_ResetModule parameter */
#define QSPI0_RST   ((0x4UL<<24)|(uint32_t)SYS_IPRST1_QSPI0RST_Pos)     /*!< QSPI0 reset is one of the SYS_ResetModule parameter */
#define SPI0_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_SPI0RST_Pos)      /*!< SPI0 reset is one of the SYS_ResetModule parameter */
#define SPI1_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_SPI1RST_Pos)      /*!< SPI1 reset is one of the SYS_ResetModule parameter */
#define SPI2_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_SPI2RST_Pos)      /*!< SPI2 reset is one of the SYS_ResetModule parameter */
#define UART0_RST   ((0x4UL<<24)|(uint32_t)SYS_IPRST1_UART0RST_Pos)     /*!< UART0 reset is one of the SYS_ResetModule parameter */
#define UART1_RST   ((0x4UL<<24)|(uint32_t)SYS_IPRST1_UART1RST_Pos)     /*!< UART1 reset is one of the SYS_ResetModule parameter */
#define UART2_RST   ((0x4UL<<24)|(uint32_t)SYS_IPRST1_UART2RST_Pos)     /*!< UART2 reset is one of the SYS_ResetModule parameter */
#define UART3_RST   ((0x4UL<<24)|(uint32_t)SYS_IPRST1_UART3RST_Pos)     /*!< UART3 reset is one of the SYS_ResetModule parameter */
#define UART4_RST   ((0x4UL<<24)|(uint32_t)SYS_IPRST1_UART4RST_Pos)     /*!< UART4 reset is one of the SYS_ResetModule parameter */
#define UART5_RST   ((0x4UL<<24)|(uint32_t)SYS_IPRST1_UART5RST_Pos)     /*!< UART5 reset is one of the SYS_ResetModule parameter */
#define CAN0_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_CAN0RST_Pos)      /*!< CAN0 reset is one of the SYS_ResetModule parameter */
#define OTG_RST     ((0x4UL<<24)|(uint32_t)SYS_IPRST1_OTGRST_Pos)       /*!< OTG reset is one of the SYS_ResetModule parameter */
#define USBD_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_USBDRST_Pos)      /*!< USBD reset is one of the SYS_ResetModule parameter */
#define EADC_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_EADCRST_Pos)      /*!< EADC reset is one of the SYS_ResetModule parameter */
#define I2S0_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_I2S0RST_Pos)      /*!< I2S0 reset is one of the SYS_ResetModule parameter */
#define TRNG_RST    ((0x4UL<<24)|(uint32_t)SYS_IPRST1_TRNGRST_Pos)      /*!< TRNG reset is one of the SYS_ResetModule parameter */

#define SC0_RST     ((0x8UL<<24)|(uint32_t)SYS_IPRST2_SC0RST_Pos)       /*!< SC0 reset is one of the SYS_ResetModule parameter */
#define SC1_RST     ((0x8UL<<24)|(uint32_t)SYS_IPRST2_SC1RST_Pos)       /*!< SC1 reset is one of the SYS_ResetModule parameter */
#define SC2_RST     ((0x8UL<<24)|(uint32_t)SYS_IPRST2_SC2RST_Pos)       /*!< SC2 reset is one of the SYS_ResetModule parameter */
#define SPI3_RST    ((0x8UL<<24)|(uint32_t)SYS_IPRST2_SPI3RST_Pos)      /*!< SPI3 reset is one of the SYS_ResetModule parameter */
#define USCI0_RST   ((0x8UL<<24)|(uint32_t)SYS_IPRST2_USCI0RST_Pos)     /*!< USCI0 reset is one of the SYS_ResetModule parameter */
#define USCI1_RST   ((0x8UL<<24)|(uint32_t)SYS_IPRST2_USCI1RST_Pos)     /*!< USCI1 reset is one of the SYS_ResetModule parameter */
#define USCI2_RST   ((0x8UL<<24)|(uint32_t)SYS_IPRST2_USCI2RST_Pos)     /*!< USCI2 reset is one of the SYS_ResetModule parameter */
#define DAC_RST     ((0x8UL<<24)|(uint32_t)SYS_IPRST2_DACRST_Pos)       /*!< DAC reset is one of the SYS_ResetModule parameter */
#define EPWM0_RST   ((0x8UL<<24)|(uint32_t)SYS_IPRST2_EPWM0RST_Pos)     /*!< EPWM0 reset is one of the SYS_ResetModule parameter */
#define EPWM1_RST   ((0x8UL<<24)|(uint32_t)SYS_IPRST2_EPWM1RST_Pos)     /*!< EPWM1 reset is one of the SYS_ResetModule parameter */
#define BPWM0_RST   ((0x8UL<<24)|(uint32_t)SYS_IPRST2_BPWM0RST_Pos)     /*!< BPWM0 reset is one of the SYS_ResetModule parameter */
#define BPWM1_RST   ((0x8UL<<24)|(uint32_t)SYS_IPRST2_BPWM1RST_Pos)     /*!< BPWM1 reset is one of the SYS_ResetModule parameter */
#define QEI0_RST    ((0x8UL<<24)|(uint32_t)SYS_IPRST2_QEI0RST_Pos)      /*!< QEI0 reset is one of the SYS_ResetModule parameter */
#define QEI1_RST    ((0x8UL<<24)|(uint32_t)SYS_IPRST2_QEI1RST_Pos)      /*!< QEI1 reset is one of the SYS_ResetModule parameter */
#define ECAP0_RST   ((0x8UL<<24)|(uint32_t)SYS_IPRST2_ECAP0RST_Pos)     /*!< ECAP0 reset is one of the SYS_ResetModule parameter */
#define ECAP1_RST   ((0x8UL<<24)|(uint32_t)SYS_IPRST2_ECAP1RST_Pos)     /*!< ECAP1 reset is one of the SYS_ResetModule parameter */


/*---------------------------------------------------------------------------------------------------------*/
/*  Brown Out Detector Threshold Voltage Selection constant definitions.                                   */
/*---------------------------------------------------------------------------------------------------------*/
#define SYS_BODCTL_BOD_RST_EN           (1UL<<SYS_BODCTL_BODRSTEN_Pos)    /*!< Brown-out Reset Enable */
#define SYS_BODCTL_BOD_INTERRUPT_EN     (0UL<<SYS_BODCTL_BODRSTEN_Pos)    /*!< Brown-out Interrupt Enable */
#define SYS_BODCTL_BODVL_3_0V           (7UL<<SYS_BODCTL_BODVL_Pos)       /*!< Setting Brown Out Detector Threshold Voltage as 3.0V */
#define SYS_BODCTL_BODVL_2_8V           (6UL<<SYS_BODCTL_BODVL_Pos)       /*!< Setting Brown Out Detector Threshold Voltage as 2.8V */
#define SYS_BODCTL_BODVL_2_6V           (5UL<<SYS_BODCTL_BODVL_Pos)       /*!< Setting Brown Out Detector Threshold Voltage as 2.6V */
#define SYS_BODCTL_BODVL_2_4V           (4UL<<SYS_BODCTL_BODVL_Pos)       /*!< Setting Brown Out Detector Threshold Voltage as 2.4V */
#define SYS_BODCTL_BODVL_2_2V           (3UL<<SYS_BODCTL_BODVL_Pos)       /*!< Setting Brown Out Detector Threshold Voltage as 2.2V */
#define SYS_BODCTL_BODVL_2_0V           (2UL<<SYS_BODCTL_BODVL_Pos)       /*!< Setting Brown Out Detector Threshold Voltage as 2.0V */
#define SYS_BODCTL_BODVL_1_8V           (1UL<<SYS_BODCTL_BODVL_Pos)       /*!< Setting Brown Out Detector Threshold Voltage as 1.8V */
#define SYS_BODCTL_BODVL_1_6V           (0UL<<SYS_BODCTL_BODVL_Pos)       /*!< Setting Brown Out Detector Threshold Voltage as 1.6V */


/*---------------------------------------------------------------------------------------------------------*/
/*  VREFCTL constant definitions. (Write-Protection Register)                                              */
/*---------------------------------------------------------------------------------------------------------*/
#define SYS_VREFCTL_VREF_PIN        (0x0UL<<SYS_VREFCTL_VREFCTL_Pos)    /*!< Vref = Vref pin */
#define SYS_VREFCTL_VREF_1_6V       (0x3UL<<SYS_VREFCTL_VREFCTL_Pos)    /*!< Vref = 1.6V */
#define SYS_VREFCTL_VREF_2_0V       (0x7UL<<SYS_VREFCTL_VREFCTL_Pos)    /*!< Vref = 2.0V */
#define SYS_VREFCTL_VREF_2_5V       (0xBUL<<SYS_VREFCTL_VREFCTL_Pos)    /*!< Vref = 2.5V */
#define SYS_VREFCTL_VREF_3_0V       (0xFUL<<SYS_VREFCTL_VREFCTL_Pos)    /*!< Vref = 3.0V */
#define SYS_VREFCTL_VREF_AVDD       (0x10UL<<SYS_VREFCTL_VREFCTL_Pos)   /*!< Vref = AVDD */


/*---------------------------------------------------------------------------------------------------------*/
/*  USBPHY constant definitions. (Write-Protection Register)                                               */
/*---------------------------------------------------------------------------------------------------------*/
#define SYS_USBPHY_USBROLE_STD_USBD   (0x0UL<<SYS_USBPHY_USBROLE_Pos)   /*!< Standard USB device */
#define SYS_USBPHY_USBROLE_STD_USBH   (0x1UL<<SYS_USBPHY_USBROLE_Pos)   /*!< Standard USB host */
#define SYS_USBPHY_USBROLE_ID_DEPH    (0x2UL<<SYS_USBPHY_USBROLE_Pos)   /*!< ID dependent device */
#define SYS_USBPHY_USBROLE_ON_THE_GO  (0x3UL<<SYS_USBPHY_USBROLE_Pos)   /*!< On-The-Go device */


/*---------------------------------------------------------------------------------------------------------*/
/*  PLCTL constant definitions. (Write-Protection Register)                                                */
/*---------------------------------------------------------------------------------------------------------*/
#define SYS_PLCTL_PLSEL_PL0     (0x0UL<<SYS_PLCTL_PLSEL_Pos)   /*!< Set power level to power level 0 */
#define SYS_PLCTL_PLSEL_PL1     (0x1UL<<SYS_PLCTL_PLSEL_Pos)   /*!< Set power level to power level 1 */
#define SYS_PLCTL_MVRS_LDO      (0x0UL<<SYS_PLCTL_MVRS_Pos)    /*!< Set main voltage regulator type to LDO */
#define SYS_PLCTL_MVRS_DCDC     (0x1UL<<SYS_PLCTL_MVRS_Pos)    /*!< Set main voltage regulator type to DCDC */


/*---------------------------------------------------------------------------------------------------------*/
/*  PLSTS constant definitions. (Write-Protection Register)                                                */
/*---------------------------------------------------------------------------------------------------------*/
#define SYS_PLSTS_PLSTATUS_PL0  (0x0UL<<SYS_PLSTS_PLSTATUS_Pos) /*!< Power level is power level 0 */
#define SYS_PLSTS_PLSTATUS_PL1  (0x1UL<<SYS_PLSTS_PLSTATUS_Pos) /*!< Power level is power level 1 */
#define SYS_PLSTS_CURMVR_LDO    (0x0UL<<SYS_PLSTS_CURMVR_Pos)   /*!< Main voltage regulator type is LDO */
#define SYS_PLSTS_CURMVR_DCDC   (0x1UL<<SYS_PLSTS_CURMVR_Pos)   /*!< Main voltage regulator type is DCDC */


/*---------------------------------------------------------------------------------------------------------*/
/*  SRAMPCTL constant definitions. (Write-Protection Register)                                             */
/*---------------------------------------------------------------------------------------------------------*/
#define SYS_SRAMPCTL_SRAM_NORMAL          0x0UL   /*!< Select system SRAM power mode to normal mode */
#define SYS_SRAMPCTL_SRAM_RETENTION       0x1UL   /*!< Select system SRAM power mode to retention mode */
#define SYS_SRAMPCTL_SRAM_POWER_SHUT_DOWN 0x2UL   /*!< Select system SRAM power mode to power shut down mode */

/*---------------------------------------------------------------------------------------------------------*/
/*  SRAMPPCTL constant definitions. (Write-Protection Register)                                            */
/*---------------------------------------------------------------------------------------------------------*/
#define SYS_SRAMPPCT_SRAM_NORMAL          0x0UL   /*!< Select peripheral SRAM power mode to normal mode */
#define SYS_SRAMPPCT_SRAM_RETENTION       0x1UL   /*!< Select peripheral SRAM power mode to retention mode */
#define SYS_SRAMPPCT_SRAM_POWER_SHUT_DOWN 0x2UL   /*!< Select peripheral SRAM power mode to power shut down mode */

/*---------------------------------------------------------------------------------------------------------*/
/*  Multi-Function constant definitions.                                                                   */
/*---------------------------------------------------------------------------------------------------------*/

/* How to use below #define?

Example: If user want to set PA.1 as UART0_TXD and PA.0 as UART0_RXD in initial function,
         user can issue following command to achieve it.

    SYS->GPA_MFPL = (SYS->GPA_MFPL & (~SYS_GPA_MFPL_PA0MFP_Msk)) | SYS_GPA_MFPL_PA0MFP_UART0_RXD;
    SYS->GPA_MFPL = (SYS->GPA_MFPL & (~SYS_GPA_MFPL_PA1MFP_Msk)) | SYS_GPA_MFPL_PA1MFP_UART0_TXD;
*/

/* PA.0 MFP */
#define SYS_GPA_MFPL_PA0MFP_GPIO         (0x00UL<<SYS_GPA_MFPL_PA0MFP_Pos) /*!< GPA_MFPL PA0 setting for GPIO        */
#define SYS_GPA_MFPL_PA0MFP_QSPI0_MOSI0  (0x03UL<<SYS_GPA_MFPL_PA0MFP_Pos) /*!< GPA_MFPL PA0 setting for QSPI0_MOSI0 */
#define SYS_GPA_MFPL_PA0MFP_SPI0_MOSI    (0x04UL<<SYS_GPA_MFPL_PA0MFP_Pos) /*!< GPA_MFPL PA0 setting for SPI0_MOSI   */
#define SYS_GPA_MFPL_PA0MFP_SC0_CLK      (0x06UL<<SYS_GPA_MFPL_PA0MFP_Pos) /*!< GPA_MFPL PA0 setting for SC0_CLK     */
#define SYS_GPA_MFPL_PA0MFP_UART0_RXD    (0x07UL<<SYS_GPA_MFPL_PA0MFP_Pos) /*!< GPA_MFPL PA0 setting for UART0_RXD   */
#define SYS_GPA_MFPL_PA0MFP_UART1_nRTS   (0x08UL<<SYS_GPA_MFPL_PA0MFP_Pos) /*!< GPA_MFPL PA0 setting for UART1_nRTS  */
#define SYS_GPA_MFPL_PA0MFP_I2C2_SDA     (0x09UL<<SYS_GPA_MFPL_PA0MFP_Pos) /*!< GPA_MFPL PA0 setting for I2C2_SDA    */
#define SYS_GPA_MFPL_PA0MFP_BPWM0_CH0    (0x0cUL<<SYS_GPA_MFPL_PA0MFP_Pos) /*!< GPA_MFPL PA0 setting for BPWM0_CH0   */
#define SYS_GPA_MFPL_PA0MFP_EPWM0_CH5    (0x0dUL<<SYS_GPA_MFPL_PA0MFP_Pos) /*!< GPA_MFPL PA0 setting for EPWM0_CH5   */
#define SYS_GPA_MFPL_PA0MFP_DAC0_ST      (0x0fUL<<SYS_GPA_MFPL_PA0MFP_Pos) /*!< GPA_MFPL PA0 setting for DAC0_ST     */

/* PA.1 MFP */
#define SYS_GPA_MFPL_PA1MFP_GPIO         (0x00UL<<SYS_GPA_MFPL_PA1MFP_Pos) /*!< GPA_MFPL PA1 setting for GPIO        */
#define SYS_GPA_MFPL_PA1MFP_QSPI0_MISO0  (0x03UL<<SYS_GPA_MFPL_PA1MFP_Pos) /*!< GPA_MFPL PA1 setting for QSPI0_MISO0 */
#define SYS_GPA_MFPL_PA1MFP_SPI0_MISO    (0x04UL<<SYS_GPA_MFPL_PA1MFP_Pos) /*!< GPA_MFPL PA1 setting for SPI0_MISO   */
#define SYS_GPA_MFPL_PA1MFP_SC0_DAT      (0x06UL<<SYS_GPA_MFPL_PA1MFP_Pos) /*!< GPA_MFPL PA1 setting for SC0_DAT     */
#define SYS_GPA_MFPL_PA1MFP_UART0_TXD    (0x07UL<<SYS_GPA_MFPL_PA1MFP_Pos) /*!< GPA_MFPL PA1 setting for UART0_TXD   */
#define SYS_GPA_MFPL_PA1MFP_UART1_nCTS   (0x08UL<<SYS_GPA_MFPL_PA1MFP_Pos) /*!< GPA_MFPL PA1 setting for UART1_nCTS  */
#define SYS_GPA_MFPL_PA1MFP_I2C2_SCL     (0x09UL<<SYS_GPA_MFPL_PA1MFP_Pos) /*!< GPA_MFPL PA1 setting for I2C2_SCL    */
#define SYS_GPA_MFPL_PA1MFP_BPWM0_CH1    (0x0cUL<<SYS_GPA_MFPL_PA1MFP_Pos) /*!< GPA_MFPL PA1 setting for BPWM0_CH1   */
#define SYS_GPA_MFPL_PA1MFP_EPWM0_CH4    (0x0dUL<<SYS_GPA_MFPL_PA1MFP_Pos) /*!< GPA_MFPL PA1 setting for EPWM0_CH4   */
#define SYS_GPA_MFPL_PA1MFP_DAC1_ST      (0x0fUL<<SYS_GPA_MFPL_PA1MFP_Pos) /*!< GPA_MFPL PA1 setting for DAC1_ST     */

/* PA.2 MFP */
#define SYS_GPA_MFPL_PA2MFP_GPIO         (0x00UL<<SYS_GPA_MFPL_PA2MFP_Pos) /*!< GPA_MFPL PA2 setting for GPIO        */
#define SYS_GPA_MFPL_PA2MFP_QSPI0_CLK    (0x03UL<<SYS_GPA_MFPL_PA2MFP_Pos) /*!< GPA_MFPL PA2 setting for QSPI0_CLK   */
#define SYS_GPA_MFPL_PA2MFP_SPI0_CLK     (0x04UL<<SYS_GPA_MFPL_PA2MFP_Pos) /*!< GPA_MFPL PA2 setting for SPI0_CLK    */
#define SYS_GPA_MFPL_PA2MFP_SC0_RST      (0x06UL<<SYS_GPA_MFPL_PA2MFP_Pos) /*!< GPA_MFPL PA2 setting for SC0_RST     */
#define SYS_GPA_MFPL_PA2MFP_UART4_RXD    (0x07UL<<SYS_GPA_MFPL_PA2MFP_Pos) /*!< GPA_MFPL PA2 setting for UART4_RXD   */
#define SYS_GPA_MFPL_PA2MFP_UART1_RXD    (0x08UL<<SYS_GPA_MFPL_PA2MFP_Pos) /*!< GPA_MFPL PA2 setting for UART1_RXD   */
#define SYS_GPA_MFPL_PA2MFP_I2C1_SDA     (0x09UL<<SYS_GPA_MFPL_PA2MFP_Pos) /*!< GPA_MFPL PA2 setting for I2C1_SDA    */
#define SYS_GPA_MFPL_PA2MFP_BPWM0_CH2    (0x0cUL<<SYS_GPA_MFPL_PA2MFP_Pos) /*!< GPA_MFPL PA2 setting for BPWM0_CH2   */
#define SYS_GPA_MFPL_PA2MFP_EPWM0_CH3    (0x0dUL<<SYS_GPA_MFPL_PA2MFP_Pos) /*!< GPA_MFPL PA2 setting for EPWM0_CH3   */

/* PA.3 MFP */
#define SYS_GPA_MFPL_PA3MFP_GPIO         (0x00UL<<SYS_GPA_MFPL_PA3MFP_Pos) /*!< GPA_MFPL PA3 setting for GPIO        */
#define SYS_GPA_MFPL_PA3MFP_QSPI0_SS     (0x03UL<<SYS_GPA_MFPL_PA3MFP_Pos) /*!< GPA_MFPL PA3 setting for QSPI0_SS    */
#define SYS_GPA_MFPL_PA3MFP_SPI0_SS      (0x04UL<<SYS_GPA_MFPL_PA3MFP_Pos) /*!< GPA_MFPL PA3 setting for SPI0_SS     */
#define SYS_GPA_MFPL_PA3MFP_SC0_PWR      (0x06UL<<SYS_GPA_MFPL_PA3MFP_Pos) /*!< GPA_MFPL PA3 setting for SC0_PWR     */
#define SYS_GPA_MFPL_PA3MFP_UART4_TXD    (0x07UL<<SYS_GPA_MFPL_PA3MFP_Pos) /*!< GPA_MFPL PA3 setting for UART4_TXD   */
#define SYS_GPA_MFPL_PA3MFP_UART1_TXD    (0x08UL<<SYS_GPA_MFPL_PA3MFP_Pos) /*!< GPA_MFPL PA3 setting for UART1_TXD   */
#define SYS_GPA_MFPL_PA3MFP_I2C1_SCL     (0x09UL<<SYS_GPA_MFPL_PA3MFP_Pos) /*!< GPA_MFPL PA3 setting for I2C1_SCL    */
#define SYS_GPA_MFPL_PA3MFP_BPWM0_CH3    (0x0cUL<<SYS_GPA_MFPL_PA3MFP_Pos) /*!< GPA_MFPL PA3 setting for BPWM0_CH3   */
#define SYS_GPA_MFPL_PA3MFP_EPWM0_CH2    (0x0dUL<<SYS_GPA_MFPL_PA3MFP_Pos) /*!< GPA_MFPL PA3 setting for EPWM0_CH2   */
#define SYS_GPA_MFPL_PA3MFP_QEI0_B       (0x0eUL<<SYS_GPA_MFPL_PA3MFP_Pos) /*!< GPA_MFPL PA3 setting for QEI0_B      */

/* PA.4 MFP */
#define SYS_GPA_MFPL_PA4MFP_GPIO         (0x00UL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for GPIO        */
#define SYS_GPA_MFPL_PA4MFP_QSPI0_MOSI1  (0x03UL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for QSPI0_MOSI1 */
#define SYS_GPA_MFPL_PA4MFP_SPI0_I2SMCLK (0x04UL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for SPI0_I2SMCLK*/
#define SYS_GPA_MFPL_PA4MFP_SC0_nCD      (0x06UL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for SC0_nCD     */
#define SYS_GPA_MFPL_PA4MFP_UART0_nRTS   (0x07UL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for UART0_nRTS  */
#define SYS_GPA_MFPL_PA4MFP_UART5_RXD    (0x08UL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for UART5_RXD   */
#define SYS_GPA_MFPL_PA4MFP_I2C0_SDA     (0x09UL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for I2C0_SDA    */
#define SYS_GPA_MFPL_PA4MFP_CAN0_RXD     (0x0aUL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for CAN0_RXD    */
#define SYS_GPA_MFPL_PA4MFP_BPWM0_CH4    (0x0cUL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for BPWM0_CH4   */
#define SYS_GPA_MFPL_PA4MFP_EPWM0_CH1    (0x0dUL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for EPWM0_CH1   */
#define SYS_GPA_MFPL_PA4MFP_QEI0_A       (0x0eUL<<SYS_GPA_MFPL_PA4MFP_Pos) /*!< GPA_MFPL PA4 setting for QEI0_A      */

/* PA.5 MFP */
#define SYS_GPA_MFPL_PA5MFP_GPIO         (0x00UL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for GPIO        */
#define SYS_GPA_MFPL_PA5MFP_QSPI0_MISO1  (0x03UL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for QSPI0_MISO1 */
#define SYS_GPA_MFPL_PA5MFP_SPI1_I2SMCLK (0x04UL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for SPI1_I2SMCLK*/
#define SYS_GPA_MFPL_PA5MFP_SC2_nCD      (0x06UL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for SC2_nCD     */
#define SYS_GPA_MFPL_PA5MFP_UART0_nCTS   (0x07UL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for UART0_nCTS  */
#define SYS_GPA_MFPL_PA5MFP_UART5_TXD    (0x08UL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for UART5_TXD   */
#define SYS_GPA_MFPL_PA5MFP_I2C0_SCL     (0x09UL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for I2C0_SCL    */
#define SYS_GPA_MFPL_PA5MFP_CAN0_TXD     (0x0aUL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for CAN0_TXD    */
#define SYS_GPA_MFPL_PA5MFP_BPWM0_CH5    (0x0cUL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for BPWM0_CH5   */
#define SYS_GPA_MFPL_PA5MFP_EPWM0_CH0    (0x0dUL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for EPWM0_CH0   */
#define SYS_GPA_MFPL_PA5MFP_QEI0_INDEX   (0x0eUL<<SYS_GPA_MFPL_PA5MFP_Pos) /*!< GPA_MFPL PA5 setting for QEI0_INDEX  */

/* PA.6 MFP */
#define SYS_GPA_MFPL_PA6MFP_GPIO         (0x00UL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for GPIO        */
#define SYS_GPA_MFPL_PA6MFP_EBI_AD6      (0x02UL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for EBI_AD6     */
#define SYS_GPA_MFPL_PA6MFP_SPI1_SS      (0x04UL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for SPI1_SS     */
#define SYS_GPA_MFPL_PA6MFP_SC2_CLK      (0x06UL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for SC2_CLK     */
#define SYS_GPA_MFPL_PA6MFP_UART0_RXD    (0x07UL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for UART0_RXD   */
#define SYS_GPA_MFPL_PA6MFP_I2C1_SDA     (0x08UL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for I2C1_SDA    */
#define SYS_GPA_MFPL_PA6MFP_EPWM1_CH5    (0x0bUL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for EPWM1_CH5   */
#define SYS_GPA_MFPL_PA6MFP_BPWM1_CH3    (0x0cUL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for BPWM1_CH3   */
#define SYS_GPA_MFPL_PA6MFP_ACMP1_WLAT   (0x0dUL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for ACMP1_WLAT  */
#define SYS_GPA_MFPL_PA6MFP_TM3          (0x0eUL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for TM3         */
#define SYS_GPA_MFPL_PA6MFP_INT0         (0x0fUL<<SYS_GPA_MFPL_PA6MFP_Pos) /*!< GPA_MFPL PA6 setting for INT0        */

/* PA.7 MFP */
#define SYS_GPA_MFPL_PA7MFP_GPIO         (0x00UL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for GPIO        */
#define SYS_GPA_MFPL_PA7MFP_EBI_AD7      (0x02UL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for EBI_AD7     */
#define SYS_GPA_MFPL_PA7MFP_SPI1_CLK     (0x04UL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for SPI1_CLK    */
#define SYS_GPA_MFPL_PA7MFP_SC2_DAT      (0x06UL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for SC2_DAT     */
#define SYS_GPA_MFPL_PA7MFP_UART0_TXD    (0x07UL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for UART0_TXD   */
#define SYS_GPA_MFPL_PA7MFP_I2C1_SCL     (0x08UL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for I2C1_SCL    */
#define SYS_GPA_MFPL_PA7MFP_EPWM1_CH4    (0x0bUL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for EPWM1_CH4   */
#define SYS_GPA_MFPL_PA7MFP_BPWM1_CH2    (0x0cUL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for BPWM1_CH2   */
#define SYS_GPA_MFPL_PA7MFP_ACMP0_WLAT   (0x0dUL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for ACMP0_WLAT  */
#define SYS_GPA_MFPL_PA7MFP_TM2          (0x0eUL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for TM2         */
#define SYS_GPA_MFPL_PA7MFP_INT1         (0x0fUL<<SYS_GPA_MFPL_PA7MFP_Pos) /*!< GPA_MFPL PA7 setting for INT1        */

/* PA.8 MFP */
#define SYS_GPA_MFPH_PA8MFP_GPIO         (0x00UL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for GPIO        */
#define SYS_GPA_MFPH_PA8MFP_EBI_ALE      (0x02UL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for EBI_ALE     */
#define SYS_GPA_MFPH_PA8MFP_SC2_CLK      (0x03UL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for SC2_CLK     */
#define SYS_GPA_MFPH_PA8MFP_SPI2_MOSI    (0x04UL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for SPI2_MOSI   */
#define SYS_GPA_MFPH_PA8MFP_USCI0_CTL1   (0x06UL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for USCI0_CTL1  */
#define SYS_GPA_MFPH_PA8MFP_UART1_RXD    (0x07UL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for UART1_RXD   */
#define SYS_GPA_MFPH_PA8MFP_BPWM0_CH3    (0x09UL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for BPWM0_CH3   */
#define SYS_GPA_MFPH_PA8MFP_QEI1_B       (0x0aUL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for QEI1_B      */
#define SYS_GPA_MFPH_PA8MFP_ECAP0_IC2    (0x0bUL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for ECAP0_IC2   */
#define SYS_GPA_MFPH_PA8MFP_TM3_EXT      (0x0dUL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for TM3_EXT     */
#define SYS_GPA_MFPH_PA8MFP_INT4         (0x0fUL<<SYS_GPA_MFPH_PA8MFP_Pos) /*!< GPA_MFPH PA8 setting for INT4        */

/* PA.9 MFP */
#define SYS_GPA_MFPH_PA9MFP_GPIO         (0x00UL<<SYS_GPA_MFPH_PA9MFP_Pos) /*!< GPA_MFPH PA9 setting for GPIO        */
#define SYS_GPA_MFPH_PA9MFP_EBI_MCLK     (0x02UL<<SYS_GPA_MFPH_PA9MFP_Pos) /*!< GPA_MFPH PA9 setting for EBI_MCLK    */
#define SYS_GPA_MFPH_PA9MFP_SC2_DAT      (0x03UL<<SYS_GPA_MFPH_PA9MFP_Pos) /*!< GPA_MFPH PA9 setting for SC2_DAT     */
#define SYS_GPA_MFPH_PA9MFP_SPI2_MISO    (0x04UL<<SYS_GPA_MFPH_PA9MFP_Pos) /*!< GPA_MFPH PA9 setting for SPI2_MISO   */
#define SYS_GPA_MFPH_PA9MFP_USCI0_DAT1   (0x06UL<<SYS_GPA_MFPH_PA9MFP_Pos) /*!< GPA_MFPH PA9 setting for USCI0_DAT1  */
#define SYS_GPA_MFPH_PA9MFP_UART1_TXD    (0x07UL<<SYS_GPA_MFPH_PA9MFP_Pos) /*!< GPA_MFPH PA9 setting for UART1_TXD   */
#define SYS_GPA_MFPH_PA9MFP_BPWM0_CH2    (0x09UL<<SYS_GPA_MFPH_PA9MFP_Pos) /*!< GPA_MFPH PA9 setting for BPWM0_CH2   */
#define SYS_GPA_MFPH_PA9MFP_QEI1_A       (0x0aUL<<SYS_GPA_MFPH_PA9MFP_Pos) /*!< GPA_MFPH PA9 setting for QEI1_A      */
#define SYS_GPA_MFPH_PA9MFP_ECAP0_IC1    (0x0bUL<<SYS_GPA_MFPH_PA9MFP_Pos) /*!< GPA_MFPH PA9 setting for ECAP0_IC1   */
#define SYS_GPA_MFPH_PA9MFP_TM2_EXT      (0x0dUL<<SYS_GPA_MFPH_PA9MFP_Pos) /*!< GPA_MFPH PA9 setting for TM2_EXT     */

/* PA.10 MFP */
#define SYS_GPA_MFPH_PA10MFP_GPIO        (0x00UL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for GPIO       */
#define SYS_GPA_MFPH_PA10MFP_ACMP1_P0    (0x01UL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for ACMP1_P0   */
#define SYS_GPA_MFPH_PA10MFP_EBI_nWR     (0x02UL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for EBI_nWR    */
#define SYS_GPA_MFPH_PA10MFP_SC2_RST     (0x03UL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for SC2_RST    */
#define SYS_GPA_MFPH_PA10MFP_SPI2_CLK    (0x04UL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for SPI2_CLK   */
#define SYS_GPA_MFPH_PA10MFP_USCI0_DAT0  (0x06UL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for USCI0_DAT0 */
#define SYS_GPA_MFPH_PA10MFP_I2C2_SDA    (0x07UL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for I2C2_SDA   */
#define SYS_GPA_MFPH_PA10MFP_BPWM0_CH1   (0x09UL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for BPWM0_CH1  */
#define SYS_GPA_MFPH_PA10MFP_QEI1_INDEX  (0x0aUL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for QEI1_INDEX */
#define SYS_GPA_MFPH_PA10MFP_ECAP0_IC0   (0x0bUL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for ECAP0_IC0  */
#define SYS_GPA_MFPH_PA10MFP_TM1_EXT     (0x0dUL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for TM1_EXT    */
#define SYS_GPA_MFPH_PA10MFP_DAC0_ST     (0x0eUL<<SYS_GPA_MFPH_PA10MFP_Pos)/*!< GPA_MFPH PA10 setting for DAC0_ST    */

/* PA.11 MFP */
#define SYS_GPA_MFPH_PA11MFP_GPIO        (0x00UL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for GPIO       */
#define SYS_GPA_MFPH_PA11MFP_ACMP0_P0    (0x01UL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for ACMP0_P0   */
#define SYS_GPA_MFPH_PA11MFP_EBI_nRD     (0x02UL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for EBI_nRD    */
#define SYS_GPA_MFPH_PA11MFP_SC2_PWR     (0x03UL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for SC2_PWR    */
#define SYS_GPA_MFPH_PA11MFP_SPI2_SS     (0x04UL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for SPI2_SS    */
#define SYS_GPA_MFPH_PA11MFP_USCI0_CLK   (0x06UL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for USCI0_CLK  */
#define SYS_GPA_MFPH_PA11MFP_I2C2_SCL    (0x07UL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for I2C2_SCL   */
#define SYS_GPA_MFPH_PA11MFP_BPWM0_CH0   (0x09UL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for BPWM0_CH0  */
#define SYS_GPA_MFPH_PA11MFP_EPWM0_SYNC_OUT (0x0aUL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for EPWM0_SYNC_OUT*/
#define SYS_GPA_MFPH_PA11MFP_TM0_EXT     (0x0dUL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for TM0_EXT    */
#define SYS_GPA_MFPH_PA11MFP_DAC1_ST     (0x0eUL<<SYS_GPA_MFPH_PA11MFP_Pos)/*!< GPA_MFPH PA11 setting for DAC1_ST    */

/* PA.12 MFP */
#define SYS_GPA_MFPH_PA12MFP_GPIO        (0x00UL<<SYS_GPA_MFPH_PA12MFP_Pos)/*!< GPA_MFPH PA12 setting for GPIO       */
#define SYS_GPA_MFPH_PA12MFP_I2S0_BCLK   (0x02UL<<SYS_GPA_MFPH_PA12MFP_Pos)/*!< GPA_MFPH PA12 setting for I2S0_BCLK  */
#define SYS_GPA_MFPH_PA12MFP_UART4_TXD   (0x03UL<<SYS_GPA_MFPH_PA12MFP_Pos)/*!< GPA_MFPH PA12 setting for UART4_TXD  */
#define SYS_GPA_MFPH_PA12MFP_I2C1_SCL    (0x04UL<<SYS_GPA_MFPH_PA12MFP_Pos)/*!< GPA_MFPH PA12 setting for I2C1_SCL   */
#define SYS_GPA_MFPH_PA12MFP_SPI2_SS     (0x05UL<<SYS_GPA_MFPH_PA12MFP_Pos)/*!< GPA_MFPH PA12 setting for SPI2_SS    */
#define SYS_GPA_MFPH_PA12MFP_CAN0_TXD    (0x06UL<<SYS_GPA_MFPH_PA12MFP_Pos)/*!< GPA_MFPH PA12 setting for CAN0_TXD   */
#define SYS_GPA_MFPH_PA12MFP_SC2_PWR     (0x07UL<<SYS_GPA_MFPH_PA12MFP_Pos)/*!< GPA_MFPH PA12 setting for SC2_PWR    */
#define SYS_GPA_MFPH_PA12MFP_BPWM1_CH2   (0x0bUL<<SYS_GPA_MFPH_PA12MFP_Pos)/*!< GPA_MFPH PA12 setting for BPWM1_CH2  */
#define SYS_GPA_MFPH_PA12MFP_QEI1_INDEX  (0x0cUL<<SYS_GPA_MFPH_PA12MFP_Pos)/*!< GPA_MFPH PA12 setting for QEI1_INDEX */
#define SYS_GPA_MFPH_PA12MFP_USB_VBUS    (0x0eUL<<SYS_GPA_MFPH_PA12MFP_Pos)/*!< GPA_MFPH PA12 setting for USB_VBUS   */

/* PA.13 MFP */
#define SYS_GPA_MFPH_PA13MFP_GPIO        (0x00UL<<SYS_GPA_MFPH_PA13MFP_Pos)/*!< GPA_MFPH PA13 setting for GPIO       */
#define SYS_GPA_MFPH_PA13MFP_I2S0_MCLK   (0x02UL<<SYS_GPA_MFPH_PA13MFP_Pos)/*!< GPA_MFPH PA13 setting for I2S0_MCLK  */
#define SYS_GPA_MFPH_PA13MFP_UART4_RXD   (0x03UL<<SYS_GPA_MFPH_PA13MFP_Pos)/*!< GPA_MFPH PA13 setting for UART4_RXD  */
#define SYS_GPA_MFPH_PA13MFP_I2C1_SDA    (0x04UL<<SYS_GPA_MFPH_PA13MFP_Pos)/*!< GPA_MFPH PA13 setting for I2C1_SDA   */
#define SYS_GPA_MFPH_PA13MFP_SPI2_CLK    (0x05UL<<SYS_GPA_MFPH_PA13MFP_Pos)/*!< GPA_MFPH PA13 setting for SPI2_CLK   */
#define SYS_GPA_MFPH_PA13MFP_CAN0_RXD    (0x06UL<<SYS_GPA_MFPH_PA13MFP_Pos)/*!< GPA_MFPH PA13 setting for CAN0_RXD   */
#define SYS_GPA_MFPH_PA13MFP_SC2_RST     (0x07UL<<SYS_GPA_MFPH_PA13MFP_Pos)/*!< GPA_MFPH PA13 setting for SC2_RST    */
#define SYS_GPA_MFPH_PA13MFP_BPWM1_CH3   (0x0bUL<<SYS_GPA_MFPH_PA13MFP_Pos)/*!< GPA_MFPH PA13 setting for BPWM1_CH3  */
#define SYS_GPA_MFPH_PA13MFP_QEI1_A      (0x0cUL<<SYS_GPA_MFPH_PA13MFP_Pos)/*!< GPA_MFPH PA13 setting for QEI1_A     */
#define SYS_GPA_MFPH_PA13MFP_USB_D_N     (0x0eUL<<SYS_GPA_MFPH_PA13MFP_Pos)/*!< GPA_MFPH PA13 setting for USB_D_N    */

/* PA.14 MFP */
#define SYS_GPA_MFPH_PA14MFP_GPIO        (0x00UL<<SYS_GPA_MFPH_PA14MFP_Pos)/*!< GPA_MFPH PA14 setting for GPIO       */
#define SYS_GPA_MFPH_PA14MFP_I2S0_DI     (0x02UL<<SYS_GPA_MFPH_PA14MFP_Pos)/*!< GPA_MFPH PA14 setting for I2S0_DI    */
#define SYS_GPA_MFPH_PA14MFP_UART0_TXD   (0x03UL<<SYS_GPA_MFPH_PA14MFP_Pos)/*!< GPA_MFPH PA14 setting for UART0_TXD  */
#define SYS_GPA_MFPH_PA14MFP_SPI2_MISO   (0x05UL<<SYS_GPA_MFPH_PA14MFP_Pos)/*!< GPA_MFPH PA14 setting for SPI2_MISO  */
#define SYS_GPA_MFPH_PA14MFP_I2C2_SCL    (0x06UL<<SYS_GPA_MFPH_PA14MFP_Pos)/*!< GPA_MFPH PA14 setting for I2C2_SCL   */
#define SYS_GPA_MFPH_PA14MFP_SC2_DAT     (0x07UL<<SYS_GPA_MFPH_PA14MFP_Pos)/*!< GPA_MFPH PA14 setting for SC2_DAT    */
#define SYS_GPA_MFPH_PA14MFP_BPWM1_CH4   (0x0bUL<<SYS_GPA_MFPH_PA14MFP_Pos)/*!< GPA_MFPH PA14 setting for BPWM1_CH4  */
#define SYS_GPA_MFPH_PA14MFP_QEI1_B      (0x0cUL<<SYS_GPA_MFPH_PA14MFP_Pos)/*!< GPA_MFPH PA14 setting for QEI1_B     */
#define SYS_GPA_MFPH_PA14MFP_USB_D_P     (0x0eUL<<SYS_GPA_MFPH_PA14MFP_Pos)/*!< GPA_MFPH PA14 setting for USB_D_P    */

/* PA.15 MFP */
#define SYS_GPA_MFPH_PA15MFP_GPIO        (0x00UL<<SYS_GPA_MFPH_PA15MFP_Pos)/*!< GPA_MFPH PA15 setting for GPIO       */
#define SYS_GPA_MFPH_PA15MFP_I2S0_DO     (0x02UL<<SYS_GPA_MFPH_PA15MFP_Pos)/*!< GPA_MFPH PA15 setting for I2S0_DO    */
#define SYS_GPA_MFPH_PA15MFP_UART0_RXD   (0x03UL<<SYS_GPA_MFPH_PA15MFP_Pos)/*!< GPA_MFPH PA15 setting for UART0_RXD  */
#define SYS_GPA_MFPH_PA15MFP_SPI2_MOSI   (0x05UL<<SYS_GPA_MFPH_PA15MFP_Pos)/*!< GPA_MFPH PA15 setting for SPI2_MOSI  */
#define SYS_GPA_MFPH_PA15MFP_I2C2_SDA    (0x06UL<<SYS_GPA_MFPH_PA15MFP_Pos)/*!< GPA_MFPH PA15 setting for I2C2_SDA   */
#define SYS_GPA_MFPH_PA15MFP_SC2_CLK     (0x07UL<<SYS_GPA_MFPH_PA15MFP_Pos)/*!< GPA_MFPH PA15 setting for SC2_CLK    */
#define SYS_GPA_MFPH_PA15MFP_BPWM1_CH5   (0x0bUL<<SYS_GPA_MFPH_PA15MFP_Pos)/*!< GPA_MFPH PA15 setting for BPWM1_CH5  */
#define SYS_GPA_MFPH_PA15MFP_EPWM0_SYNC_IN (0x0cUL<<SYS_GPA_MFPH_PA15MFP_Pos)/*!< GPA_MFPH PA15 setting for EPWM0_SYNC_IN*/
#define SYS_GPA_MFPH_PA15MFP_USB_OTG_ID  (0x0eUL<<SYS_GPA_MFPH_PA15MFP_Pos)/*!< GPA_MFPH PA15 setting for USB_OTG_ID */

/* PB.0 MFP */
#define SYS_GPB_MFPL_PB0MFP_GPIO         (0x00UL<<SYS_GPB_MFPL_PB0MFP_Pos) /*!< GPB_MFPL PB0 setting for GPIO        */
#define SYS_GPB_MFPL_PB0MFP_EADC0_CH0    (0x01UL<<SYS_GPB_MFPL_PB0MFP_Pos) /*!< GPB_MFPL PB0 setting for EADC0_CH0   */
#define SYS_GPB_MFPL_PB0MFP_EBI_ADR9     (0x02UL<<SYS_GPB_MFPL_PB0MFP_Pos) /*!< GPB_MFPL PB0 setting for EBI_ADR9    */
#define SYS_GPB_MFPL_PB0MFP_SD0_CMD      (0x03UL<<SYS_GPB_MFPL_PB0MFP_Pos) /*!< GPB_MFPL PB0 setting for SD0_CMD     */
#define SYS_GPB_MFPL_PB0MFP_UART2_RXD    (0x07UL<<SYS_GPB_MFPL_PB0MFP_Pos) /*!< GPB_MFPL PB0 setting for UART2_RXD   */
#define SYS_GPB_MFPL_PB0MFP_SPI0_I2SMCLK (0x08UL<<SYS_GPB_MFPL_PB0MFP_Pos) /*!< GPB_MFPL PB0 setting for SPI0_I2SMCLK*/
#define SYS_GPB_MFPL_PB0MFP_I2C1_SDA     (0x09UL<<SYS_GPB_MFPL_PB0MFP_Pos) /*!< GPB_MFPL PB0 setting for I2C1_SDA    */
#define SYS_GPB_MFPL_PB0MFP_EPWM0_CH5    (0x0bUL<<SYS_GPB_MFPL_PB0MFP_Pos) /*!< GPB_MFPL PB0 setting for EPWM0_CH5   */
#define SYS_GPB_MFPL_PB0MFP_EPWM1_CH5    (0x0cUL<<SYS_GPB_MFPL_PB0MFP_Pos) /*!< GPB_MFPL PB0 setting for EPWM1_CH5   */
#define SYS_GPB_MFPL_PB0MFP_EPWM0_BRAKE1 (0x0dUL<<SYS_GPB_MFPL_PB0MFP_Pos) /*!< GPB_MFPL PB0 setting for EPWM0_BRAKE1*/

/* PB.1 MFP */
#define SYS_GPB_MFPL_PB1MFP_GPIO         (0x00UL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for GPIO        */
#define SYS_GPB_MFPL_PB1MFP_EADC0_CH1    (0x01UL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for EADC0_CH1   */
#define SYS_GPB_MFPL_PB1MFP_EBI_ADR8     (0x02UL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for EBI_ADR8    */
#define SYS_GPB_MFPL_PB1MFP_SD0_CLK      (0x03UL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for SD0_CLK     */
#define SYS_GPB_MFPL_PB1MFP_SPI1_I2SMCLK (0x05UL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for SPI1_I2SMCLK*/
#define SYS_GPB_MFPL_PB1MFP_SPI3_I2SMCLK (0x06UL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for SPI3_I2SMCLK*/
#define SYS_GPB_MFPL_PB1MFP_UART2_TXD    (0x07UL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for UART2_TXD   */
#define SYS_GPB_MFPL_PB1MFP_USCI1_CLK    (0x08UL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for USCI1_CLK   */
#define SYS_GPB_MFPL_PB1MFP_I2C1_SCL     (0x09UL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for I2C1_SCL    */
#define SYS_GPB_MFPL_PB1MFP_I2S0_LRCK    (0x0aUL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for I2S0_LRCK   */
#define SYS_GPB_MFPL_PB1MFP_EPWM0_CH4    (0x0bUL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for EPWM0_CH4   */
#define SYS_GPB_MFPL_PB1MFP_EPWM1_CH4    (0x0cUL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for EPWM1_CH4   */
#define SYS_GPB_MFPL_PB1MFP_EPWM0_BRAKE0 (0x0dUL<<SYS_GPB_MFPL_PB1MFP_Pos) /*!< GPB_MFPL PB1 setting for EPWM0_BRAKE0*/

/* PB.2 MFP */
#define SYS_GPB_MFPL_PB2MFP_GPIO         (0x00UL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for GPIO        */
#define SYS_GPB_MFPL_PB2MFP_EADC0_CH2    (0x01UL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for EADC0_CH2   */
#define SYS_GPB_MFPL_PB2MFP_ACMP0_P1     (0x01UL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for ACMP0_P1    */
#define SYS_GPB_MFPL_PB2MFP_EBI_ADR3     (0x02UL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for EBI_ADR3    */
#define SYS_GPB_MFPL_PB2MFP_SD0_DAT0     (0x03UL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for SD0_DAT0    */
#define SYS_GPB_MFPL_PB2MFP_SPI1_SS      (0x05UL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for SPI1_SS     */
#define SYS_GPB_MFPL_PB2MFP_UART1_RXD    (0x06UL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for UART1_RXD   */
#define SYS_GPB_MFPL_PB2MFP_UART5_nCTS   (0x07UL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for UART5_nCTS  */
#define SYS_GPB_MFPL_PB2MFP_USCI1_DAT0   (0x08UL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for USCI1_DAT0  */
#define SYS_GPB_MFPL_PB2MFP_SC0_PWR      (0x09UL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for SC0_PWR     */
#define SYS_GPB_MFPL_PB2MFP_I2S0_DO      (0x0aUL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for I2S0_DO     */
#define SYS_GPB_MFPL_PB2MFP_EPWM0_CH3    (0x0bUL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for EPWM0_CH3   */
#define SYS_GPB_MFPL_PB2MFP_TM3          (0x0eUL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for TM3         */
#define SYS_GPB_MFPL_PB2MFP_INT3         (0x0fUL<<SYS_GPB_MFPL_PB2MFP_Pos) /*!< GPB_MFPL PB2 setting for INT3        */

/* PB.3 MFP */
#define SYS_GPB_MFPL_PB3MFP_GPIO         (0x00UL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for GPIO        */
#define SYS_GPB_MFPL_PB3MFP_EADC0_CH3    (0x01UL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for EADC0_CH3   */
#define SYS_GPB_MFPL_PB3MFP_ACMP0_N      (0x01UL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for ACMP0_N     */
#define SYS_GPB_MFPL_PB3MFP_EBI_ADR2     (0x02UL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for EBI_ADR2    */
#define SYS_GPB_MFPL_PB3MFP_SD0_DAT1     (0x03UL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for SD0_DAT1    */
#define SYS_GPB_MFPL_PB3MFP_SPI1_CLK     (0x05UL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for SPI1_CLK    */
#define SYS_GPB_MFPL_PB3MFP_UART1_TXD    (0x06UL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for UART1_TXD   */
#define SYS_GPB_MFPL_PB3MFP_UART5_nRTS   (0x07UL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for UART5_nRTS  */
#define SYS_GPB_MFPL_PB3MFP_USCI1_DAT1   (0x08UL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for USCI1_DAT1  */
#define SYS_GPB_MFPL_PB3MFP_SC0_RST      (0x09UL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for SC0_RST     */
#define SYS_GPB_MFPL_PB3MFP_I2S0_DI      (0x0aUL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for I2S0_DI     */
#define SYS_GPB_MFPL_PB3MFP_EPWM0_CH2    (0x0bUL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for EPWM0_CH2   */
#define SYS_GPB_MFPL_PB3MFP_TM2          (0x0eUL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for TM2         */
#define SYS_GPB_MFPL_PB3MFP_INT2         (0x0fUL<<SYS_GPB_MFPL_PB3MFP_Pos) /*!< GPB_MFPL PB3 setting for INT2        */

/* PB.4 MFP */
#define SYS_GPB_MFPL_PB4MFP_GPIO         (0x00UL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for GPIO        */
#define SYS_GPB_MFPL_PB4MFP_EADC0_CH4    (0x01UL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for EADC0_CH4   */
#define SYS_GPB_MFPL_PB4MFP_ACMP1_P1     (0x01UL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for ACMP1_P1    */
#define SYS_GPB_MFPL_PB4MFP_EBI_ADR1     (0x02UL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for EBI_ADR1    */
#define SYS_GPB_MFPL_PB4MFP_SD0_DAT2     (0x03UL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for SD0_DAT2    */
#define SYS_GPB_MFPL_PB4MFP_SPI1_MOSI    (0x05UL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for SPI1_MOSI   */
#define SYS_GPB_MFPL_PB4MFP_I2C0_SDA     (0x06UL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for I2C0_SDA    */
#define SYS_GPB_MFPL_PB4MFP_UART5_RXD    (0x07UL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for UART5_RXD   */
#define SYS_GPB_MFPL_PB4MFP_USCI1_CTL1   (0x08UL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for USCI1_CTL1  */
#define SYS_GPB_MFPL_PB4MFP_SC0_DAT      (0x09UL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for SC0_DAT     */
#define SYS_GPB_MFPL_PB4MFP_I2S0_MCLK    (0x0aUL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for I2S0_MCLK   */
#define SYS_GPB_MFPL_PB4MFP_EPWM0_CH1    (0x0bUL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for EPWM0_CH1   */
#define SYS_GPB_MFPL_PB4MFP_TM1          (0x0eUL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for TM1         */
#define SYS_GPB_MFPL_PB4MFP_INT1         (0x0fUL<<SYS_GPB_MFPL_PB4MFP_Pos) /*!< GPB_MFPL PB4 setting for INT1        */

/* PB.5 MFP */
#define SYS_GPB_MFPL_PB5MFP_GPIO         (0x00UL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for GPIO        */
#define SYS_GPB_MFPL_PB5MFP_EADC0_CH5    (0x01UL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for EADC0_CH5   */
#define SYS_GPB_MFPL_PB5MFP_ACMP1_N      (0x01UL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for ACMP1_N     */
#define SYS_GPB_MFPL_PB5MFP_EBI_ADR0     (0x02UL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for EBI_ADR0    */
#define SYS_GPB_MFPL_PB5MFP_SD0_DAT3     (0x03UL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for SD0_DAT3    */
#define SYS_GPB_MFPL_PB5MFP_SPI1_MISO    (0x05UL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for SPI1_MISO   */
#define SYS_GPB_MFPL_PB5MFP_I2C0_SCL     (0x06UL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for I2C0_SCL    */
#define SYS_GPB_MFPL_PB5MFP_UART5_TXD    (0x07UL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for UART5_TXD   */
#define SYS_GPB_MFPL_PB5MFP_USCI1_CTL0   (0x08UL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for USCI1_CTL0  */
#define SYS_GPB_MFPL_PB5MFP_SC0_CLK      (0x09UL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for SC0_CLK     */
#define SYS_GPB_MFPL_PB5MFP_I2S0_BCLK    (0x0aUL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for I2S0_BCLK   */
#define SYS_GPB_MFPL_PB5MFP_EPWM0_CH0    (0x0bUL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for EPWM0_CH0   */
#define SYS_GPB_MFPL_PB5MFP_TM0          (0x0eUL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for TM0         */
#define SYS_GPB_MFPL_PB5MFP_INT0         (0x0fUL<<SYS_GPB_MFPL_PB5MFP_Pos) /*!< GPB_MFPL PB5 setting for INT0        */

/* PB.6 MFP */
#define SYS_GPB_MFPL_PB6MFP_GPIO         (0x00UL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for GPIO        */
#define SYS_GPB_MFPL_PB6MFP_EADC0_CH6    (0x01UL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for EADC0_CH6   */
#define SYS_GPB_MFPL_PB6MFP_EBI_nWRH     (0x02UL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for EBI_nWRH    */
#define SYS_GPB_MFPL_PB6MFP_USCI1_DAT1   (0x04UL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for USCI1_DAT1  */
#define SYS_GPB_MFPL_PB6MFP_UART1_RXD    (0x06UL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for UART1_RXD   */
#define SYS_GPB_MFPL_PB6MFP_EBI_nCS1     (0x08UL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for EBI_nCS1    */
#define SYS_GPB_MFPL_PB6MFP_BPWM1_CH5    (0x0aUL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for BPWM1_CH5   */
#define SYS_GPB_MFPL_PB6MFP_EPWM1_BRAKE1 (0x0bUL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for EPWM1_BRAKE1*/
#define SYS_GPB_MFPL_PB6MFP_EPWM1_CH5    (0x0cUL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for EPWM1_CH5   */
#define SYS_GPB_MFPL_PB6MFP_INT4         (0x0dUL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for INT4        */
#define SYS_GPB_MFPL_PB6MFP_USB_VBUS_EN  (0x0eUL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for USB_VBUS_EN */
#define SYS_GPB_MFPL_PB6MFP_ACMP1_O      (0x0fUL<<SYS_GPB_MFPL_PB6MFP_Pos) /*!< GPB_MFPL PB6 setting for ACMP1_O     */

/* PB.7 MFP */
#define SYS_GPB_MFPL_PB7MFP_GPIO         (0x00UL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for GPIO        */
#define SYS_GPB_MFPL_PB7MFP_EADC0_CH7    (0x01UL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for EADC0_CH7   */
#define SYS_GPB_MFPL_PB7MFP_EBI_nWRL     (0x02UL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for EBI_nWRL    */
#define SYS_GPB_MFPL_PB7MFP_USCI1_DAT0   (0x04UL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for USCI1_DAT0  */
#define SYS_GPB_MFPL_PB7MFP_UART1_TXD    (0x06UL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for UART1_TXD   */
#define SYS_GPB_MFPL_PB7MFP_EBI_nCS0     (0x08UL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for EBI_nCS0    */
#define SYS_GPB_MFPL_PB7MFP_BPWM1_CH4    (0x0aUL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for BPWM1_CH4   */
#define SYS_GPB_MFPL_PB7MFP_EPWM1_BRAKE0 (0x0bUL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for EPWM1_BRAKE0*/
#define SYS_GPB_MFPL_PB7MFP_EPWM1_CH4    (0x0cUL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for EPWM1_CH4   */
#define SYS_GPB_MFPL_PB7MFP_INT5         (0x0dUL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for INT5        */
#define SYS_GPB_MFPL_PB7MFP_USB_VBUS_ST  (0x0eUL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for USB_VBUS_ST */
#define SYS_GPB_MFPL_PB7MFP_ACMP0_O      (0x0fUL<<SYS_GPB_MFPL_PB7MFP_Pos) /*!< GPB_MFPL PB7 setting for ACMP0_O     */

/* PB.8 MFP */
#define SYS_GPB_MFPH_PB8MFP_GPIO         (0x00UL<<SYS_GPB_MFPH_PB8MFP_Pos) /*!< GPB_MFPH PB8 setting for GPIO        */
#define SYS_GPB_MFPH_PB8MFP_EADC0_CH8    (0x01UL<<SYS_GPB_MFPH_PB8MFP_Pos) /*!< GPB_MFPH PB8 setting for EADC0_CH8   */
#define SYS_GPB_MFPH_PB8MFP_EBI_ADR19    (0x02UL<<SYS_GPB_MFPH_PB8MFP_Pos) /*!< GPB_MFPH PB8 setting for EBI_ADR19   */
#define SYS_GPB_MFPH_PB8MFP_USCI1_CLK    (0x04UL<<SYS_GPB_MFPH_PB8MFP_Pos) /*!< GPB_MFPH PB8 setting for USCI1_CLK   */
#define SYS_GPB_MFPH_PB8MFP_UART0_RXD    (0x05UL<<SYS_GPB_MFPH_PB8MFP_Pos) /*!< GPB_MFPH PB8 setting for UART0_RXD   */
#define SYS_GPB_MFPH_PB8MFP_UART1_nRTS   (0x06UL<<SYS_GPB_MFPH_PB8MFP_Pos) /*!< GPB_MFPH PB8 setting for UART1_nRTS  */
#define SYS_GPB_MFPH_PB8MFP_I2C1_SMBSUS  (0x07UL<<SYS_GPB_MFPH_PB8MFP_Pos) /*!< GPB_MFPH PB8 setting for I2C1_SMBSUS */
#define SYS_GPB_MFPH_PB8MFP_BPWM1_CH3    (0x0aUL<<SYS_GPB_MFPH_PB8MFP_Pos) /*!< GPB_MFPH PB8 setting for BPWM1_CH3   */
#define SYS_GPB_MFPH_PB8MFP_SPI3_MOSI    (0x0bUL<<SYS_GPB_MFPH_PB8MFP_Pos) /*!< GPB_MFPH PB8 setting for SPI3_MOSI   */
#define SYS_GPB_MFPH_PB8MFP_INT6         (0x0dUL<<SYS_GPB_MFPH_PB8MFP_Pos) /*!< GPB_MFPH PB8 setting for INT6        */

/* PB.9 MFP */
#define SYS_GPB_MFPH_PB9MFP_GPIO         (0x00UL<<SYS_GPB_MFPH_PB9MFP_Pos) /*!< GPB_MFPH PB9 setting for GPIO        */
#define SYS_GPB_MFPH_PB9MFP_EADC0_CH9    (0x01UL<<SYS_GPB_MFPH_PB9MFP_Pos) /*!< GPB_MFPH PB9 setting for EADC0_CH9   */
#define SYS_GPB_MFPH_PB9MFP_EBI_ADR18    (0x02UL<<SYS_GPB_MFPH_PB9MFP_Pos) /*!< GPB_MFPH PB9 setting for EBI_ADR18   */
#define SYS_GPB_MFPH_PB9MFP_USCI1_CTL1   (0x04UL<<SYS_GPB_MFPH_PB9MFP_Pos) /*!< GPB_MFPH PB9 setting for USCI1_CTL1  */
#define SYS_GPB_MFPH_PB9MFP_UART0_TXD    (0x05UL<<SYS_GPB_MFPH_PB9MFP_Pos) /*!< GPB_MFPH PB9 setting for UART0_TXD   */
#define SYS_GPB_MFPH_PB9MFP_UART1_nCTS   (0x06UL<<SYS_GPB_MFPH_PB9MFP_Pos) /*!< GPB_MFPH PB9 setting for UART1_nCTS  */
#define SYS_GPB_MFPH_PB9MFP_I2C1_SMBAL   (0x07UL<<SYS_GPB_MFPH_PB9MFP_Pos) /*!< GPB_MFPH PB9 setting for I2C1_SMBAL  */
#define SYS_GPB_MFPH_PB9MFP_BPWM1_CH2    (0x0aUL<<SYS_GPB_MFPH_PB9MFP_Pos) /*!< GPB_MFPH PB9 setting for BPWM1_CH2   */
#define SYS_GPB_MFPH_PB9MFP_SPI3_MISO    (0x0bUL<<SYS_GPB_MFPH_PB9MFP_Pos) /*!< GPB_MFPH PB9 setting for SPI3_MISO   */
#define SYS_GPB_MFPH_PB9MFP_INT7         (0x0dUL<<SYS_GPB_MFPH_PB9MFP_Pos) /*!< GPB_MFPH PB9 setting for INT7        */

/* PB.10 MFP */
#define SYS_GPB_MFPH_PB10MFP_GPIO        (0x00UL<<SYS_GPB_MFPH_PB10MFP_Pos)/*!< GPB_MFPH PB10 setting for GPIO       */
#define SYS_GPB_MFPH_PB10MFP_EADC0_CH10  (0x01UL<<SYS_GPB_MFPH_PB10MFP_Pos)/*!< GPB_MFPH PB10 setting for EADC0_CH10 */
#define SYS_GPB_MFPH_PB10MFP_EBI_ADR17   (0x02UL<<SYS_GPB_MFPH_PB10MFP_Pos)/*!< GPB_MFPH PB10 setting for EBI_ADR17  */
#define SYS_GPB_MFPH_PB10MFP_USCI1_CTL0  (0x04UL<<SYS_GPB_MFPH_PB10MFP_Pos)/*!< GPB_MFPH PB10 setting for USCI1_CTL0 */
#define SYS_GPB_MFPH_PB10MFP_UART0_nRTS  (0x05UL<<SYS_GPB_MFPH_PB10MFP_Pos)/*!< GPB_MFPH PB10 setting for UART0_nRTS */
#define SYS_GPB_MFPH_PB10MFP_UART4_RXD   (0x06UL<<SYS_GPB_MFPH_PB10MFP_Pos)/*!< GPB_MFPH PB10 setting for UART4_RXD  */
#define SYS_GPB_MFPH_PB10MFP_I2C1_SDA    (0x07UL<<SYS_GPB_MFPH_PB10MFP_Pos)/*!< GPB_MFPH PB10 setting for I2C1_SDA   */
#define SYS_GPB_MFPH_PB10MFP_CAN0_RXD    (0x08UL<<SYS_GPB_MFPH_PB10MFP_Pos)/*!< GPB_MFPH PB10 setting for CAN0_RXD   */
#define SYS_GPB_MFPH_PB10MFP_BPWM1_CH1   (0x0aUL<<SYS_GPB_MFPH_PB10MFP_Pos)/*!< GPB_MFPH PB10 setting for BPWM1_CH1  */
#define SYS_GPB_MFPH_PB10MFP_SPI3_SS     (0x0bUL<<SYS_GPB_MFPH_PB10MFP_Pos)/*!< GPB_MFPH PB10 setting for SPI3_SS    */

/* PB.11 MFP */
#define SYS_GPB_MFPH_PB11MFP_GPIO        (0x00UL<<SYS_GPB_MFPH_PB11MFP_Pos)/*!< GPB_MFPH PB11 setting for GPIO       */
#define SYS_GPB_MFPH_PB11MFP_EADC0_CH11  (0x01UL<<SYS_GPB_MFPH_PB11MFP_Pos)/*!< GPB_MFPH PB11 setting for EADC0_CH11 */
#define SYS_GPB_MFPH_PB11MFP_EBI_ADR16   (0x02UL<<SYS_GPB_MFPH_PB11MFP_Pos)/*!< GPB_MFPH PB11 setting for EBI_ADR16  */
#define SYS_GPB_MFPH_PB11MFP_UART0_nCTS  (0x05UL<<SYS_GPB_MFPH_PB11MFP_Pos)/*!< GPB_MFPH PB11 setting for UART0_nCTS */
#define SYS_GPB_MFPH_PB11MFP_UART4_TXD   (0x06UL<<SYS_GPB_MFPH_PB11MFP_Pos)/*!< GPB_MFPH PB11 setting for UART4_TXD  */
#define SYS_GPB_MFPH_PB11MFP_I2C1_SCL    (0x07UL<<SYS_GPB_MFPH_PB11MFP_Pos)/*!< GPB_MFPH PB11 setting for I2C1_SCL   */
#define SYS_GPB_MFPH_PB11MFP_CAN0_TXD    (0x08UL<<SYS_GPB_MFPH_PB11MFP_Pos)/*!< GPB_MFPH PB11 setting for CAN0_TXD   */
#define SYS_GPB_MFPH_PB11MFP_SPI0_I2SMCLK (0x09UL<<SYS_GPB_MFPH_PB11MFP_Pos)/*!< GPB_MFPH PB11 setting for SPI0_I2SMCLK*/
#define SYS_GPB_MFPH_PB11MFP_BPWM1_CH0   (0x0aUL<<SYS_GPB_MFPH_PB11MFP_Pos)/*!< GPB_MFPH PB11 setting for BPWM1_CH0  */
#define SYS_GPB_MFPH_PB11MFP_SPI3_CLK    (0x0bUL<<SYS_GPB_MFPH_PB11MFP_Pos)/*!< GPB_MFPH PB11 setting for SPI3_CLK   */

/* PB.12 MFP */
#define SYS_GPB_MFPH_PB12MFP_GPIO        (0x00UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for GPIO       */
#define SYS_GPB_MFPH_PB12MFP_EADC0_CH12  (0x01UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for EADC0_CH12 */
#define SYS_GPB_MFPH_PB12MFP_DAC0_OUT    (0x01UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for DAC0_OUT   */
#define SYS_GPB_MFPH_PB12MFP_ACMP0_P2    (0x01UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for ACMP0_P2   */
#define SYS_GPB_MFPH_PB12MFP_ACMP1_P2    (0x01UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for ACMP1_P2   */
#define SYS_GPB_MFPH_PB12MFP_EBI_AD15    (0x02UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for EBI_AD15   */
#define SYS_GPB_MFPH_PB12MFP_SC1_CLK     (0x03UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for SC1_CLK    */
#define SYS_GPB_MFPH_PB12MFP_SPI0_MOSI   (0x04UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for SPI0_MOSI  */
#define SYS_GPB_MFPH_PB12MFP_USCI0_CLK   (0x05UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for USCI0_CLK  */
#define SYS_GPB_MFPH_PB12MFP_UART0_RXD   (0x06UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for UART0_RXD  */
#define SYS_GPB_MFPH_PB12MFP_UART3_nCTS  (0x07UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for UART3_nCTS */
#define SYS_GPB_MFPH_PB12MFP_I2C2_SDA    (0x08UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for I2C2_SDA   */
#define SYS_GPB_MFPH_PB12MFP_SD0_nCD     (0x09UL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for SD0_nCD    */
#define SYS_GPB_MFPH_PB12MFP_EPWM1_CH3   (0x0bUL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for EPWM1_CH3  */
#define SYS_GPB_MFPH_PB12MFP_TM3_EXT     (0x0dUL<<SYS_GPB_MFPH_PB12MFP_Pos)/*!< GPB_MFPH PB12 setting for TM3_EXT    */

/* PB.13 MFP */
#define SYS_GPB_MFPH_PB13MFP_GPIO        (0x00UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for GPIO       */
#define SYS_GPB_MFPH_PB13MFP_EADC0_CH13  (0x01UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for EADC0_CH13 */
#define SYS_GPB_MFPH_PB13MFP_DAC1_OUT    (0x01UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for DAC1_OUT   */
#define SYS_GPB_MFPH_PB13MFP_ACMP0_P3    (0x01UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for ACMP0_P3   */
#define SYS_GPB_MFPH_PB13MFP_ACMP1_P3    (0x01UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for ACMP1_P3   */
#define SYS_GPB_MFPH_PB13MFP_EBI_AD14    (0x02UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for EBI_AD14   */
#define SYS_GPB_MFPH_PB13MFP_SC1_DAT     (0x03UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for SC1_DAT    */
#define SYS_GPB_MFPH_PB13MFP_SPI0_MISO   (0x04UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for SPI0_MISO  */
#define SYS_GPB_MFPH_PB13MFP_USCI0_DAT0  (0x05UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for USCI0_DAT0 */
#define SYS_GPB_MFPH_PB13MFP_UART0_TXD   (0x06UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for UART0_TXD  */
#define SYS_GPB_MFPH_PB13MFP_UART3_nRTS  (0x07UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for UART3_nRTS */
#define SYS_GPB_MFPH_PB13MFP_I2C2_SCL    (0x08UL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for I2C2_SCL   */
#define SYS_GPB_MFPH_PB13MFP_EPWM1_CH2   (0x0bUL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for EPWM1_CH2  */
#define SYS_GPB_MFPH_PB13MFP_TM2_EXT     (0x0dUL<<SYS_GPB_MFPH_PB13MFP_Pos)/*!< GPB_MFPH PB13 setting for TM2_EXT    */

/* PB.14 MFP */
#define SYS_GPB_MFPH_PB14MFP_GPIO        (0x00UL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for GPIO       */
#define SYS_GPB_MFPH_PB14MFP_EADC0_CH14  (0x01UL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for EADC0_CH14 */
#define SYS_GPB_MFPH_PB14MFP_EBI_AD13    (0x02UL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for EBI_AD13   */
#define SYS_GPB_MFPH_PB14MFP_SC1_RST     (0x03UL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for SC1_RST    */
#define SYS_GPB_MFPH_PB14MFP_SPI0_CLK    (0x04UL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for SPI0_CLK   */
#define SYS_GPB_MFPH_PB14MFP_USCI0_DAT1  (0x05UL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for USCI0_DAT1 */
#define SYS_GPB_MFPH_PB14MFP_UART0_nRTS  (0x06UL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for UART0_nRTS */
#define SYS_GPB_MFPH_PB14MFP_UART3_RXD   (0x07UL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for UART3_RXD  */
#define SYS_GPB_MFPH_PB14MFP_I2C2_SMBSUS (0x08UL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for I2C2_SMBSUS*/
#define SYS_GPB_MFPH_PB14MFP_EPWM1_CH1   (0x0bUL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for EPWM1_CH1  */
#define SYS_GPB_MFPH_PB14MFP_TM1_EXT     (0x0dUL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for TM1_EXT    */
#define SYS_GPB_MFPH_PB14MFP_CLKO        (0x0eUL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for CLKO       */
#define SYS_GPB_MFPH_PB14MFP_USB_VBUS_ST (0x0fUL<<SYS_GPB_MFPH_PB14MFP_Pos)/*!< GPB_MFPH PB14 setting for USB_VBUS_ST*/

/* PB.15 MFP */
#define SYS_GPB_MFPH_PB15MFP_GPIO        (0x00UL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for GPIO       */
#define SYS_GPB_MFPH_PB15MFP_EADC0_CH15  (0x01UL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for EADC0_CH15 */
#define SYS_GPB_MFPH_PB15MFP_EBI_AD12    (0x02UL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for EBI_AD12   */
#define SYS_GPB_MFPH_PB15MFP_SC1_PWR     (0x03UL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for SC1_PWR    */
#define SYS_GPB_MFPH_PB15MFP_SPI0_SS     (0x04UL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for SPI0_SS    */
#define SYS_GPB_MFPH_PB15MFP_USCI0_CTL1  (0x05UL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for USCI0_CTL1 */
#define SYS_GPB_MFPH_PB15MFP_UART0_nCTS  (0x06UL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for UART0_nCTS */
#define SYS_GPB_MFPH_PB15MFP_UART3_TXD   (0x07UL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for UART3_TXD  */
#define SYS_GPB_MFPH_PB15MFP_I2C2_SMBAL  (0x08UL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for I2C2_SMBAL */
#define SYS_GPB_MFPH_PB15MFP_EPWM1_CH0   (0x0bUL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for EPWM1_CH0  */
#define SYS_GPB_MFPH_PB15MFP_TM0_EXT     (0x0dUL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for TM0_EXT    */
#define SYS_GPB_MFPH_PB15MFP_USB_VBUS_EN (0x0eUL<<SYS_GPB_MFPH_PB15MFP_Pos)/*!< GPB_MFPH PB15 setting for USB_VBUS_EN*/

/* PC.0 MFP */
#define SYS_GPC_MFPL_PC0MFP_GPIO         (0x00UL<<SYS_GPC_MFPL_PC0MFP_Pos) /*!< GPC_MFPL PC0 setting for GPIO        */
#define SYS_GPC_MFPL_PC0MFP_EBI_AD0      (0x02UL<<SYS_GPC_MFPL_PC0MFP_Pos) /*!< GPC_MFPL PC0 setting for EBI_AD0     */
#define SYS_GPC_MFPL_PC0MFP_QSPI0_MOSI0  (0x04UL<<SYS_GPC_MFPL_PC0MFP_Pos) /*!< GPC_MFPL PC0 setting for QSPI0_MOSI0 */
#define SYS_GPC_MFPL_PC0MFP_SC1_CLK      (0x05UL<<SYS_GPC_MFPL_PC0MFP_Pos) /*!< GPC_MFPL PC0 setting for SC1_CLK     */
#define SYS_GPC_MFPL_PC0MFP_I2S0_LRCK    (0x06UL<<SYS_GPC_MFPL_PC0MFP_Pos) /*!< GPC_MFPL PC0 setting for I2S0_LRCK   */
#define SYS_GPC_MFPL_PC0MFP_SPI1_SS      (0x07UL<<SYS_GPC_MFPL_PC0MFP_Pos) /*!< GPC_MFPL PC0 setting for SPI1_SS     */
#define SYS_GPC_MFPL_PC0MFP_UART2_RXD    (0x08UL<<SYS_GPC_MFPL_PC0MFP_Pos) /*!< GPC_MFPL PC0 setting for UART2_RXD   */
#define SYS_GPC_MFPL_PC0MFP_I2C0_SDA     (0x09UL<<SYS_GPC_MFPL_PC0MFP_Pos) /*!< GPC_MFPL PC0 setting for I2C0_SDA    */
#define SYS_GPC_MFPL_PC0MFP_EPWM1_CH5    (0x0cUL<<SYS_GPC_MFPL_PC0MFP_Pos) /*!< GPC_MFPL PC0 setting for EPWM1_CH5   */
#define SYS_GPC_MFPL_PC0MFP_ACMP1_O      (0x0eUL<<SYS_GPC_MFPL_PC0MFP_Pos) /*!< GPC_MFPL PC0 setting for ACMP1_O     */

/* PC.1 MFP */
#define SYS_GPC_MFPL_PC1MFP_GPIO         (0x00UL<<SYS_GPC_MFPL_PC1MFP_Pos) /*!< GPC_MFPL PC1 setting for GPIO        */
#define SYS_GPC_MFPL_PC1MFP_EBI_AD1      (0x02UL<<SYS_GPC_MFPL_PC1MFP_Pos) /*!< GPC_MFPL PC1 setting for EBI_AD1     */
#define SYS_GPC_MFPL_PC1MFP_QSPI0_MISO0  (0x04UL<<SYS_GPC_MFPL_PC1MFP_Pos) /*!< GPC_MFPL PC1 setting for QSPI0_MISO0 */
#define SYS_GPC_MFPL_PC1MFP_SC1_DAT      (0x05UL<<SYS_GPC_MFPL_PC1MFP_Pos) /*!< GPC_MFPL PC1 setting for SC1_DAT     */
#define SYS_GPC_MFPL_PC1MFP_I2S0_DO      (0x06UL<<SYS_GPC_MFPL_PC1MFP_Pos) /*!< GPC_MFPL PC1 setting for I2S0_DO     */
#define SYS_GPC_MFPL_PC1MFP_SPI1_CLK     (0x07UL<<SYS_GPC_MFPL_PC1MFP_Pos) /*!< GPC_MFPL PC1 setting for SPI1_CLK    */
#define SYS_GPC_MFPL_PC1MFP_UART2_TXD    (0x08UL<<SYS_GPC_MFPL_PC1MFP_Pos) /*!< GPC_MFPL PC1 setting for UART2_TXD   */
#define SYS_GPC_MFPL_PC1MFP_I2C0_SCL     (0x09UL<<SYS_GPC_MFPL_PC1MFP_Pos) /*!< GPC_MFPL PC1 setting for I2C0_SCL    */
#define SYS_GPC_MFPL_PC1MFP_EPWM1_CH4    (0x0cUL<<SYS_GPC_MFPL_PC1MFP_Pos) /*!< GPC_MFPL PC1 setting for EPWM1_CH4   */
#define SYS_GPC_MFPL_PC1MFP_ACMP0_O      (0x0eUL<<SYS_GPC_MFPL_PC1MFP_Pos) /*!< GPC_MFPL PC1 setting for ACMP0_O     */

/* PC.2 MFP */
#define SYS_GPC_MFPL_PC2MFP_GPIO         (0x00UL<<SYS_GPC_MFPL_PC2MFP_Pos) /*!< GPC_MFPL PC2 setting for GPIO        */
#define SYS_GPC_MFPL_PC2MFP_EBI_AD2      (0x02UL<<SYS_GPC_MFPL_PC2MFP_Pos) /*!< GPC_MFPL PC2 setting for EBI_AD2     */
#define SYS_GPC_MFPL_PC2MFP_QSPI0_CLK    (0x04UL<<SYS_GPC_MFPL_PC2MFP_Pos) /*!< GPC_MFPL PC2 setting for QSPI0_CLK   */
#define SYS_GPC_MFPL_PC2MFP_SC1_RST      (0x05UL<<SYS_GPC_MFPL_PC2MFP_Pos) /*!< GPC_MFPL PC2 setting for SC1_RST     */
#define SYS_GPC_MFPL_PC2MFP_I2S0_DI      (0x06UL<<SYS_GPC_MFPL_PC2MFP_Pos) /*!< GPC_MFPL PC2 setting for I2S0_DI     */
#define SYS_GPC_MFPL_PC2MFP_SPI1_MOSI    (0x07UL<<SYS_GPC_MFPL_PC2MFP_Pos) /*!< GPC_MFPL PC2 setting for SPI1_MOSI   */
#define SYS_GPC_MFPL_PC2MFP_UART2_nCTS   (0x08UL<<SYS_GPC_MFPL_PC2MFP_Pos) /*!< GPC_MFPL PC2 setting for UART2_nCTS  */
#define SYS_GPC_MFPL_PC2MFP_I2C0_SMBSUS  (0x09UL<<SYS_GPC_MFPL_PC2MFP_Pos) /*!< GPC_MFPL PC2 setting for I2C0_SMBSUS */
#define SYS_GPC_MFPL_PC2MFP_UART3_RXD    (0x0bUL<<SYS_GPC_MFPL_PC2MFP_Pos) /*!< GPC_MFPL PC2 setting for UART3_RXD   */
#define SYS_GPC_MFPL_PC2MFP_EPWM1_CH3    (0x0cUL<<SYS_GPC_MFPL_PC2MFP_Pos) /*!< GPC_MFPL PC2 setting for EPWM1_CH3   */

/* PC.3 MFP */
#define SYS_GPC_MFPL_PC3MFP_GPIO         (0x00UL<<SYS_GPC_MFPL_PC3MFP_Pos) /*!< GPC_MFPL PC3 setting for GPIO        */
#define SYS_GPC_MFPL_PC3MFP_EBI_AD3      (0x02UL<<SYS_GPC_MFPL_PC3MFP_Pos) /*!< GPC_MFPL PC3 setting for EBI_AD3     */
#define SYS_GPC_MFPL_PC3MFP_QSPI0_SS     (0x04UL<<SYS_GPC_MFPL_PC3MFP_Pos) /*!< GPC_MFPL PC3 setting for QSPI0_SS    */
#define SYS_GPC_MFPL_PC3MFP_SC1_PWR      (0x05UL<<SYS_GPC_MFPL_PC3MFP_Pos) /*!< GPC_MFPL PC3 setting for SC1_PWR     */
#define SYS_GPC_MFPL_PC3MFP_I2S0_MCLK    (0x06UL<<SYS_GPC_MFPL_PC3MFP_Pos) /*!< GPC_MFPL PC3 setting for I2S0_MCLK   */
#define SYS_GPC_MFPL_PC3MFP_SPI1_MISO    (0x07UL<<SYS_GPC_MFPL_PC3MFP_Pos) /*!< GPC_MFPL PC3 setting for SPI1_MISO   */
#define SYS_GPC_MFPL_PC3MFP_UART2_nRTS   (0x08UL<<SYS_GPC_MFPL_PC3MFP_Pos) /*!< GPC_MFPL PC3 setting for UART2_nRTS  */
#define SYS_GPC_MFPL_PC3MFP_I2C0_SMBAL   (0x09UL<<SYS_GPC_MFPL_PC3MFP_Pos) /*!< GPC_MFPL PC3 setting for I2C0_SMBAL  */
#define SYS_GPC_MFPL_PC3MFP_UART3_TXD    (0x0bUL<<SYS_GPC_MFPL_PC3MFP_Pos) /*!< GPC_MFPL PC3 setting for UART3_TXD   */
#define SYS_GPC_MFPL_PC3MFP_EPWM1_CH2    (0x0cUL<<SYS_GPC_MFPL_PC3MFP_Pos) /*!< GPC_MFPL PC3 setting for EPWM1_CH2   */

/* PC.4 MFP */
#define SYS_GPC_MFPL_PC4MFP_GPIO         (0x00UL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for GPIO        */
#define SYS_GPC_MFPL_PC4MFP_EBI_AD4      (0x02UL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for EBI_AD4     */
#define SYS_GPC_MFPL_PC4MFP_QSPI0_MOSI1  (0x04UL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for QSPI0_MOSI1 */
#define SYS_GPC_MFPL_PC4MFP_SC1_nCD      (0x05UL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for SC1_nCD     */
#define SYS_GPC_MFPL_PC4MFP_I2S0_BCLK    (0x06UL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for I2S0_BCLK   */
#define SYS_GPC_MFPL_PC4MFP_SPI1_I2SMCLK (0x07UL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for SPI1_I2SMCLK*/
#define SYS_GPC_MFPL_PC4MFP_UART2_RXD    (0x08UL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for UART2_RXD   */
#define SYS_GPC_MFPL_PC4MFP_I2C1_SDA     (0x09UL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for I2C1_SDA    */
#define SYS_GPC_MFPL_PC4MFP_CAN0_RXD     (0x0aUL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for CAN0_RXD    */
#define SYS_GPC_MFPL_PC4MFP_UART4_RXD    (0x0bUL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for UART4_RXD   */
#define SYS_GPC_MFPL_PC4MFP_EPWM1_CH1    (0x0cUL<<SYS_GPC_MFPL_PC4MFP_Pos) /*!< GPC_MFPL PC4 setting for EPWM1_CH1   */

/* PC.5 MFP */
#define SYS_GPC_MFPL_PC5MFP_GPIO         (0x00UL<<SYS_GPC_MFPL_PC5MFP_Pos) /*!< GPC_MFPL PC5 setting for GPIO        */
#define SYS_GPC_MFPL_PC5MFP_EBI_AD5      (0x02UL<<SYS_GPC_MFPL_PC5MFP_Pos) /*!< GPC_MFPL PC5 setting for EBI_AD5     */
#define SYS_GPC_MFPL_PC5MFP_QSPI0_MISO1  (0x04UL<<SYS_GPC_MFPL_PC5MFP_Pos) /*!< GPC_MFPL PC5 setting for QSPI0_MISO1 */
#define SYS_GPC_MFPL_PC5MFP_UART2_TXD    (0x08UL<<SYS_GPC_MFPL_PC5MFP_Pos) /*!< GPC_MFPL PC5 setting for UART2_TXD   */
#define SYS_GPC_MFPL_PC5MFP_I2C1_SCL     (0x09UL<<SYS_GPC_MFPL_PC5MFP_Pos) /*!< GPC_MFPL PC5 setting for I2C1_SCL    */
#define SYS_GPC_MFPL_PC5MFP_CAN0_TXD     (0x0aUL<<SYS_GPC_MFPL_PC5MFP_Pos) /*!< GPC_MFPL PC5 setting for CAN0_TXD    */
#define SYS_GPC_MFPL_PC5MFP_UART4_TXD    (0x0bUL<<SYS_GPC_MFPL_PC5MFP_Pos) /*!< GPC_MFPL PC5 setting for UART4_TXD   */
#define SYS_GPC_MFPL_PC5MFP_EPWM1_CH0    (0x0cUL<<SYS_GPC_MFPL_PC5MFP_Pos) /*!< GPC_MFPL PC5 setting for EPWM1_CH0   */

/* PC.6 MFP */
#define SYS_GPC_MFPL_PC6MFP_GPIO         (0x00UL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for GPIO        */
#define SYS_GPC_MFPL_PC6MFP_EBI_AD8      (0x02UL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for EBI_AD8     */
#define SYS_GPC_MFPL_PC6MFP_SPI1_MOSI    (0x04UL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for SPI1_MOSI   */
#define SYS_GPC_MFPL_PC6MFP_UART4_RXD    (0x05UL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for UART4_RXD   */
#define SYS_GPC_MFPL_PC6MFP_SC2_RST      (0x06UL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for SC2_RST     */
#define SYS_GPC_MFPL_PC6MFP_UART0_nRTS   (0x07UL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for UART0_nRTS  */
#define SYS_GPC_MFPL_PC6MFP_I2C1_SMBSUS  (0x08UL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for I2C1_SMBSUS */
#define SYS_GPC_MFPL_PC6MFP_EPWM1_CH3    (0x0bUL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for EPWM1_CH3   */
#define SYS_GPC_MFPL_PC6MFP_BPWM1_CH1    (0x0cUL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for BPWM1_CH1   */
#define SYS_GPC_MFPL_PC6MFP_TM1          (0x0eUL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for TM1         */
#define SYS_GPC_MFPL_PC6MFP_INT2         (0x0fUL<<SYS_GPC_MFPL_PC6MFP_Pos) /*!< GPC_MFPL PC6 setting for INT2        */

/* PC.7 MFP */
#define SYS_GPC_MFPL_PC7MFP_GPIO         (0x00UL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for GPIO        */
#define SYS_GPC_MFPL_PC7MFP_EBI_AD9      (0x02UL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for EBI_AD9     */
#define SYS_GPC_MFPL_PC7MFP_SPI1_MISO    (0x04UL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for SPI1_MISO   */
#define SYS_GPC_MFPL_PC7MFP_UART4_TXD    (0x05UL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for UART4_TXD   */
#define SYS_GPC_MFPL_PC7MFP_SC2_PWR      (0x06UL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for SC2_PWR     */
#define SYS_GPC_MFPL_PC7MFP_UART0_nCTS   (0x07UL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for UART0_nCTS  */
#define SYS_GPC_MFPL_PC7MFP_I2C1_SMBAL   (0x08UL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for I2C1_SMBAL  */
#define SYS_GPC_MFPL_PC7MFP_EPWM1_CH2    (0x0bUL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for EPWM1_CH2   */
#define SYS_GPC_MFPL_PC7MFP_BPWM1_CH0    (0x0cUL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for BPWM1_CH0   */
#define SYS_GPC_MFPL_PC7MFP_TM0          (0x0eUL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for TM0         */
#define SYS_GPC_MFPL_PC7MFP_INT3         (0x0fUL<<SYS_GPC_MFPL_PC7MFP_Pos) /*!< GPC_MFPL PC7 setting for INT3        */

/* PC.8 MFP */
#define SYS_GPC_MFPH_PC8MFP_GPIO         (0x00UL<<SYS_GPC_MFPH_PC8MFP_Pos) /*!< GPC_MFPH PC8 setting for GPIO        */
#define SYS_GPC_MFPH_PC8MFP_EBI_ADR16    (0x02UL<<SYS_GPC_MFPH_PC8MFP_Pos) /*!< GPC_MFPH PC8 setting for EBI_ADR16   */
#define SYS_GPC_MFPH_PC8MFP_I2C0_SDA     (0x04UL<<SYS_GPC_MFPH_PC8MFP_Pos) /*!< GPC_MFPH PC8 setting for I2C0_SDA    */
#define SYS_GPC_MFPH_PC8MFP_UART4_nCTS   (0x05UL<<SYS_GPC_MFPH_PC8MFP_Pos) /*!< GPC_MFPH PC8 setting for UART4_nCTS  */
#define SYS_GPC_MFPH_PC8MFP_UART1_RXD    (0x08UL<<SYS_GPC_MFPH_PC8MFP_Pos) /*!< GPC_MFPH PC8 setting for UART1_RXD   */
#define SYS_GPC_MFPH_PC8MFP_EPWM1_CH1    (0x0bUL<<SYS_GPC_MFPH_PC8MFP_Pos) /*!< GPC_MFPH PC8 setting for EPWM1_CH1   */
#define SYS_GPC_MFPH_PC8MFP_BPWM1_CH4    (0x0cUL<<SYS_GPC_MFPH_PC8MFP_Pos) /*!< GPC_MFPH PC8 setting for BPWM1_CH4   */

/* PC.9 MFP */
#define SYS_GPC_MFPH_PC9MFP_GPIO         (0x00UL<<SYS_GPC_MFPH_PC9MFP_Pos) /*!< GPC_MFPH PC9 setting for GPIO        */
#define SYS_GPC_MFPH_PC9MFP_EBI_ADR7     (0x02UL<<SYS_GPC_MFPH_PC9MFP_Pos) /*!< GPC_MFPH PC9 setting for EBI_ADR7    */
#define SYS_GPC_MFPH_PC9MFP_SPI3_SS      (0x06UL<<SYS_GPC_MFPH_PC9MFP_Pos) /*!< GPC_MFPH PC9 setting for SPI3_SS     */
#define SYS_GPC_MFPH_PC9MFP_UART3_RXD    (0x07UL<<SYS_GPC_MFPH_PC9MFP_Pos) /*!< GPC_MFPH PC9 setting for UART3_RXD   */
#define SYS_GPC_MFPH_PC9MFP_EPWM1_CH3    (0x0cUL<<SYS_GPC_MFPH_PC9MFP_Pos) /*!< GPC_MFPH PC9 setting for EPWM1_CH3   */

/* PC.10 MFP */
#define SYS_GPC_MFPH_PC10MFP_GPIO        (0x00UL<<SYS_GPC_MFPH_PC10MFP_Pos)/*!< GPC_MFPH PC10 setting for GPIO       */
#define SYS_GPC_MFPH_PC10MFP_EBI_ADR6    (0x02UL<<SYS_GPC_MFPH_PC10MFP_Pos)/*!< GPC_MFPH PC10 setting for EBI_ADR6   */
#define SYS_GPC_MFPH_PC10MFP_SPI3_CLK    (0x06UL<<SYS_GPC_MFPH_PC10MFP_Pos)/*!< GPC_MFPH PC10 setting for SPI3_CLK   */
#define SYS_GPC_MFPH_PC10MFP_UART3_TXD   (0x07UL<<SYS_GPC_MFPH_PC10MFP_Pos)/*!< GPC_MFPH PC10 setting for UART3_TXD  */
#define SYS_GPC_MFPH_PC10MFP_ECAP1_IC0   (0x0bUL<<SYS_GPC_MFPH_PC10MFP_Pos)/*!< GPC_MFPH PC10 setting for ECAP1_IC0  */
#define SYS_GPC_MFPH_PC10MFP_EPWM1_CH2   (0x0cUL<<SYS_GPC_MFPH_PC10MFP_Pos)/*!< GPC_MFPH PC10 setting for EPWM1_CH2  */

/* PC.11 MFP */
#define SYS_GPC_MFPH_PC11MFP_GPIO        (0x00UL<<SYS_GPC_MFPH_PC11MFP_Pos)/*!< GPC_MFPH PC11 setting for GPIO       */
#define SYS_GPC_MFPH_PC11MFP_EBI_ADR5    (0x02UL<<SYS_GPC_MFPH_PC11MFP_Pos)/*!< GPC_MFPH PC11 setting for EBI_ADR5   */
#define SYS_GPC_MFPH_PC11MFP_UART0_RXD   (0x03UL<<SYS_GPC_MFPH_PC11MFP_Pos)/*!< GPC_MFPH PC11 setting for UART0_RXD  */
#define SYS_GPC_MFPH_PC11MFP_I2C0_SDA    (0x04UL<<SYS_GPC_MFPH_PC11MFP_Pos)/*!< GPC_MFPH PC11 setting for I2C0_SDA   */
#define SYS_GPC_MFPH_PC11MFP_SPI3_MOSI   (0x06UL<<SYS_GPC_MFPH_PC11MFP_Pos)/*!< GPC_MFPH PC11 setting for SPI3_MOSI  */
#define SYS_GPC_MFPH_PC11MFP_ECAP1_IC1   (0x0bUL<<SYS_GPC_MFPH_PC11MFP_Pos)/*!< GPC_MFPH PC11 setting for ECAP1_IC1  */
#define SYS_GPC_MFPH_PC11MFP_EPWM1_CH1   (0x0cUL<<SYS_GPC_MFPH_PC11MFP_Pos)/*!< GPC_MFPH PC11 setting for EPWM1_CH1  */
#define SYS_GPC_MFPH_PC11MFP_ACMP1_O     (0x0eUL<<SYS_GPC_MFPH_PC11MFP_Pos)/*!< GPC_MFPH PC11 setting for ACMP1_O    */

/* PC.12 MFP */
#define SYS_GPC_MFPH_PC12MFP_GPIO        (0x00UL<<SYS_GPC_MFPH_PC12MFP_Pos)/*!< GPC_MFPH PC12 setting for GPIO       */
#define SYS_GPC_MFPH_PC12MFP_EBI_ADR4    (0x02UL<<SYS_GPC_MFPH_PC12MFP_Pos)/*!< GPC_MFPH PC12 setting for EBI_ADR4   */
#define SYS_GPC_MFPH_PC12MFP_UART0_TXD   (0x03UL<<SYS_GPC_MFPH_PC12MFP_Pos)/*!< GPC_MFPH PC12 setting for UART0_TXD  */
#define SYS_GPC_MFPH_PC12MFP_I2C0_SCL    (0x04UL<<SYS_GPC_MFPH_PC12MFP_Pos)/*!< GPC_MFPH PC12 setting for I2C0_SCL   */
#define SYS_GPC_MFPH_PC12MFP_SPI3_MISO   (0x06UL<<SYS_GPC_MFPH_PC12MFP_Pos)/*!< GPC_MFPH PC12 setting for SPI3_MISO  */
#define SYS_GPC_MFPH_PC12MFP_SC0_nCD     (0x09UL<<SYS_GPC_MFPH_PC12MFP_Pos)/*!< GPC_MFPH PC12 setting for SC0_nCD    */
#define SYS_GPC_MFPH_PC12MFP_ECAP1_IC2   (0x0bUL<<SYS_GPC_MFPH_PC12MFP_Pos)/*!< GPC_MFPH PC12 setting for ECAP1_IC2  */
#define SYS_GPC_MFPH_PC12MFP_EPWM1_CH0   (0x0cUL<<SYS_GPC_MFPH_PC12MFP_Pos)/*!< GPC_MFPH PC12 setting for EPWM1_CH0  */
#define SYS_GPC_MFPH_PC12MFP_ACMP0_O     (0x0eUL<<SYS_GPC_MFPH_PC12MFP_Pos)/*!< GPC_MFPH PC12 setting for ACMP0_O    */

/* PC.13 MFP */
#define SYS_GPC_MFPH_PC13MFP_GPIO        (0x00UL<<SYS_GPC_MFPH_PC13MFP_Pos)/*!< GPC_MFPH PC13 setting for GPIO       */
#define SYS_GPC_MFPH_PC13MFP_EBI_ADR10   (0x02UL<<SYS_GPC_MFPH_PC13MFP_Pos)/*!< GPC_MFPH PC13 setting for EBI_ADR10  */
#define SYS_GPC_MFPH_PC13MFP_SC2_nCD     (0x03UL<<SYS_GPC_MFPH_PC13MFP_Pos)/*!< GPC_MFPH PC13 setting for SC2_nCD    */
#define SYS_GPC_MFPH_PC13MFP_SPI2_I2SMCLK (0x04UL<<SYS_GPC_MFPH_PC13MFP_Pos)/*!< GPC_MFPH PC13 setting for SPI2_I2SMCLK*/
#define SYS_GPC_MFPH_PC13MFP_USCI0_CTL0  (0x06UL<<SYS_GPC_MFPH_PC13MFP_Pos)/*!< GPC_MFPH PC13 setting for USCI0_CTL0 */
#define SYS_GPC_MFPH_PC13MFP_UART2_TXD   (0x07UL<<SYS_GPC_MFPH_PC13MFP_Pos)/*!< GPC_MFPH PC13 setting for UART2_TXD  */
#define SYS_GPC_MFPH_PC13MFP_BPWM0_CH4   (0x09UL<<SYS_GPC_MFPH_PC13MFP_Pos)/*!< GPC_MFPH PC13 setting for BPWM0_CH4  */
#define SYS_GPC_MFPH_PC13MFP_CLKO        (0x0dUL<<SYS_GPC_MFPH_PC13MFP_Pos)/*!< GPC_MFPH PC13 setting for CLKO       */
#define SYS_GPC_MFPH_PC13MFP_EADC0_ST    (0x0eUL<<SYS_GPC_MFPH_PC13MFP_Pos)/*!< GPC_MFPH PC13 setting for EADC0_ST   */

/* PD.0 MFP */
#define SYS_GPD_MFPL_PD0MFP_GPIO         (0x00UL<<SYS_GPD_MFPL_PD0MFP_Pos) /*!< GPD_MFPL PD0 setting for GPIO        */
#define SYS_GPD_MFPL_PD0MFP_EBI_AD13     (0x02UL<<SYS_GPD_MFPL_PD0MFP_Pos) /*!< GPD_MFPL PD0 setting for EBI_AD13    */
#define SYS_GPD_MFPL_PD0MFP_USCI0_CLK    (0x03UL<<SYS_GPD_MFPL_PD0MFP_Pos) /*!< GPD_MFPL PD0 setting for USCI0_CLK   */
#define SYS_GPD_MFPL_PD0MFP_SPI0_MOSI    (0x04UL<<SYS_GPD_MFPL_PD0MFP_Pos) /*!< GPD_MFPL PD0 setting for SPI0_MOSI   */
#define SYS_GPD_MFPL_PD0MFP_UART3_RXD    (0x05UL<<SYS_GPD_MFPL_PD0MFP_Pos) /*!< GPD_MFPL PD0 setting for UART3_RXD   */
#define SYS_GPD_MFPL_PD0MFP_I2C2_SDA     (0x06UL<<SYS_GPD_MFPL_PD0MFP_Pos) /*!< GPD_MFPL PD0 setting for I2C2_SDA    */
#define SYS_GPD_MFPL_PD0MFP_SC2_CLK      (0x07UL<<SYS_GPD_MFPL_PD0MFP_Pos) /*!< GPD_MFPL PD0 setting for SC2_CLK     */
#define SYS_GPD_MFPL_PD0MFP_TM2          (0x0eUL<<SYS_GPD_MFPL_PD0MFP_Pos) /*!< GPD_MFPL PD0 setting for TM2         */

/* PD.1 MFP */
#define SYS_GPD_MFPL_PD1MFP_GPIO         (0x00UL<<SYS_GPD_MFPL_PD1MFP_Pos) /*!< GPD_MFPL PD1 setting for GPIO        */
#define SYS_GPD_MFPL_PD1MFP_EBI_AD12     (0x02UL<<SYS_GPD_MFPL_PD1MFP_Pos) /*!< GPD_MFPL PD1 setting for EBI_AD12    */
#define SYS_GPD_MFPL_PD1MFP_USCI0_DAT0   (0x03UL<<SYS_GPD_MFPL_PD1MFP_Pos) /*!< GPD_MFPL PD1 setting for USCI0_DAT0  */
#define SYS_GPD_MFPL_PD1MFP_SPI0_MISO    (0x04UL<<SYS_GPD_MFPL_PD1MFP_Pos) /*!< GPD_MFPL PD1 setting for SPI0_MISO   */
#define SYS_GPD_MFPL_PD1MFP_UART3_TXD    (0x05UL<<SYS_GPD_MFPL_PD1MFP_Pos) /*!< GPD_MFPL PD1 setting for UART3_TXD   */
#define SYS_GPD_MFPL_PD1MFP_I2C2_SCL     (0x06UL<<SYS_GPD_MFPL_PD1MFP_Pos) /*!< GPD_MFPL PD1 setting for I2C2_SCL    */
#define SYS_GPD_MFPL_PD1MFP_SC2_DAT      (0x07UL<<SYS_GPD_MFPL_PD1MFP_Pos) /*!< GPD_MFPL PD1 setting for SC2_DAT     */

/* PD.2 MFP */
#define SYS_GPD_MFPL_PD2MFP_GPIO         (0x00UL<<SYS_GPD_MFPL_PD2MFP_Pos) /*!< GPD_MFPL PD2 setting for GPIO        */
#define SYS_GPD_MFPL_PD2MFP_EBI_AD11     (0x02UL<<SYS_GPD_MFPL_PD2MFP_Pos) /*!< GPD_MFPL PD2 setting for EBI_AD11    */
#define SYS_GPD_MFPL_PD2MFP_USCI0_DAT1   (0x03UL<<SYS_GPD_MFPL_PD2MFP_Pos) /*!< GPD_MFPL PD2 setting for USCI0_DAT1  */
#define SYS_GPD_MFPL_PD2MFP_SPI0_CLK     (0x04UL<<SYS_GPD_MFPL_PD2MFP_Pos) /*!< GPD_MFPL PD2 setting for SPI0_CLK    */
#define SYS_GPD_MFPL_PD2MFP_UART3_nCTS   (0x05UL<<SYS_GPD_MFPL_PD2MFP_Pos) /*!< GPD_MFPL PD2 setting for UART3_nCTS  */
#define SYS_GPD_MFPL_PD2MFP_SC2_RST      (0x07UL<<SYS_GPD_MFPL_PD2MFP_Pos) /*!< GPD_MFPL PD2 setting for SC2_RST     */
#define SYS_GPD_MFPL_PD2MFP_UART0_RXD    (0x09UL<<SYS_GPD_MFPL_PD2MFP_Pos) /*!< GPD_MFPL PD2 setting for UART0_RXD   */

/* PD.3 MFP */
#define SYS_GPD_MFPL_PD3MFP_GPIO         (0x00UL<<SYS_GPD_MFPL_PD3MFP_Pos) /*!< GPD_MFPL PD3 setting for GPIO        */
#define SYS_GPD_MFPL_PD3MFP_EBI_AD10     (0x02UL<<SYS_GPD_MFPL_PD3MFP_Pos) /*!< GPD_MFPL PD3 setting for EBI_AD10    */
#define SYS_GPD_MFPL_PD3MFP_USCI0_CTL1   (0x03UL<<SYS_GPD_MFPL_PD3MFP_Pos) /*!< GPD_MFPL PD3 setting for USCI0_CTL1  */
#define SYS_GPD_MFPL_PD3MFP_SPI0_SS      (0x04UL<<SYS_GPD_MFPL_PD3MFP_Pos) /*!< GPD_MFPL PD3 setting for SPI0_SS     */
#define SYS_GPD_MFPL_PD3MFP_UART3_nRTS   (0x05UL<<SYS_GPD_MFPL_PD3MFP_Pos) /*!< GPD_MFPL PD3 setting for UART3_nRTS  */
#define SYS_GPD_MFPL_PD3MFP_USCI1_CTL0   (0x06UL<<SYS_GPD_MFPL_PD3MFP_Pos) /*!< GPD_MFPL PD3 setting for USCI1_CTL0  */
#define SYS_GPD_MFPL_PD3MFP_SC2_PWR      (0x07UL<<SYS_GPD_MFPL_PD3MFP_Pos) /*!< GPD_MFPL PD3 setting for SC2_PWR     */
#define SYS_GPD_MFPL_PD3MFP_SC1_nCD      (0x08UL<<SYS_GPD_MFPL_PD3MFP_Pos) /*!< GPD_MFPL PD3 setting for SC1_nCD     */
#define SYS_GPD_MFPL_PD3MFP_UART0_TXD    (0x09UL<<SYS_GPD_MFPL_PD3MFP_Pos) /*!< GPD_MFPL PD3 setting for UART0_TXD   */

/* PD.4 MFP */
#define SYS_GPD_MFPL_PD4MFP_GPIO         (0x00UL<<SYS_GPD_MFPL_PD4MFP_Pos) /*!< GPD_MFPL PD4 setting for GPIO        */
#define SYS_GPD_MFPL_PD4MFP_USCI0_CTL0   (0x03UL<<SYS_GPD_MFPL_PD4MFP_Pos) /*!< GPD_MFPL PD4 setting for USCI0_CTL0  */
#define SYS_GPD_MFPL_PD4MFP_I2C1_SDA     (0x04UL<<SYS_GPD_MFPL_PD4MFP_Pos) /*!< GPD_MFPL PD4 setting for I2C1_SDA    */
#define SYS_GPD_MFPL_PD4MFP_SPI1_SS      (0x05UL<<SYS_GPD_MFPL_PD4MFP_Pos) /*!< GPD_MFPL PD4 setting for SPI1_SS     */
#define SYS_GPD_MFPL_PD4MFP_USCI1_CTL1   (0x06UL<<SYS_GPD_MFPL_PD4MFP_Pos) /*!< GPD_MFPL PD4 setting for USCI1_CTL1  */
#define SYS_GPD_MFPL_PD4MFP_SC1_CLK      (0x08UL<<SYS_GPD_MFPL_PD4MFP_Pos) /*!< GPD_MFPL PD4 setting for SC1_CLK     */
#define SYS_GPD_MFPL_PD4MFP_USB_VBUS_ST  (0x0eUL<<SYS_GPD_MFPL_PD4MFP_Pos) /*!< GPD_MFPL PD4 setting for USB_VBUS_ST */

/* PD.5 MFP */
#define SYS_GPD_MFPL_PD5MFP_GPIO         (0x00UL<<SYS_GPD_MFPL_PD5MFP_Pos) /*!< GPD_MFPL PD5 setting for GPIO        */
#define SYS_GPD_MFPL_PD5MFP_I2C1_SCL     (0x04UL<<SYS_GPD_MFPL_PD5MFP_Pos) /*!< GPD_MFPL PD5 setting for I2C1_SCL    */
#define SYS_GPD_MFPL_PD5MFP_SPI1_CLK     (0x05UL<<SYS_GPD_MFPL_PD5MFP_Pos) /*!< GPD_MFPL PD5 setting for SPI1_CLK    */
#define SYS_GPD_MFPL_PD5MFP_USCI1_DAT0   (0x06UL<<SYS_GPD_MFPL_PD5MFP_Pos) /*!< GPD_MFPL PD5 setting for USCI1_DAT0  */
#define SYS_GPD_MFPL_PD5MFP_SC1_DAT      (0x08UL<<SYS_GPD_MFPL_PD5MFP_Pos) /*!< GPD_MFPL PD5 setting for SC1_DAT     */

/* PD.6 MFP */
#define SYS_GPD_MFPL_PD6MFP_GPIO         (0x00UL<<SYS_GPD_MFPL_PD6MFP_Pos) /*!< GPD_MFPL PD6 setting for GPIO        */
#define SYS_GPD_MFPL_PD6MFP_UART1_RXD    (0x03UL<<SYS_GPD_MFPL_PD6MFP_Pos) /*!< GPD_MFPL PD6 setting for UART1_RXD   */
#define SYS_GPD_MFPL_PD6MFP_I2C0_SDA     (0x04UL<<SYS_GPD_MFPL_PD6MFP_Pos) /*!< GPD_MFPL PD6 setting for I2C0_SDA    */
#define SYS_GPD_MFPL_PD6MFP_SPI1_MOSI    (0x05UL<<SYS_GPD_MFPL_PD6MFP_Pos) /*!< GPD_MFPL PD6 setting for SPI1_MOSI   */
#define SYS_GPD_MFPL_PD6MFP_USCI1_DAT1   (0x06UL<<SYS_GPD_MFPL_PD6MFP_Pos) /*!< GPD_MFPL PD6 setting for USCI1_DAT1  */
#define SYS_GPD_MFPL_PD6MFP_SC1_RST      (0x08UL<<SYS_GPD_MFPL_PD6MFP_Pos) /*!< GPD_MFPL PD6 setting for SC1_RST     */

/* PD.7 MFP */
#define SYS_GPD_MFPL_PD7MFP_GPIO         (0x00UL<<SYS_GPD_MFPL_PD7MFP_Pos) /*!< GPD_MFPL PD7 setting for GPIO        */
#define SYS_GPD_MFPL_PD7MFP_UART1_TXD    (0x03UL<<SYS_GPD_MFPL_PD7MFP_Pos) /*!< GPD_MFPL PD7 setting for UART1_TXD   */
#define SYS_GPD_MFPL_PD7MFP_I2C0_SCL     (0x04UL<<SYS_GPD_MFPL_PD7MFP_Pos) /*!< GPD_MFPL PD7 setting for I2C0_SCL    */
#define SYS_GPD_MFPL_PD7MFP_SPI1_MISO    (0x05UL<<SYS_GPD_MFPL_PD7MFP_Pos) /*!< GPD_MFPL PD7 setting for SPI1_MISO   */
#define SYS_GPD_MFPL_PD7MFP_USCI1_CLK    (0x06UL<<SYS_GPD_MFPL_PD7MFP_Pos) /*!< GPD_MFPL PD7 setting for USCI1_CLK   */
#define SYS_GPD_MFPL_PD7MFP_SC1_PWR      (0x08UL<<SYS_GPD_MFPL_PD7MFP_Pos) /*!< GPD_MFPL PD7 setting for SC1_PWR     */

/* PD.8 MFP */
#define SYS_GPD_MFPH_PD8MFP_GPIO         (0x00UL<<SYS_GPD_MFPH_PD8MFP_Pos) /*!< GPD_MFPH PD8 setting for GPIO        */
#define SYS_GPD_MFPH_PD8MFP_EBI_AD6      (0x02UL<<SYS_GPD_MFPH_PD8MFP_Pos) /*!< GPD_MFPH PD8 setting for EBI_AD6     */
#define SYS_GPD_MFPH_PD8MFP_I2C2_SDA     (0x03UL<<SYS_GPD_MFPH_PD8MFP_Pos) /*!< GPD_MFPH PD8 setting for I2C2_SDA    */
#define SYS_GPD_MFPH_PD8MFP_UART2_nRTS   (0x04UL<<SYS_GPD_MFPH_PD8MFP_Pos) /*!< GPD_MFPH PD8 setting for UART2_nRTS  */

/* PD.9 MFP */
#define SYS_GPD_MFPH_PD9MFP_GPIO         (0x00UL<<SYS_GPD_MFPH_PD9MFP_Pos) /*!< GPD_MFPH PD9 setting for GPIO        */
#define SYS_GPD_MFPH_PD9MFP_EBI_AD7      (0x02UL<<SYS_GPD_MFPH_PD9MFP_Pos) /*!< GPD_MFPH PD9 setting for EBI_AD7     */
#define SYS_GPD_MFPH_PD9MFP_I2C2_SCL     (0x03UL<<SYS_GPD_MFPH_PD9MFP_Pos) /*!< GPD_MFPH PD9 setting for I2C2_SCL    */
#define SYS_GPD_MFPH_PD9MFP_UART2_nCTS   (0x04UL<<SYS_GPD_MFPH_PD9MFP_Pos) /*!< GPD_MFPH PD9 setting for UART2_nCTS  */

/* PD.10 MFP */
#define SYS_GPD_MFPH_PD10MFP_GPIO        (0x00UL<<SYS_GPD_MFPH_PD10MFP_Pos)/*!< GPD_MFPH PD10 setting for GPIO       */
#define SYS_GPD_MFPH_PD10MFP_EBI_nCS2    (0x02UL<<SYS_GPD_MFPH_PD10MFP_Pos)/*!< GPD_MFPH PD10 setting for EBI_nCS2   */
#define SYS_GPD_MFPH_PD10MFP_UART1_RXD   (0x03UL<<SYS_GPD_MFPH_PD10MFP_Pos)/*!< GPD_MFPH PD10 setting for UART1_RXD  */
#define SYS_GPD_MFPH_PD10MFP_CAN0_RXD    (0x04UL<<SYS_GPD_MFPH_PD10MFP_Pos)/*!< GPD_MFPH PD10 setting for CAN0_RXD   */
#define SYS_GPD_MFPH_PD10MFP_QEI0_B      (0x0aUL<<SYS_GPD_MFPH_PD10MFP_Pos)/*!< GPD_MFPH PD10 setting for QEI0_B     */
#define SYS_GPD_MFPH_PD10MFP_INT7        (0x0fUL<<SYS_GPD_MFPH_PD10MFP_Pos)/*!< GPD_MFPH PD10 setting for INT7       */

/* PD.11 MFP */
#define SYS_GPD_MFPH_PD11MFP_GPIO        (0x00UL<<SYS_GPD_MFPH_PD11MFP_Pos)/*!< GPD_MFPH PD11 setting for GPIO       */
#define SYS_GPD_MFPH_PD11MFP_EBI_nCS1    (0x02UL<<SYS_GPD_MFPH_PD11MFP_Pos)/*!< GPD_MFPH PD11 setting for EBI_nCS1   */
#define SYS_GPD_MFPH_PD11MFP_UART1_TXD   (0x03UL<<SYS_GPD_MFPH_PD11MFP_Pos)/*!< GPD_MFPH PD11 setting for UART1_TXD  */
#define SYS_GPD_MFPH_PD11MFP_CAN0_TXD    (0x04UL<<SYS_GPD_MFPH_PD11MFP_Pos)/*!< GPD_MFPH PD11 setting for CAN0_TXD   */
#define SYS_GPD_MFPH_PD11MFP_QEI0_A      (0x0aUL<<SYS_GPD_MFPH_PD11MFP_Pos)/*!< GPD_MFPH PD11 setting for QEI0_A     */
#define SYS_GPD_MFPH_PD11MFP_INT6        (0x0fUL<<SYS_GPD_MFPH_PD11MFP_Pos)/*!< GPD_MFPH PD11 setting for INT6       */

/* PD.12 MFP */
#define SYS_GPD_MFPH_PD12MFP_GPIO        (0x00UL<<SYS_GPD_MFPH_PD12MFP_Pos)/*!< GPD_MFPH PD12 setting for GPIO       */
#define SYS_GPD_MFPH_PD12MFP_EBI_nCS0    (0x02UL<<SYS_GPD_MFPH_PD12MFP_Pos)/*!< GPD_MFPH PD12 setting for EBI_nCS0   */
#define SYS_GPD_MFPH_PD12MFP_UART2_RXD   (0x07UL<<SYS_GPD_MFPH_PD12MFP_Pos)/*!< GPD_MFPH PD12 setting for UART2_RXD  */
#define SYS_GPD_MFPH_PD12MFP_BPWM0_CH5   (0x09UL<<SYS_GPD_MFPH_PD12MFP_Pos)/*!< GPD_MFPH PD12 setting for BPWM0_CH5  */
#define SYS_GPD_MFPH_PD12MFP_QEI0_INDEX  (0x0aUL<<SYS_GPD_MFPH_PD12MFP_Pos)/*!< GPD_MFPH PD12 setting for QEI0_INDEX */
#define SYS_GPD_MFPH_PD12MFP_CLKO        (0x0dUL<<SYS_GPD_MFPH_PD12MFP_Pos)/*!< GPD_MFPH PD12 setting for CLKO       */
#define SYS_GPD_MFPH_PD12MFP_EADC0_ST    (0x0eUL<<SYS_GPD_MFPH_PD12MFP_Pos)/*!< GPD_MFPH PD12 setting for EADC0_ST   */
#define SYS_GPD_MFPH_PD12MFP_INT5        (0x0fUL<<SYS_GPD_MFPH_PD12MFP_Pos)/*!< GPD_MFPH PD12 setting for INT5       */

/* PD.13 MFP */
#define SYS_GPD_MFPH_PD13MFP_GPIO        (0x00UL<<SYS_GPD_MFPH_PD13MFP_Pos)/*!< GPD_MFPH PD13 setting for GPIO       */
#define SYS_GPD_MFPH_PD13MFP_EBI_AD10    (0x02UL<<SYS_GPD_MFPH_PD13MFP_Pos)/*!< GPD_MFPH PD13 setting for EBI_AD10   */
#define SYS_GPD_MFPH_PD13MFP_SD0_nCD     (0x03UL<<SYS_GPD_MFPH_PD13MFP_Pos)/*!< GPD_MFPH PD13 setting for SD0_nCD    */
#define SYS_GPD_MFPH_PD13MFP_SPI0_I2SMCLK (0x04UL<<SYS_GPD_MFPH_PD13MFP_Pos)/*!< GPD_MFPH PD13 setting for SPI0_I2SMCLK*/
#define SYS_GPD_MFPH_PD13MFP_SPI1_I2SMCLK (0x05UL<<SYS_GPD_MFPH_PD13MFP_Pos)/*!< GPD_MFPH PD13 setting for SPI1_I2SMCLK*/
#define SYS_GPD_MFPH_PD13MFP_SC2_nCD     (0x07UL<<SYS_GPD_MFPH_PD13MFP_Pos)/*!< GPD_MFPH PD13 setting for SC2_nCD    */

/* PD.14 MFP */
#define SYS_GPD_MFPH_PD14MFP_GPIO        (0x00UL<<SYS_GPD_MFPH_PD14MFP_Pos)/*!< GPD_MFPH PD14 setting for GPIO       */
#define SYS_GPD_MFPH_PD14MFP_EBI_nCS0    (0x02UL<<SYS_GPD_MFPH_PD14MFP_Pos)/*!< GPD_MFPH PD14 setting for EBI_nCS0   */
#define SYS_GPD_MFPH_PD14MFP_SPI3_I2SMCLK (0x03UL<<SYS_GPD_MFPH_PD14MFP_Pos)/*!< GPD_MFPH PD14 setting for SPI3_I2SMCLK*/
#define SYS_GPD_MFPH_PD14MFP_SC1_nCD     (0x04UL<<SYS_GPD_MFPH_PD14MFP_Pos)/*!< GPD_MFPH PD14 setting for SC1_nCD    */
#define SYS_GPD_MFPH_PD14MFP_USCI0_CTL0  (0x05UL<<SYS_GPD_MFPH_PD14MFP_Pos)/*!< GPD_MFPH PD14 setting for USCI0_CTL0 */
#define SYS_GPD_MFPH_PD14MFP_SPI0_I2SMCLK (0x06UL<<SYS_GPD_MFPH_PD14MFP_Pos)/*!< GPD_MFPH PD14 setting for SPI0_I2SMCLK*/
#define SYS_GPD_MFPH_PD14MFP_EPWM0_CH4   (0x0bUL<<SYS_GPD_MFPH_PD14MFP_Pos)/*!< GPD_MFPH PD14 setting for EPWM0_CH4  */

/* PE.0 MFP */
#define SYS_GPE_MFPL_PE0MFP_GPIO         (0x00UL<<SYS_GPE_MFPL_PE0MFP_Pos) /*!< GPE_MFPL PE0 setting for GPIO        */
#define SYS_GPE_MFPL_PE0MFP_EBI_AD11     (0x02UL<<SYS_GPE_MFPL_PE0MFP_Pos) /*!< GPE_MFPL PE0 setting for EBI_AD11    */
#define SYS_GPE_MFPL_PE0MFP_QSPI0_MOSI0  (0x03UL<<SYS_GPE_MFPL_PE0MFP_Pos) /*!< GPE_MFPL PE0 setting for QSPI0_MOSI0 */
#define SYS_GPE_MFPL_PE0MFP_SC2_CLK      (0x04UL<<SYS_GPE_MFPL_PE0MFP_Pos) /*!< GPE_MFPL PE0 setting for SC2_CLK     */
#define SYS_GPE_MFPL_PE0MFP_I2S0_MCLK    (0x05UL<<SYS_GPE_MFPL_PE0MFP_Pos) /*!< GPE_MFPL PE0 setting for I2S0_MCLK   */
#define SYS_GPE_MFPL_PE0MFP_SPI1_MOSI    (0x06UL<<SYS_GPE_MFPL_PE0MFP_Pos) /*!< GPE_MFPL PE0 setting for SPI1_MOSI   */
#define SYS_GPE_MFPL_PE0MFP_UART3_RXD    (0x07UL<<SYS_GPE_MFPL_PE0MFP_Pos) /*!< GPE_MFPL PE0 setting for UART3_RXD   */
#define SYS_GPE_MFPL_PE0MFP_I2C1_SDA     (0x08UL<<SYS_GPE_MFPL_PE0MFP_Pos) /*!< GPE_MFPL PE0 setting for I2C1_SDA    */
#define SYS_GPE_MFPL_PE0MFP_UART4_nRTS   (0x09UL<<SYS_GPE_MFPL_PE0MFP_Pos) /*!< GPE_MFPL PE0 setting for UART4_nRTS  */

/* PE.1 MFP */
#define SYS_GPE_MFPL_PE1MFP_GPIO         (0x00UL<<SYS_GPE_MFPL_PE1MFP_Pos) /*!< GPE_MFPL PE1 setting for GPIO        */
#define SYS_GPE_MFPL_PE1MFP_EBI_AD10     (0x02UL<<SYS_GPE_MFPL_PE1MFP_Pos) /*!< GPE_MFPL PE1 setting for EBI_AD10    */
#define SYS_GPE_MFPL_PE1MFP_QSPI0_MISO0  (0x03UL<<SYS_GPE_MFPL_PE1MFP_Pos) /*!< GPE_MFPL PE1 setting for QSPI0_MISO0 */
#define SYS_GPE_MFPL_PE1MFP_SC2_DAT      (0x04UL<<SYS_GPE_MFPL_PE1MFP_Pos) /*!< GPE_MFPL PE1 setting for SC2_DAT     */
#define SYS_GPE_MFPL_PE1MFP_I2S0_BCLK    (0x05UL<<SYS_GPE_MFPL_PE1MFP_Pos) /*!< GPE_MFPL PE1 setting for I2S0_BCLK   */
#define SYS_GPE_MFPL_PE1MFP_SPI1_MISO    (0x06UL<<SYS_GPE_MFPL_PE1MFP_Pos) /*!< GPE_MFPL PE1 setting for SPI1_MISO   */
#define SYS_GPE_MFPL_PE1MFP_UART3_TXD    (0x07UL<<SYS_GPE_MFPL_PE1MFP_Pos) /*!< GPE_MFPL PE1 setting for UART3_TXD   */
#define SYS_GPE_MFPL_PE1MFP_I2C1_SCL     (0x08UL<<SYS_GPE_MFPL_PE1MFP_Pos) /*!< GPE_MFPL PE1 setting for I2C1_SCL    */
#define SYS_GPE_MFPL_PE1MFP_UART4_nCTS   (0x09UL<<SYS_GPE_MFPL_PE1MFP_Pos) /*!< GPE_MFPL PE1 setting for UART4_nCTS  */

/* PE.2 MFP */
#define SYS_GPE_MFPL_PE2MFP_GPIO         (0x00UL<<SYS_GPE_MFPL_PE2MFP_Pos) /*!< GPE_MFPL PE2 setting for GPIO        */
#define SYS_GPE_MFPL_PE2MFP_EBI_ALE      (0x02UL<<SYS_GPE_MFPL_PE2MFP_Pos) /*!< GPE_MFPL PE2 setting for EBI_ALE     */
#define SYS_GPE_MFPL_PE2MFP_SD0_DAT0     (0x03UL<<SYS_GPE_MFPL_PE2MFP_Pos) /*!< GPE_MFPL PE2 setting for SD0_DAT0    */
#define SYS_GPE_MFPL_PE2MFP_SPI3_MOSI    (0x05UL<<SYS_GPE_MFPL_PE2MFP_Pos) /*!< GPE_MFPL PE2 setting for SPI3_MOSI   */
#define SYS_GPE_MFPL_PE2MFP_SC0_CLK      (0x06UL<<SYS_GPE_MFPL_PE2MFP_Pos) /*!< GPE_MFPL PE2 setting for SC0_CLK     */
#define SYS_GPE_MFPL_PE2MFP_USCI0_CLK    (0x07UL<<SYS_GPE_MFPL_PE2MFP_Pos) /*!< GPE_MFPL PE2 setting for USCI0_CLK   */
#define SYS_GPE_MFPL_PE2MFP_QEI0_B       (0x0bUL<<SYS_GPE_MFPL_PE2MFP_Pos) /*!< GPE_MFPL PE2 setting for QEI0_B      */
#define SYS_GPE_MFPL_PE2MFP_EPWM0_CH5    (0x0cUL<<SYS_GPE_MFPL_PE2MFP_Pos) /*!< GPE_MFPL PE2 setting for EPWM0_CH5   */
#define SYS_GPE_MFPL_PE2MFP_BPWM0_CH0    (0x0dUL<<SYS_GPE_MFPL_PE2MFP_Pos) /*!< GPE_MFPL PE2 setting for BPWM0_CH0   */

/* PE.3 MFP */
#define SYS_GPE_MFPL_PE3MFP_GPIO         (0x00UL<<SYS_GPE_MFPL_PE3MFP_Pos) /*!< GPE_MFPL PE3 setting for GPIO        */
#define SYS_GPE_MFPL_PE3MFP_EBI_MCLK     (0x02UL<<SYS_GPE_MFPL_PE3MFP_Pos) /*!< GPE_MFPL PE3 setting for EBI_MCLK    */
#define SYS_GPE_MFPL_PE3MFP_SD0_DAT1     (0x03UL<<SYS_GPE_MFPL_PE3MFP_Pos) /*!< GPE_MFPL PE3 setting for SD0_DAT1    */
#define SYS_GPE_MFPL_PE3MFP_SPI3_MISO    (0x05UL<<SYS_GPE_MFPL_PE3MFP_Pos) /*!< GPE_MFPL PE3 setting for SPI3_MISO   */
#define SYS_GPE_MFPL_PE3MFP_SC0_DAT      (0x06UL<<SYS_GPE_MFPL_PE3MFP_Pos) /*!< GPE_MFPL PE3 setting for SC0_DAT     */
#define SYS_GPE_MFPL_PE3MFP_USCI0_DAT0   (0x07UL<<SYS_GPE_MFPL_PE3MFP_Pos) /*!< GPE_MFPL PE3 setting for USCI0_DAT0  */
#define SYS_GPE_MFPL_PE3MFP_QEI0_A       (0x0bUL<<SYS_GPE_MFPL_PE3MFP_Pos) /*!< GPE_MFPL PE3 setting for QEI0_A      */
#define SYS_GPE_MFPL_PE3MFP_EPWM0_CH4    (0x0cUL<<SYS_GPE_MFPL_PE3MFP_Pos) /*!< GPE_MFPL PE3 setting for EPWM0_CH4   */
#define SYS_GPE_MFPL_PE3MFP_BPWM0_CH1    (0x0dUL<<SYS_GPE_MFPL_PE3MFP_Pos) /*!< GPE_MFPL PE3 setting for BPWM0_CH1   */

/* PE.4 MFP */
#define SYS_GPE_MFPL_PE4MFP_GPIO         (0x00UL<<SYS_GPE_MFPL_PE4MFP_Pos) /*!< GPE_MFPL PE4 setting for GPIO        */
#define SYS_GPE_MFPL_PE4MFP_EBI_nWR      (0x02UL<<SYS_GPE_MFPL_PE4MFP_Pos) /*!< GPE_MFPL PE4 setting for EBI_nWR     */
#define SYS_GPE_MFPL_PE4MFP_SD0_DAT2     (0x03UL<<SYS_GPE_MFPL_PE4MFP_Pos) /*!< GPE_MFPL PE4 setting for SD0_DAT2    */
#define SYS_GPE_MFPL_PE4MFP_SPI3_CLK     (0x05UL<<SYS_GPE_MFPL_PE4MFP_Pos) /*!< GPE_MFPL PE4 setting for SPI3_CLK    */
#define SYS_GPE_MFPL_PE4MFP_SC0_RST      (0x06UL<<SYS_GPE_MFPL_PE4MFP_Pos) /*!< GPE_MFPL PE4 setting for SC0_RST     */
#define SYS_GPE_MFPL_PE4MFP_USCI0_DAT1   (0x07UL<<SYS_GPE_MFPL_PE4MFP_Pos) /*!< GPE_MFPL PE4 setting for USCI0_DAT1  */
#define SYS_GPE_MFPL_PE4MFP_QEI0_INDEX   (0x0bUL<<SYS_GPE_MFPL_PE4MFP_Pos) /*!< GPE_MFPL PE4 setting for QEI0_INDEX  */
#define SYS_GPE_MFPL_PE4MFP_EPWM0_CH3    (0x0cUL<<SYS_GPE_MFPL_PE4MFP_Pos) /*!< GPE_MFPL PE4 setting for EPWM0_CH3   */
#define SYS_GPE_MFPL_PE4MFP_BPWM0_CH2    (0x0dUL<<SYS_GPE_MFPL_PE4MFP_Pos) /*!< GPE_MFPL PE4 setting for BPWM0_CH2   */

/* PE.5 MFP */
#define SYS_GPE_MFPL_PE5MFP_GPIO         (0x00UL<<SYS_GPE_MFPL_PE5MFP_Pos) /*!< GPE_MFPL PE5 setting for GPIO        */
#define SYS_GPE_MFPL_PE5MFP_EBI_nRD      (0x02UL<<SYS_GPE_MFPL_PE5MFP_Pos) /*!< GPE_MFPL PE5 setting for EBI_nRD     */
#define SYS_GPE_MFPL_PE5MFP_SD0_DAT3     (0x03UL<<SYS_GPE_MFPL_PE5MFP_Pos) /*!< GPE_MFPL PE5 setting for SD0_DAT3    */
#define SYS_GPE_MFPL_PE5MFP_SPI3_SS      (0x05UL<<SYS_GPE_MFPL_PE5MFP_Pos) /*!< GPE_MFPL PE5 setting for SPI3_SS     */
#define SYS_GPE_MFPL_PE5MFP_SC0_PWR      (0x06UL<<SYS_GPE_MFPL_PE5MFP_Pos) /*!< GPE_MFPL PE5 setting for SC0_PWR     */
#define SYS_GPE_MFPL_PE5MFP_USCI0_CTL1   (0x07UL<<SYS_GPE_MFPL_PE5MFP_Pos) /*!< GPE_MFPL PE5 setting for USCI0_CTL1  */
#define SYS_GPE_MFPL_PE5MFP_QEI1_B       (0x0bUL<<SYS_GPE_MFPL_PE5MFP_Pos) /*!< GPE_MFPL PE5 setting for QEI1_B      */
#define SYS_GPE_MFPL_PE5MFP_EPWM0_CH2    (0x0cUL<<SYS_GPE_MFPL_PE5MFP_Pos) /*!< GPE_MFPL PE5 setting for EPWM0_CH2   */
#define SYS_GPE_MFPL_PE5MFP_BPWM0_CH3    (0x0dUL<<SYS_GPE_MFPL_PE5MFP_Pos) /*!< GPE_MFPL PE5 setting for BPWM0_CH3   */

/* PE.6 MFP */
#define SYS_GPE_MFPL_PE6MFP_GPIO         (0x00UL<<SYS_GPE_MFPL_PE6MFP_Pos) /*!< GPE_MFPL PE6 setting for GPIO        */
#define SYS_GPE_MFPL_PE6MFP_SD0_CLK      (0x03UL<<SYS_GPE_MFPL_PE6MFP_Pos) /*!< GPE_MFPL PE6 setting for SD0_CLK     */
#define SYS_GPE_MFPL_PE6MFP_SPI3_I2SMCLK (0x05UL<<SYS_GPE_MFPL_PE6MFP_Pos) /*!< GPE_MFPL PE6 setting for SPI3_I2SMCLK*/
#define SYS_GPE_MFPL_PE6MFP_SC0_nCD      (0x06UL<<SYS_GPE_MFPL_PE6MFP_Pos) /*!< GPE_MFPL PE6 setting for SC0_nCD     */
#define SYS_GPE_MFPL_PE6MFP_USCI0_CTL0   (0x07UL<<SYS_GPE_MFPL_PE6MFP_Pos) /*!< GPE_MFPL PE6 setting for USCI0_CTL0  */
#define SYS_GPE_MFPL_PE6MFP_UART5_RXD    (0x08UL<<SYS_GPE_MFPL_PE6MFP_Pos) /*!< GPE_MFPL PE6 setting for UART5_RXD   */
#define SYS_GPE_MFPL_PE6MFP_QEI1_A       (0x0bUL<<SYS_GPE_MFPL_PE6MFP_Pos) /*!< GPE_MFPL PE6 setting for QEI1_A      */
#define SYS_GPE_MFPL_PE6MFP_EPWM0_CH1    (0x0cUL<<SYS_GPE_MFPL_PE6MFP_Pos) /*!< GPE_MFPL PE6 setting for EPWM0_CH1   */
#define SYS_GPE_MFPL_PE6MFP_BPWM0_CH4    (0x0dUL<<SYS_GPE_MFPL_PE6MFP_Pos) /*!< GPE_MFPL PE6 setting for BPWM0_CH4   */

/* PE.7 MFP */
#define SYS_GPE_MFPL_PE7MFP_GPIO         (0x00UL<<SYS_GPE_MFPL_PE7MFP_Pos) /*!< GPE_MFPL PE7 setting for GPIO        */
#define SYS_GPE_MFPL_PE7MFP_SD0_CMD      (0x03UL<<SYS_GPE_MFPL_PE7MFP_Pos) /*!< GPE_MFPL PE7 setting for SD0_CMD     */
#define SYS_GPE_MFPL_PE7MFP_UART5_TXD    (0x08UL<<SYS_GPE_MFPL_PE7MFP_Pos) /*!< GPE_MFPL PE7 setting for UART5_TXD   */
#define SYS_GPE_MFPL_PE7MFP_QEI1_INDEX   (0x0bUL<<SYS_GPE_MFPL_PE7MFP_Pos) /*!< GPE_MFPL PE7 setting for QEI1_INDEX  */
#define SYS_GPE_MFPL_PE7MFP_EPWM0_CH0    (0x0cUL<<SYS_GPE_MFPL_PE7MFP_Pos) /*!< GPE_MFPL PE7 setting for EPWM0_CH0   */
#define SYS_GPE_MFPL_PE7MFP_BPWM0_CH5    (0x0dUL<<SYS_GPE_MFPL_PE7MFP_Pos) /*!< GPE_MFPL PE7 setting for BPWM0_CH5   */

/* PE.8 MFP */
#define SYS_GPE_MFPH_PE8MFP_GPIO         (0x00UL<<SYS_GPE_MFPH_PE8MFP_Pos) /*!< GPE_MFPH PE8 setting for GPIO        */
#define SYS_GPE_MFPH_PE8MFP_EBI_ADR10    (0x02UL<<SYS_GPE_MFPH_PE8MFP_Pos) /*!< GPE_MFPH PE8 setting for EBI_ADR10   */
#define SYS_GPE_MFPH_PE8MFP_I2S0_BCLK    (0x04UL<<SYS_GPE_MFPH_PE8MFP_Pos) /*!< GPE_MFPH PE8 setting for I2S0_BCLK   */
#define SYS_GPE_MFPH_PE8MFP_SPI2_CLK     (0x05UL<<SYS_GPE_MFPH_PE8MFP_Pos) /*!< GPE_MFPH PE8 setting for SPI2_CLK    */
#define SYS_GPE_MFPH_PE8MFP_USCI1_CTL1   (0x06UL<<SYS_GPE_MFPH_PE8MFP_Pos) /*!< GPE_MFPH PE8 setting for USCI1_CTL1  */
#define SYS_GPE_MFPH_PE8MFP_UART2_TXD    (0x07UL<<SYS_GPE_MFPH_PE8MFP_Pos) /*!< GPE_MFPH PE8 setting for UART2_TXD   */
#define SYS_GPE_MFPH_PE8MFP_EPWM0_CH0    (0x0aUL<<SYS_GPE_MFPH_PE8MFP_Pos) /*!< GPE_MFPH PE8 setting for EPWM0_CH0   */
#define SYS_GPE_MFPH_PE8MFP_EPWM0_BRAKE0 (0x0bUL<<SYS_GPE_MFPH_PE8MFP_Pos) /*!< GPE_MFPH PE8 setting for EPWM0_BRAKE0*/
#define SYS_GPE_MFPH_PE8MFP_ECAP0_IC0    (0x0cUL<<SYS_GPE_MFPH_PE8MFP_Pos) /*!< GPE_MFPH PE8 setting for ECAP0_IC0   */
#define SYS_GPE_MFPH_PE8MFP_TRACE_DATA3  (0x0eUL<<SYS_GPE_MFPH_PE8MFP_Pos) /*!< GPE_MFPH PE8 setting for TRACE_DATA3 */

/* PE.9 MFP */
#define SYS_GPE_MFPH_PE9MFP_GPIO         (0x00UL<<SYS_GPE_MFPH_PE9MFP_Pos) /*!< GPE_MFPH PE9 setting for GPIO        */
#define SYS_GPE_MFPH_PE9MFP_EBI_ADR11    (0x02UL<<SYS_GPE_MFPH_PE9MFP_Pos) /*!< GPE_MFPH PE9 setting for EBI_ADR11   */
#define SYS_GPE_MFPH_PE9MFP_I2S0_MCLK    (0x04UL<<SYS_GPE_MFPH_PE9MFP_Pos) /*!< GPE_MFPH PE9 setting for I2S0_MCLK   */
#define SYS_GPE_MFPH_PE9MFP_SPI2_MISO    (0x05UL<<SYS_GPE_MFPH_PE9MFP_Pos) /*!< GPE_MFPH PE9 setting for SPI2_MISO   */
#define SYS_GPE_MFPH_PE9MFP_USCI1_CTL0   (0x06UL<<SYS_GPE_MFPH_PE9MFP_Pos) /*!< GPE_MFPH PE9 setting for USCI1_CTL0  */
#define SYS_GPE_MFPH_PE9MFP_UART2_RXD    (0x07UL<<SYS_GPE_MFPH_PE9MFP_Pos) /*!< GPE_MFPH PE9 setting for UART2_RXD   */
#define SYS_GPE_MFPH_PE9MFP_EPWM0_CH1    (0x0aUL<<SYS_GPE_MFPH_PE9MFP_Pos) /*!< GPE_MFPH PE9 setting for EPWM0_CH1   */
#define SYS_GPE_MFPH_PE9MFP_EPWM0_BRAKE1 (0x0bUL<<SYS_GPE_MFPH_PE9MFP_Pos) /*!< GPE_MFPH PE9 setting for EPWM0_BRAKE1*/
#define SYS_GPE_MFPH_PE9MFP_ECAP0_IC1    (0x0cUL<<SYS_GPE_MFPH_PE9MFP_Pos) /*!< GPE_MFPH PE9 setting for ECAP0_IC1   */
#define SYS_GPE_MFPH_PE9MFP_TRACE_DATA2  (0x0eUL<<SYS_GPE_MFPH_PE9MFP_Pos) /*!< GPE_MFPH PE9 setting for TRACE_DATA2 */

/* PE.10 MFP */
#define SYS_GPE_MFPH_PE10MFP_GPIO        (0x00UL<<SYS_GPE_MFPH_PE10MFP_Pos)/*!< GPE_MFPH PE10 setting for GPIO       */
#define SYS_GPE_MFPH_PE10MFP_EBI_ADR12   (0x02UL<<SYS_GPE_MFPH_PE10MFP_Pos)/*!< GPE_MFPH PE10 setting for EBI_ADR12  */
#define SYS_GPE_MFPH_PE10MFP_I2S0_DI     (0x04UL<<SYS_GPE_MFPH_PE10MFP_Pos)/*!< GPE_MFPH PE10 setting for I2S0_DI    */
#define SYS_GPE_MFPH_PE10MFP_SPI2_MOSI   (0x05UL<<SYS_GPE_MFPH_PE10MFP_Pos)/*!< GPE_MFPH PE10 setting for SPI2_MOSI  */
#define SYS_GPE_MFPH_PE10MFP_USCI1_DAT0  (0x06UL<<SYS_GPE_MFPH_PE10MFP_Pos)/*!< GPE_MFPH PE10 setting for USCI1_DAT0 */
#define SYS_GPE_MFPH_PE10MFP_UART3_TXD   (0x07UL<<SYS_GPE_MFPH_PE10MFP_Pos)/*!< GPE_MFPH PE10 setting for UART3_TXD  */
#define SYS_GPE_MFPH_PE10MFP_EPWM0_CH2   (0x0aUL<<SYS_GPE_MFPH_PE10MFP_Pos)/*!< GPE_MFPH PE10 setting for EPWM0_CH2  */
#define SYS_GPE_MFPH_PE10MFP_EPWM1_BRAKE0 (0x0bUL<<SYS_GPE_MFPH_PE10MFP_Pos)/*!< GPE_MFPH PE10 setting for EPWM1_BRAKE0*/
#define SYS_GPE_MFPH_PE10MFP_ECAP0_IC2   (0x0cUL<<SYS_GPE_MFPH_PE10MFP_Pos)/*!< GPE_MFPH PE10 setting for ECAP0_IC2  */
#define SYS_GPE_MFPH_PE10MFP_TRACE_DATA1 (0x0eUL<<SYS_GPE_MFPH_PE10MFP_Pos)/*!< GPE_MFPH PE10 setting for TRACE_DATA1*/

/* PE.11 MFP */
#define SYS_GPE_MFPH_PE11MFP_GPIO        (0x00UL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for GPIO       */
#define SYS_GPE_MFPH_PE11MFP_EBI_ADR13   (0x02UL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for EBI_ADR13  */
#define SYS_GPE_MFPH_PE11MFP_I2S0_DO     (0x04UL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for I2S0_DO    */
#define SYS_GPE_MFPH_PE11MFP_SPI2_SS     (0x05UL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for SPI2_SS    */
#define SYS_GPE_MFPH_PE11MFP_USCI1_DAT1  (0x06UL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for USCI1_DAT1 */
#define SYS_GPE_MFPH_PE11MFP_UART3_RXD   (0x07UL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for UART3_RXD  */
#define SYS_GPE_MFPH_PE11MFP_UART1_nCTS  (0x08UL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for UART1_nCTS */
#define SYS_GPE_MFPH_PE11MFP_EPWM0_CH3   (0x0aUL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for EPWM0_CH3  */
#define SYS_GPE_MFPH_PE11MFP_EPWM1_BRAKE1 (0x0bUL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for EPWM1_BRAKE1*/
#define SYS_GPE_MFPH_PE11MFP_ECAP1_IC2   (0x0dUL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for ECAP1_IC2  */
#define SYS_GPE_MFPH_PE11MFP_TRACE_DATA0 (0x0eUL<<SYS_GPE_MFPH_PE11MFP_Pos)/*!< GPE_MFPH PE11 setting for TRACE_DATA0*/

/* PE.12 MFP */
#define SYS_GPE_MFPH_PE12MFP_GPIO        (0x00UL<<SYS_GPE_MFPH_PE12MFP_Pos)/*!< GPE_MFPH PE12 setting for GPIO       */
#define SYS_GPE_MFPH_PE12MFP_EBI_ADR14   (0x02UL<<SYS_GPE_MFPH_PE12MFP_Pos)/*!< GPE_MFPH PE12 setting for EBI_ADR14  */
#define SYS_GPE_MFPH_PE12MFP_I2S0_LRCK   (0x04UL<<SYS_GPE_MFPH_PE12MFP_Pos)/*!< GPE_MFPH PE12 setting for I2S0_LRCK  */
#define SYS_GPE_MFPH_PE12MFP_SPI2_I2SMCLK (0x05UL<<SYS_GPE_MFPH_PE12MFP_Pos)/*!< GPE_MFPH PE12 setting for SPI2_I2SMCLK*/
#define SYS_GPE_MFPH_PE12MFP_USCI1_CLK   (0x06UL<<SYS_GPE_MFPH_PE12MFP_Pos)/*!< GPE_MFPH PE12 setting for USCI1_CLK  */
#define SYS_GPE_MFPH_PE12MFP_UART1_nRTS  (0x08UL<<SYS_GPE_MFPH_PE12MFP_Pos)/*!< GPE_MFPH PE12 setting for UART1_nRTS */
#define SYS_GPE_MFPH_PE12MFP_EPWM0_CH4   (0x0aUL<<SYS_GPE_MFPH_PE12MFP_Pos)/*!< GPE_MFPH PE12 setting for EPWM0_CH4  */
#define SYS_GPE_MFPH_PE12MFP_ECAP1_IC1   (0x0dUL<<SYS_GPE_MFPH_PE12MFP_Pos)/*!< GPE_MFPH PE12 setting for ECAP1_IC1  */
#define SYS_GPE_MFPH_PE12MFP_TRACE_CLK   (0x0eUL<<SYS_GPE_MFPH_PE12MFP_Pos)/*!< GPE_MFPH PE12 setting for TRACE_CLK  */

/* PE.13 MFP */
#define SYS_GPE_MFPH_PE13MFP_GPIO        (0x00UL<<SYS_GPE_MFPH_PE13MFP_Pos)/*!< GPE_MFPH PE13 setting for GPIO       */
#define SYS_GPE_MFPH_PE13MFP_EBI_ADR15   (0x02UL<<SYS_GPE_MFPH_PE13MFP_Pos)/*!< GPE_MFPH PE13 setting for EBI_ADR15  */
#define SYS_GPE_MFPH_PE13MFP_I2C0_SCL    (0x04UL<<SYS_GPE_MFPH_PE13MFP_Pos)/*!< GPE_MFPH PE13 setting for I2C0_SCL   */
#define SYS_GPE_MFPH_PE13MFP_UART4_nRTS  (0x05UL<<SYS_GPE_MFPH_PE13MFP_Pos)/*!< GPE_MFPH PE13 setting for UART4_nRTS */
#define SYS_GPE_MFPH_PE13MFP_UART1_TXD   (0x08UL<<SYS_GPE_MFPH_PE13MFP_Pos)/*!< GPE_MFPH PE13 setting for UART1_TXD  */
#define SYS_GPE_MFPH_PE13MFP_EPWM0_CH5   (0x0aUL<<SYS_GPE_MFPH_PE13MFP_Pos)/*!< GPE_MFPH PE13 setting for EPWM0_CH5  */
#define SYS_GPE_MFPH_PE13MFP_EPWM1_CH0   (0x0bUL<<SYS_GPE_MFPH_PE13MFP_Pos)/*!< GPE_MFPH PE13 setting for EPWM1_CH0  */
#define SYS_GPE_MFPH_PE13MFP_BPWM1_CH5   (0x0cUL<<SYS_GPE_MFPH_PE13MFP_Pos)/*!< GPE_MFPH PE13 setting for BPWM1_CH5  */
#define SYS_GPE_MFPH_PE13MFP_ECAP1_IC0   (0x0dUL<<SYS_GPE_MFPH_PE13MFP_Pos)/*!< GPE_MFPH PE13 setting for ECAP1_IC0  */

/* PE.14 MFP */
#define SYS_GPE_MFPH_PE14MFP_GPIO        (0x00UL<<SYS_GPE_MFPH_PE14MFP_Pos)/*!< GPE_MFPH PE14 setting for GPIO       */
#define SYS_GPE_MFPH_PE14MFP_EBI_AD8     (0x02UL<<SYS_GPE_MFPH_PE14MFP_Pos)/*!< GPE_MFPH PE14 setting for EBI_AD8    */
#define SYS_GPE_MFPH_PE14MFP_UART2_TXD   (0x03UL<<SYS_GPE_MFPH_PE14MFP_Pos)/*!< GPE_MFPH PE14 setting for UART2_TXD  */
#define SYS_GPE_MFPH_PE14MFP_CAN0_TXD    (0x04UL<<SYS_GPE_MFPH_PE14MFP_Pos)/*!< GPE_MFPH PE14 setting for CAN0_TXD   */

/* PE.15 MFP */
#define SYS_GPE_MFPH_PE15MFP_GPIO        (0x00UL<<SYS_GPE_MFPH_PE15MFP_Pos)/*!< GPE_MFPH PE15 setting for GPIO       */
#define SYS_GPE_MFPH_PE15MFP_EBI_AD9     (0x02UL<<SYS_GPE_MFPH_PE15MFP_Pos)/*!< GPE_MFPH PE15 setting for EBI_AD9    */
#define SYS_GPE_MFPH_PE15MFP_UART2_RXD   (0x03UL<<SYS_GPE_MFPH_PE15MFP_Pos)/*!< GPE_MFPH PE15 setting for UART2_RXD  */
#define SYS_GPE_MFPH_PE15MFP_CAN0_RXD    (0x04UL<<SYS_GPE_MFPH_PE15MFP_Pos)/*!< GPE_MFPH PE15 setting for CAN0_RXD   */

/* PF.0 MFP */
#define SYS_GPF_MFPL_PF0MFP_GPIO         (0x00UL<<SYS_GPF_MFPL_PF0MFP_Pos) /*!< GPF_MFPL PF0 setting for GPIO        */
#define SYS_GPF_MFPL_PF0MFP_UART1_TXD    (0x02UL<<SYS_GPF_MFPL_PF0MFP_Pos) /*!< GPF_MFPL PF0 setting for UART1_TXD   */
#define SYS_GPF_MFPL_PF0MFP_I2C1_SCL     (0x03UL<<SYS_GPF_MFPL_PF0MFP_Pos) /*!< GPF_MFPL PF0 setting for I2C1_SCL    */
#define SYS_GPF_MFPL_PF0MFP_BPWM1_CH0    (0x0cUL<<SYS_GPF_MFPL_PF0MFP_Pos) /*!< GPF_MFPL PF0 setting for BPWM1_CH0   */
#define SYS_GPF_MFPL_PF0MFP_ICE_DAT      (0x0eUL<<SYS_GPF_MFPL_PF0MFP_Pos) /*!< GPF_MFPL PF0 setting for ICE_DAT     */

/* PF.1 MFP */
#define SYS_GPF_MFPL_PF1MFP_GPIO         (0x00UL<<SYS_GPF_MFPL_PF1MFP_Pos) /*!< GPF_MFPL PF1 setting for GPIO        */
#define SYS_GPF_MFPL_PF1MFP_UART1_RXD    (0x02UL<<SYS_GPF_MFPL_PF1MFP_Pos) /*!< GPF_MFPL PF1 setting for UART1_RXD   */
#define SYS_GPF_MFPL_PF1MFP_I2C1_SDA     (0x03UL<<SYS_GPF_MFPL_PF1MFP_Pos) /*!< GPF_MFPL PF1 setting for I2C1_SDA    */
#define SYS_GPF_MFPL_PF1MFP_BPWM1_CH1    (0x0cUL<<SYS_GPF_MFPL_PF1MFP_Pos) /*!< GPF_MFPL PF1 setting for BPWM1_CH1   */
#define SYS_GPF_MFPL_PF1MFP_ICE_CLK      (0x0eUL<<SYS_GPF_MFPL_PF1MFP_Pos) /*!< GPF_MFPL PF1 setting for ICE_CLK     */

/* PF.2 MFP */
#define SYS_GPF_MFPL_PF2MFP_GPIO         (0x00UL<<SYS_GPF_MFPL_PF2MFP_Pos) /*!< GPF_MFPL PF2 setting for GPIO        */
#define SYS_GPF_MFPL_PF2MFP_EBI_nCS1     (0x02UL<<SYS_GPF_MFPL_PF2MFP_Pos) /*!< GPF_MFPL PF2 setting for EBI_nCS1    */
#define SYS_GPF_MFPL_PF2MFP_UART0_RXD    (0x03UL<<SYS_GPF_MFPL_PF2MFP_Pos) /*!< GPF_MFPL PF2 setting for UART0_RXD   */
#define SYS_GPF_MFPL_PF2MFP_I2C0_SDA     (0x04UL<<SYS_GPF_MFPL_PF2MFP_Pos) /*!< GPF_MFPL PF2 setting for I2C0_SDA    */
#define SYS_GPF_MFPL_PF2MFP_QSPI0_CLK    (0x05UL<<SYS_GPF_MFPL_PF2MFP_Pos) /*!< GPF_MFPL PF2 setting for QSPI0_CLK   */
#define SYS_GPF_MFPL_PF2MFP_XT1_OUT      (0x0aUL<<SYS_GPF_MFPL_PF2MFP_Pos) /*!< GPF_MFPL PF2 setting for XT1_OUT     */
#define SYS_GPF_MFPL_PF2MFP_BPWM1_CH1    (0x0bUL<<SYS_GPF_MFPL_PF2MFP_Pos) /*!< GPF_MFPL PF2 setting for BPWM1_CH1   */

/* PF.3 MFP */
#define SYS_GPF_MFPL_PF3MFP_GPIO         (0x00UL<<SYS_GPF_MFPL_PF3MFP_Pos) /*!< GPF_MFPL PF3 setting for GPIO        */
#define SYS_GPF_MFPL_PF3MFP_EBI_nCS0     (0x02UL<<SYS_GPF_MFPL_PF3MFP_Pos) /*!< GPF_MFPL PF3 setting for EBI_nCS0    */
#define SYS_GPF_MFPL_PF3MFP_UART0_TXD    (0x03UL<<SYS_GPF_MFPL_PF3MFP_Pos) /*!< GPF_MFPL PF3 setting for UART0_TXD   */
#define SYS_GPF_MFPL_PF3MFP_I2C0_SCL     (0x04UL<<SYS_GPF_MFPL_PF3MFP_Pos) /*!< GPF_MFPL PF3 setting for I2C0_SCL    */
#define SYS_GPF_MFPL_PF3MFP_XT1_IN       (0x0aUL<<SYS_GPF_MFPL_PF3MFP_Pos) /*!< GPF_MFPL PF3 setting for XT1_IN      */
#define SYS_GPF_MFPL_PF3MFP_BPWM1_CH0    (0x0bUL<<SYS_GPF_MFPL_PF3MFP_Pos) /*!< GPF_MFPL PF3 setting for BPWM1_CH0   */

/* PF.4 MFP */
#define SYS_GPF_MFPL_PF4MFP_GPIO         (0x00UL<<SYS_GPF_MFPL_PF4MFP_Pos) /*!< GPF_MFPL PF4 setting for GPIO        */
#define SYS_GPF_MFPL_PF4MFP_UART2_TXD    (0x02UL<<SYS_GPF_MFPL_PF4MFP_Pos) /*!< GPF_MFPL PF4 setting for UART2_TXD   */
#define SYS_GPF_MFPL_PF4MFP_UART2_nRTS   (0x04UL<<SYS_GPF_MFPL_PF4MFP_Pos) /*!< GPF_MFPL PF4 setting for UART2_nRTS  */
#define SYS_GPF_MFPL_PF4MFP_BPWM0_CH5    (0x08UL<<SYS_GPF_MFPL_PF4MFP_Pos) /*!< GPF_MFPL PF4 setting for BPWM0_CH5   */
#define SYS_GPF_MFPL_PF4MFP_X32_OUT      (0x0aUL<<SYS_GPF_MFPL_PF4MFP_Pos) /*!< GPF_MFPL PF4 setting for X32_OUT     */

/* PF.5 MFP */
#define SYS_GPF_MFPL_PF5MFP_GPIO         (0x00UL<<SYS_GPF_MFPL_PF5MFP_Pos) /*!< GPF_MFPL PF5 setting for GPIO        */
#define SYS_GPF_MFPL_PF5MFP_UART2_RXD    (0x02UL<<SYS_GPF_MFPL_PF5MFP_Pos) /*!< GPF_MFPL PF5 setting for UART2_RXD   */
#define SYS_GPF_MFPL_PF5MFP_UART2_nCTS   (0x04UL<<SYS_GPF_MFPL_PF5MFP_Pos) /*!< GPF_MFPL PF5 setting for UART2_nCTS  */
#define SYS_GPF_MFPL_PF5MFP_BPWM0_CH4    (0x08UL<<SYS_GPF_MFPL_PF5MFP_Pos) /*!< GPF_MFPL PF5 setting for BPWM0_CH4   */
#define SYS_GPF_MFPL_PF5MFP_EPWM0_SYNC_OUT (0x09UL<<SYS_GPF_MFPL_PF5MFP_Pos) /*!< GPF_MFPL PF5 setting for EPWM0_SYNC_OUT*/
#define SYS_GPF_MFPL_PF5MFP_X32_IN       (0x0aUL<<SYS_GPF_MFPL_PF5MFP_Pos) /*!< GPF_MFPL PF5 setting for X32_IN      */
#define SYS_GPF_MFPL_PF5MFP_EADC0_ST     (0x0bUL<<SYS_GPF_MFPL_PF5MFP_Pos) /*!< GPF_MFPL PF5 setting for EADC0_ST    */

/* PF.6 MFP */
#define SYS_GPF_MFPL_PF6MFP_GPIO         (0x00UL<<SYS_GPF_MFPL_PF6MFP_Pos) /*!< GPF_MFPL PF6 setting for GPIO        */
#define SYS_GPF_MFPL_PF6MFP_EBI_ADR19    (0x02UL<<SYS_GPF_MFPL_PF6MFP_Pos) /*!< GPF_MFPL PF6 setting for EBI_ADR19   */
#define SYS_GPF_MFPL_PF6MFP_SC0_CLK      (0x03UL<<SYS_GPF_MFPL_PF6MFP_Pos) /*!< GPF_MFPL PF6 setting for SC0_CLK     */
#define SYS_GPF_MFPL_PF6MFP_I2S0_LRCK    (0x04UL<<SYS_GPF_MFPL_PF6MFP_Pos) /*!< GPF_MFPL PF6 setting for I2S0_LRCK   */
#define SYS_GPF_MFPL_PF6MFP_SPI0_MOSI    (0x05UL<<SYS_GPF_MFPL_PF6MFP_Pos) /*!< GPF_MFPL PF6 setting for SPI0_MOSI   */
#define SYS_GPF_MFPL_PF6MFP_UART4_RXD    (0x06UL<<SYS_GPF_MFPL_PF6MFP_Pos) /*!< GPF_MFPL PF6 setting for UART4_RXD   */
#define SYS_GPF_MFPL_PF6MFP_EBI_nCS0     (0x07UL<<SYS_GPF_MFPL_PF6MFP_Pos) /*!< GPF_MFPL PF6 setting for EBI_nCS0    */
#define SYS_GPF_MFPL_PF6MFP_TAMPER0      (0x0aUL<<SYS_GPF_MFPL_PF6MFP_Pos) /*!< GPF_MFPL PF6 setting for TAMPER0     */

/* PF.7 MFP */
#define SYS_GPF_MFPL_PF7MFP_GPIO         (0x00UL<<SYS_GPF_MFPL_PF7MFP_Pos) /*!< GPF_MFPL PF7 setting for GPIO        */
#define SYS_GPF_MFPL_PF7MFP_EBI_ADR18    (0x02UL<<SYS_GPF_MFPL_PF7MFP_Pos) /*!< GPF_MFPL PF7 setting for EBI_ADR18   */
#define SYS_GPF_MFPL_PF7MFP_SC0_DAT      (0x03UL<<SYS_GPF_MFPL_PF7MFP_Pos) /*!< GPF_MFPL PF7 setting for SC0_DAT     */
#define SYS_GPF_MFPL_PF7MFP_I2S0_DO      (0x04UL<<SYS_GPF_MFPL_PF7MFP_Pos) /*!< GPF_MFPL PF7 setting for I2S0_DO     */
#define SYS_GPF_MFPL_PF7MFP_SPI0_MISO    (0x05UL<<SYS_GPF_MFPL_PF7MFP_Pos) /*!< GPF_MFPL PF7 setting for SPI0_MISO   */
#define SYS_GPF_MFPL_PF7MFP_UART4_TXD    (0x06UL<<SYS_GPF_MFPL_PF7MFP_Pos) /*!< GPF_MFPL PF7 setting for UART4_TXD   */
#define SYS_GPF_MFPL_PF7MFP_TAMPER1      (0x0aUL<<SYS_GPF_MFPL_PF7MFP_Pos) /*!< GPF_MFPL PF7 setting for TAMPER1     */

/* PF.8 MFP */
#define SYS_GPF_MFPH_PF8MFP_GPIO         (0x00UL<<SYS_GPF_MFPH_PF8MFP_Pos) /*!< GPF_MFPH PF8 setting for GPIO        */
#define SYS_GPF_MFPH_PF8MFP_EBI_ADR17    (0x02UL<<SYS_GPF_MFPH_PF8MFP_Pos) /*!< GPF_MFPH PF8 setting for EBI_ADR17   */
#define SYS_GPF_MFPH_PF8MFP_SC0_RST      (0x03UL<<SYS_GPF_MFPH_PF8MFP_Pos) /*!< GPF_MFPH PF8 setting for SC0_RST     */
#define SYS_GPF_MFPH_PF8MFP_I2S0_DI      (0x04UL<<SYS_GPF_MFPH_PF8MFP_Pos) /*!< GPF_MFPH PF8 setting for I2S0_DI     */
#define SYS_GPF_MFPH_PF8MFP_SPI0_CLK     (0x05UL<<SYS_GPF_MFPH_PF8MFP_Pos) /*!< GPF_MFPH PF8 setting for SPI0_CLK    */
#define SYS_GPF_MFPH_PF8MFP_TAMPER2      (0x0aUL<<SYS_GPF_MFPH_PF8MFP_Pos) /*!< GPF_MFPH PF8 setting for TAMPER2     */

/* PF.9 MFP */
#define SYS_GPF_MFPH_PF9MFP_GPIO         (0x00UL<<SYS_GPF_MFPH_PF9MFP_Pos) /*!< GPF_MFPH PF9 setting for GPIO        */
#define SYS_GPF_MFPH_PF9MFP_EBI_ADR16    (0x02UL<<SYS_GPF_MFPH_PF9MFP_Pos) /*!< GPF_MFPH PF9 setting for EBI_ADR16   */
#define SYS_GPF_MFPH_PF9MFP_SC0_PWR      (0x03UL<<SYS_GPF_MFPH_PF9MFP_Pos) /*!< GPF_MFPH PF9 setting for SC0_PWR     */
#define SYS_GPF_MFPH_PF9MFP_I2S0_MCLK    (0x04UL<<SYS_GPF_MFPH_PF9MFP_Pos) /*!< GPF_MFPH PF9 setting for I2S0_MCLK   */
#define SYS_GPF_MFPH_PF9MFP_SPI0_SS      (0x05UL<<SYS_GPF_MFPH_PF9MFP_Pos) /*!< GPF_MFPH PF9 setting for SPI0_SS     */
#define SYS_GPF_MFPH_PF9MFP_TAMPER3      (0x0aUL<<SYS_GPF_MFPH_PF9MFP_Pos) /*!< GPF_MFPH PF9 setting for TAMPER3     */

/* PF.10 MFP */
#define SYS_GPF_MFPH_PF10MFP_GPIO        (0x00UL<<SYS_GPF_MFPH_PF10MFP_Pos)/*!< GPF_MFPH PF10 setting for GPIO       */
#define SYS_GPF_MFPH_PF10MFP_EBI_ADR15   (0x02UL<<SYS_GPF_MFPH_PF10MFP_Pos)/*!< GPF_MFPH PF10 setting for EBI_ADR15  */
#define SYS_GPF_MFPH_PF10MFP_SC0_nCD     (0x03UL<<SYS_GPF_MFPH_PF10MFP_Pos)/*!< GPF_MFPH PF10 setting for SC0_nCD    */
#define SYS_GPF_MFPH_PF10MFP_I2S0_BCLK   (0x04UL<<SYS_GPF_MFPH_PF10MFP_Pos)/*!< GPF_MFPH PF10 setting for I2S0_BCLK  */
#define SYS_GPF_MFPH_PF10MFP_SPI0_I2SMCLK (0x05UL<<SYS_GPF_MFPH_PF10MFP_Pos)/*!< GPF_MFPH PF10 setting for SPI0_I2SMCLK*/
#define SYS_GPF_MFPH_PF10MFP_TAMPER4     (0x0aUL<<SYS_GPF_MFPH_PF10MFP_Pos)/*!< GPF_MFPH PF10 setting for TAMPER4    */

/* PF.11 MFP */
#define SYS_GPF_MFPH_PF11MFP_GPIO        (0x00UL<<SYS_GPF_MFPH_PF11MFP_Pos)/*!< GPF_MFPH PF11 setting for GPIO       */
#define SYS_GPF_MFPH_PF11MFP_EBI_ADR14   (0x02UL<<SYS_GPF_MFPH_PF11MFP_Pos)/*!< GPF_MFPH PF11 setting for EBI_ADR14  */
#define SYS_GPF_MFPH_PF11MFP_SPI2_MOSI   (0x03UL<<SYS_GPF_MFPH_PF11MFP_Pos)/*!< GPF_MFPH PF11 setting for SPI2_MOSI  */
#define SYS_GPF_MFPH_PF11MFP_TAMPER5     (0x0aUL<<SYS_GPF_MFPH_PF11MFP_Pos)/*!< GPF_MFPH PF11 setting for TAMPER5    */
#define SYS_GPF_MFPH_PF11MFP_TM3         (0x0dUL<<SYS_GPF_MFPH_PF11MFP_Pos)/*!< GPF_MFPH PF11 setting for TM3        */

/* PG.2 MFP */
#define SYS_GPG_MFPL_PG2MFP_GPIO         (0x00UL<<SYS_GPG_MFPL_PG2MFP_Pos) /*!< GPG_MFPL PG2 setting for GPIO        */
#define SYS_GPG_MFPL_PG2MFP_EBI_ADR11    (0x02UL<<SYS_GPG_MFPL_PG2MFP_Pos) /*!< GPG_MFPL PG2 setting for EBI_ADR11   */
#define SYS_GPG_MFPL_PG2MFP_SPI2_SS      (0x03UL<<SYS_GPG_MFPL_PG2MFP_Pos) /*!< GPG_MFPL PG2 setting for SPI2_SS     */
#define SYS_GPG_MFPL_PG2MFP_I2C0_SMBAL   (0x04UL<<SYS_GPG_MFPL_PG2MFP_Pos) /*!< GPG_MFPL PG2 setting for I2C0_SMBAL  */
#define SYS_GPG_MFPL_PG2MFP_I2C1_SCL     (0x05UL<<SYS_GPG_MFPL_PG2MFP_Pos) /*!< GPG_MFPL PG2 setting for I2C1_SCL    */
#define SYS_GPG_MFPL_PG2MFP_TM0          (0x0dUL<<SYS_GPG_MFPL_PG2MFP_Pos) /*!< GPG_MFPL PG2 setting for TM0         */

/* PG.3 MFP */
#define SYS_GPG_MFPL_PG3MFP_GPIO         (0x00UL<<SYS_GPG_MFPL_PG3MFP_Pos) /*!< GPG_MFPL PG3 setting for GPIO        */
#define SYS_GPG_MFPL_PG3MFP_EBI_ADR12    (0x02UL<<SYS_GPG_MFPL_PG3MFP_Pos) /*!< GPG_MFPL PG3 setting for EBI_ADR12   */
#define SYS_GPG_MFPL_PG3MFP_SPI2_CLK     (0x03UL<<SYS_GPG_MFPL_PG3MFP_Pos) /*!< GPG_MFPL PG3 setting for SPI2_CLK    */
#define SYS_GPG_MFPL_PG3MFP_I2C0_SMBSUS  (0x04UL<<SYS_GPG_MFPL_PG3MFP_Pos) /*!< GPG_MFPL PG3 setting for I2C0_SMBSUS */
#define SYS_GPG_MFPL_PG3MFP_I2C1_SDA     (0x05UL<<SYS_GPG_MFPL_PG3MFP_Pos) /*!< GPG_MFPL PG3 setting for I2C1_SDA    */
#define SYS_GPG_MFPL_PG3MFP_TM1          (0x0dUL<<SYS_GPG_MFPL_PG3MFP_Pos) /*!< GPG_MFPL PG3 setting for TM1         */

/* PG.4 MFP */
#define SYS_GPG_MFPL_PG4MFP_GPIO         (0x00UL<<SYS_GPG_MFPL_PG4MFP_Pos) /*!< GPG_MFPL PG4 setting for GPIO        */
#define SYS_GPG_MFPL_PG4MFP_EBI_ADR13    (0x02UL<<SYS_GPG_MFPL_PG4MFP_Pos) /*!< GPG_MFPL PG4 setting for EBI_ADR13   */
#define SYS_GPG_MFPL_PG4MFP_SPI2_MISO    (0x03UL<<SYS_GPG_MFPL_PG4MFP_Pos) /*!< GPG_MFPL PG4 setting for SPI2_MISO   */
#define SYS_GPG_MFPL_PG4MFP_TM2          (0x0dUL<<SYS_GPG_MFPL_PG4MFP_Pos) /*!< GPG_MFPL PG4 setting for TM2         */

/* PG.9 MFP */
#define SYS_GPG_MFPH_PG9MFP_GPIO         (0x00UL<<SYS_GPG_MFPH_PG9MFP_Pos) /*!< GPG_MFPH PG9 setting for GPIO        */
#define SYS_GPG_MFPH_PG9MFP_EBI_AD0      (0x02UL<<SYS_GPG_MFPH_PG9MFP_Pos) /*!< GPG_MFPH PG9 setting for EBI_AD0     */
#define SYS_GPG_MFPH_PG9MFP_BPWM0_CH5    (0x0cUL<<SYS_GPG_MFPH_PG9MFP_Pos) /*!< GPG_MFPH PG9 setting for BPWM0_CH5   */

/* PG.10 MFP */
#define SYS_GPG_MFPH_PG10MFP_GPIO        (0x00UL<<SYS_GPG_MFPH_PG10MFP_Pos)/*!< GPG_MFPH PG10 setting for GPIO       */
#define SYS_GPG_MFPH_PG10MFP_EBI_AD1     (0x02UL<<SYS_GPG_MFPH_PG10MFP_Pos)/*!< GPG_MFPH PG10 setting for EBI_AD1    */
#define SYS_GPG_MFPH_PG10MFP_BPWM0_CH4   (0x0cUL<<SYS_GPG_MFPH_PG10MFP_Pos)/*!< GPG_MFPH PG10 setting for BPWM0_CH4  */

/* PG.11 MFP */
#define SYS_GPG_MFPH_PG11MFP_GPIO        (0x00UL<<SYS_GPG_MFPH_PG11MFP_Pos)/*!< GPG_MFPH PG11 setting for GPIO       */
#define SYS_GPG_MFPH_PG11MFP_EBI_AD2     (0x02UL<<SYS_GPG_MFPH_PG11MFP_Pos)/*!< GPG_MFPH PG11 setting for EBI_AD2    */
#define SYS_GPG_MFPH_PG11MFP_BPWM0_CH3   (0x0cUL<<SYS_GPG_MFPH_PG11MFP_Pos)/*!< GPG_MFPH PG11 setting for BPWM0_CH3  */

/* PG.12 MFP */
#define SYS_GPG_MFPH_PG12MFP_GPIO        (0x00UL<<SYS_GPG_MFPH_PG12MFP_Pos)/*!< GPG_MFPH PG12 setting for GPIO       */
#define SYS_GPG_MFPH_PG12MFP_EBI_AD3     (0x02UL<<SYS_GPG_MFPH_PG12MFP_Pos)/*!< GPG_MFPH PG12 setting for EBI_AD3    */
#define SYS_GPG_MFPH_PG12MFP_BPWM0_CH2   (0x0cUL<<SYS_GPG_MFPH_PG12MFP_Pos)/*!< GPG_MFPH PG12 setting for BPWM0_CH2  */

/* PG.13 MFP */
#define SYS_GPG_MFPH_PG13MFP_GPIO        (0x00UL<<SYS_GPG_MFPH_PG13MFP_Pos)/*!< GPG_MFPH PG13 setting for GPIO       */
#define SYS_GPG_MFPH_PG13MFP_EBI_AD4     (0x02UL<<SYS_GPG_MFPH_PG13MFP_Pos)/*!< GPG_MFPH PG13 setting for EBI_AD4    */
#define SYS_GPG_MFPH_PG13MFP_BPWM0_CH1   (0x0cUL<<SYS_GPG_MFPH_PG13MFP_Pos)/*!< GPG_MFPH PG13 setting for BPWM0_CH1  */

/* PG.14 MFP */
#define SYS_GPG_MFPH_PG14MFP_GPIO        (0x00UL<<SYS_GPG_MFPH_PG14MFP_Pos)/*!< GPG_MFPH PG14 setting for GPIO       */
#define SYS_GPG_MFPH_PG14MFP_EBI_AD5     (0x02UL<<SYS_GPG_MFPH_PG14MFP_Pos)/*!< GPG_MFPH PG14 setting for EBI_AD5    */
#define SYS_GPG_MFPH_PG14MFP_BPWM0_CH0   (0x0cUL<<SYS_GPG_MFPH_PG14MFP_Pos)/*!< GPG_MFPH PG14 setting for BPWM0_CH0  */

/* PG.15 MFP */
#define SYS_GPG_MFPH_PG15MFP_GPIO        (0x00UL<<SYS_GPG_MFPH_PG15MFP_Pos)/*!< GPG_MFPH PG15 setting for GPIO       */
#define SYS_GPG_MFPH_PG15MFP_CLKO        (0x0eUL<<SYS_GPG_MFPH_PG15MFP_Pos)/*!< GPG_MFPH PG15 setting for CLKO       */
#define SYS_GPG_MFPH_PG15MFP_EADC0_ST    (0x0fUL<<SYS_GPG_MFPH_PG15MFP_Pos)/*!< GPG_MFPH PG15 setting for EADC0_ST   */

/* PH.4 MFP */
#define SYS_GPH_MFPL_PH4MFP_GPIO         (0x00UL<<SYS_GPH_MFPL_PH4MFP_Pos) /*!< GPH_MFPL PH4 setting for GPIO        */
#define SYS_GPH_MFPL_PH4MFP_EBI_ADR3     (0x02UL<<SYS_GPH_MFPL_PH4MFP_Pos) /*!< GPH_MFPL PH4 setting for EBI_ADR3    */
#define SYS_GPH_MFPL_PH4MFP_SPI1_MISO    (0x03UL<<SYS_GPH_MFPL_PH4MFP_Pos) /*!< GPH_MFPL PH4 setting for SPI1_MISO   */

/* PH.5 MFP */
#define SYS_GPH_MFPL_PH5MFP_GPIO         (0x00UL<<SYS_GPH_MFPL_PH5MFP_Pos) /*!< GPH_MFPL PH5 setting for GPIO        */
#define SYS_GPH_MFPL_PH5MFP_EBI_ADR2     (0x02UL<<SYS_GPH_MFPL_PH5MFP_Pos) /*!< GPH_MFPL PH5 setting for EBI_ADR2    */
#define SYS_GPH_MFPL_PH5MFP_SPI1_MOSI    (0x03UL<<SYS_GPH_MFPL_PH5MFP_Pos) /*!< GPH_MFPL PH5 setting for SPI1_MOSI   */

/* PH.6 MFP */
#define SYS_GPH_MFPL_PH6MFP_GPIO         (0x00UL<<SYS_GPH_MFPL_PH6MFP_Pos) /*!< GPH_MFPL PH6 setting for GPIO        */
#define SYS_GPH_MFPL_PH6MFP_EBI_ADR1     (0x02UL<<SYS_GPH_MFPL_PH6MFP_Pos) /*!< GPH_MFPL PH6 setting for EBI_ADR1    */
#define SYS_GPH_MFPL_PH6MFP_SPI1_CLK     (0x03UL<<SYS_GPH_MFPL_PH6MFP_Pos) /*!< GPH_MFPL PH6 setting for SPI1_CLK    */

/* PH.7 MFP */
#define SYS_GPH_MFPL_PH7MFP_GPIO         (0x00UL<<SYS_GPH_MFPL_PH7MFP_Pos) /*!< GPH_MFPL PH7 setting for GPIO        */
#define SYS_GPH_MFPL_PH7MFP_EBI_ADR0     (0x02UL<<SYS_GPH_MFPL_PH7MFP_Pos) /*!< GPH_MFPL PH7 setting for EBI_ADR0    */
#define SYS_GPH_MFPL_PH7MFP_SPI1_SS      (0x03UL<<SYS_GPH_MFPL_PH7MFP_Pos) /*!< GPH_MFPL PH7 setting for SPI1_SS     */

/* PH.8 MFP */
#define SYS_GPH_MFPH_PH8MFP_GPIO         (0x00UL<<SYS_GPH_MFPH_PH8MFP_Pos) /*!< GPH_MFPH PH8 setting for GPIO        */
#define SYS_GPH_MFPH_PH8MFP_EBI_AD12     (0x02UL<<SYS_GPH_MFPH_PH8MFP_Pos) /*!< GPH_MFPH PH8 setting for EBI_AD12    */
#define SYS_GPH_MFPH_PH8MFP_QSPI0_CLK    (0x03UL<<SYS_GPH_MFPH_PH8MFP_Pos) /*!< GPH_MFPH PH8 setting for QSPI0_CLK   */
#define SYS_GPH_MFPH_PH8MFP_SC2_PWR      (0x04UL<<SYS_GPH_MFPH_PH8MFP_Pos) /*!< GPH_MFPH PH8 setting for SC2_PWR     */
#define SYS_GPH_MFPH_PH8MFP_I2S0_DI      (0x05UL<<SYS_GPH_MFPH_PH8MFP_Pos) /*!< GPH_MFPH PH8 setting for I2S0_DI     */
#define SYS_GPH_MFPH_PH8MFP_SPI1_CLK     (0x06UL<<SYS_GPH_MFPH_PH8MFP_Pos) /*!< GPH_MFPH PH8 setting for SPI1_CLK    */
#define SYS_GPH_MFPH_PH8MFP_UART3_nRTS   (0x07UL<<SYS_GPH_MFPH_PH8MFP_Pos) /*!< GPH_MFPH PH8 setting for UART3_nRTS  */
#define SYS_GPH_MFPH_PH8MFP_I2C1_SMBAL   (0x08UL<<SYS_GPH_MFPH_PH8MFP_Pos) /*!< GPH_MFPH PH8 setting for I2C1_SMBAL  */
#define SYS_GPH_MFPH_PH8MFP_I2C2_SCL     (0x09UL<<SYS_GPH_MFPH_PH8MFP_Pos) /*!< GPH_MFPH PH8 setting for I2C2_SCL    */
#define SYS_GPH_MFPH_PH8MFP_UART1_TXD    (0x0aUL<<SYS_GPH_MFPH_PH8MFP_Pos) /*!< GPH_MFPH PH8 setting for UART1_TXD   */

/* PH.9 MFP */
#define SYS_GPH_MFPH_PH9MFP_GPIO         (0x00UL<<SYS_GPH_MFPH_PH9MFP_Pos) /*!< GPH_MFPH PH9 setting for GPIO        */
#define SYS_GPH_MFPH_PH9MFP_EBI_AD13     (0x02UL<<SYS_GPH_MFPH_PH9MFP_Pos) /*!< GPH_MFPH PH9 setting for EBI_AD13    */
#define SYS_GPH_MFPH_PH9MFP_QSPI0_SS     (0x03UL<<SYS_GPH_MFPH_PH9MFP_Pos) /*!< GPH_MFPH PH9 setting for QSPI0_SS    */
#define SYS_GPH_MFPH_PH9MFP_SC2_RST      (0x04UL<<SYS_GPH_MFPH_PH9MFP_Pos) /*!< GPH_MFPH PH9 setting for SC2_RST     */
#define SYS_GPH_MFPH_PH9MFP_I2S0_DO      (0x05UL<<SYS_GPH_MFPH_PH9MFP_Pos) /*!< GPH_MFPH PH9 setting for I2S0_DO     */
#define SYS_GPH_MFPH_PH9MFP_SPI1_SS      (0x06UL<<SYS_GPH_MFPH_PH9MFP_Pos) /*!< GPH_MFPH PH9 setting for SPI1_SS     */
#define SYS_GPH_MFPH_PH9MFP_UART3_nCTS   (0x07UL<<SYS_GPH_MFPH_PH9MFP_Pos) /*!< GPH_MFPH PH9 setting for UART3_nCTS  */
#define SYS_GPH_MFPH_PH9MFP_I2C1_SMBSUS  (0x08UL<<SYS_GPH_MFPH_PH9MFP_Pos) /*!< GPH_MFPH PH9 setting for I2C1_SMBSUS */
#define SYS_GPH_MFPH_PH9MFP_I2C2_SDA     (0x09UL<<SYS_GPH_MFPH_PH9MFP_Pos) /*!< GPH_MFPH PH9 setting for I2C2_SDA    */
#define SYS_GPH_MFPH_PH9MFP_UART1_RXD    (0x0aUL<<SYS_GPH_MFPH_PH9MFP_Pos) /*!< GPH_MFPH PH9 setting for UART1_RXD   */

/* PH.10 MFP */
#define SYS_GPH_MFPH_PH10MFP_GPIO        (0x00UL<<SYS_GPH_MFPH_PH10MFP_Pos)/*!< GPH_MFPH PH10 setting for GPIO       */
#define SYS_GPH_MFPH_PH10MFP_EBI_AD14    (0x02UL<<SYS_GPH_MFPH_PH10MFP_Pos)/*!< GPH_MFPH PH10 setting for EBI_AD14   */
#define SYS_GPH_MFPH_PH10MFP_QSPI0_MISO1 (0x03UL<<SYS_GPH_MFPH_PH10MFP_Pos)/*!< GPH_MFPH PH10 setting for QSPI0_MISO1*/
#define SYS_GPH_MFPH_PH10MFP_SC2_nCD     (0x04UL<<SYS_GPH_MFPH_PH10MFP_Pos)/*!< GPH_MFPH PH10 setting for SC2_nCD    */
#define SYS_GPH_MFPH_PH10MFP_I2S0_LRCK   (0x05UL<<SYS_GPH_MFPH_PH10MFP_Pos)/*!< GPH_MFPH PH10 setting for I2S0_LRCK  */
#define SYS_GPH_MFPH_PH10MFP_SPI1_I2SMCLK (0x06UL<<SYS_GPH_MFPH_PH10MFP_Pos)/*!< GPH_MFPH PH10 setting for SPI1_I2SMCLK*/
#define SYS_GPH_MFPH_PH10MFP_UART4_TXD   (0x07UL<<SYS_GPH_MFPH_PH10MFP_Pos)/*!< GPH_MFPH PH10 setting for UART4_TXD  */
#define SYS_GPH_MFPH_PH10MFP_UART0_TXD   (0x08UL<<SYS_GPH_MFPH_PH10MFP_Pos)/*!< GPH_MFPH PH10 setting for UART0_TXD  */

/* PH.11 MFP */
#define SYS_GPH_MFPH_PH11MFP_GPIO        (0x00UL<<SYS_GPH_MFPH_PH11MFP_Pos)/*!< GPH_MFPH PH11 setting for GPIO       */
#define SYS_GPH_MFPH_PH11MFP_EBI_AD15    (0x02UL<<SYS_GPH_MFPH_PH11MFP_Pos)/*!< GPH_MFPH PH11 setting for EBI_AD15   */
#define SYS_GPH_MFPH_PH11MFP_QSPI0_MOSI1 (0x03UL<<SYS_GPH_MFPH_PH11MFP_Pos)/*!< GPH_MFPH PH11 setting for QSPI0_MOSI1*/
#define SYS_GPH_MFPH_PH11MFP_UART4_RXD   (0x07UL<<SYS_GPH_MFPH_PH11MFP_Pos)/*!< GPH_MFPH PH11 setting for UART4_RXD  */
#define SYS_GPH_MFPH_PH11MFP_UART0_RXD   (0x08UL<<SYS_GPH_MFPH_PH11MFP_Pos)/*!< GPH_MFPH PH11 setting for UART0_RXD  */
#define SYS_GPH_MFPH_PH11MFP_EPWM0_CH5   (0x0bUL<<SYS_GPH_MFPH_PH11MFP_Pos)/*!< GPH_MFPH PH11 setting for EPWM0_CH5  */


/*---------------------------------------------------------------------------------------------------------*/
/*  Multi-Function setting constant definitions abbreviation.                                              */
/*---------------------------------------------------------------------------------------------------------*/

#define ACMP0_N_PB3              SYS_GPB_MFPL_PB3MFP_ACMP0_N          /*!< GPB_MFPL PB3 setting for ACMP0_N*/
#define ACMP0_O_PB7              SYS_GPB_MFPL_PB7MFP_ACMP0_O          /*!< GPB_MFPL PB7 setting for ACMP0_O*/
#define ACMP0_O_PC1              SYS_GPC_MFPL_PC1MFP_ACMP0_O          /*!< GPC_MFPL PC1 setting for ACMP0_O*/
#define ACMP0_O_PC12             SYS_GPC_MFPH_PC12MFP_ACMP0_O         /*!< GPC_MFPH PC12 setting for ACMP0_O*/
#define ACMP0_P0_PA11            SYS_GPA_MFPH_PA11MFP_ACMP0_P0        /*!< GPA_MFPH PA11 setting for ACMP0_P0*/
#define ACMP0_P1_PB2             SYS_GPB_MFPL_PB2MFP_ACMP0_P1         /*!< GPB_MFPL PB2 setting for ACMP0_P1*/
#define ACMP0_P2_PB12            SYS_GPB_MFPH_PB12MFP_ACMP0_P2        /*!< GPB_MFPH PB12 setting for ACMP0_P2*/
#define ACMP0_P3_PB13            SYS_GPB_MFPH_PB13MFP_ACMP0_P3        /*!< GPB_MFPH PB13 setting for ACMP0_P3*/
#define ACMP0_WLAT_PA7           SYS_GPA_MFPL_PA7MFP_ACMP0_WLAT       /*!< GPA_MFPL PA7 setting for ACMP0_WLAT*/
#define ACMP1_N_PB5              SYS_GPB_MFPL_PB5MFP_ACMP1_N          /*!< GPB_MFPL PB5 setting for ACMP1_N*/
#define ACMP1_O_PB6              SYS_GPB_MFPL_PB6MFP_ACMP1_O          /*!< GPB_MFPL PB6 setting for ACMP1_O*/
#define ACMP1_O_PC11             SYS_GPC_MFPH_PC11MFP_ACMP1_O         /*!< GPC_MFPH PC11 setting for ACMP1_O*/
#define ACMP1_O_PC0              SYS_GPC_MFPL_PC0MFP_ACMP1_O          /*!< GPC_MFPL PC0 setting for ACMP1_O*/
#define ACMP1_P0_PA10            SYS_GPA_MFPH_PA10MFP_ACMP1_P0        /*!< GPA_MFPH PA10 setting for ACMP1_P0*/
#define ACMP1_P1_PB4             SYS_GPB_MFPL_PB4MFP_ACMP1_P1         /*!< GPB_MFPL PB4 setting for ACMP1_P1*/
#define ACMP1_P2_PB12            SYS_GPB_MFPH_PB12MFP_ACMP1_P2        /*!< GPB_MFPH PB12 setting for ACMP1_P2*/
#define ACMP1_P3_PB13            SYS_GPB_MFPH_PB13MFP_ACMP1_P3        /*!< GPB_MFPH PB13 setting for ACMP1_P3*/
#define ACMP1_WLAT_PA6           SYS_GPA_MFPL_PA6MFP_ACMP1_WLAT       /*!< GPA_MFPL PA6 setting for ACMP1_WLAT*/
#define BPWM0_CH0_PA0            SYS_GPA_MFPL_PA0MFP_BPWM0_CH0        /*!< GPA_MFPL PA0 setting for BPWM0_CH0*/
#define BPWM0_CH0_PA11           SYS_GPA_MFPH_PA11MFP_BPWM0_CH0       /*!< GPA_MFPH PA11 setting for BPWM0_CH0*/
#define BPWM0_CH0_PE2            SYS_GPE_MFPL_PE2MFP_BPWM0_CH0        /*!< GPE_MFPL PE2 setting for BPWM0_CH0*/
#define BPWM0_CH0_PG14           SYS_GPG_MFPH_PG14MFP_BPWM0_CH0       /*!< GPG_MFPH PG14 setting for BPWM0_CH0*/
#define BPWM0_CH1_PA1            SYS_GPA_MFPL_PA1MFP_BPWM0_CH1        /*!< GPA_MFPL PA1 setting for BPWM0_CH1*/
#define BPWM0_CH1_PE3            SYS_GPE_MFPL_PE3MFP_BPWM0_CH1        /*!< GPE_MFPL PE3 setting for BPWM0_CH1*/
#define BPWM0_CH1_PG13           SYS_GPG_MFPH_PG13MFP_BPWM0_CH1       /*!< GPG_MFPH PG13 setting for BPWM0_CH1*/
#define BPWM0_CH1_PA10           SYS_GPA_MFPH_PA10MFP_BPWM0_CH1       /*!< GPA_MFPH PA10 setting for BPWM0_CH1*/
#define BPWM0_CH2_PE4            SYS_GPE_MFPL_PE4MFP_BPWM0_CH2        /*!< GPE_MFPL PE4 setting for BPWM0_CH2*/
#define BPWM0_CH2_PG12           SYS_GPG_MFPH_PG12MFP_BPWM0_CH2       /*!< GPG_MFPH PG12 setting for BPWM0_CH2*/
#define BPWM0_CH2_PA2            SYS_GPA_MFPL_PA2MFP_BPWM0_CH2        /*!< GPA_MFPL PA2 setting for BPWM0_CH2*/
#define BPWM0_CH2_PA9            SYS_GPA_MFPH_PA9MFP_BPWM0_CH2        /*!< GPA_MFPH PA9 setting for BPWM0_CH2*/
#define BPWM0_CH3_PG11           SYS_GPG_MFPH_PG11MFP_BPWM0_CH3       /*!< GPG_MFPH PG11 setting for BPWM0_CH3*/
#define BPWM0_CH3_PA3            SYS_GPA_MFPL_PA3MFP_BPWM0_CH3        /*!< GPA_MFPL PA3 setting for BPWM0_CH3*/
#define BPWM0_CH3_PA8            SYS_GPA_MFPH_PA8MFP_BPWM0_CH3        /*!< GPA_MFPH PA8 setting for BPWM0_CH3*/
#define BPWM0_CH3_PE5            SYS_GPE_MFPL_PE5MFP_BPWM0_CH3        /*!< GPE_MFPL PE5 setting for BPWM0_CH3*/
#define BPWM0_CH4_PG10           SYS_GPG_MFPH_PG10MFP_BPWM0_CH4       /*!< GPG_MFPH PG10 setting for BPWM0_CH4*/
#define BPWM0_CH4_PA4            SYS_GPA_MFPL_PA4MFP_BPWM0_CH4        /*!< GPA_MFPL PA4 setting for BPWM0_CH4*/
#define BPWM0_CH4_PC13           SYS_GPC_MFPH_PC13MFP_BPWM0_CH4       /*!< GPC_MFPH PC13 setting for BPWM0_CH4*/
#define BPWM0_CH4_PE6            SYS_GPE_MFPL_PE6MFP_BPWM0_CH4        /*!< GPE_MFPL PE6 setting for BPWM0_CH4*/
#define BPWM0_CH4_PF5            SYS_GPF_MFPL_PF5MFP_BPWM0_CH4        /*!< GPF_MFPL PF5 setting for BPWM0_CH4*/
#define BPWM0_CH5_PA5            SYS_GPA_MFPL_PA5MFP_BPWM0_CH5        /*!< GPA_MFPL PA5 setting for BPWM0_CH5*/
#define BPWM0_CH5_PE7            SYS_GPE_MFPL_PE7MFP_BPWM0_CH5        /*!< GPE_MFPL PE7 setting for BPWM0_CH5*/
#define BPWM0_CH5_PF4            SYS_GPF_MFPL_PF4MFP_BPWM0_CH5        /*!< GPF_MFPL PF4 setting for BPWM0_CH5*/
#define BPWM0_CH5_PD12           SYS_GPD_MFPH_PD12MFP_BPWM0_CH5       /*!< GPD_MFPH PD12 setting for BPWM0_CH5*/
#define BPWM0_CH5_PG9            SYS_GPG_MFPH_PG9MFP_BPWM0_CH5        /*!< GPG_MFPH PG9 setting for BPWM0_CH5*/
#define BPWM1_CH0_PB11           SYS_GPB_MFPH_PB11MFP_BPWM1_CH0       /*!< GPB_MFPH PB11 setting for BPWM1_CH0*/
#define BPWM1_CH0_PC7            SYS_GPC_MFPL_PC7MFP_BPWM1_CH0        /*!< GPC_MFPL PC7 setting for BPWM1_CH0*/
#define BPWM1_CH0_PF0            SYS_GPF_MFPL_PF0MFP_BPWM1_CH0        /*!< GPF_MFPL PF0 setting for BPWM1_CH0*/
#define BPWM1_CH0_PF3            SYS_GPF_MFPL_PF3MFP_BPWM1_CH0        /*!< GPF_MFPL PF3 setting for BPWM1_CH0*/
#define BPWM1_CH1_PC6            SYS_GPC_MFPL_PC6MFP_BPWM1_CH1        /*!< GPC_MFPL PC6 setting for BPWM1_CH1*/
#define BPWM1_CH1_PF1            SYS_GPF_MFPL_PF1MFP_BPWM1_CH1        /*!< GPF_MFPL PF1 setting for BPWM1_CH1*/
#define BPWM1_CH1_PF2            SYS_GPF_MFPL_PF2MFP_BPWM1_CH1        /*!< GPF_MFPL PF2 setting for BPWM1_CH1*/
#define BPWM1_CH1_PB10           SYS_GPB_MFPH_PB10MFP_BPWM1_CH1       /*!< GPB_MFPH PB10 setting for BPWM1_CH1*/
#define BPWM1_CH2_PB9            SYS_GPB_MFPH_PB9MFP_BPWM1_CH2        /*!< GPB_MFPH PB9 setting for BPWM1_CH2*/
#define BPWM1_CH2_PA7            SYS_GPA_MFPL_PA7MFP_BPWM1_CH2        /*!< GPA_MFPL PA7 setting for BPWM1_CH2*/
#define BPWM1_CH2_PA12           SYS_GPA_MFPH_PA12MFP_BPWM1_CH2       /*!< GPA_MFPH PA12 setting for BPWM1_CH2*/
#define BPWM1_CH3_PA6            SYS_GPA_MFPL_PA6MFP_BPWM1_CH3        /*!< GPA_MFPL PA6 setting for BPWM1_CH3*/
#define BPWM1_CH3_PA13           SYS_GPA_MFPH_PA13MFP_BPWM1_CH3       /*!< GPA_MFPH PA13 setting for BPWM1_CH3*/
#define BPWM1_CH3_PB8            SYS_GPB_MFPH_PB8MFP_BPWM1_CH3        /*!< GPB_MFPH PB8 setting for BPWM1_CH3*/
#define BPWM1_CH4_PA14           SYS_GPA_MFPH_PA14MFP_BPWM1_CH4       /*!< GPA_MFPH PA14 setting for BPWM1_CH4*/
#define BPWM1_CH4_PC8            SYS_GPC_MFPH_PC8MFP_BPWM1_CH4        /*!< GPC_MFPH PC8 setting for BPWM1_CH4*/
#define BPWM1_CH4_PB7            SYS_GPB_MFPL_PB7MFP_BPWM1_CH4        /*!< GPB_MFPL PB7 setting for BPWM1_CH4*/
#define BPWM1_CH5_PA15           SYS_GPA_MFPH_PA15MFP_BPWM1_CH5       /*!< GPA_MFPH PA15 setting for BPWM1_CH5*/
#define BPWM1_CH5_PB6            SYS_GPB_MFPL_PB6MFP_BPWM1_CH5        /*!< GPB_MFPL PB6 setting for BPWM1_CH5*/
#define BPWM1_CH5_PE13           SYS_GPE_MFPH_PE13MFP_BPWM1_CH5       /*!< GPE_MFPH PE13 setting for BPWM1_CH5*/
#define CAN0_RXD_PA13            SYS_GPA_MFPH_PA13MFP_CAN0_RXD        /*!< GPA_MFPH PA13 setting for CAN0_RXD*/
#define CAN0_RXD_PD10            SYS_GPD_MFPH_PD10MFP_CAN0_RXD        /*!< GPD_MFPH PD10 setting for CAN0_RXD*/
#define CAN0_RXD_PA4             SYS_GPA_MFPL_PA4MFP_CAN0_RXD         /*!< GPA_MFPL PA4 setting for CAN0_RXD*/
#define CAN0_RXD_PC4             SYS_GPC_MFPL_PC4MFP_CAN0_RXD         /*!< GPC_MFPL PC4 setting for CAN0_RXD*/
#define CAN0_RXD_PB10            SYS_GPB_MFPH_PB10MFP_CAN0_RXD        /*!< GPB_MFPH PB10 setting for CAN0_RXD*/
#define CAN0_RXD_PE15            SYS_GPE_MFPH_PE15MFP_CAN0_RXD        /*!< GPE_MFPH PE15 setting for CAN0_RXD*/
#define CAN0_TXD_PD11            SYS_GPD_MFPH_PD11MFP_CAN0_TXD        /*!< GPD_MFPH PD11 setting for CAN0_TXD*/
#define CAN0_TXD_PC5             SYS_GPC_MFPL_PC5MFP_CAN0_TXD         /*!< GPC_MFPL PC5 setting for CAN0_TXD*/
#define CAN0_TXD_PB11            SYS_GPB_MFPH_PB11MFP_CAN0_TXD        /*!< GPB_MFPH PB11 setting for CAN0_TXD*/
#define CAN0_TXD_PA12            SYS_GPA_MFPH_PA12MFP_CAN0_TXD        /*!< GPA_MFPH PA12 setting for CAN0_TXD*/
#define CAN0_TXD_PE14            SYS_GPE_MFPH_PE14MFP_CAN0_TXD        /*!< GPE_MFPH PE14 setting for CAN0_TXD*/
#define CAN0_TXD_PA5             SYS_GPA_MFPL_PA5MFP_CAN0_TXD         /*!< GPA_MFPL PA5 setting for CAN0_TXD*/
#define CLKO_PC13                SYS_GPC_MFPH_PC13MFP_CLKO            /*!< GPC_MFPH PC13 setting for CLKO*/
#define CLKO_PB14                SYS_GPB_MFPH_PB14MFP_CLKO            /*!< GPB_MFPH PB14 setting for CLKO*/
#define CLKO_PD12                SYS_GPD_MFPH_PD12MFP_CLKO            /*!< GPD_MFPH PD12 setting for CLKO*/
#define CLKO_PG15                SYS_GPG_MFPH_PG15MFP_CLKO            /*!< GPG_MFPH PG15 setting for CLKO*/
#define DAC0_OUT_PB12            SYS_GPB_MFPH_PB12MFP_DAC0_OUT        /*!< GPB_MFPH PB12 setting for DAC0_OUT*/
#define DAC0_ST_PA10             SYS_GPA_MFPH_PA10MFP_DAC0_ST         /*!< GPA_MFPH PA10 setting for DAC0_ST*/
#define DAC0_ST_PA0              SYS_GPA_MFPL_PA0MFP_DAC0_ST          /*!< GPA_MFPL PA0 setting for DAC0_ST*/
#define DAC1_OUT_PB13            SYS_GPB_MFPH_PB13MFP_DAC1_OUT        /*!< GPB_MFPH PB13 setting for DAC1_OUT*/
#define DAC1_ST_PA1              SYS_GPA_MFPL_PA1MFP_DAC1_ST          /*!< GPA_MFPL PA1 setting for DAC1_ST*/
#define DAC1_ST_PA11             SYS_GPA_MFPH_PA11MFP_DAC1_ST         /*!< GPA_MFPH PA11 setting for DAC1_ST*/
#define EADC0_CH0_PB0            SYS_GPB_MFPL_PB0MFP_EADC0_CH0        /*!< GPB_MFPL PB0 setting for EADC0_CH0*/
#define EADC0_CH1_PB1            SYS_GPB_MFPL_PB1MFP_EADC0_CH1        /*!< GPB_MFPL PB1 setting for EADC0_CH1*/
#define EADC0_CH10_PB10          SYS_GPB_MFPH_PB10MFP_EADC0_CH10      /*!< GPB_MFPH PB10 setting for EADC0_CH10*/
#define EADC0_CH11_PB11          SYS_GPB_MFPH_PB11MFP_EADC0_CH11      /*!< GPB_MFPH PB11 setting for EADC0_CH11*/
#define EADC0_CH12_PB12          SYS_GPB_MFPH_PB12MFP_EADC0_CH12      /*!< GPB_MFPH PB12 setting for EADC0_CH12*/
#define EADC0_CH13_PB13          SYS_GPB_MFPH_PB13MFP_EADC0_CH13      /*!< GPB_MFPH PB13 setting for EADC0_CH13*/
#define EADC0_CH14_PB14          SYS_GPB_MFPH_PB14MFP_EADC0_CH14      /*!< GPB_MFPH PB14 setting for EADC0_CH14*/
#define EADC0_CH15_PB15          SYS_GPB_MFPH_PB15MFP_EADC0_CH15      /*!< GPB_MFPH PB15 setting for EADC0_CH15*/
#define EADC0_CH2_PB2            SYS_GPB_MFPL_PB2MFP_EADC0_CH2        /*!< GPB_MFPL PB2 setting for EADC0_CH2*/
#define EADC0_CH3_PB3            SYS_GPB_MFPL_PB3MFP_EADC0_CH3        /*!< GPB_MFPL PB3 setting for EADC0_CH3*/
#define EADC0_CH4_PB4            SYS_GPB_MFPL_PB4MFP_EADC0_CH4        /*!< GPB_MFPL PB4 setting for EADC0_CH4*/
#define EADC0_CH5_PB5            SYS_GPB_MFPL_PB5MFP_EADC0_CH5        /*!< GPB_MFPL PB5 setting for EADC0_CH5*/
#define EADC0_CH6_PB6            SYS_GPB_MFPL_PB6MFP_EADC0_CH6        /*!< GPB_MFPL PB6 setting for EADC0_CH6*/
#define EADC0_CH7_PB7            SYS_GPB_MFPL_PB7MFP_EADC0_CH7        /*!< GPB_MFPL PB7 setting for EADC0_CH7*/
#define EADC0_CH8_PB8            SYS_GPB_MFPH_PB8MFP_EADC0_CH8        /*!< GPB_MFPH PB8 setting for EADC0_CH8*/
#define EADC0_CH9_PB9            SYS_GPB_MFPH_PB9MFP_EADC0_CH9        /*!< GPB_MFPH PB9 setting for EADC0_CH9*/
#define EADC0_ST_PD12            SYS_GPD_MFPH_PD12MFP_EADC0_ST        /*!< GPD_MFPH PD12 setting for EADC0_ST*/
#define EADC0_ST_PF5             SYS_GPF_MFPL_PF5MFP_EADC0_ST         /*!< GPF_MFPL PF5 setting for EADC0_ST*/
#define EADC0_ST_PC13            SYS_GPC_MFPH_PC13MFP_EADC0_ST        /*!< GPC_MFPH PC13 setting for EADC0_ST*/
#define EADC0_ST_PG15            SYS_GPG_MFPH_PG15MFP_EADC0_ST        /*!< GPG_MFPH PG15 setting for EADC0_ST*/
#define EBI_AD0_PG9              SYS_GPG_MFPH_PG9MFP_EBI_AD0          /*!< GPG_MFPH PG9 setting for EBI_AD0*/
#define EBI_AD0_PC0              SYS_GPC_MFPL_PC0MFP_EBI_AD0          /*!< GPC_MFPL PC0 setting for EBI_AD0*/
#define EBI_AD1_PC1              SYS_GPC_MFPL_PC1MFP_EBI_AD1          /*!< GPC_MFPL PC1 setting for EBI_AD1*/
#define EBI_AD1_PG10             SYS_GPG_MFPH_PG10MFP_EBI_AD1         /*!< GPG_MFPH PG10 setting for EBI_AD1*/
#define EBI_AD10_PE1             SYS_GPE_MFPL_PE1MFP_EBI_AD10         /*!< GPE_MFPL PE1 setting for EBI_AD10*/
#define EBI_AD10_PD3             SYS_GPD_MFPL_PD3MFP_EBI_AD10         /*!< GPD_MFPL PD3 setting for EBI_AD10*/
#define EBI_AD10_PD13            SYS_GPD_MFPH_PD13MFP_EBI_AD10        /*!< GPD_MFPH PD13 setting for EBI_AD10*/
#define EBI_AD11_PE0             SYS_GPE_MFPL_PE0MFP_EBI_AD11         /*!< GPE_MFPL PE0 setting for EBI_AD11*/
#define EBI_AD11_PD2             SYS_GPD_MFPL_PD2MFP_EBI_AD11         /*!< GPD_MFPL PD2 setting for EBI_AD11*/
#define EBI_AD12_PD1             SYS_GPD_MFPL_PD1MFP_EBI_AD12         /*!< GPD_MFPL PD1 setting for EBI_AD12*/
#define EBI_AD12_PB15            SYS_GPB_MFPH_PB15MFP_EBI_AD12        /*!< GPB_MFPH PB15 setting for EBI_AD12*/
#define EBI_AD12_PH8             SYS_GPH_MFPH_PH8MFP_EBI_AD12         /*!< GPH_MFPH PH8 setting for EBI_AD12*/
#define EBI_AD13_PD0             SYS_GPD_MFPL_PD0MFP_EBI_AD13         /*!< GPD_MFPL PD0 setting for EBI_AD13*/
#define EBI_AD13_PB14            SYS_GPB_MFPH_PB14MFP_EBI_AD13        /*!< GPB_MFPH PB14 setting for EBI_AD13*/
#define EBI_AD13_PH9             SYS_GPH_MFPH_PH9MFP_EBI_AD13         /*!< GPH_MFPH PH9 setting for EBI_AD13*/
#define EBI_AD14_PB13            SYS_GPB_MFPH_PB13MFP_EBI_AD14        /*!< GPB_MFPH PB13 setting for EBI_AD14*/
#define EBI_AD14_PH10            SYS_GPH_MFPH_PH10MFP_EBI_AD14        /*!< GPH_MFPH PH10 setting for EBI_AD14*/
#define EBI_AD15_PB12            SYS_GPB_MFPH_PB12MFP_EBI_AD15        /*!< GPB_MFPH PB12 setting for EBI_AD15*/
#define EBI_AD15_PH11            SYS_GPH_MFPH_PH11MFP_EBI_AD15        /*!< GPH_MFPH PH11 setting for EBI_AD15*/
#define EBI_AD2_PG11             SYS_GPG_MFPH_PG11MFP_EBI_AD2         /*!< GPG_MFPH PG11 setting for EBI_AD2*/
#define EBI_AD2_PC2              SYS_GPC_MFPL_PC2MFP_EBI_AD2          /*!< GPC_MFPL PC2 setting for EBI_AD2*/
#define EBI_AD3_PC3              SYS_GPC_MFPL_PC3MFP_EBI_AD3          /*!< GPC_MFPL PC3 setting for EBI_AD3*/
#define EBI_AD3_PG12             SYS_GPG_MFPH_PG12MFP_EBI_AD3         /*!< GPG_MFPH PG12 setting for EBI_AD3*/
#define EBI_AD4_PG13             SYS_GPG_MFPH_PG13MFP_EBI_AD4         /*!< GPG_MFPH PG13 setting for EBI_AD4*/
#define EBI_AD4_PC4              SYS_GPC_MFPL_PC4MFP_EBI_AD4          /*!< GPC_MFPL PC4 setting for EBI_AD4*/
#define EBI_AD5_PG14             SYS_GPG_MFPH_PG14MFP_EBI_AD5         /*!< GPG_MFPH PG14 setting for EBI_AD5*/
#define EBI_AD5_PC5              SYS_GPC_MFPL_PC5MFP_EBI_AD5          /*!< GPC_MFPL PC5 setting for EBI_AD5*/
#define EBI_AD6_PD8              SYS_GPD_MFPH_PD8MFP_EBI_AD6          /*!< GPD_MFPH PD8 setting for EBI_AD6*/
#define EBI_AD6_PA6              SYS_GPA_MFPL_PA6MFP_EBI_AD6          /*!< GPA_MFPL PA6 setting for EBI_AD6*/
#define EBI_AD7_PA7              SYS_GPA_MFPL_PA7MFP_EBI_AD7          /*!< GPA_MFPL PA7 setting for EBI_AD7*/
#define EBI_AD7_PD9              SYS_GPD_MFPH_PD9MFP_EBI_AD7          /*!< GPD_MFPH PD9 setting for EBI_AD7*/
#define EBI_AD8_PC6              SYS_GPC_MFPL_PC6MFP_EBI_AD8          /*!< GPC_MFPL PC6 setting for EBI_AD8*/
#define EBI_AD8_PE14             SYS_GPE_MFPH_PE14MFP_EBI_AD8         /*!< GPE_MFPH PE14 setting for EBI_AD8*/
#define EBI_AD9_PE15             SYS_GPE_MFPH_PE15MFP_EBI_AD9         /*!< GPE_MFPH PE15 setting for EBI_AD9*/
#define EBI_AD9_PC7              SYS_GPC_MFPL_PC7MFP_EBI_AD9          /*!< GPC_MFPL PC7 setting for EBI_AD9*/
#define EBI_ADR0_PB5             SYS_GPB_MFPL_PB5MFP_EBI_ADR0         /*!< GPB_MFPL PB5 setting for EBI_ADR0*/
#define EBI_ADR0_PH7             SYS_GPH_MFPL_PH7MFP_EBI_ADR0         /*!< GPH_MFPL PH7 setting for EBI_ADR0*/
#define EBI_ADR1_PH6             SYS_GPH_MFPL_PH6MFP_EBI_ADR1         /*!< GPH_MFPL PH6 setting for EBI_ADR1*/
#define EBI_ADR1_PB4             SYS_GPB_MFPL_PB4MFP_EBI_ADR1         /*!< GPB_MFPL PB4 setting for EBI_ADR1*/
#define EBI_ADR10_PE8            SYS_GPE_MFPH_PE8MFP_EBI_ADR10        /*!< GPE_MFPH PE8 setting for EBI_ADR10*/
#define EBI_ADR10_PC13           SYS_GPC_MFPH_PC13MFP_EBI_ADR10       /*!< GPC_MFPH PC13 setting for EBI_ADR10*/
#define EBI_ADR11_PG2            SYS_GPG_MFPL_PG2MFP_EBI_ADR11        /*!< GPG_MFPL PG2 setting for EBI_ADR11*/
#define EBI_ADR11_PE9            SYS_GPE_MFPH_PE9MFP_EBI_ADR11        /*!< GPE_MFPH PE9 setting for EBI_ADR11*/
#define EBI_ADR12_PG3            SYS_GPG_MFPL_PG3MFP_EBI_ADR12        /*!< GPG_MFPL PG3 setting for EBI_ADR12*/
#define EBI_ADR12_PE10           SYS_GPE_MFPH_PE10MFP_EBI_ADR12       /*!< GPE_MFPH PE10 setting for EBI_ADR12*/
#define EBI_ADR13_PG4            SYS_GPG_MFPL_PG4MFP_EBI_ADR13        /*!< GPG_MFPL PG4 setting for EBI_ADR13*/
#define EBI_ADR13_PE11           SYS_GPE_MFPH_PE11MFP_EBI_ADR13       /*!< GPE_MFPH PE11 setting for EBI_ADR13*/
#define EBI_ADR14_PE12           SYS_GPE_MFPH_PE12MFP_EBI_ADR14       /*!< GPE_MFPH PE12 setting for EBI_ADR14*/
#define EBI_ADR14_PF11           SYS_GPF_MFPH_PF11MFP_EBI_ADR14       /*!< GPF_MFPH PF11 setting for EBI_ADR14*/
#define EBI_ADR15_PF10           SYS_GPF_MFPH_PF10MFP_EBI_ADR15       /*!< GPF_MFPH PF10 setting for EBI_ADR15*/
#define EBI_ADR15_PE13           SYS_GPE_MFPH_PE13MFP_EBI_ADR15       /*!< GPE_MFPH PE13 setting for EBI_ADR15*/
#define EBI_ADR16_PB11           SYS_GPB_MFPH_PB11MFP_EBI_ADR16       /*!< GPB_MFPH PB11 setting for EBI_ADR16*/
#define EBI_ADR16_PF9            SYS_GPF_MFPH_PF9MFP_EBI_ADR16        /*!< GPF_MFPH PF9 setting for EBI_ADR16*/
#define EBI_ADR16_PC8            SYS_GPC_MFPH_PC8MFP_EBI_ADR16        /*!< GPC_MFPH PC8 setting for EBI_ADR16*/
#define EBI_ADR17_PF8            SYS_GPF_MFPH_PF8MFP_EBI_ADR17        /*!< GPF_MFPH PF8 setting for EBI_ADR17*/
#define EBI_ADR17_PB10           SYS_GPB_MFPH_PB10MFP_EBI_ADR17       /*!< GPB_MFPH PB10 setting for EBI_ADR17*/
#define EBI_ADR18_PB9            SYS_GPB_MFPH_PB9MFP_EBI_ADR18        /*!< GPB_MFPH PB9 setting for EBI_ADR18*/
#define EBI_ADR18_PF7            SYS_GPF_MFPL_PF7MFP_EBI_ADR18        /*!< GPF_MFPL PF7 setting for EBI_ADR18*/
#define EBI_ADR19_PF6            SYS_GPF_MFPL_PF6MFP_EBI_ADR19        /*!< GPF_MFPL PF6 setting for EBI_ADR19*/
#define EBI_ADR19_PB8            SYS_GPB_MFPH_PB8MFP_EBI_ADR19        /*!< GPB_MFPH PB8 setting for EBI_ADR19*/
#define EBI_ADR2_PB3             SYS_GPB_MFPL_PB3MFP_EBI_ADR2         /*!< GPB_MFPL PB3 setting for EBI_ADR2*/
#define EBI_ADR2_PH5             SYS_GPH_MFPL_PH5MFP_EBI_ADR2         /*!< GPH_MFPL PH5 setting for EBI_ADR2*/
#define EBI_ADR3_PH4             SYS_GPH_MFPL_PH4MFP_EBI_ADR3         /*!< GPH_MFPL PH4 setting for EBI_ADR3*/
#define EBI_ADR3_PB2             SYS_GPB_MFPL_PB2MFP_EBI_ADR3         /*!< GPB_MFPL PB2 setting for EBI_ADR3*/
#define EBI_ADR4_PC12            SYS_GPC_MFPH_PC12MFP_EBI_ADR4        /*!< GPC_MFPH PC12 setting for EBI_ADR4*/
#define EBI_ADR5_PC11            SYS_GPC_MFPH_PC11MFP_EBI_ADR5        /*!< GPC_MFPH PC11 setting for EBI_ADR5*/
#define EBI_ADR6_PC10            SYS_GPC_MFPH_PC10MFP_EBI_ADR6        /*!< GPC_MFPH PC10 setting for EBI_ADR6*/
#define EBI_ADR7_PC9             SYS_GPC_MFPH_PC9MFP_EBI_ADR7         /*!< GPC_MFPH PC9 setting for EBI_ADR7*/
#define EBI_ADR8_PB1             SYS_GPB_MFPL_PB1MFP_EBI_ADR8         /*!< GPB_MFPL PB1 setting for EBI_ADR8*/
#define EBI_ADR9_PB0             SYS_GPB_MFPL_PB0MFP_EBI_ADR9         /*!< GPB_MFPL PB0 setting for EBI_ADR9*/
#define EBI_ALE_PA8              SYS_GPA_MFPH_PA8MFP_EBI_ALE          /*!< GPA_MFPH PA8 setting for EBI_ALE*/
#define EBI_ALE_PE2              SYS_GPE_MFPL_PE2MFP_EBI_ALE          /*!< GPE_MFPL PE2 setting for EBI_ALE*/
#define EBI_MCLK_PE3             SYS_GPE_MFPL_PE3MFP_EBI_MCLK         /*!< GPE_MFPL PE3 setting for EBI_MCLK*/
#define EBI_MCLK_PA9             SYS_GPA_MFPH_PA9MFP_EBI_MCLK         /*!< GPA_MFPH PA9 setting for EBI_MCLK*/
#define EBI_nCS0_PB7             SYS_GPB_MFPL_PB7MFP_EBI_nCS0         /*!< GPB_MFPL PB7 setting for EBI_nCS0*/
#define EBI_nCS0_PF6             SYS_GPF_MFPL_PF6MFP_EBI_nCS0         /*!< GPF_MFPL PF6 setting for EBI_nCS0*/
#define EBI_nCS0_PD12            SYS_GPD_MFPH_PD12MFP_EBI_nCS0        /*!< GPD_MFPH PD12 setting for EBI_nCS0*/
#define EBI_nCS0_PD14            SYS_GPD_MFPH_PD14MFP_EBI_nCS0        /*!< GPD_MFPH PD14 setting for EBI_nCS0*/
#define EBI_nCS0_PF3             SYS_GPF_MFPL_PF3MFP_EBI_nCS0         /*!< GPF_MFPL PF3 setting for EBI_nCS0*/
#define EBI_nCS1_PF2             SYS_GPF_MFPL_PF2MFP_EBI_nCS1         /*!< GPF_MFPL PF2 setting for EBI_nCS1*/
#define EBI_nCS1_PD11            SYS_GPD_MFPH_PD11MFP_EBI_nCS1        /*!< GPD_MFPH PD11 setting for EBI_nCS1*/
#define EBI_nCS1_PB6             SYS_GPB_MFPL_PB6MFP_EBI_nCS1         /*!< GPB_MFPL PB6 setting for EBI_nCS1*/
#define EBI_nCS2_PD10            SYS_GPD_MFPH_PD10MFP_EBI_nCS2        /*!< GPD_MFPH PD10 setting for EBI_nCS2*/
#define EBI_nRD_PA11             SYS_GPA_MFPH_PA11MFP_EBI_nRD         /*!< GPA_MFPH PA11 setting for EBI_nRD*/
#define EBI_nRD_PE5              SYS_GPE_MFPL_PE5MFP_EBI_nRD          /*!< GPE_MFPL PE5 setting for EBI_nRD*/
#define EBI_nWR_PA10             SYS_GPA_MFPH_PA10MFP_EBI_nWR         /*!< GPA_MFPH PA10 setting for EBI_nWR*/
#define EBI_nWR_PE4              SYS_GPE_MFPL_PE4MFP_EBI_nWR          /*!< GPE_MFPL PE4 setting for EBI_nWR*/
#define EBI_nWRH_PB6             SYS_GPB_MFPL_PB6MFP_EBI_nWRH         /*!< GPB_MFPL PB6 setting for EBI_nWRH*/
#define EBI_nWRL_PB7             SYS_GPB_MFPL_PB7MFP_EBI_nWRL         /*!< GPB_MFPL PB7 setting for EBI_nWRL*/
#define ECAP0_IC0_PA10           SYS_GPA_MFPH_PA10MFP_ECAP0_IC0       /*!< GPA_MFPH PA10 setting for ECAP0_IC0*/
#define ECAP0_IC0_PE8            SYS_GPE_MFPH_PE8MFP_ECAP0_IC0        /*!< GPE_MFPH PE8 setting for ECAP0_IC0*/
#define ECAP0_IC1_PE9            SYS_GPE_MFPH_PE9MFP_ECAP0_IC1        /*!< GPE_MFPH PE9 setting for ECAP0_IC1*/
#define ECAP0_IC1_PA9            SYS_GPA_MFPH_PA9MFP_ECAP0_IC1        /*!< GPA_MFPH PA9 setting for ECAP0_IC1*/
#define ECAP0_IC2_PA8            SYS_GPA_MFPH_PA8MFP_ECAP0_IC2        /*!< GPA_MFPH PA8 setting for ECAP0_IC2*/
#define ECAP0_IC2_PE10           SYS_GPE_MFPH_PE10MFP_ECAP0_IC2       /*!< GPE_MFPH PE10 setting for ECAP0_IC2*/
#define ECAP1_IC0_PC10           SYS_GPC_MFPH_PC10MFP_ECAP1_IC0       /*!< GPC_MFPH PC10 setting for ECAP1_IC0*/
#define ECAP1_IC0_PE13           SYS_GPE_MFPH_PE13MFP_ECAP1_IC0       /*!< GPE_MFPH PE13 setting for ECAP1_IC0*/
#define ECAP1_IC1_PE12           SYS_GPE_MFPH_PE12MFP_ECAP1_IC1       /*!< GPE_MFPH PE12 setting for ECAP1_IC1*/
#define ECAP1_IC1_PC11           SYS_GPC_MFPH_PC11MFP_ECAP1_IC1       /*!< GPC_MFPH PC11 setting for ECAP1_IC1*/
#define ECAP1_IC2_PE11           SYS_GPE_MFPH_PE11MFP_ECAP1_IC2       /*!< GPE_MFPH PE11 setting for ECAP1_IC2*/
#define ECAP1_IC2_PC12           SYS_GPC_MFPH_PC12MFP_ECAP1_IC2       /*!< GPC_MFPH PC12 setting for ECAP1_IC2*/
#define I2C0_SCL_PB5             SYS_GPB_MFPL_PB5MFP_I2C0_SCL         /*!< GPB_MFPL PB5 setting for I2C0_SCL*/
#define I2C0_SCL_PC1             SYS_GPC_MFPL_PC1MFP_I2C0_SCL         /*!< GPC_MFPL PC1 setting for I2C0_SCL*/
#define I2C0_SCL_PF3             SYS_GPF_MFPL_PF3MFP_I2C0_SCL         /*!< GPF_MFPL PF3 setting for I2C0_SCL*/
#define I2C0_SCL_PE13            SYS_GPE_MFPH_PE13MFP_I2C0_SCL        /*!< GPE_MFPH PE13 setting for I2C0_SCL*/
#define I2C0_SCL_PD7             SYS_GPD_MFPL_PD7MFP_I2C0_SCL         /*!< GPD_MFPL PD7 setting for I2C0_SCL*/
#define I2C0_SCL_PA5             SYS_GPA_MFPL_PA5MFP_I2C0_SCL         /*!< GPA_MFPL PA5 setting for I2C0_SCL*/
#define I2C0_SCL_PC12            SYS_GPC_MFPH_PC12MFP_I2C0_SCL        /*!< GPC_MFPH PC12 setting for I2C0_SCL*/
#define I2C0_SDA_PB4             SYS_GPB_MFPL_PB4MFP_I2C0_SDA         /*!< GPB_MFPL PB4 setting for I2C0_SDA*/
#define I2C0_SDA_PC8             SYS_GPC_MFPH_PC8MFP_I2C0_SDA         /*!< GPC_MFPH PC8 setting for I2C0_SDA*/
#define I2C0_SDA_PC0             SYS_GPC_MFPL_PC0MFP_I2C0_SDA         /*!< GPC_MFPL PC0 setting for I2C0_SDA*/
#define I2C0_SDA_PD6             SYS_GPD_MFPL_PD6MFP_I2C0_SDA         /*!< GPD_MFPL PD6 setting for I2C0_SDA*/
#define I2C0_SDA_PC11            SYS_GPC_MFPH_PC11MFP_I2C0_SDA        /*!< GPC_MFPH PC11 setting for I2C0_SDA*/
#define I2C0_SDA_PA4             SYS_GPA_MFPL_PA4MFP_I2C0_SDA         /*!< GPA_MFPL PA4 setting for I2C0_SDA*/
#define I2C0_SDA_PF2             SYS_GPF_MFPL_PF2MFP_I2C0_SDA         /*!< GPF_MFPL PF2 setting for I2C0_SDA*/
#define I2C0_SMBAL_PG2           SYS_GPG_MFPL_PG2MFP_I2C0_SMBAL       /*!< GPG_MFPL PG2 setting for I2C0_SMBAL*/
#define I2C0_SMBAL_PC3           SYS_GPC_MFPL_PC3MFP_I2C0_SMBAL       /*!< GPC_MFPL PC3 setting for I2C0_SMBAL*/
#define I2C0_SMBSUS_PC2          SYS_GPC_MFPL_PC2MFP_I2C0_SMBSUS      /*!< GPC_MFPL PC2 setting for I2C0_SMBSUS*/
#define I2C0_SMBSUS_PG3          SYS_GPG_MFPL_PG3MFP_I2C0_SMBSUS      /*!< GPG_MFPL PG3 setting for I2C0_SMBSUS*/
#define I2C1_SCL_PA3             SYS_GPA_MFPL_PA3MFP_I2C1_SCL         /*!< GPA_MFPL PA3 setting for I2C1_SCL*/
#define I2C1_SCL_PG2             SYS_GPG_MFPL_PG2MFP_I2C1_SCL         /*!< GPG_MFPL PG2 setting for I2C1_SCL*/
#define I2C1_SCL_PB1             SYS_GPB_MFPL_PB1MFP_I2C1_SCL         /*!< GPB_MFPL PB1 setting for I2C1_SCL*/
#define I2C1_SCL_PB11            SYS_GPB_MFPH_PB11MFP_I2C1_SCL        /*!< GPB_MFPH PB11 setting for I2C1_SCL*/
#define I2C1_SCL_PD5             SYS_GPD_MFPL_PD5MFP_I2C1_SCL         /*!< GPD_MFPL PD5 setting for I2C1_SCL*/
#define I2C1_SCL_PA12            SYS_GPA_MFPH_PA12MFP_I2C1_SCL        /*!< GPA_MFPH PA12 setting for I2C1_SCL*/
#define I2C1_SCL_PC5             SYS_GPC_MFPL_PC5MFP_I2C1_SCL         /*!< GPC_MFPL PC5 setting for I2C1_SCL*/
#define I2C1_SCL_PA7             SYS_GPA_MFPL_PA7MFP_I2C1_SCL         /*!< GPA_MFPL PA7 setting for I2C1_SCL*/
#define I2C1_SCL_PF0             SYS_GPF_MFPL_PF0MFP_I2C1_SCL         /*!< GPF_MFPL PF0 setting for I2C1_SCL*/
#define I2C1_SCL_PE1             SYS_GPE_MFPL_PE1MFP_I2C1_SCL         /*!< GPE_MFPL PE1 setting for I2C1_SCL*/
#define I2C1_SDA_PB0             SYS_GPB_MFPL_PB0MFP_I2C1_SDA         /*!< GPB_MFPL PB0 setting for I2C1_SDA*/
#define I2C1_SDA_PA6             SYS_GPA_MFPL_PA6MFP_I2C1_SDA         /*!< GPA_MFPL PA6 setting for I2C1_SDA*/
#define I2C1_SDA_PA13            SYS_GPA_MFPH_PA13MFP_I2C1_SDA        /*!< GPA_MFPH PA13 setting for I2C1_SDA*/
#define I2C1_SDA_PG3             SYS_GPG_MFPL_PG3MFP_I2C1_SDA         /*!< GPG_MFPL PG3 setting for I2C1_SDA*/
#define I2C1_SDA_PE0             SYS_GPE_MFPL_PE0MFP_I2C1_SDA         /*!< GPE_MFPL PE0 setting for I2C1_SDA*/
#define I2C1_SDA_PC4             SYS_GPC_MFPL_PC4MFP_I2C1_SDA         /*!< GPC_MFPL PC4 setting for I2C1_SDA*/
#define I2C1_SDA_PA2             SYS_GPA_MFPL_PA2MFP_I2C1_SDA         /*!< GPA_MFPL PA2 setting for I2C1_SDA*/
#define I2C1_SDA_PB10            SYS_GPB_MFPH_PB10MFP_I2C1_SDA        /*!< GPB_MFPH PB10 setting for I2C1_SDA*/
#define I2C1_SDA_PF1             SYS_GPF_MFPL_PF1MFP_I2C1_SDA         /*!< GPF_MFPL PF1 setting for I2C1_SDA*/
#define I2C1_SDA_PD4             SYS_GPD_MFPL_PD4MFP_I2C1_SDA         /*!< GPD_MFPL PD4 setting for I2C1_SDA*/
#define I2C1_SMBAL_PB9           SYS_GPB_MFPH_PB9MFP_I2C1_SMBAL       /*!< GPB_MFPH PB9 setting for I2C1_SMBAL*/
#define I2C1_SMBAL_PC7           SYS_GPC_MFPL_PC7MFP_I2C1_SMBAL       /*!< GPC_MFPL PC7 setting for I2C1_SMBAL*/
#define I2C1_SMBAL_PH8           SYS_GPH_MFPH_PH8MFP_I2C1_SMBAL       /*!< GPH_MFPH PH8 setting for I2C1_SMBAL*/
#define I2C1_SMBSUS_PH9          SYS_GPH_MFPH_PH9MFP_I2C1_SMBSUS      /*!< GPH_MFPH PH9 setting for I2C1_SMBSUS*/
#define I2C1_SMBSUS_PC6          SYS_GPC_MFPL_PC6MFP_I2C1_SMBSUS      /*!< GPC_MFPL PC6 setting for I2C1_SMBSUS*/
#define I2C1_SMBSUS_PB8          SYS_GPB_MFPH_PB8MFP_I2C1_SMBSUS      /*!< GPB_MFPH PB8 setting for I2C1_SMBSUS*/
#define I2C2_SCL_PB13            SYS_GPB_MFPH_PB13MFP_I2C2_SCL        /*!< GPB_MFPH PB13 setting for I2C2_SCL*/
#define I2C2_SCL_PA11            SYS_GPA_MFPH_PA11MFP_I2C2_SCL        /*!< GPA_MFPH PA11 setting for I2C2_SCL*/
#define I2C2_SCL_PH8             SYS_GPH_MFPH_PH8MFP_I2C2_SCL         /*!< GPH_MFPH PH8 setting for I2C2_SCL*/
#define I2C2_SCL_PD9             SYS_GPD_MFPH_PD9MFP_I2C2_SCL         /*!< GPD_MFPH PD9 setting for I2C2_SCL*/
#define I2C2_SCL_PD1             SYS_GPD_MFPL_PD1MFP_I2C2_SCL         /*!< GPD_MFPL PD1 setting for I2C2_SCL*/
#define I2C2_SCL_PA14            SYS_GPA_MFPH_PA14MFP_I2C2_SCL        /*!< GPA_MFPH PA14 setting for I2C2_SCL*/
#define I2C2_SCL_PA1             SYS_GPA_MFPL_PA1MFP_I2C2_SCL         /*!< GPA_MFPL PA1 setting for I2C2_SCL*/
#define I2C2_SDA_PA0             SYS_GPA_MFPL_PA0MFP_I2C2_SDA         /*!< GPA_MFPL PA0 setting for I2C2_SDA*/
#define I2C2_SDA_PB12            SYS_GPB_MFPH_PB12MFP_I2C2_SDA        /*!< GPB_MFPH PB12 setting for I2C2_SDA*/
#define I2C2_SDA_PA10            SYS_GPA_MFPH_PA10MFP_I2C2_SDA        /*!< GPA_MFPH PA10 setting for I2C2_SDA*/
#define I2C2_SDA_PA15            SYS_GPA_MFPH_PA15MFP_I2C2_SDA        /*!< GPA_MFPH PA15 setting for I2C2_SDA*/
#define I2C2_SDA_PH9             SYS_GPH_MFPH_PH9MFP_I2C2_SDA         /*!< GPH_MFPH PH9 setting for I2C2_SDA*/
#define I2C2_SDA_PD8             SYS_GPD_MFPH_PD8MFP_I2C2_SDA         /*!< GPD_MFPH PD8 setting for I2C2_SDA*/
#define I2C2_SDA_PD0             SYS_GPD_MFPL_PD0MFP_I2C2_SDA         /*!< GPD_MFPL PD0 setting for I2C2_SDA*/
#define I2C2_SMBAL_PB15          SYS_GPB_MFPH_PB15MFP_I2C2_SMBAL      /*!< GPB_MFPH PB15 setting for I2C2_SMBAL*/
#define I2C2_SMBSUS_PB14         SYS_GPB_MFPH_PB14MFP_I2C2_SMBSUS     /*!< GPB_MFPH PB14 setting for I2C2_SMBSUS*/
#define I2S0_BCLK_PA12           SYS_GPA_MFPH_PA12MFP_I2S0_BCLK       /*!< GPA_MFPH PA12 setting for I2S0_BCLK*/
#define I2S0_BCLK_PB5            SYS_GPB_MFPL_PB5MFP_I2S0_BCLK        /*!< GPB_MFPL PB5 setting for I2S0_BCLK*/
#define I2S0_BCLK_PE8            SYS_GPE_MFPH_PE8MFP_I2S0_BCLK        /*!< GPE_MFPH PE8 setting for I2S0_BCLK*/
#define I2S0_BCLK_PE1            SYS_GPE_MFPL_PE1MFP_I2S0_BCLK        /*!< GPE_MFPL PE1 setting for I2S0_BCLK*/
#define I2S0_BCLK_PF10           SYS_GPF_MFPH_PF10MFP_I2S0_BCLK       /*!< GPF_MFPH PF10 setting for I2S0_BCLK*/
#define I2S0_BCLK_PC4            SYS_GPC_MFPL_PC4MFP_I2S0_BCLK        /*!< GPC_MFPL PC4 setting for I2S0_BCLK*/
#define I2S0_DI_PF8              SYS_GPF_MFPH_PF8MFP_I2S0_DI          /*!< GPF_MFPH PF8 setting for I2S0_DI*/
#define I2S0_DI_PB3              SYS_GPB_MFPL_PB3MFP_I2S0_DI          /*!< GPB_MFPL PB3 setting for I2S0_DI*/
#define I2S0_DI_PE10             SYS_GPE_MFPH_PE10MFP_I2S0_DI         /*!< GPE_MFPH PE10 setting for I2S0_DI*/
#define I2S0_DI_PA14             SYS_GPA_MFPH_PA14MFP_I2S0_DI         /*!< GPA_MFPH PA14 setting for I2S0_DI*/
#define I2S0_DI_PH8              SYS_GPH_MFPH_PH8MFP_I2S0_DI          /*!< GPH_MFPH PH8 setting for I2S0_DI*/
#define I2S0_DI_PC2              SYS_GPC_MFPL_PC2MFP_I2S0_DI          /*!< GPC_MFPL PC2 setting for I2S0_DI*/
#define I2S0_DO_PB2              SYS_GPB_MFPL_PB2MFP_I2S0_DO          /*!< GPB_MFPL PB2 setting for I2S0_DO*/
#define I2S0_DO_PH9              SYS_GPH_MFPH_PH9MFP_I2S0_DO          /*!< GPH_MFPH PH9 setting for I2S0_DO*/
#define I2S0_DO_PF7              SYS_GPF_MFPL_PF7MFP_I2S0_DO          /*!< GPF_MFPL PF7 setting for I2S0_DO*/
#define I2S0_DO_PE11             SYS_GPE_MFPH_PE11MFP_I2S0_DO         /*!< GPE_MFPH PE11 setting for I2S0_DO*/
#define I2S0_DO_PC1              SYS_GPC_MFPL_PC1MFP_I2S0_DO          /*!< GPC_MFPL PC1 setting for I2S0_DO*/
#define I2S0_DO_PA15             SYS_GPA_MFPH_PA15MFP_I2S0_DO         /*!< GPA_MFPH PA15 setting for I2S0_DO*/
#define I2S0_LRCK_PF6            SYS_GPF_MFPL_PF6MFP_I2S0_LRCK        /*!< GPF_MFPL PF6 setting for I2S0_LRCK*/
#define I2S0_LRCK_PE12           SYS_GPE_MFPH_PE12MFP_I2S0_LRCK       /*!< GPE_MFPH PE12 setting for I2S0_LRCK*/
#define I2S0_LRCK_PC0            SYS_GPC_MFPL_PC0MFP_I2S0_LRCK        /*!< GPC_MFPL PC0 setting for I2S0_LRCK*/
#define I2S0_LRCK_PH10           SYS_GPH_MFPH_PH10MFP_I2S0_LRCK       /*!< GPH_MFPH PH10 setting for I2S0_LRCK*/
#define I2S0_LRCK_PB1            SYS_GPB_MFPL_PB1MFP_I2S0_LRCK        /*!< GPB_MFPL PB1 setting for I2S0_LRCK*/
#define I2S0_MCLK_PE9            SYS_GPE_MFPH_PE9MFP_I2S0_MCLK        /*!< GPE_MFPH PE9 setting for I2S0_MCLK*/
#define I2S0_MCLK_PB4            SYS_GPB_MFPL_PB4MFP_I2S0_MCLK        /*!< GPB_MFPL PB4 setting for I2S0_MCLK*/
#define I2S0_MCLK_PC3            SYS_GPC_MFPL_PC3MFP_I2S0_MCLK        /*!< GPC_MFPL PC3 setting for I2S0_MCLK*/
#define I2S0_MCLK_PE0            SYS_GPE_MFPL_PE0MFP_I2S0_MCLK        /*!< GPE_MFPL PE0 setting for I2S0_MCLK*/
#define I2S0_MCLK_PA13           SYS_GPA_MFPH_PA13MFP_I2S0_MCLK       /*!< GPA_MFPH PA13 setting for I2S0_MCLK*/
#define I2S0_MCLK_PF9            SYS_GPF_MFPH_PF9MFP_I2S0_MCLK        /*!< GPF_MFPH PF9 setting for I2S0_MCLK*/
#define ICE_CLK_PF1              SYS_GPF_MFPL_PF1MFP_ICE_CLK          /*!< GPF_MFPL PF1 setting for ICE_CLK*/
#define ICE_DAT_PF0              SYS_GPF_MFPL_PF0MFP_ICE_DAT          /*!< GPF_MFPL PF0 setting for ICE_DAT*/
#define INT0_PB5                 SYS_GPB_MFPL_PB5MFP_INT0             /*!< GPB_MFPL PB5 setting for INT0*/
#define INT0_PA6                 SYS_GPA_MFPL_PA6MFP_INT0             /*!< GPA_MFPL PA6 setting for INT0*/
#define INT1_PB4                 SYS_GPB_MFPL_PB4MFP_INT1             /*!< GPB_MFPL PB4 setting for INT1*/
#define INT1_PA7                 SYS_GPA_MFPL_PA7MFP_INT1             /*!< GPA_MFPL PA7 setting for INT1*/
#define INT2_PB3                 SYS_GPB_MFPL_PB3MFP_INT2             /*!< GPB_MFPL PB3 setting for INT2*/
#define INT2_PC6                 SYS_GPC_MFPL_PC6MFP_INT2             /*!< GPC_MFPL PC6 setting for INT2*/
#define INT3_PC7                 SYS_GPC_MFPL_PC7MFP_INT3             /*!< GPC_MFPL PC7 setting for INT3*/
#define INT3_PB2                 SYS_GPB_MFPL_PB2MFP_INT3             /*!< GPB_MFPL PB2 setting for INT3*/
#define INT4_PB6                 SYS_GPB_MFPL_PB6MFP_INT4             /*!< GPB_MFPL PB6 setting for INT4*/
#define INT4_PA8                 SYS_GPA_MFPH_PA8MFP_INT4             /*!< GPA_MFPH PA8 setting for INT4*/
#define INT5_PB7                 SYS_GPB_MFPL_PB7MFP_INT5             /*!< GPB_MFPL PB7 setting for INT5*/
#define INT5_PD12                SYS_GPD_MFPH_PD12MFP_INT5            /*!< GPD_MFPH PD12 setting for INT5*/
#define INT6_PD11                SYS_GPD_MFPH_PD11MFP_INT6            /*!< GPD_MFPH PD11 setting for INT6*/
#define INT6_PB8                 SYS_GPB_MFPH_PB8MFP_INT6             /*!< GPB_MFPH PB8 setting for INT6*/
#define INT7_PB9                 SYS_GPB_MFPH_PB9MFP_INT7             /*!< GPB_MFPH PB9 setting for INT7*/
#define INT7_PD10                SYS_GPD_MFPH_PD10MFP_INT7            /*!< GPD_MFPH PD10 setting for INT7*/
#define EPWM0_BRAKE0_PE8         SYS_GPE_MFPH_PE8MFP_EPWM0_BRAKE0     /*!< GPE_MFPH PE8 setting for EPWM0_BRAKE0*/
#define EPWM0_BRAKE0_PB1         SYS_GPB_MFPL_PB1MFP_EPWM0_BRAKE0     /*!< GPB_MFPL PB1 setting for EPWM0_BRAKE0*/
#define EPWM0_BRAKE1_PB0         SYS_GPB_MFPL_PB0MFP_EPWM0_BRAKE1     /*!< GPB_MFPL PB0 setting for EPWM0_BRAKE1*/
#define EPWM0_BRAKE1_PE9         SYS_GPE_MFPH_PE9MFP_EPWM0_BRAKE1     /*!< GPE_MFPH PE9 setting for EPWM0_BRAKE1*/
#define EPWM0_CH0_PA5            SYS_GPA_MFPL_PA5MFP_EPWM0_CH0        /*!< GPA_MFPL PA5 setting for EPWM0_CH0*/
#define EPWM0_CH0_PE7            SYS_GPE_MFPL_PE7MFP_EPWM0_CH0        /*!< GPE_MFPL PE7 setting for EPWM0_CH0*/
#define EPWM0_CH0_PE8            SYS_GPE_MFPH_PE8MFP_EPWM0_CH0        /*!< GPE_MFPH PE8 setting for EPWM0_CH0*/
#define EPWM0_CH0_PB5            SYS_GPB_MFPL_PB5MFP_EPWM0_CH0        /*!< GPB_MFPL PB5 setting for EPWM0_CH0*/
#define EPWM0_CH1_PA4            SYS_GPA_MFPL_PA4MFP_EPWM0_CH1        /*!< GPA_MFPL PA4 setting for EPWM0_CH1*/
#define EPWM0_CH1_PB4            SYS_GPB_MFPL_PB4MFP_EPWM0_CH1        /*!< GPB_MFPL PB4 setting for EPWM0_CH1*/
#define EPWM0_CH1_PE9            SYS_GPE_MFPH_PE9MFP_EPWM0_CH1        /*!< GPE_MFPH PE9 setting for EPWM0_CH1*/
#define EPWM0_CH1_PE6            SYS_GPE_MFPL_PE6MFP_EPWM0_CH1        /*!< GPE_MFPL PE6 setting for EPWM0_CH1*/
#define EPWM0_CH2_PE5            SYS_GPE_MFPL_PE5MFP_EPWM0_CH2        /*!< GPE_MFPL PE5 setting for EPWM0_CH2*/
#define EPWM0_CH2_PB3            SYS_GPB_MFPL_PB3MFP_EPWM0_CH2        /*!< GPB_MFPL PB3 setting for EPWM0_CH2*/
#define EPWM0_CH2_PE10           SYS_GPE_MFPH_PE10MFP_EPWM0_CH2       /*!< GPE_MFPH PE10 setting for EPWM0_CH2*/
#define EPWM0_CH2_PA3            SYS_GPA_MFPL_PA3MFP_EPWM0_CH2        /*!< GPA_MFPL PA3 setting for EPWM0_CH2*/
#define EPWM0_CH3_PA2            SYS_GPA_MFPL_PA2MFP_EPWM0_CH3        /*!< GPA_MFPL PA2 setting for EPWM0_CH3*/
#define EPWM0_CH3_PE11           SYS_GPE_MFPH_PE11MFP_EPWM0_CH3       /*!< GPE_MFPH PE11 setting for EPWM0_CH3*/
#define EPWM0_CH3_PE4            SYS_GPE_MFPL_PE4MFP_EPWM0_CH3        /*!< GPE_MFPL PE4 setting for EPWM0_CH3*/
#define EPWM0_CH3_PB2            SYS_GPB_MFPL_PB2MFP_EPWM0_CH3        /*!< GPB_MFPL PB2 setting for EPWM0_CH3*/
#define EPWM0_CH4_PD14           SYS_GPD_MFPH_PD14MFP_EPWM0_CH4       /*!< GPD_MFPH PD14 setting for EPWM0_CH4*/
#define EPWM0_CH4_PB1            SYS_GPB_MFPL_PB1MFP_EPWM0_CH4        /*!< GPB_MFPL PB1 setting for EPWM0_CH4*/
#define EPWM0_CH4_PE3            SYS_GPE_MFPL_PE3MFP_EPWM0_CH4        /*!< GPE_MFPL PE3 setting for EPWM0_CH4*/
#define EPWM0_CH4_PA1            SYS_GPA_MFPL_PA1MFP_EPWM0_CH4        /*!< GPA_MFPL PA1 setting for EPWM0_CH4*/
#define EPWM0_CH4_PE12           SYS_GPE_MFPH_PE12MFP_EPWM0_CH4       /*!< GPE_MFPH PE12 setting for EPWM0_CH4*/
#define EPWM0_CH5_PB0            SYS_GPB_MFPL_PB0MFP_EPWM0_CH5        /*!< GPB_MFPL PB0 setting for EPWM0_CH5*/
#define EPWM0_CH5_PE2            SYS_GPE_MFPL_PE2MFP_EPWM0_CH5        /*!< GPE_MFPL PE2 setting for EPWM0_CH5*/
#define EPWM0_CH5_PA0            SYS_GPA_MFPL_PA0MFP_EPWM0_CH5        /*!< GPA_MFPL PA0 setting for EPWM0_CH5*/
#define EPWM0_CH5_PE13           SYS_GPE_MFPH_PE13MFP_EPWM0_CH5       /*!< GPE_MFPH PE13 setting for EPWM0_CH5*/
#define EPWM0_CH5_PH11           SYS_GPH_MFPH_PH11MFP_EPWM0_CH5       /*!< GPH_MFPH PH11 setting for EPWM0_CH5*/
#define EPWM0_SYNC_IN_PA15       SYS_GPA_MFPH_PA15MFP_EPWM0_SYNC_IN   /*!< GPA_MFPH PA15 setting for EPWM0_SYNC_IN*/
#define EPWM0_SYNC_OUT_PF5       SYS_GPF_MFPL_PF5MFP_EPWM0_SYNC_OUT   /*!< GPF_MFPL PF5 setting for EPWM0_SYNC_OUT*/
#define EPWM0_SYNC_OUT_PA11      SYS_GPA_MFPH_PA11MFP_EPWM0_SYNC_OUT  /*!< GPA_MFPH PA11 setting for EPWM0_SYNC_OUT*/
#define EPWM1_BRAKE0_PB7         SYS_GPB_MFPL_PB7MFP_EPWM1_BRAKE0     /*!< GPB_MFPL PB7 setting for EPWM1_BRAKE0*/
#define EPWM1_BRAKE0_PE10        SYS_GPE_MFPH_PE10MFP_EPWM1_BRAKE0    /*!< GPE_MFPH PE10 setting for EPWM1_BRAKE0*/
#define EPWM1_BRAKE1_PB6         SYS_GPB_MFPL_PB6MFP_EPWM1_BRAKE1     /*!< GPB_MFPL PB6 setting for EPWM1_BRAKE1*/
#define EPWM1_BRAKE1_PE11        SYS_GPE_MFPH_PE11MFP_EPWM1_BRAKE1    /*!< GPE_MFPH PE11 setting for EPWM1_BRAKE1*/
#define EPWM1_CH0_PC5            SYS_GPC_MFPL_PC5MFP_EPWM1_CH0        /*!< GPC_MFPL PC5 setting for EPWM1_CH0*/
#define EPWM1_CH0_PE13           SYS_GPE_MFPH_PE13MFP_EPWM1_CH0       /*!< GPE_MFPH PE13 setting for EPWM1_CH0*/
#define EPWM1_CH0_PC12           SYS_GPC_MFPH_PC12MFP_EPWM1_CH0       /*!< GPC_MFPH PC12 setting for EPWM1_CH0*/
#define EPWM1_CH0_PB15           SYS_GPB_MFPH_PB15MFP_EPWM1_CH0       /*!< GPB_MFPH PB15 setting for EPWM1_CH0*/
#define EPWM1_CH1_PB14           SYS_GPB_MFPH_PB14MFP_EPWM1_CH1       /*!< GPB_MFPH PB14 setting for EPWM1_CH1*/
#define EPWM1_CH1_PC11           SYS_GPC_MFPH_PC11MFP_EPWM1_CH1       /*!< GPC_MFPH PC11 setting for EPWM1_CH1*/
#define EPWM1_CH1_PC4            SYS_GPC_MFPL_PC4MFP_EPWM1_CH1        /*!< GPC_MFPL PC4 setting for EPWM1_CH1*/
#define EPWM1_CH1_PC8            SYS_GPC_MFPH_PC8MFP_EPWM1_CH1        /*!< GPC_MFPH PC8 setting for EPWM1_CH1*/
#define EPWM1_CH2_PC7            SYS_GPC_MFPL_PC7MFP_EPWM1_CH2        /*!< GPC_MFPL PC7 setting for EPWM1_CH2*/
#define EPWM1_CH2_PC10           SYS_GPC_MFPH_PC10MFP_EPWM1_CH2       /*!< GPC_MFPH PC10 setting for EPWM1_CH2*/
#define EPWM1_CH2_PC3            SYS_GPC_MFPL_PC3MFP_EPWM1_CH2        /*!< GPC_MFPL PC3 setting for EPWM1_CH2*/
#define EPWM1_CH2_PB13           SYS_GPB_MFPH_PB13MFP_EPWM1_CH2       /*!< GPB_MFPH PB13 setting for EPWM1_CH2*/
#define EPWM1_CH3_PB12           SYS_GPB_MFPH_PB12MFP_EPWM1_CH3       /*!< GPB_MFPH PB12 setting for EPWM1_CH3*/
#define EPWM1_CH3_PC6            SYS_GPC_MFPL_PC6MFP_EPWM1_CH3        /*!< GPC_MFPL PC6 setting for EPWM1_CH3*/
#define EPWM1_CH3_PC9            SYS_GPC_MFPH_PC9MFP_EPWM1_CH3        /*!< GPC_MFPH PC9 setting for EPWM1_CH3*/
#define EPWM1_CH3_PC2            SYS_GPC_MFPL_PC2MFP_EPWM1_CH3        /*!< GPC_MFPL PC2 setting for EPWM1_CH3*/
#define EPWM1_CH4_PB7            SYS_GPB_MFPL_PB7MFP_EPWM1_CH4        /*!< GPB_MFPL PB7 setting for EPWM1_CH4*/
#define EPWM1_CH4_PB1            SYS_GPB_MFPL_PB1MFP_EPWM1_CH4        /*!< GPB_MFPL PB1 setting for EPWM1_CH4*/
#define EPWM1_CH4_PC1            SYS_GPC_MFPL_PC1MFP_EPWM1_CH4        /*!< GPC_MFPL PC1 setting for EPWM1_CH4*/
#define EPWM1_CH4_PA7            SYS_GPA_MFPL_PA7MFP_EPWM1_CH4        /*!< GPA_MFPL PA7 setting for EPWM1_CH4*/
#define EPWM1_CH5_PA6            SYS_GPA_MFPL_PA6MFP_EPWM1_CH5        /*!< GPA_MFPL PA6 setting for EPWM1_CH5*/
#define EPWM1_CH5_PC0            SYS_GPC_MFPL_PC0MFP_EPWM1_CH5        /*!< GPC_MFPL PC0 setting for EPWM1_CH5*/
#define EPWM1_CH5_PB6            SYS_GPB_MFPL_PB6MFP_EPWM1_CH5        /*!< GPB_MFPL PB6 setting for EPWM1_CH5*/
#define EPWM1_CH5_PB0            SYS_GPB_MFPL_PB0MFP_EPWM1_CH5        /*!< GPB_MFPL PB0 setting for EPWM1_CH5*/
#define QEI0_A_PE3               SYS_GPE_MFPL_PE3MFP_QEI0_A           /*!< GPE_MFPL PE3 setting for QEI0_A*/
#define QEI0_A_PA4               SYS_GPA_MFPL_PA4MFP_QEI0_A           /*!< GPA_MFPL PA4 setting for QEI0_A*/
#define QEI0_A_PD11              SYS_GPD_MFPH_PD11MFP_QEI0_A          /*!< GPD_MFPH PD11 setting for QEI0_A*/
#define QEI0_B_PD10              SYS_GPD_MFPH_PD10MFP_QEI0_B          /*!< GPD_MFPH PD10 setting for QEI0_B*/
#define QEI0_B_PA3               SYS_GPA_MFPL_PA3MFP_QEI0_B           /*!< GPA_MFPL PA3 setting for QEI0_B*/
#define QEI0_B_PE2               SYS_GPE_MFPL_PE2MFP_QEI0_B           /*!< GPE_MFPL PE2 setting for QEI0_B*/
#define QEI0_INDEX_PE4           SYS_GPE_MFPL_PE4MFP_QEI0_INDEX       /*!< GPE_MFPL PE4 setting for QEI0_INDEX*/
#define QEI0_INDEX_PA5           SYS_GPA_MFPL_PA5MFP_QEI0_INDEX       /*!< GPA_MFPL PA5 setting for QEI0_INDEX*/
#define QEI0_INDEX_PD12          SYS_GPD_MFPH_PD12MFP_QEI0_INDEX      /*!< GPD_MFPH PD12 setting for QEI0_INDEX*/
#define QEI1_A_PE6               SYS_GPE_MFPL_PE6MFP_QEI1_A           /*!< GPE_MFPL PE6 setting for QEI1_A*/
#define QEI1_A_PA13              SYS_GPA_MFPH_PA13MFP_QEI1_A          /*!< GPA_MFPH PA13 setting for QEI1_A*/
#define QEI1_A_PA9               SYS_GPA_MFPH_PA9MFP_QEI1_A           /*!< GPA_MFPH PA9 setting for QEI1_A*/
#define QEI1_B_PA14              SYS_GPA_MFPH_PA14MFP_QEI1_B          /*!< GPA_MFPH PA14 setting for QEI1_B*/
#define QEI1_B_PA8               SYS_GPA_MFPH_PA8MFP_QEI1_B           /*!< GPA_MFPH PA8 setting for QEI1_B*/
#define QEI1_B_PE5               SYS_GPE_MFPL_PE5MFP_QEI1_B           /*!< GPE_MFPL PE5 setting for QEI1_B*/
#define QEI1_INDEX_PE7           SYS_GPE_MFPL_PE7MFP_QEI1_INDEX       /*!< GPE_MFPL PE7 setting for QEI1_INDEX*/
#define QEI1_INDEX_PA10          SYS_GPA_MFPH_PA10MFP_QEI1_INDEX      /*!< GPA_MFPH PA10 setting for QEI1_INDEX*/
#define QEI1_INDEX_PA12          SYS_GPA_MFPH_PA12MFP_QEI1_INDEX      /*!< GPA_MFPH PA12 setting for QEI1_INDEX*/
#define SC0_CLK_PF6              SYS_GPF_MFPL_PF6MFP_SC0_CLK          /*!< GPF_MFPL PF6 setting for SC0_CLK*/
#define SC0_CLK_PE2              SYS_GPE_MFPL_PE2MFP_SC0_CLK          /*!< GPE_MFPL PE2 setting for SC0_CLK*/
#define SC0_CLK_PA0              SYS_GPA_MFPL_PA0MFP_SC0_CLK          /*!< GPA_MFPL PA0 setting for SC0_CLK*/
#define SC0_CLK_PB5              SYS_GPB_MFPL_PB5MFP_SC0_CLK          /*!< GPB_MFPL PB5 setting for SC0_CLK*/
#define SC0_DAT_PE3              SYS_GPE_MFPL_PE3MFP_SC0_DAT          /*!< GPE_MFPL PE3 setting for SC0_DAT*/
#define SC0_DAT_PB4              SYS_GPB_MFPL_PB4MFP_SC0_DAT          /*!< GPB_MFPL PB4 setting for SC0_DAT*/
#define SC0_DAT_PA1              SYS_GPA_MFPL_PA1MFP_SC0_DAT          /*!< GPA_MFPL PA1 setting for SC0_DAT*/
#define SC0_DAT_PF7              SYS_GPF_MFPL_PF7MFP_SC0_DAT          /*!< GPF_MFPL PF7 setting for SC0_DAT*/
#define SC0_PWR_PE5              SYS_GPE_MFPL_PE5MFP_SC0_PWR          /*!< GPE_MFPL PE5 setting for SC0_PWR*/
#define SC0_PWR_PA3              SYS_GPA_MFPL_PA3MFP_SC0_PWR          /*!< GPA_MFPL PA3 setting for SC0_PWR*/
#define SC0_PWR_PB2              SYS_GPB_MFPL_PB2MFP_SC0_PWR          /*!< GPB_MFPL PB2 setting for SC0_PWR*/
#define SC0_PWR_PF9              SYS_GPF_MFPH_PF9MFP_SC0_PWR          /*!< GPF_MFPH PF9 setting for SC0_PWR*/
#define SC0_RST_PF8              SYS_GPF_MFPH_PF8MFP_SC0_RST          /*!< GPF_MFPH PF8 setting for SC0_RST*/
#define SC0_RST_PE4              SYS_GPE_MFPL_PE4MFP_SC0_RST          /*!< GPE_MFPL PE4 setting for SC0_RST*/
#define SC0_RST_PA2              SYS_GPA_MFPL_PA2MFP_SC0_RST          /*!< GPA_MFPL PA2 setting for SC0_RST*/
#define SC0_RST_PB3              SYS_GPB_MFPL_PB3MFP_SC0_RST          /*!< GPB_MFPL PB3 setting for SC0_RST*/
#define SC0_nCD_PE6              SYS_GPE_MFPL_PE6MFP_SC0_nCD          /*!< GPE_MFPL PE6 setting for SC0_nCD*/
#define SC0_nCD_PF10             SYS_GPF_MFPH_PF10MFP_SC0_nCD         /*!< GPF_MFPH PF10 setting for SC0_nCD*/
#define SC0_nCD_PA4              SYS_GPA_MFPL_PA4MFP_SC0_nCD          /*!< GPA_MFPL PA4 setting for SC0_nCD*/
#define SC0_nCD_PC12             SYS_GPC_MFPH_PC12MFP_SC0_nCD         /*!< GPC_MFPH PC12 setting for SC0_nCD*/
#define SC1_CLK_PC0              SYS_GPC_MFPL_PC0MFP_SC1_CLK          /*!< GPC_MFPL PC0 setting for SC1_CLK*/
#define SC1_CLK_PB12             SYS_GPB_MFPH_PB12MFP_SC1_CLK         /*!< GPB_MFPH PB12 setting for SC1_CLK*/
#define SC1_CLK_PD4              SYS_GPD_MFPL_PD4MFP_SC1_CLK          /*!< GPD_MFPL PD4 setting for SC1_CLK*/
#define SC1_DAT_PD5              SYS_GPD_MFPL_PD5MFP_SC1_DAT          /*!< GPD_MFPL PD5 setting for SC1_DAT*/
#define SC1_DAT_PB13             SYS_GPB_MFPH_PB13MFP_SC1_DAT         /*!< GPB_MFPH PB13 setting for SC1_DAT*/
#define SC1_DAT_PC1              SYS_GPC_MFPL_PC1MFP_SC1_DAT          /*!< GPC_MFPL PC1 setting for SC1_DAT*/
#define SC1_PWR_PB15             SYS_GPB_MFPH_PB15MFP_SC1_PWR         /*!< GPB_MFPH PB15 setting for SC1_PWR*/
#define SC1_PWR_PC3              SYS_GPC_MFPL_PC3MFP_SC1_PWR          /*!< GPC_MFPL PC3 setting for SC1_PWR*/
#define SC1_PWR_PD7              SYS_GPD_MFPL_PD7MFP_SC1_PWR          /*!< GPD_MFPL PD7 setting for SC1_PWR*/
#define SC1_RST_PD6              SYS_GPD_MFPL_PD6MFP_SC1_RST          /*!< GPD_MFPL PD6 setting for SC1_RST*/
#define SC1_RST_PB14             SYS_GPB_MFPH_PB14MFP_SC1_RST         /*!< GPB_MFPH PB14 setting for SC1_RST*/
#define SC1_RST_PC2              SYS_GPC_MFPL_PC2MFP_SC1_RST          /*!< GPC_MFPL PC2 setting for SC1_RST*/
#define SC1_nCD_PD3              SYS_GPD_MFPL_PD3MFP_SC1_nCD          /*!< GPD_MFPL PD3 setting for SC1_nCD*/
#define SC1_nCD_PC4              SYS_GPC_MFPL_PC4MFP_SC1_nCD          /*!< GPC_MFPL PC4 setting for SC1_nCD*/
#define SC1_nCD_PD14             SYS_GPD_MFPH_PD14MFP_SC1_nCD         /*!< GPD_MFPH PD14 setting for SC1_nCD*/
#define SC2_CLK_PD0              SYS_GPD_MFPL_PD0MFP_SC2_CLK          /*!< GPD_MFPL PD0 setting for SC2_CLK*/
#define SC2_CLK_PA15             SYS_GPA_MFPH_PA15MFP_SC2_CLK         /*!< GPA_MFPH PA15 setting for SC2_CLK*/
#define SC2_CLK_PE0              SYS_GPE_MFPL_PE0MFP_SC2_CLK          /*!< GPE_MFPL PE0 setting for SC2_CLK*/
#define SC2_CLK_PA8              SYS_GPA_MFPH_PA8MFP_SC2_CLK          /*!< GPA_MFPH PA8 setting for SC2_CLK*/
#define SC2_CLK_PA6              SYS_GPA_MFPL_PA6MFP_SC2_CLK          /*!< GPA_MFPL PA6 setting for SC2_CLK*/
#define SC2_DAT_PE1              SYS_GPE_MFPL_PE1MFP_SC2_DAT          /*!< GPE_MFPL PE1 setting for SC2_DAT*/
#define SC2_DAT_PD1              SYS_GPD_MFPL_PD1MFP_SC2_DAT          /*!< GPD_MFPL PD1 setting for SC2_DAT*/
#define SC2_DAT_PA9              SYS_GPA_MFPH_PA9MFP_SC2_DAT          /*!< GPA_MFPH PA9 setting for SC2_DAT*/
#define SC2_DAT_PA14             SYS_GPA_MFPH_PA14MFP_SC2_DAT         /*!< GPA_MFPH PA14 setting for SC2_DAT*/
#define SC2_DAT_PA7              SYS_GPA_MFPL_PA7MFP_SC2_DAT          /*!< GPA_MFPL PA7 setting for SC2_DAT*/
#define SC2_PWR_PD3              SYS_GPD_MFPL_PD3MFP_SC2_PWR          /*!< GPD_MFPL PD3 setting for SC2_PWR*/
#define SC2_PWR_PA11             SYS_GPA_MFPH_PA11MFP_SC2_PWR         /*!< GPA_MFPH PA11 setting for SC2_PWR*/
#define SC2_PWR_PA12             SYS_GPA_MFPH_PA12MFP_SC2_PWR         /*!< GPA_MFPH PA12 setting for SC2_PWR*/
#define SC2_PWR_PH8              SYS_GPH_MFPH_PH8MFP_SC2_PWR          /*!< GPH_MFPH PH8 setting for SC2_PWR*/
#define SC2_PWR_PC7              SYS_GPC_MFPL_PC7MFP_SC2_PWR          /*!< GPC_MFPL PC7 setting for SC2_PWR*/
#define SC2_RST_PD2              SYS_GPD_MFPL_PD2MFP_SC2_RST          /*!< GPD_MFPL PD2 setting for SC2_RST*/
#define SC2_RST_PC6              SYS_GPC_MFPL_PC6MFP_SC2_RST          /*!< GPC_MFPL PC6 setting for SC2_RST*/
#define SC2_RST_PH9              SYS_GPH_MFPH_PH9MFP_SC2_RST          /*!< GPH_MFPH PH9 setting for SC2_RST*/
#define SC2_RST_PA10             SYS_GPA_MFPH_PA10MFP_SC2_RST         /*!< GPA_MFPH PA10 setting for SC2_RST*/
#define SC2_RST_PA13             SYS_GPA_MFPH_PA13MFP_SC2_RST         /*!< GPA_MFPH PA13 setting for SC2_RST*/
#define SC2_nCD_PH10             SYS_GPH_MFPH_PH10MFP_SC2_nCD         /*!< GPH_MFPH PH10 setting for SC2_nCD*/
#define SC2_nCD_PA5              SYS_GPA_MFPL_PA5MFP_SC2_nCD          /*!< GPA_MFPL PA5 setting for SC2_nCD*/
#define SC2_nCD_PC13             SYS_GPC_MFPH_PC13MFP_SC2_nCD         /*!< GPC_MFPH PC13 setting for SC2_nCD*/
#define SC2_nCD_PD13             SYS_GPD_MFPH_PD13MFP_SC2_nCD         /*!< GPD_MFPH PD13 setting for SC2_nCD*/
#define SD0_CLK_PE6              SYS_GPE_MFPL_PE6MFP_SD0_CLK          /*!< GPE_MFPL PE6 setting for SD0_CLK*/
#define SD0_CLK_PB1              SYS_GPB_MFPL_PB1MFP_SD0_CLK          /*!< GPB_MFPL PB1 setting for SD0_CLK*/
#define SD0_CMD_PB0              SYS_GPB_MFPL_PB0MFP_SD0_CMD          /*!< GPB_MFPL PB0 setting for SD0_CMD*/
#define SD0_CMD_PE7              SYS_GPE_MFPL_PE7MFP_SD0_CMD          /*!< GPE_MFPL PE7 setting for SD0_CMD*/
#define SD0_DAT0_PB2             SYS_GPB_MFPL_PB2MFP_SD0_DAT0         /*!< GPB_MFPL PB2 setting for SD0_DAT0*/
#define SD0_DAT0_PE2             SYS_GPE_MFPL_PE2MFP_SD0_DAT0         /*!< GPE_MFPL PE2 setting for SD0_DAT0*/
#define SD0_DAT1_PE3             SYS_GPE_MFPL_PE3MFP_SD0_DAT1         /*!< GPE_MFPL PE3 setting for SD0_DAT1*/
#define SD0_DAT1_PB3             SYS_GPB_MFPL_PB3MFP_SD0_DAT1         /*!< GPB_MFPL PB3 setting for SD0_DAT1*/
#define SD0_DAT2_PB4             SYS_GPB_MFPL_PB4MFP_SD0_DAT2         /*!< GPB_MFPL PB4 setting for SD0_DAT2*/
#define SD0_DAT2_PE4             SYS_GPE_MFPL_PE4MFP_SD0_DAT2         /*!< GPE_MFPL PE4 setting for SD0_DAT2*/
#define SD0_DAT3_PE5             SYS_GPE_MFPL_PE5MFP_SD0_DAT3         /*!< GPE_MFPL PE5 setting for SD0_DAT3*/
#define SD0_DAT3_PB5             SYS_GPB_MFPL_PB5MFP_SD0_DAT3         /*!< GPB_MFPL PB5 setting for SD0_DAT3*/
#define SD0_nCD_PB12             SYS_GPB_MFPH_PB12MFP_SD0_nCD         /*!< GPB_MFPH PB12 setting for SD0_nCD*/
#define SD0_nCD_PD13             SYS_GPD_MFPH_PD13MFP_SD0_nCD         /*!< GPD_MFPH PD13 setting for SD0_nCD*/
#define QSPI0_CLK_PF2            SYS_GPF_MFPL_PF2MFP_QSPI0_CLK        /*!< GPF_MFPL PF2 setting for QSPI0_CLK*/
#define QSPI0_CLK_PH8            SYS_GPH_MFPH_PH8MFP_QSPI0_CLK        /*!< GPH_MFPH PH8 setting for QSPI0_CLK*/
#define QSPI0_CLK_PA2            SYS_GPA_MFPL_PA2MFP_QSPI0_CLK        /*!< GPA_MFPL PA2 setting for QSPI0_CLK*/
#define QSPI0_CLK_PC2            SYS_GPC_MFPL_PC2MFP_QSPI0_CLK        /*!< GPC_MFPL PC2 setting for QSPI0_CLK*/
#define QSPI0_MISO0_PC1          SYS_GPC_MFPL_PC1MFP_QSPI0_MISO0      /*!< GPC_MFPL PC1 setting for QSPI0_MISO0*/
#define QSPI0_MISO0_PE1          SYS_GPE_MFPL_PE1MFP_QSPI0_MISO0      /*!< GPE_MFPL PE1 setting for QSPI0_MISO0*/
#define QSPI0_MISO0_PA1          SYS_GPA_MFPL_PA1MFP_QSPI0_MISO0      /*!< GPA_MFPL PA1 setting for QSPI0_MISO0*/
#define QSPI0_MISO1_PC5          SYS_GPC_MFPL_PC5MFP_QSPI0_MISO1      /*!< GPC_MFPL PC5 setting for QSPI0_MISO1*/
#define QSPI0_MISO1_PH10         SYS_GPH_MFPH_PH10MFP_QSPI0_MISO1     /*!< GPH_MFPH PH10 setting for QSPI0_MISO1*/
#define QSPI0_MISO1_PA5          SYS_GPA_MFPL_PA5MFP_QSPI0_MISO1      /*!< GPA_MFPL PA5 setting for QSPI0_MISO1*/
#define QSPI0_MOSI0_PC0          SYS_GPC_MFPL_PC0MFP_QSPI0_MOSI0      /*!< GPC_MFPL PC0 setting for QSPI0_MOSI0*/
#define QSPI0_MOSI0_PE0          SYS_GPE_MFPL_PE0MFP_QSPI0_MOSI0      /*!< GPE_MFPL PE0 setting for QSPI0_MOSI0*/
#define QSPI0_MOSI0_PA0          SYS_GPA_MFPL_PA0MFP_QSPI0_MOSI0      /*!< GPA_MFPL PA0 setting for QSPI0_MOSI0*/
#define QSPI0_MOSI1_PA4          SYS_GPA_MFPL_PA4MFP_QSPI0_MOSI1      /*!< GPA_MFPL PA4 setting for QSPI0_MOSI1*/
#define QSPI0_MOSI1_PH11         SYS_GPH_MFPH_PH11MFP_QSPI0_MOSI1     /*!< GPH_MFPH PH11 setting for QSPI0_MOSI1*/
#define QSPI0_MOSI1_PC4          SYS_GPC_MFPL_PC4MFP_QSPI0_MOSI1      /*!< GPC_MFPL PC4 setting for QSPI0_MOSI1*/
#define QSPI0_SS_PH9             SYS_GPH_MFPH_PH9MFP_QSPI0_SS         /*!< GPH_MFPH PH9 setting for QSPI0_SS*/
#define QSPI0_SS_PA3             SYS_GPA_MFPL_PA3MFP_QSPI0_SS         /*!< GPA_MFPL PA3 setting for QSPI0_SS*/
#define QSPI0_SS_PC3             SYS_GPC_MFPL_PC3MFP_QSPI0_SS         /*!< GPC_MFPL PC3 setting for QSPI0_SS*/
#define SPI0_CLK_PD2             SYS_GPD_MFPL_PD2MFP_SPI0_CLK         /*!< GPD_MFPL PD2 setting for SPI0_CLK*/
#define SPI0_CLK_PF8             SYS_GPF_MFPH_PF8MFP_SPI0_CLK         /*!< GPF_MFPH PF8 setting for SPI0_CLK*/
#define SPI0_CLK_PA2             SYS_GPA_MFPL_PA2MFP_SPI0_CLK         /*!< GPA_MFPL PA2 setting for SPI0_CLK*/
#define SPI0_CLK_PB14            SYS_GPB_MFPH_PB14MFP_SPI0_CLK        /*!< GPB_MFPH PB14 setting for SPI0_CLK*/
#define SPI0_I2SMCLK_PD13        SYS_GPD_MFPH_PD13MFP_SPI0_I2SMCLK    /*!< GPD_MFPH PD13 setting for SPI0_I2SMCLK*/
#define SPI0_I2SMCLK_PA4         SYS_GPA_MFPL_PA4MFP_SPI0_I2SMCLK     /*!< GPA_MFPL PA4 setting for SPI0_I2SMCLK*/
#define SPI0_I2SMCLK_PB11        SYS_GPB_MFPH_PB11MFP_SPI0_I2SMCLK    /*!< GPB_MFPH PB11 setting for SPI0_I2SMCLK*/
#define SPI0_I2SMCLK_PB0         SYS_GPB_MFPL_PB0MFP_SPI0_I2SMCLK     /*!< GPB_MFPL PB0 setting for SPI0_I2SMCLK*/
#define SPI0_I2SMCLK_PD14        SYS_GPD_MFPH_PD14MFP_SPI0_I2SMCLK    /*!< GPD_MFPH PD14 setting for SPI0_I2SMCLK*/
#define SPI0_I2SMCLK_PF10        SYS_GPF_MFPH_PF10MFP_SPI0_I2SMCLK    /*!< GPF_MFPH PF10 setting for SPI0_I2SMCLK*/
#define SPI0_MISO_PF7            SYS_GPF_MFPL_PF7MFP_SPI0_MISO        /*!< GPF_MFPL PF7 setting for SPI0_MISO*/
#define SPI0_MISO_PB13           SYS_GPB_MFPH_PB13MFP_SPI0_MISO       /*!< GPB_MFPH PB13 setting for SPI0_MISO*/
#define SPI0_MISO_PA1            SYS_GPA_MFPL_PA1MFP_SPI0_MISO        /*!< GPA_MFPL PA1 setting for SPI0_MISO*/
#define SPI0_MISO_PD1            SYS_GPD_MFPL_PD1MFP_SPI0_MISO        /*!< GPD_MFPL PD1 setting for SPI0_MISO*/
#define SPI0_MOSI_PA0            SYS_GPA_MFPL_PA0MFP_SPI0_MOSI        /*!< GPA_MFPL PA0 setting for SPI0_MOSI*/
#define SPI0_MOSI_PB12           SYS_GPB_MFPH_PB12MFP_SPI0_MOSI       /*!< GPB_MFPH PB12 setting for SPI0_MOSI*/
#define SPI0_MOSI_PD0            SYS_GPD_MFPL_PD0MFP_SPI0_MOSI        /*!< GPD_MFPL PD0 setting for SPI0_MOSI*/
#define SPI0_MOSI_PF6            SYS_GPF_MFPL_PF6MFP_SPI0_MOSI        /*!< GPF_MFPL PF6 setting for SPI0_MOSI*/
#define SPI0_SS_PB15             SYS_GPB_MFPH_PB15MFP_SPI0_SS         /*!< GPB_MFPH PB15 setting for SPI0_SS*/
#define SPI0_SS_PA3              SYS_GPA_MFPL_PA3MFP_SPI0_SS          /*!< GPA_MFPL PA3 setting for SPI0_SS*/
#define SPI0_SS_PD3              SYS_GPD_MFPL_PD3MFP_SPI0_SS          /*!< GPD_MFPL PD3 setting for SPI0_SS*/
#define SPI0_SS_PF9              SYS_GPF_MFPH_PF9MFP_SPI0_SS          /*!< GPF_MFPH PF9 setting for SPI0_SS*/
#define SPI1_CLK_PB3             SYS_GPB_MFPL_PB3MFP_SPI1_CLK         /*!< GPB_MFPL PB3 setting for SPI1_CLK*/
#define SPI1_CLK_PH6             SYS_GPH_MFPL_PH6MFP_SPI1_CLK         /*!< GPH_MFPL PH6 setting for SPI1_CLK*/
#define SPI1_CLK_PH8             SYS_GPH_MFPH_PH8MFP_SPI1_CLK         /*!< GPH_MFPH PH8 setting for SPI1_CLK*/
#define SPI1_CLK_PC1             SYS_GPC_MFPL_PC1MFP_SPI1_CLK         /*!< GPC_MFPL PC1 setting for SPI1_CLK*/
#define SPI1_CLK_PD5             SYS_GPD_MFPL_PD5MFP_SPI1_CLK         /*!< GPD_MFPL PD5 setting for SPI1_CLK*/
#define SPI1_CLK_PA7             SYS_GPA_MFPL_PA7MFP_SPI1_CLK         /*!< GPA_MFPL PA7 setting for SPI1_CLK*/
#define SPI1_I2SMCLK_PB1         SYS_GPB_MFPL_PB1MFP_SPI1_I2SMCLK     /*!< GPB_MFPL PB1 setting for SPI1_I2SMCLK*/
#define SPI1_I2SMCLK_PH10        SYS_GPH_MFPH_PH10MFP_SPI1_I2SMCLK    /*!< GPH_MFPH PH10 setting for SPI1_I2SMCLK*/
#define SPI1_I2SMCLK_PC4         SYS_GPC_MFPL_PC4MFP_SPI1_I2SMCLK     /*!< GPC_MFPL PC4 setting for SPI1_I2SMCLK*/
#define SPI1_I2SMCLK_PD13        SYS_GPD_MFPH_PD13MFP_SPI1_I2SMCLK    /*!< GPD_MFPH PD13 setting for SPI1_I2SMCLK*/
#define SPI1_I2SMCLK_PA5         SYS_GPA_MFPL_PA5MFP_SPI1_I2SMCLK     /*!< GPA_MFPL PA5 setting for SPI1_I2SMCLK*/
#define SPI1_MISO_PD7            SYS_GPD_MFPL_PD7MFP_SPI1_MISO        /*!< GPD_MFPL PD7 setting for SPI1_MISO*/
#define SPI1_MISO_PC7            SYS_GPC_MFPL_PC7MFP_SPI1_MISO        /*!< GPC_MFPL PC7 setting for SPI1_MISO*/
#define SPI1_MISO_PB5            SYS_GPB_MFPL_PB5MFP_SPI1_MISO        /*!< GPB_MFPL PB5 setting for SPI1_MISO*/
#define SPI1_MISO_PE1            SYS_GPE_MFPL_PE1MFP_SPI1_MISO        /*!< GPE_MFPL PE1 setting for SPI1_MISO*/
#define SPI1_MISO_PH4            SYS_GPH_MFPL_PH4MFP_SPI1_MISO        /*!< GPH_MFPL PH4 setting for SPI1_MISO*/
#define SPI1_MISO_PC3            SYS_GPC_MFPL_PC3MFP_SPI1_MISO        /*!< GPC_MFPL PC3 setting for SPI1_MISO*/
#define SPI1_MOSI_PD6            SYS_GPD_MFPL_PD6MFP_SPI1_MOSI        /*!< GPD_MFPL PD6 setting for SPI1_MOSI*/
#define SPI1_MOSI_PE0            SYS_GPE_MFPL_PE0MFP_SPI1_MOSI        /*!< GPE_MFPL PE0 setting for SPI1_MOSI*/
#define SPI1_MOSI_PB4            SYS_GPB_MFPL_PB4MFP_SPI1_MOSI        /*!< GPB_MFPL PB4 setting for SPI1_MOSI*/
#define SPI1_MOSI_PC6            SYS_GPC_MFPL_PC6MFP_SPI1_MOSI        /*!< GPC_MFPL PC6 setting for SPI1_MOSI*/
#define SPI1_MOSI_PC2            SYS_GPC_MFPL_PC2MFP_SPI1_MOSI        /*!< GPC_MFPL PC2 setting for SPI1_MOSI*/
#define SPI1_MOSI_PH5            SYS_GPH_MFPL_PH5MFP_SPI1_MOSI        /*!< GPH_MFPL PH5 setting for SPI1_MOSI*/
#define SPI1_SS_PB2              SYS_GPB_MFPL_PB2MFP_SPI1_SS          /*!< GPB_MFPL PB2 setting for SPI1_SS*/
#define SPI1_SS_PH9              SYS_GPH_MFPH_PH9MFP_SPI1_SS          /*!< GPH_MFPH PH9 setting for SPI1_SS*/
#define SPI1_SS_PD4              SYS_GPD_MFPL_PD4MFP_SPI1_SS          /*!< GPD_MFPL PD4 setting for SPI1_SS*/
#define SPI1_SS_PC0              SYS_GPC_MFPL_PC0MFP_SPI1_SS          /*!< GPC_MFPL PC0 setting for SPI1_SS*/
#define SPI1_SS_PA6              SYS_GPA_MFPL_PA6MFP_SPI1_SS          /*!< GPA_MFPL PA6 setting for SPI1_SS*/
#define SPI1_SS_PH7              SYS_GPH_MFPL_PH7MFP_SPI1_SS          /*!< GPH_MFPL PH7 setting for SPI1_SS*/
#define SPI2_CLK_PE8             SYS_GPE_MFPH_PE8MFP_SPI2_CLK         /*!< GPE_MFPH PE8 setting for SPI2_CLK*/
#define SPI2_CLK_PG3             SYS_GPG_MFPL_PG3MFP_SPI2_CLK         /*!< GPG_MFPL PG3 setting for SPI2_CLK*/
#define SPI2_CLK_PA10            SYS_GPA_MFPH_PA10MFP_SPI2_CLK        /*!< GPA_MFPH PA10 setting for SPI2_CLK*/
#define SPI2_CLK_PA13            SYS_GPA_MFPH_PA13MFP_SPI2_CLK        /*!< GPA_MFPH PA13 setting for SPI2_CLK*/
#define SPI2_I2SMCLK_PC13        SYS_GPC_MFPH_PC13MFP_SPI2_I2SMCLK    /*!< GPC_MFPH PC13 setting for SPI2_I2SMCLK*/
#define SPI2_I2SMCLK_PE12        SYS_GPE_MFPH_PE12MFP_SPI2_I2SMCLK    /*!< GPE_MFPH PE12 setting for SPI2_I2SMCLK*/
#define SPI2_MISO_PG4            SYS_GPG_MFPL_PG4MFP_SPI2_MISO        /*!< GPG_MFPL PG4 setting for SPI2_MISO*/
#define SPI2_MISO_PA9            SYS_GPA_MFPH_PA9MFP_SPI2_MISO        /*!< GPA_MFPH PA9 setting for SPI2_MISO*/
#define SPI2_MISO_PA14           SYS_GPA_MFPH_PA14MFP_SPI2_MISO       /*!< GPA_MFPH PA14 setting for SPI2_MISO*/
#define SPI2_MISO_PE9            SYS_GPE_MFPH_PE9MFP_SPI2_MISO        /*!< GPE_MFPH PE9 setting for SPI2_MISO*/
#define SPI2_MOSI_PE10           SYS_GPE_MFPH_PE10MFP_SPI2_MOSI       /*!< GPE_MFPH PE10 setting for SPI2_MOSI*/
#define SPI2_MOSI_PA15           SYS_GPA_MFPH_PA15MFP_SPI2_MOSI       /*!< GPA_MFPH PA15 setting for SPI2_MOSI*/
#define SPI2_MOSI_PA8            SYS_GPA_MFPH_PA8MFP_SPI2_MOSI        /*!< GPA_MFPH PA8 setting for SPI2_MOSI*/
#define SPI2_MOSI_PF11           SYS_GPF_MFPH_PF11MFP_SPI2_MOSI       /*!< GPF_MFPH PF11 setting for SPI2_MOSI*/
#define SPI2_SS_PG2              SYS_GPG_MFPL_PG2MFP_SPI2_SS          /*!< GPG_MFPL PG2 setting for SPI2_SS*/
#define SPI2_SS_PE11             SYS_GPE_MFPH_PE11MFP_SPI2_SS         /*!< GPE_MFPH PE11 setting for SPI2_SS*/
#define SPI2_SS_PA11             SYS_GPA_MFPH_PA11MFP_SPI2_SS         /*!< GPA_MFPH PA11 setting for SPI2_SS*/
#define SPI2_SS_PA12             SYS_GPA_MFPH_PA12MFP_SPI2_SS         /*!< GPA_MFPH PA12 setting for SPI2_SS*/
#define SPI3_CLK_PB11            SYS_GPB_MFPH_PB11MFP_SPI3_CLK        /*!< GPB_MFPH PB11 setting for SPI3_CLK*/
#define SPI3_CLK_PE4             SYS_GPE_MFPL_PE4MFP_SPI3_CLK         /*!< GPE_MFPL PE4 setting for SPI3_CLK*/
#define SPI3_CLK_PC10            SYS_GPC_MFPH_PC10MFP_SPI3_CLK        /*!< GPC_MFPH PC10 setting for SPI3_CLK*/
#define SPI3_I2SMCLK_PE6         SYS_GPE_MFPL_PE6MFP_SPI3_I2SMCLK     /*!< GPE_MFPL PE6 setting for SPI3_I2SMCLK*/
#define SPI3_I2SMCLK_PB1         SYS_GPB_MFPL_PB1MFP_SPI3_I2SMCLK     /*!< GPB_MFPL PB1 setting for SPI3_I2SMCLK*/
#define SPI3_I2SMCLK_PD14        SYS_GPD_MFPH_PD14MFP_SPI3_I2SMCLK    /*!< GPD_MFPH PD14 setting for SPI3_I2SMCLK*/
#define SPI3_MISO_PC12           SYS_GPC_MFPH_PC12MFP_SPI3_MISO       /*!< GPC_MFPH PC12 setting for SPI3_MISO*/
#define SPI3_MISO_PB9            SYS_GPB_MFPH_PB9MFP_SPI3_MISO        /*!< GPB_MFPH PB9 setting for SPI3_MISO*/
#define SPI3_MISO_PE3            SYS_GPE_MFPL_PE3MFP_SPI3_MISO        /*!< GPE_MFPL PE3 setting for SPI3_MISO*/
#define SPI3_MOSI_PB8            SYS_GPB_MFPH_PB8MFP_SPI3_MOSI        /*!< GPB_MFPH PB8 setting for SPI3_MOSI*/
#define SPI3_MOSI_PE2            SYS_GPE_MFPL_PE2MFP_SPI3_MOSI        /*!< GPE_MFPL PE2 setting for SPI3_MOSI*/
#define SPI3_MOSI_PC11           SYS_GPC_MFPH_PC11MFP_SPI3_MOSI       /*!< GPC_MFPH PC11 setting for SPI3_MOSI*/
#define SPI3_SS_PE5              SYS_GPE_MFPL_PE5MFP_SPI3_SS          /*!< GPE_MFPL PE5 setting for SPI3_SS*/
#define SPI3_SS_PB10             SYS_GPB_MFPH_PB10MFP_SPI3_SS         /*!< GPB_MFPH PB10 setting for SPI3_SS*/
#define SPI3_SS_PC9              SYS_GPC_MFPH_PC9MFP_SPI3_SS          /*!< GPC_MFPH PC9 setting for SPI3_SS*/
#define TAMPER0_PF6              SYS_GPF_MFPL_PF6MFP_TAMPER0          /*!< GPF_MFPL PF6 setting for TAMPER0*/
#define TAMPER1_PF7              SYS_GPF_MFPL_PF7MFP_TAMPER1          /*!< GPF_MFPL PF7 setting for TAMPER1*/
#define TAMPER2_PF8              SYS_GPF_MFPH_PF8MFP_TAMPER2          /*!< GPF_MFPH PF8 setting for TAMPER2*/
#define TAMPER3_PF9              SYS_GPF_MFPH_PF9MFP_TAMPER3          /*!< GPF_MFPH PF9 setting for TAMPER3*/
#define TAMPER4_PF10             SYS_GPF_MFPH_PF10MFP_TAMPER4         /*!< GPF_MFPH PF10 setting for TAMPER4*/
#define TAMPER5_PF11             SYS_GPF_MFPH_PF11MFP_TAMPER5         /*!< GPF_MFPH PF11 setting for TAMPER5*/
#define TM0_PC7                  SYS_GPC_MFPL_PC7MFP_TM0              /*!< GPC_MFPL PC7 setting for TM0*/
#define TM0_PB5                  SYS_GPB_MFPL_PB5MFP_TM0              /*!< GPB_MFPL PB5 setting for TM0*/
#define TM0_PG2                  SYS_GPG_MFPL_PG2MFP_TM0              /*!< GPG_MFPL PG2 setting for TM0*/
#define TM0_EXT_PA11             SYS_GPA_MFPH_PA11MFP_TM0_EXT         /*!< GPA_MFPH PA11 setting for TM0_EXT*/
#define TM0_EXT_PB15             SYS_GPB_MFPH_PB15MFP_TM0_EXT         /*!< GPB_MFPH PB15 setting for TM0_EXT*/
#define TM1_PG3                  SYS_GPG_MFPL_PG3MFP_TM1              /*!< GPG_MFPL PG3 setting for TM1*/
#define TM1_PB4                  SYS_GPB_MFPL_PB4MFP_TM1              /*!< GPB_MFPL PB4 setting for TM1*/
#define TM1_PC6                  SYS_GPC_MFPL_PC6MFP_TM1              /*!< GPC_MFPL PC6 setting for TM1*/
#define TM1_EXT_PA10             SYS_GPA_MFPH_PA10MFP_TM1_EXT         /*!< GPA_MFPH PA10 setting for TM1_EXT*/
#define TM1_EXT_PB14             SYS_GPB_MFPH_PB14MFP_TM1_EXT         /*!< GPB_MFPH PB14 setting for TM1_EXT*/
#define TM2_PG4                  SYS_GPG_MFPL_PG4MFP_TM2              /*!< GPG_MFPL PG4 setting for TM2*/
#define TM2_PD0                  SYS_GPD_MFPL_PD0MFP_TM2              /*!< GPD_MFPL PD0 setting for TM2*/
#define TM2_PB3                  SYS_GPB_MFPL_PB3MFP_TM2              /*!< GPB_MFPL PB3 setting for TM2*/
#define TM2_PA7                  SYS_GPA_MFPL_PA7MFP_TM2              /*!< GPA_MFPL PA7 setting for TM2*/
#define TM2_EXT_PB13             SYS_GPB_MFPH_PB13MFP_TM2_EXT         /*!< GPB_MFPH PB13 setting for TM2_EXT*/
#define TM2_EXT_PA9              SYS_GPA_MFPH_PA9MFP_TM2_EXT          /*!< GPA_MFPH PA9 setting for TM2_EXT*/
#define TM3_PA6                  SYS_GPA_MFPL_PA6MFP_TM3              /*!< GPA_MFPL PA6 setting for TM3*/
#define TM3_PF11                 SYS_GPF_MFPH_PF11MFP_TM3             /*!< GPF_MFPH PF11 setting for TM3*/
#define TM3_PB2                  SYS_GPB_MFPL_PB2MFP_TM3              /*!< GPB_MFPL PB2 setting for TM3*/
#define TM3_EXT_PA8              SYS_GPA_MFPH_PA8MFP_TM3_EXT          /*!< GPA_MFPH PA8 setting for TM3_EXT*/
#define TM3_EXT_PB12             SYS_GPB_MFPH_PB12MFP_TM3_EXT         /*!< GPB_MFPH PB12 setting for TM3_EXT*/
#define TRACE_CLK_PE12           SYS_GPE_MFPH_PE12MFP_TRACE_CLK       /*!< GPE_MFPH PE12 setting for TRACE_CLK*/
#define TRACE_DATA0_PE11         SYS_GPE_MFPH_PE11MFP_TRACE_DATA0     /*!< GPE_MFPH PE11 setting for TRACE_DATA0*/
#define TRACE_DATA1_PE10         SYS_GPE_MFPH_PE10MFP_TRACE_DATA1     /*!< GPE_MFPH PE10 setting for TRACE_DATA1*/
#define TRACE_DATA2_PE9          SYS_GPE_MFPH_PE9MFP_TRACE_DATA2      /*!< GPE_MFPH PE9 setting for TRACE_DATA2*/
#define TRACE_DATA3_PE8          SYS_GPE_MFPH_PE8MFP_TRACE_DATA3      /*!< GPE_MFPH PE8 setting for TRACE_DATA3*/
#define UART0_RXD_PD2            SYS_GPD_MFPL_PD2MFP_UART0_RXD        /*!< GPD_MFPL PD2 setting for UART0_RXD*/
#define UART0_RXD_PB8            SYS_GPB_MFPH_PB8MFP_UART0_RXD        /*!< GPB_MFPH PB8 setting for UART0_RXD*/
#define UART0_RXD_PA0            SYS_GPA_MFPL_PA0MFP_UART0_RXD        /*!< GPA_MFPL PA0 setting for UART0_RXD*/
#define UART0_RXD_PA6            SYS_GPA_MFPL_PA6MFP_UART0_RXD        /*!< GPA_MFPL PA6 setting for UART0_RXD*/
#define UART0_RXD_PB12           SYS_GPB_MFPH_PB12MFP_UART0_RXD       /*!< GPB_MFPH PB12 setting for UART0_RXD*/
#define UART0_RXD_PA15           SYS_GPA_MFPH_PA15MFP_UART0_RXD       /*!< GPA_MFPH PA15 setting for UART0_RXD*/
#define UART0_RXD_PC11           SYS_GPC_MFPH_PC11MFP_UART0_RXD       /*!< GPC_MFPH PC11 setting for UART0_RXD*/
#define UART0_RXD_PH11           SYS_GPH_MFPH_PH11MFP_UART0_RXD       /*!< GPH_MFPH PH11 setting for UART0_RXD*/
#define UART0_RXD_PF2            SYS_GPF_MFPL_PF2MFP_UART0_RXD        /*!< GPF_MFPL PF2 setting for UART0_RXD*/
#define UART0_TXD_PA7            SYS_GPA_MFPL_PA7MFP_UART0_TXD        /*!< GPA_MFPL PA7 setting for UART0_TXD*/
#define UART0_TXD_PD3            SYS_GPD_MFPL_PD3MFP_UART0_TXD        /*!< GPD_MFPL PD3 setting for UART0_TXD*/
#define UART0_TXD_PF3            SYS_GPF_MFPL_PF3MFP_UART0_TXD        /*!< GPF_MFPL PF3 setting for UART0_TXD*/
#define UART0_TXD_PC12           SYS_GPC_MFPH_PC12MFP_UART0_TXD       /*!< GPC_MFPH PC12 setting for UART0_TXD*/
#define UART0_TXD_PH10           SYS_GPH_MFPH_PH10MFP_UART0_TXD       /*!< GPH_MFPH PH10 setting for UART0_TXD*/
#define UART0_TXD_PA1            SYS_GPA_MFPL_PA1MFP_UART0_TXD        /*!< GPA_MFPL PA1 setting for UART0_TXD*/
#define UART0_TXD_PB9            SYS_GPB_MFPH_PB9MFP_UART0_TXD        /*!< GPB_MFPH PB9 setting for UART0_TXD*/
#define UART0_TXD_PB13           SYS_GPB_MFPH_PB13MFP_UART0_TXD       /*!< GPB_MFPH PB13 setting for UART0_TXD*/
#define UART0_TXD_PA14           SYS_GPA_MFPH_PA14MFP_UART0_TXD       /*!< GPA_MFPH PA14 setting for UART0_TXD*/
#define UART0_nCTS_PA5           SYS_GPA_MFPL_PA5MFP_UART0_nCTS       /*!< GPA_MFPL PA5 setting for UART0_nCTS*/
#define UART0_nCTS_PB11          SYS_GPB_MFPH_PB11MFP_UART0_nCTS      /*!< GPB_MFPH PB11 setting for UART0_nCTS*/
#define UART0_nCTS_PB15          SYS_GPB_MFPH_PB15MFP_UART0_nCTS      /*!< GPB_MFPH PB15 setting for UART0_nCTS*/
#define UART0_nCTS_PC7           SYS_GPC_MFPL_PC7MFP_UART0_nCTS       /*!< GPC_MFPL PC7 setting for UART0_nCTS*/
#define UART0_nRTS_PB14          SYS_GPB_MFPH_PB14MFP_UART0_nRTS      /*!< GPB_MFPH PB14 setting for UART0_nRTS*/
#define UART0_nRTS_PB10          SYS_GPB_MFPH_PB10MFP_UART0_nRTS      /*!< GPB_MFPH PB10 setting for UART0_nRTS*/
#define UART0_nRTS_PC6           SYS_GPC_MFPL_PC6MFP_UART0_nRTS       /*!< GPC_MFPL PC6 setting for UART0_nRTS*/
#define UART0_nRTS_PA4           SYS_GPA_MFPL_PA4MFP_UART0_nRTS       /*!< GPA_MFPL PA4 setting for UART0_nRTS*/
#define UART1_RXD_PF1            SYS_GPF_MFPL_PF1MFP_UART1_RXD        /*!< GPF_MFPL PF1 setting for UART1_RXD*/
#define UART1_RXD_PA8            SYS_GPA_MFPH_PA8MFP_UART1_RXD        /*!< GPA_MFPH PA8 setting for UART1_RXD*/
#define UART1_RXD_PA2            SYS_GPA_MFPL_PA2MFP_UART1_RXD        /*!< GPA_MFPL PA2 setting for UART1_RXD*/
#define UART1_RXD_PB2            SYS_GPB_MFPL_PB2MFP_UART1_RXD        /*!< GPB_MFPL PB2 setting for UART1_RXD*/
#define UART1_RXD_PB6            SYS_GPB_MFPL_PB6MFP_UART1_RXD        /*!< GPB_MFPL PB6 setting for UART1_RXD*/
#define UART1_RXD_PD6            SYS_GPD_MFPL_PD6MFP_UART1_RXD        /*!< GPD_MFPL PD6 setting for UART1_RXD*/
#define UART1_RXD_PD10           SYS_GPD_MFPH_PD10MFP_UART1_RXD       /*!< GPD_MFPH PD10 setting for UART1_RXD*/
#define UART1_RXD_PH9            SYS_GPH_MFPH_PH9MFP_UART1_RXD        /*!< GPH_MFPH PH9 setting for UART1_RXD*/
#define UART1_RXD_PC8            SYS_GPC_MFPH_PC8MFP_UART1_RXD        /*!< GPC_MFPH PC8 setting for UART1_RXD*/
#define UART1_TXD_PB3            SYS_GPB_MFPL_PB3MFP_UART1_TXD        /*!< GPB_MFPL PB3 setting for UART1_TXD*/
#define UART1_TXD_PA3            SYS_GPA_MFPL_PA3MFP_UART1_TXD        /*!< GPA_MFPL PA3 setting for UART1_TXD*/
#define UART1_TXD_PE13           SYS_GPE_MFPH_PE13MFP_UART1_TXD       /*!< GPE_MFPH PE13 setting for UART1_TXD*/
#define UART1_TXD_PA9            SYS_GPA_MFPH_PA9MFP_UART1_TXD        /*!< GPA_MFPH PA9 setting for UART1_TXD*/
#define UART1_TXD_PF0            SYS_GPF_MFPL_PF0MFP_UART1_TXD        /*!< GPF_MFPL PF0 setting for UART1_TXD*/
#define UART1_TXD_PD11           SYS_GPD_MFPH_PD11MFP_UART1_TXD       /*!< GPD_MFPH PD11 setting for UART1_TXD*/
#define UART1_TXD_PD7            SYS_GPD_MFPL_PD7MFP_UART1_TXD        /*!< GPD_MFPL PD7 setting for UART1_TXD*/
#define UART1_TXD_PB7            SYS_GPB_MFPL_PB7MFP_UART1_TXD        /*!< GPB_MFPL PB7 setting for UART1_TXD*/
#define UART1_TXD_PH8            SYS_GPH_MFPH_PH8MFP_UART1_TXD        /*!< GPH_MFPH PH8 setting for UART1_TXD*/
#define UART1_nCTS_PE11          SYS_GPE_MFPH_PE11MFP_UART1_nCTS      /*!< GPE_MFPH PE11 setting for UART1_nCTS*/
#define UART1_nCTS_PB9           SYS_GPB_MFPH_PB9MFP_UART1_nCTS       /*!< GPB_MFPH PB9 setting for UART1_nCTS*/
#define UART1_nCTS_PA1           SYS_GPA_MFPL_PA1MFP_UART1_nCTS       /*!< GPA_MFPL PA1 setting for UART1_nCTS*/
#define UART1_nRTS_PA0           SYS_GPA_MFPL_PA0MFP_UART1_nRTS       /*!< GPA_MFPL PA0 setting for UART1_nRTS*/
#define UART1_nRTS_PE12          SYS_GPE_MFPH_PE12MFP_UART1_nRTS      /*!< GPE_MFPH PE12 setting for UART1_nRTS*/
#define UART1_nRTS_PB8           SYS_GPB_MFPH_PB8MFP_UART1_nRTS       /*!< GPB_MFPH PB8 setting for UART1_nRTS*/
#define UART2_RXD_PB0            SYS_GPB_MFPL_PB0MFP_UART2_RXD        /*!< GPB_MFPL PB0 setting for UART2_RXD*/
#define UART2_RXD_PE15           SYS_GPE_MFPH_PE15MFP_UART2_RXD       /*!< GPE_MFPH PE15 setting for UART2_RXD*/
#define UART2_RXD_PD12           SYS_GPD_MFPH_PD12MFP_UART2_RXD       /*!< GPD_MFPH PD12 setting for UART2_RXD*/
#define UART2_RXD_PF5            SYS_GPF_MFPL_PF5MFP_UART2_RXD        /*!< GPF_MFPL PF5 setting for UART2_RXD*/
#define UART2_RXD_PC0            SYS_GPC_MFPL_PC0MFP_UART2_RXD        /*!< GPC_MFPL PC0 setting for UART2_RXD*/
#define UART2_RXD_PC4            SYS_GPC_MFPL_PC4MFP_UART2_RXD        /*!< GPC_MFPL PC4 setting for UART2_RXD*/
#define UART2_RXD_PE9            SYS_GPE_MFPH_PE9MFP_UART2_RXD        /*!< GPE_MFPH PE9 setting for UART2_RXD*/
#define UART2_TXD_PE8            SYS_GPE_MFPH_PE8MFP_UART2_TXD        /*!< GPE_MFPH PE8 setting for UART2_TXD*/
#define UART2_TXD_PF4            SYS_GPF_MFPL_PF4MFP_UART2_TXD        /*!< GPF_MFPL PF4 setting for UART2_TXD*/
#define UART2_TXD_PC13           SYS_GPC_MFPH_PC13MFP_UART2_TXD       /*!< GPC_MFPH PC13 setting for UART2_TXD*/
#define UART2_TXD_PC1            SYS_GPC_MFPL_PC1MFP_UART2_TXD        /*!< GPC_MFPL PC1 setting for UART2_TXD*/
#define UART2_TXD_PE14           SYS_GPE_MFPH_PE14MFP_UART2_TXD       /*!< GPE_MFPH PE14 setting for UART2_TXD*/
#define UART2_TXD_PC5            SYS_GPC_MFPL_PC5MFP_UART2_TXD        /*!< GPC_MFPL PC5 setting for UART2_TXD*/
#define UART2_TXD_PB1            SYS_GPB_MFPL_PB1MFP_UART2_TXD        /*!< GPB_MFPL PB1 setting for UART2_TXD*/
#define UART2_nCTS_PF5           SYS_GPF_MFPL_PF5MFP_UART2_nCTS       /*!< GPF_MFPL PF5 setting for UART2_nCTS*/
#define UART2_nCTS_PD9           SYS_GPD_MFPH_PD9MFP_UART2_nCTS       /*!< GPD_MFPH PD9 setting for UART2_nCTS*/
#define UART2_nCTS_PC2           SYS_GPC_MFPL_PC2MFP_UART2_nCTS       /*!< GPC_MFPL PC2 setting for UART2_nCTS*/
#define UART2_nRTS_PF4           SYS_GPF_MFPL_PF4MFP_UART2_nRTS       /*!< GPF_MFPL PF4 setting for UART2_nRTS*/
#define UART2_nRTS_PD8           SYS_GPD_MFPH_PD8MFP_UART2_nRTS       /*!< GPD_MFPH PD8 setting for UART2_nRTS*/
#define UART2_nRTS_PC3           SYS_GPC_MFPL_PC3MFP_UART2_nRTS       /*!< GPC_MFPL PC3 setting for UART2_nRTS*/
#define UART3_RXD_PD0            SYS_GPD_MFPL_PD0MFP_UART3_RXD        /*!< GPD_MFPL PD0 setting for UART3_RXD*/
#define UART3_RXD_PE11           SYS_GPE_MFPH_PE11MFP_UART3_RXD       /*!< GPE_MFPH PE11 setting for UART3_RXD*/
#define UART3_RXD_PC9            SYS_GPC_MFPH_PC9MFP_UART3_RXD        /*!< GPC_MFPH PC9 setting for UART3_RXD*/
#define UART3_RXD_PE0            SYS_GPE_MFPL_PE0MFP_UART3_RXD        /*!< GPE_MFPL PE0 setting for UART3_RXD*/
#define UART3_RXD_PC2            SYS_GPC_MFPL_PC2MFP_UART3_RXD        /*!< GPC_MFPL PC2 setting for UART3_RXD*/
#define UART3_RXD_PB14           SYS_GPB_MFPH_PB14MFP_UART3_RXD       /*!< GPB_MFPH PB14 setting for UART3_RXD*/
#define UART3_TXD_PD1            SYS_GPD_MFPL_PD1MFP_UART3_TXD        /*!< GPD_MFPL PD1 setting for UART3_TXD*/
#define UART3_TXD_PC10           SYS_GPC_MFPH_PC10MFP_UART3_TXD       /*!< GPC_MFPH PC10 setting for UART3_TXD*/
#define UART3_TXD_PB15           SYS_GPB_MFPH_PB15MFP_UART3_TXD       /*!< GPB_MFPH PB15 setting for UART3_TXD*/
#define UART3_TXD_PC3            SYS_GPC_MFPL_PC3MFP_UART3_TXD        /*!< GPC_MFPL PC3 setting for UART3_TXD*/
#define UART3_TXD_PE1            SYS_GPE_MFPL_PE1MFP_UART3_TXD        /*!< GPE_MFPL PE1 setting for UART3_TXD*/
#define UART3_TXD_PE10           SYS_GPE_MFPH_PE10MFP_UART3_TXD       /*!< GPE_MFPH PE10 setting for UART3_TXD*/
#define UART3_nCTS_PB12          SYS_GPB_MFPH_PB12MFP_UART3_nCTS      /*!< GPB_MFPH PB12 setting for UART3_nCTS*/
#define UART3_nCTS_PH9           SYS_GPH_MFPH_PH9MFP_UART3_nCTS       /*!< GPH_MFPH PH9 setting for UART3_nCTS*/
#define UART3_nCTS_PD2           SYS_GPD_MFPL_PD2MFP_UART3_nCTS       /*!< GPD_MFPL PD2 setting for UART3_nCTS*/
#define UART3_nRTS_PB13          SYS_GPB_MFPH_PB13MFP_UART3_nRTS      /*!< GPB_MFPH PB13 setting for UART3_nRTS*/
#define UART3_nRTS_PH8           SYS_GPH_MFPH_PH8MFP_UART3_nRTS       /*!< GPH_MFPH PH8 setting for UART3_nRTS*/
#define UART3_nRTS_PD3           SYS_GPD_MFPL_PD3MFP_UART3_nRTS       /*!< GPD_MFPL PD3 setting for UART3_nRTS*/
#define UART4_RXD_PA13           SYS_GPA_MFPH_PA13MFP_UART4_RXD       /*!< GPA_MFPH PA13 setting for UART4_RXD*/
#define UART4_RXD_PC6            SYS_GPC_MFPL_PC6MFP_UART4_RXD        /*!< GPC_MFPL PC6 setting for UART4_RXD*/
#define UART4_RXD_PC4            SYS_GPC_MFPL_PC4MFP_UART4_RXD        /*!< GPC_MFPL PC4 setting for UART4_RXD*/
#define UART4_RXD_PB10           SYS_GPB_MFPH_PB10MFP_UART4_RXD       /*!< GPB_MFPH PB10 setting for UART4_RXD*/
#define UART4_RXD_PH11           SYS_GPH_MFPH_PH11MFP_UART4_RXD       /*!< GPH_MFPH PH11 setting for UART4_RXD*/
#define UART4_RXD_PA2            SYS_GPA_MFPL_PA2MFP_UART4_RXD        /*!< GPA_MFPL PA2 setting for UART4_RXD*/
#define UART4_RXD_PF6            SYS_GPF_MFPL_PF6MFP_UART4_RXD        /*!< GPF_MFPL PF6 setting for UART4_RXD*/
#define UART4_TXD_PH10           SYS_GPH_MFPH_PH10MFP_UART4_TXD       /*!< GPH_MFPH PH10 setting for UART4_TXD*/
#define UART4_TXD_PA3            SYS_GPA_MFPL_PA3MFP_UART4_TXD        /*!< GPA_MFPL PA3 setting for UART4_TXD*/
#define UART4_TXD_PA12           SYS_GPA_MFPH_PA12MFP_UART4_TXD       /*!< GPA_MFPH PA12 setting for UART4_TXD*/
#define UART4_TXD_PC7            SYS_GPC_MFPL_PC7MFP_UART4_TXD        /*!< GPC_MFPL PC7 setting for UART4_TXD*/
#define UART4_TXD_PB11           SYS_GPB_MFPH_PB11MFP_UART4_TXD       /*!< GPB_MFPH PB11 setting for UART4_TXD*/
#define UART4_TXD_PF7            SYS_GPF_MFPL_PF7MFP_UART4_TXD        /*!< GPF_MFPL PF7 setting for UART4_TXD*/
#define UART4_TXD_PC5            SYS_GPC_MFPL_PC5MFP_UART4_TXD        /*!< GPC_MFPL PC5 setting for UART4_TXD*/
#define UART4_nCTS_PE1           SYS_GPE_MFPL_PE1MFP_UART4_nCTS       /*!< GPE_MFPL PE1 setting for UART4_nCTS*/
#define UART4_nCTS_PC8           SYS_GPC_MFPH_PC8MFP_UART4_nCTS       /*!< GPC_MFPH PC8 setting for UART4_nCTS*/
#define UART4_nRTS_PE0           SYS_GPE_MFPL_PE0MFP_UART4_nRTS       /*!< GPE_MFPL PE0 setting for UART4_nRTS*/
#define UART4_nRTS_PE13          SYS_GPE_MFPH_PE13MFP_UART4_nRTS      /*!< GPE_MFPH PE13 setting for UART4_nRTS*/
#define UART5_RXD_PB4            SYS_GPB_MFPL_PB4MFP_UART5_RXD        /*!< GPB_MFPL PB4 setting for UART5_RXD*/
#define UART5_RXD_PA4            SYS_GPA_MFPL_PA4MFP_UART5_RXD        /*!< GPA_MFPL PA4 setting for UART5_RXD*/
#define UART5_RXD_PE6            SYS_GPE_MFPL_PE6MFP_UART5_RXD        /*!< GPE_MFPL PE6 setting for UART5_RXD*/
#define UART5_TXD_PB5            SYS_GPB_MFPL_PB5MFP_UART5_TXD        /*!< GPB_MFPL PB5 setting for UART5_TXD*/
#define UART5_TXD_PE7            SYS_GPE_MFPL_PE7MFP_UART5_TXD        /*!< GPE_MFPL PE7 setting for UART5_TXD*/
#define UART5_TXD_PA5            SYS_GPA_MFPL_PA5MFP_UART5_TXD        /*!< GPA_MFPL PA5 setting for UART5_TXD*/
#define UART5_nCTS_PB2           SYS_GPB_MFPL_PB2MFP_UART5_nCTS       /*!< GPB_MFPL PB2 setting for UART5_nCTS*/
#define UART5_nRTS_PB3           SYS_GPB_MFPL_PB3MFP_UART5_nRTS       /*!< GPB_MFPL PB3 setting for UART5_nRTS*/
#define USB_D_P_PA14             SYS_GPA_MFPH_PA14MFP_USB_D_P         /*!< GPA_MFPH PA14 setting for USB_D_P*/
#define USB_D_N_PA13             SYS_GPA_MFPH_PA13MFP_USB_D_N         /*!< GPA_MFPH PA13 setting for USB_D_N*/
#define USB_OTG_ID_PA15          SYS_GPA_MFPH_PA15MFP_USB_OTG_ID      /*!< GPA_MFPH PA15 setting for USB_OTG_ID*/
#define USB_VBUS_PA12            SYS_GPA_MFPH_PA12MFP_USB_VBUS        /*!< GPA_MFPH PA12 setting for USB_VBUS*/
#define USB_VBUS_EN_PB6          SYS_GPB_MFPL_PB6MFP_USB_VBUS_EN      /*!< GPB_MFPL PB6 setting for USB_VBUS_EN*/
#define USB_VBUS_EN_PB15         SYS_GPB_MFPH_PB15MFP_USB_VBUS_EN     /*!< GPB_MFPH PB15 setting for USB_VBUS_EN*/
#define USB_VBUS_ST_PB14         SYS_GPB_MFPH_PB14MFP_USB_VBUS_ST     /*!< GPB_MFPH PB14 setting for USB_VBUS_ST*/
#define USB_VBUS_ST_PB7          SYS_GPB_MFPL_PB7MFP_USB_VBUS_ST      /*!< GPB_MFPL PB7 setting for USB_VBUS_ST*/
#define USB_VBUS_ST_PD4          SYS_GPD_MFPL_PD4MFP_USB_VBUS_ST      /*!< GPD_MFPL PD4 setting for USB_VBUS_ST*/
#define USCI0_CLK_PD0            SYS_GPD_MFPL_PD0MFP_USCI0_CLK        /*!< GPD_MFPL PD0 setting for USCI0_CLK*/
#define USCI0_CLK_PA11           SYS_GPA_MFPH_PA11MFP_USCI0_CLK       /*!< GPA_MFPH PA11 setting for USCI0_CLK*/
#define USCI0_CLK_PE2            SYS_GPE_MFPL_PE2MFP_USCI0_CLK        /*!< GPE_MFPL PE2 setting for USCI0_CLK*/
#define USCI0_CLK_PB12           SYS_GPB_MFPH_PB12MFP_USCI0_CLK       /*!< GPB_MFPH PB12 setting for USCI0_CLK*/
#define USCI0_CTL0_PD4           SYS_GPD_MFPL_PD4MFP_USCI0_CTL0       /*!< GPD_MFPL PD4 setting for USCI0_CTL0*/
#define USCI0_CTL0_PE6           SYS_GPE_MFPL_PE6MFP_USCI0_CTL0       /*!< GPE_MFPL PE6 setting for USCI0_CTL0*/
#define USCI0_CTL0_PC13          SYS_GPC_MFPH_PC13MFP_USCI0_CTL0      /*!< GPC_MFPH PC13 setting for USCI0_CTL0*/
#define USCI0_CTL0_PD14          SYS_GPD_MFPH_PD14MFP_USCI0_CTL0      /*!< GPD_MFPH PD14 setting for USCI0_CTL0*/
#define USCI0_CTL1_PD3           SYS_GPD_MFPL_PD3MFP_USCI0_CTL1       /*!< GPD_MFPL PD3 setting for USCI0_CTL1*/
#define USCI0_CTL1_PE5           SYS_GPE_MFPL_PE5MFP_USCI0_CTL1       /*!< GPE_MFPL PE5 setting for USCI0_CTL1*/
#define USCI0_CTL1_PB15          SYS_GPB_MFPH_PB15MFP_USCI0_CTL1      /*!< GPB_MFPH PB15 setting for USCI0_CTL1*/
#define USCI0_CTL1_PA8           SYS_GPA_MFPH_PA8MFP_USCI0_CTL1       /*!< GPA_MFPH PA8 setting for USCI0_CTL1*/
#define USCI0_DAT0_PE3           SYS_GPE_MFPL_PE3MFP_USCI0_DAT0       /*!< GPE_MFPL PE3 setting for USCI0_DAT0*/
#define USCI0_DAT0_PB13          SYS_GPB_MFPH_PB13MFP_USCI0_DAT0      /*!< GPB_MFPH PB13 setting for USCI0_DAT0*/
#define USCI0_DAT0_PD1           SYS_GPD_MFPL_PD1MFP_USCI0_DAT0       /*!< GPD_MFPL PD1 setting for USCI0_DAT0*/
#define USCI0_DAT0_PA10          SYS_GPA_MFPH_PA10MFP_USCI0_DAT0      /*!< GPA_MFPH PA10 setting for USCI0_DAT0*/
#define USCI0_DAT1_PE4           SYS_GPE_MFPL_PE4MFP_USCI0_DAT1       /*!< GPE_MFPL PE4 setting for USCI0_DAT1*/
#define USCI0_DAT1_PD2           SYS_GPD_MFPL_PD2MFP_USCI0_DAT1       /*!< GPD_MFPL PD2 setting for USCI0_DAT1*/
#define USCI0_DAT1_PB14          SYS_GPB_MFPH_PB14MFP_USCI0_DAT1      /*!< GPB_MFPH PB14 setting for USCI0_DAT1*/
#define USCI0_DAT1_PA9           SYS_GPA_MFPH_PA9MFP_USCI0_DAT1       /*!< GPA_MFPH PA9 setting for USCI0_DAT1*/
#define USCI1_CLK_PE12           SYS_GPE_MFPH_PE12MFP_USCI1_CLK       /*!< GPE_MFPH PE12 setting for USCI1_CLK*/
#define USCI1_CLK_PD7            SYS_GPD_MFPL_PD7MFP_USCI1_CLK        /*!< GPD_MFPL PD7 setting for USCI1_CLK*/
#define USCI1_CLK_PB8            SYS_GPB_MFPH_PB8MFP_USCI1_CLK        /*!< GPB_MFPH PB8 setting for USCI1_CLK*/
#define USCI1_CLK_PB1            SYS_GPB_MFPL_PB1MFP_USCI1_CLK        /*!< GPB_MFPL PB1 setting for USCI1_CLK*/
#define USCI1_CTL0_PB10          SYS_GPB_MFPH_PB10MFP_USCI1_CTL0      /*!< GPB_MFPH PB10 setting for USCI1_CTL0*/
#define USCI1_CTL0_PB5           SYS_GPB_MFPL_PB5MFP_USCI1_CTL0       /*!< GPB_MFPL PB5 setting for USCI1_CTL0*/
#define USCI1_CTL0_PE9           SYS_GPE_MFPH_PE9MFP_USCI1_CTL0       /*!< GPE_MFPH PE9 setting for USCI1_CTL0*/
#define USCI1_CTL0_PD3           SYS_GPD_MFPL_PD3MFP_USCI1_CTL0       /*!< GPD_MFPL PD3 setting for USCI1_CTL0*/
#define USCI1_CTL1_PD4           SYS_GPD_MFPL_PD4MFP_USCI1_CTL1       /*!< GPD_MFPL PD4 setting for USCI1_CTL1*/
#define USCI1_CTL1_PE8           SYS_GPE_MFPH_PE8MFP_USCI1_CTL1       /*!< GPE_MFPH PE8 setting for USCI1_CTL1*/
#define USCI1_CTL1_PB9           SYS_GPB_MFPH_PB9MFP_USCI1_CTL1       /*!< GPB_MFPH PB9 setting for USCI1_CTL1*/
#define USCI1_CTL1_PB4           SYS_GPB_MFPL_PB4MFP_USCI1_CTL1       /*!< GPB_MFPL PB4 setting for USCI1_CTL1*/
#define USCI1_DAT0_PB2           SYS_GPB_MFPL_PB2MFP_USCI1_DAT0       /*!< GPB_MFPL PB2 setting for USCI1_DAT0*/
#define USCI1_DAT0_PB7           SYS_GPB_MFPL_PB7MFP_USCI1_DAT0       /*!< GPB_MFPL PB7 setting for USCI1_DAT0*/
#define USCI1_DAT0_PE10          SYS_GPE_MFPH_PE10MFP_USCI1_DAT0      /*!< GPE_MFPH PE10 setting for USCI1_DAT0*/
#define USCI1_DAT0_PD5           SYS_GPD_MFPL_PD5MFP_USCI1_DAT0       /*!< GPD_MFPL PD5 setting for USCI1_DAT0*/
#define USCI1_DAT1_PD6           SYS_GPD_MFPL_PD6MFP_USCI1_DAT1       /*!< GPD_MFPL PD6 setting for USCI1_DAT1*/
#define USCI1_DAT1_PB3           SYS_GPB_MFPL_PB3MFP_USCI1_DAT1       /*!< GPB_MFPL PB3 setting for USCI1_DAT1*/
#define USCI1_DAT1_PE11          SYS_GPE_MFPH_PE11MFP_USCI1_DAT1      /*!< GPE_MFPH PE11 setting for USCI1_DAT1*/
#define USCI1_DAT1_PB6           SYS_GPB_MFPL_PB6MFP_USCI1_DAT1       /*!< GPB_MFPL PB6 setting for USCI1_DAT1*/
#define X32_IN_PF5               SYS_GPF_MFPL_PF5MFP_X32_IN           /*!< GPF_MFPL PF5 setting for X32_IN*/
#define X32_OUT_PF4              SYS_GPF_MFPL_PF4MFP_X32_OUT          /*!< GPF_MFPL PF4 setting for X32_OUT*/
#define XT1_IN_PF3               SYS_GPF_MFPL_PF3MFP_XT1_IN           /*!< GPF_MFPL PF3 setting for XT1_IN*/
#define XT1_OUT_PF2              SYS_GPF_MFPL_PF2MFP_XT1_OUT          /*!< GPF_MFPL PF2 setting for XT1_OUT*/

/*---------------------------------------------------------------------------------------------------------*/
/*  Multi-Function setting mask constant definitions abbreviation.                                         */
/*---------------------------------------------------------------------------------------------------------*/


#define ACMP0_N_PB3_Msk         SYS_GPB_MFPL_PB3MFP_Msk        /*<! ACMP0_N         PB3      MFP Mask */
#define ACMP0_O_PB7_Msk         SYS_GPB_MFPL_PB7MFP_Msk        /*<! ACMP0_O         PB7      MFP Mask */
#define ACMP0_O_PC1_Msk         SYS_GPC_MFPL_PC1MFP_Msk        /*<! ACMP0_O         PC1      MFP Mask */
#define ACMP0_O_PC12_Msk        SYS_GPC_MFPH_PC12MFP_Msk       /*<! ACMP0_O         PC12     MFP Mask */
#define ACMP0_P0_PA11_Msk       SYS_GPA_MFPH_PA11MFP_Msk       /*<! ACMP0_P0        PA11     MFP Mask */
#define ACMP0_P1_PB2_Msk        SYS_GPB_MFPL_PB2MFP_Msk        /*<! ACMP0_P1        PB2      MFP Mask */
#define ACMP0_P2_PB12_Msk       SYS_GPB_MFPH_PB12MFP_Msk       /*<! ACMP0_P2        PB12     MFP Mask */
#define ACMP0_P3_PB13_Msk       SYS_GPB_MFPH_PB13MFP_Msk       /*<! ACMP0_P3        PB13     MFP Mask */
#define ACMP0_WLAT_PA7_Msk      SYS_GPA_MFPL_PA7MFP_Msk        /*<! ACMP0_WLAT      PA7      MFP Mask */
#define ACMP1_N_PB5_Msk         SYS_GPB_MFPL_PB5MFP_Msk        /*<! ACMP1_N         PB5      MFP Mask */
#define ACMP1_O_PB6_Msk         SYS_GPB_MFPL_PB6MFP_Msk        /*<! ACMP1_O         PB6      MFP Mask */
#define ACMP1_O_PC11_Msk        SYS_GPC_MFPH_PC11MFP_Msk       /*<! ACMP1_O         PC11     MFP Mask */
#define ACMP1_O_PC0_Msk         SYS_GPC_MFPL_PC0MFP_Msk        /*<! ACMP1_O         PC0      MFP Mask */
#define ACMP1_P0_PA10_Msk       SYS_GPA_MFPH_PA10MFP_Msk       /*<! ACMP1_P0        PA10     MFP Mask */
#define ACMP1_P1_PB4_Msk        SYS_GPB_MFPL_PB4MFP_Msk        /*<! ACMP1_P1        PB4      MFP Mask */
#define ACMP1_P2_PB12_Msk       SYS_GPB_MFPH_PB12MFP_Msk       /*<! ACMP1_P2        PB12     MFP Mask */
#define ACMP1_P3_PB13_Msk       SYS_GPB_MFPH_PB13MFP_Msk       /*<! ACMP1_P3        PB13     MFP Mask */
#define ACMP1_WLAT_PA6_Msk      SYS_GPA_MFPL_PA6MFP_Msk        /*<! ACMP1_WLAT      PA6      MFP Mask */
#define BPWM0_CH0_PA0_Msk       SYS_GPA_MFPL_PA0MFP_Msk        /*<! BPWM0_CH0       PA0      MFP Mask */
#define BPWM0_CH0_PA11_Msk      SYS_GPA_MFPH_PA11MFP_Msk       /*<! BPWM0_CH0       PA11     MFP Mask */
#define BPWM0_CH0_PE2_Msk       SYS_GPE_MFPL_PE2MFP_Msk        /*<! BPWM0_CH0       PE2      MFP Mask */
#define BPWM0_CH0_PG14_Msk      SYS_GPG_MFPH_PG14MFP_Msk       /*<! BPWM0_CH0       PG14     MFP Mask */
#define BPWM0_CH1_PA1_Msk       SYS_GPA_MFPL_PA1MFP_Msk        /*<! BPWM0_CH1       PA1      MFP Mask */
#define BPWM0_CH1_PE3_Msk       SYS_GPE_MFPL_PE3MFP_Msk        /*<! BPWM0_CH1       PE3      MFP Mask */
#define BPWM0_CH1_PG13_Msk      SYS_GPG_MFPH_PG13MFP_Msk       /*<! BPWM0_CH1       PG13     MFP Mask */
#define BPWM0_CH1_PA10_Msk      SYS_GPA_MFPH_PA10MFP_Msk       /*<! BPWM0_CH1       PA10     MFP Mask */
#define BPWM0_CH2_PE4_Msk       SYS_GPE_MFPL_PE4MFP_Msk        /*<! BPWM0_CH2       PE4      MFP Mask */
#define BPWM0_CH2_PG12_Msk      SYS_GPG_MFPH_PG12MFP_Msk       /*<! BPWM0_CH2       PG12     MFP Mask */
#define BPWM0_CH2_PA2_Msk       SYS_GPA_MFPL_PA2MFP_Msk        /*<! BPWM0_CH2       PA2      MFP Mask */
#define BPWM0_CH2_PA9_Msk       SYS_GPA_MFPH_PA9MFP_Msk        /*<! BPWM0_CH2       PA9      MFP Mask */
#define BPWM0_CH3_PG11_Msk      SYS_GPG_MFPH_PG11MFP_Msk       /*<! BPWM0_CH3       PG11     MFP Mask */
#define BPWM0_CH3_PA3_Msk       SYS_GPA_MFPL_PA3MFP_Msk        /*<! BPWM0_CH3       PA3      MFP Mask */
#define BPWM0_CH3_PA8_Msk       SYS_GPA_MFPH_PA8MFP_Msk        /*<! BPWM0_CH3       PA8      MFP Mask */
#define BPWM0_CH3_PE5_Msk       SYS_GPE_MFPL_PE5MFP_Msk        /*<! BPWM0_CH3       PE5      MFP Mask */
#define BPWM0_CH4_PG10_Msk      SYS_GPG_MFPH_PG10MFP_Msk       /*<! BPWM0_CH4       PG10     MFP Mask */
#define BPWM0_CH4_PA4_Msk       SYS_GPA_MFPL_PA4MFP_Msk        /*<! BPWM0_CH4       PA4      MFP Mask */
#define BPWM0_CH4_PC13_Msk      SYS_GPC_MFPH_PC13MFP_Msk       /*<! BPWM0_CH4       PC13     MFP Mask */
#define BPWM0_CH4_PE6_Msk       SYS_GPE_MFPL_PE6MFP_Msk        /*<! BPWM0_CH4       PE6      MFP Mask */
#define BPWM0_CH4_PF5_Msk       SYS_GPF_MFPL_PF5MFP_Msk        /*<! BPWM0_CH4       PF5      MFP Mask */
#define BPWM0_CH5_PA5_Msk       SYS_GPA_MFPL_PA5MFP_Msk        /*<! BPWM0_CH5       PA5      MFP Mask */
#define BPWM0_CH5_PE7_Msk       SYS_GPE_MFPL_PE7MFP_Msk        /*<! BPWM0_CH5       PE7      MFP Mask */
#define BPWM0_CH5_PF4_Msk       SYS_GPF_MFPL_PF4MFP_Msk        /*<! BPWM0_CH5       PF4      MFP Mask */
#define BPWM0_CH5_PD12_Msk      SYS_GPD_MFPH_PD12MFP_Msk       /*<! BPWM0_CH5       PD12     MFP Mask */
#define BPWM0_CH5_PG9_Msk       SYS_GPG_MFPH_PG9MFP_Msk        /*<! BPWM0_CH5       PG9      MFP Mask */
#define BPWM1_CH0_PB11_Msk      SYS_GPB_MFPH_PB11MFP_Msk       /*<! BPWM1_CH0       PB11     MFP Mask */
#define BPWM1_CH0_PC7_Msk       SYS_GPC_MFPL_PC7MFP_Msk        /*<! BPWM1_CH0       PC7      MFP Mask */
#define BPWM1_CH0_PF0_Msk       SYS_GPF_MFPL_PF0MFP_Msk        /*<! BPWM1_CH0       PF0      MFP Mask */
#define BPWM1_CH0_PF3_Msk       SYS_GPF_MFPL_PF3MFP_Msk        /*<! BPWM1_CH0       PF3      MFP Mask */
#define BPWM1_CH1_PC6_Msk       SYS_GPC_MFPL_PC6MFP_Msk        /*<! BPWM1_CH1       PC6      MFP Mask */
#define BPWM1_CH1_PF1_Msk       SYS_GPF_MFPL_PF1MFP_Msk        /*<! BPWM1_CH1       PF1      MFP Mask */
#define BPWM1_CH1_PF2_Msk       SYS_GPF_MFPL_PF2MFP_Msk        /*<! BPWM1_CH1       PF2      MFP Mask */
#define BPWM1_CH1_PB10_Msk      SYS_GPB_MFPH_PB10MFP_Msk       /*<! BPWM1_CH1       PB10     MFP Mask */
#define BPWM1_CH2_PB9_Msk       SYS_GPB_MFPH_PB9MFP_Msk        /*<! BPWM1_CH2       PB9      MFP Mask */
#define BPWM1_CH2_PA7_Msk       SYS_GPA_MFPL_PA7MFP_Msk        /*<! BPWM1_CH2       PA7      MFP Mask */
#define BPWM1_CH2_PA12_Msk      SYS_GPA_MFPH_PA12MFP_Msk       /*<! BPWM1_CH2       PA12     MFP Mask */
#define BPWM1_CH3_PA6_Msk       SYS_GPA_MFPL_PA6MFP_Msk        /*<! BPWM1_CH3       PA6      MFP Mask */
#define BPWM1_CH3_PA13_Msk      SYS_GPA_MFPH_PA13MFP_Msk       /*<! BPWM1_CH3       PA13     MFP Mask */
#define BPWM1_CH3_PB8_Msk       SYS_GPB_MFPH_PB8MFP_Msk        /*<! BPWM1_CH3       PB8      MFP Mask */
#define BPWM1_CH4_PA14_Msk      SYS_GPA_MFPH_PA14MFP_Msk       /*<! BPWM1_CH4       PA14     MFP Mask */
#define BPWM1_CH4_PC8_Msk       SYS_GPC_MFPH_PC8MFP_Msk        /*<! BPWM1_CH4       PC8      MFP Mask */
#define BPWM1_CH4_PB7_Msk       SYS_GPB_MFPL_PB7MFP_Msk        /*<! BPWM1_CH4       PB7      MFP Mask */
#define BPWM1_CH5_PA15_Msk      SYS_GPA_MFPH_PA15MFP_Msk       /*<! BPWM1_CH5       PA15     MFP Mask */
#define BPWM1_CH5_PB6_Msk       SYS_GPB_MFPL_PB6MFP_Msk        /*<! BPWM1_CH5       PB6      MFP Mask */
#define BPWM1_CH5_PE13_Msk      SYS_GPE_MFPH_PE13MFP_Msk       /*<! BPWM1_CH5       PE13     MFP Mask */
#define CAN0_RXD_PA13_Msk       SYS_GPA_MFPH_PA13MFP_Msk       /*<! CAN0_RXD        PA13     MFP Mask */
#define CAN0_RXD_PD10_Msk       SYS_GPD_MFPH_PD10MFP_Msk       /*<! CAN0_RXD        PD10     MFP Mask */
#define CAN0_RXD_PA4_Msk        SYS_GPA_MFPL_PA4MFP_Msk        /*<! CAN0_RXD        PA4      MFP Mask */
#define CAN0_RXD_PC4_Msk        SYS_GPC_MFPL_PC4MFP_Msk        /*<! CAN0_RXD        PC4      MFP Mask */
#define CAN0_RXD_PB10_Msk       SYS_GPB_MFPH_PB10MFP_Msk       /*<! CAN0_RXD        PB10     MFP Mask */
#define CAN0_RXD_PE15_Msk       SYS_GPE_MFPH_PE15MFP_Msk       /*<! CAN0_RXD        PE15     MFP Mask */
#define CAN0_TXD_PD11_Msk       SYS_GPD_MFPH_PD11MFP_Msk       /*<! CAN0_TXD        PD11     MFP Mask */
#define CAN0_TXD_PC5_Msk        SYS_GPC_MFPL_PC5MFP_Msk        /*<! CAN0_TXD        PC5      MFP Mask */
#define CAN0_TXD_PB11_Msk       SYS_GPB_MFPH_PB11MFP_Msk       /*<! CAN0_TXD        PB11     MFP Mask */
#define CAN0_TXD_PA12_Msk       SYS_GPA_MFPH_PA12MFP_Msk       /*<! CAN0_TXD        PA12     MFP Mask */
#define CAN0_TXD_PE14_Msk       SYS_GPE_MFPH_PE14MFP_Msk       /*<! CAN0_TXD        PE14     MFP Mask */
#define CAN0_TXD_PA5_Msk        SYS_GPA_MFPL_PA5MFP_Msk        /*<! CAN0_TXD        PA5      MFP Mask */
#define CLKO_PC13_Msk           SYS_GPC_MFPH_PC13MFP_Msk       /*<! CLKO            PC13     MFP Mask */
#define CLKO_PB14_Msk           SYS_GPB_MFPH_PB14MFP_Msk       /*<! CLKO            PB14     MFP Mask */
#define CLKO_PD12_Msk           SYS_GPD_MFPH_PD12MFP_Msk       /*<! CLKO            PD12     MFP Mask */
#define CLKO_PG15_Msk           SYS_GPG_MFPH_PG15MFP_Msk       /*<! CLKO            PG15     MFP Mask */
#define DAC0_OUT_PB12_Msk       SYS_GPB_MFPH_PB12MFP_Msk       /*<! DAC0_OUT        PB12     MFP Mask */
#define DAC0_ST_PA10_Msk        SYS_GPA_MFPH_PA10MFP_Msk       /*<! DAC0_ST         PA10     MFP Mask */
#define DAC0_ST_PA0_Msk         SYS_GPA_MFPL_PA0MFP_Msk        /*<! DAC0_ST         PA0      MFP Mask */
#define DAC1_OUT_PB13_Msk       SYS_GPB_MFPH_PB13MFP_Msk       /*<! DAC1_OUT        PB13     MFP Mask */
#define DAC1_ST_PA1_Msk         SYS_GPA_MFPL_PA1MFP_Msk        /*<! DAC1_ST         PA1      MFP Mask */
#define DAC1_ST_PA11_Msk        SYS_GPA_MFPH_PA11MFP_Msk       /*<! DAC1_ST         PA11     MFP Mask */
#define EADC0_CH0_PB0_Msk       SYS_GPB_MFPL_PB0MFP_Msk        /*<! EADC0_CH0       PB0      MFP Mask */
#define EADC0_CH1_PB1_Msk       SYS_GPB_MFPL_PB1MFP_Msk        /*<! EADC0_CH1       PB1      MFP Mask */
#define EADC0_CH10_PB10_Msk     SYS_GPB_MFPH_PB10MFP_Msk       /*<! EADC0_CH10      PB10     MFP Mask */
#define EADC0_CH11_PB11_Msk     SYS_GPB_MFPH_PB11MFP_Msk       /*<! EADC0_CH11      PB11     MFP Mask */
#define EADC0_CH12_PB12_Msk     SYS_GPB_MFPH_PB12MFP_Msk       /*<! EADC0_CH12      PB12     MFP Mask */
#define EADC0_CH13_PB13_Msk     SYS_GPB_MFPH_PB13MFP_Msk       /*<! EADC0_CH13      PB13     MFP Mask */
#define EADC0_CH14_PB14_Msk     SYS_GPB_MFPH_PB14MFP_Msk       /*<! EADC0_CH14      PB14     MFP Mask */
#define EADC0_CH15_PB15_Msk     SYS_GPB_MFPH_PB15MFP_Msk       /*<! EADC0_CH15      PB15     MFP Mask */
#define EADC0_CH2_PB2_Msk       SYS_GPB_MFPL_PB2MFP_Msk        /*<! EADC0_CH2       PB2      MFP Mask */
#define EADC0_CH3_PB3_Msk       SYS_GPB_MFPL_PB3MFP_Msk        /*<! EADC0_CH3       PB3      MFP Mask */
#define EADC0_CH4_PB4_Msk       SYS_GPB_MFPL_PB4MFP_Msk        /*<! EADC0_CH4       PB4      MFP Mask */
#define EADC0_CH5_PB5_Msk       SYS_GPB_MFPL_PB5MFP_Msk        /*<! EADC0_CH5       PB5      MFP Mask */
#define EADC0_CH6_PB6_Msk       SYS_GPB_MFPL_PB6MFP_Msk        /*<! EADC0_CH6       PB6      MFP Mask */
#define EADC0_CH7_PB7_Msk       SYS_GPB_MFPL_PB7MFP_Msk        /*<! EADC0_CH7       PB7      MFP Mask */
#define EADC0_CH8_PB8_Msk       SYS_GPB_MFPH_PB8MFP_Msk        /*<! EADC0_CH8       PB8      MFP Mask */
#define EADC0_CH9_PB9_Msk       SYS_GPB_MFPH_PB9MFP_Msk        /*<! EADC0_CH9       PB9      MFP Mask */
#define EADC0_ST_PD12_Msk       SYS_GPD_MFPH_PD12MFP_Msk       /*<! EADC0_ST        PD12     MFP Mask */
#define EADC0_ST_PF5_Msk        SYS_GPF_MFPL_PF5MFP_Msk        /*<! EADC0_ST        PF5      MFP Mask */
#define EADC0_ST_PC13_Msk       SYS_GPC_MFPH_PC13MFP_Msk       /*<! EADC0_ST        PC13     MFP Mask */
#define EADC0_ST_PG15_Msk       SYS_GPG_MFPH_PG15MFP_Msk       /*<! EADC0_ST        PG15     MFP Mask */
#define EBI_AD0_PG9_Msk         SYS_GPG_MFPH_PG9MFP_Msk        /*<! EBI_AD0         PG9      MFP Mask */
#define EBI_AD0_PC0_Msk         SYS_GPC_MFPL_PC0MFP_Msk        /*<! EBI_AD0         PC0      MFP Mask */
#define EBI_AD1_PC1_Msk         SYS_GPC_MFPL_PC1MFP_Msk        /*<! EBI_AD1         PC1      MFP Mask */
#define EBI_AD1_PG10_Msk        SYS_GPG_MFPH_PG10MFP_Msk       /*<! EBI_AD1         PG10     MFP Mask */
#define EBI_AD10_PE1_Msk        SYS_GPE_MFPL_PE1MFP_Msk        /*<! EBI_AD10        PE1      MFP Mask */
#define EBI_AD10_PD3_Msk        SYS_GPD_MFPL_PD3MFP_Msk        /*<! EBI_AD10        PD3      MFP Mask */
#define EBI_AD10_PD13_Msk       SYS_GPD_MFPH_PD13MFP_Msk       /*<! EBI_AD10        PD13     MFP Mask */
#define EBI_AD11_PE0_Msk        SYS_GPE_MFPL_PE0MFP_Msk        /*<! EBI_AD11        PE0      MFP Mask */
#define EBI_AD11_PD2_Msk        SYS_GPD_MFPL_PD2MFP_Msk        /*<! EBI_AD11        PD2      MFP Mask */
#define EBI_AD12_PD1_Msk        SYS_GPD_MFPL_PD1MFP_Msk        /*<! EBI_AD12        PD1      MFP Mask */
#define EBI_AD12_PB15_Msk       SYS_GPB_MFPH_PB15MFP_Msk       /*<! EBI_AD12        PB15     MFP Mask */
#define EBI_AD12_PH8_Msk        SYS_GPH_MFPH_PH8MFP_Msk        /*<! EBI_AD12        PH8      MFP Mask */
#define EBI_AD13_PD0_Msk        SYS_GPD_MFPL_PD0MFP_Msk        /*<! EBI_AD13        PD0      MFP Mask */
#define EBI_AD13_PB14_Msk       SYS_GPB_MFPH_PB14MFP_Msk       /*<! EBI_AD13        PB14     MFP Mask */
#define EBI_AD13_PH9_Msk        SYS_GPH_MFPH_PH9MFP_Msk        /*<! EBI_AD13        PH9      MFP Mask */
#define EBI_AD14_PB13_Msk       SYS_GPB_MFPH_PB13MFP_Msk       /*<! EBI_AD14        PB13     MFP Mask */
#define EBI_AD14_PH10_Msk       SYS_GPH_MFPH_PH10MFP_Msk       /*<! EBI_AD14        PH10     MFP Mask */
#define EBI_AD15_PB12_Msk       SYS_GPB_MFPH_PB12MFP_Msk       /*<! EBI_AD15        PB12     MFP Mask */
#define EBI_AD15_PH11_Msk       SYS_GPH_MFPH_PH11MFP_Msk       /*<! EBI_AD15        PH11     MFP Mask */
#define EBI_AD2_PG11_Msk        SYS_GPG_MFPH_PG11MFP_Msk       /*<! EBI_AD2         PG11     MFP Mask */
#define EBI_AD2_PC2_Msk         SYS_GPC_MFPL_PC2MFP_Msk        /*<! EBI_AD2         PC2      MFP Mask */
#define EBI_AD3_PC3_Msk         SYS_GPC_MFPL_PC3MFP_Msk        /*<! EBI_AD3         PC3      MFP Mask */
#define EBI_AD3_PG12_Msk        SYS_GPG_MFPH_PG12MFP_Msk       /*<! EBI_AD3         PG12     MFP Mask */
#define EBI_AD4_PG13_Msk        SYS_GPG_MFPH_PG13MFP_Msk       /*<! EBI_AD4         PG13     MFP Mask */
#define EBI_AD4_PC4_Msk         SYS_GPC_MFPL_PC4MFP_Msk        /*<! EBI_AD4         PC4      MFP Mask */
#define EBI_AD5_PG14_Msk        SYS_GPG_MFPH_PG14MFP_Msk       /*<! EBI_AD5         PG14     MFP Mask */
#define EBI_AD5_PC5_Msk         SYS_GPC_MFPL_PC5MFP_Msk        /*<! EBI_AD5         PC5      MFP Mask */
#define EBI_AD6_PD8_Msk         SYS_GPD_MFPH_PD8MFP_Msk        /*<! EBI_AD6         PD8      MFP Mask */
#define EBI_AD6_PA6_Msk         SYS_GPA_MFPL_PA6MFP_Msk        /*<! EBI_AD6         PA6      MFP Mask */
#define EBI_AD7_PA7_Msk         SYS_GPA_MFPL_PA7MFP_Msk        /*<! EBI_AD7         PA7      MFP Mask */
#define EBI_AD7_PD9_Msk         SYS_GPD_MFPH_PD9MFP_Msk        /*<! EBI_AD7         PD9      MFP Mask */
#define EBI_AD8_PC6_Msk         SYS_GPC_MFPL_PC6MFP_Msk        /*<! EBI_AD8         PC6      MFP Mask */
#define EBI_AD8_PE14_Msk        SYS_GPE_MFPH_PE14MFP_Msk       /*<! EBI_AD8         PE14     MFP Mask */
#define EBI_AD9_PE15_Msk        SYS_GPE_MFPH_PE15MFP_Msk       /*<! EBI_AD9         PE15     MFP Mask */
#define EBI_AD9_PC7_Msk         SYS_GPC_MFPL_PC7MFP_Msk        /*<! EBI_AD9         PC7      MFP Mask */
#define EBI_ADR0_PB5_Msk        SYS_GPB_MFPL_PB5MFP_Msk        /*<! EBI_ADR0        PB5      MFP Mask */
#define EBI_ADR0_PH7_Msk        SYS_GPH_MFPL_PH7MFP_Msk        /*<! EBI_ADR0        PH7      MFP Mask */
#define EBI_ADR1_PH6_Msk        SYS_GPH_MFPL_PH6MFP_Msk        /*<! EBI_ADR1        PH6      MFP Mask */
#define EBI_ADR1_PB4_Msk        SYS_GPB_MFPL_PB4MFP_Msk        /*<! EBI_ADR1        PB4      MFP Mask */
#define EBI_ADR10_PE8_Msk       SYS_GPE_MFPH_PE8MFP_Msk        /*<! EBI_ADR10       PE8      MFP Mask */
#define EBI_ADR10_PC13_Msk      SYS_GPC_MFPH_PC13MFP_Msk       /*<! EBI_ADR10       PC13     MFP Mask */
#define EBI_ADR11_PG2_Msk       SYS_GPG_MFPL_PG2MFP_Msk        /*<! EBI_ADR11       PG2      MFP Mask */
#define EBI_ADR11_PE9_Msk       SYS_GPE_MFPH_PE9MFP_Msk        /*<! EBI_ADR11       PE9      MFP Mask */
#define EBI_ADR12_PG3_Msk       SYS_GPG_MFPL_PG3MFP_Msk        /*<! EBI_ADR12       PG3      MFP Mask */
#define EBI_ADR12_PE10_Msk      SYS_GPE_MFPH_PE10MFP_Msk       /*<! EBI_ADR12       PE10     MFP Mask */
#define EBI_ADR13_PG4_Msk       SYS_GPG_MFPL_PG4MFP_Msk        /*<! EBI_ADR13       PG4      MFP Mask */
#define EBI_ADR13_PE11_Msk      SYS_GPE_MFPH_PE11MFP_Msk       /*<! EBI_ADR13       PE11     MFP Mask */
#define EBI_ADR14_PE12_Msk      SYS_GPE_MFPH_PE12MFP_Msk       /*<! EBI_ADR14       PE12     MFP Mask */
#define EBI_ADR14_PF11_Msk      SYS_GPF_MFPH_PF11MFP_Msk       /*<! EBI_ADR14       PF11     MFP Mask */
#define EBI_ADR15_PF10_Msk      SYS_GPF_MFPH_PF10MFP_Msk       /*<! EBI_ADR15       PF10     MFP Mask */
#define EBI_ADR15_PE13_Msk      SYS_GPE_MFPH_PE13MFP_Msk       /*<! EBI_ADR15       PE13     MFP Mask */
#define EBI_ADR16_PB11_Msk      SYS_GPB_MFPH_PB11MFP_Msk       /*<! EBI_ADR16       PB11     MFP Mask */
#define EBI_ADR16_PF9_Msk       SYS_GPF_MFPH_PF9MFP_Msk        /*<! EBI_ADR16       PF9      MFP Mask */
#define EBI_ADR16_PC8_Msk       SYS_GPC_MFPH_PC8MFP_Msk        /*<! EBI_ADR16       PC8      MFP Mask */
#define EBI_ADR17_PF8_Msk       SYS_GPF_MFPH_PF8MFP_Msk        /*<! EBI_ADR17       PF8      MFP Mask */
#define EBI_ADR17_PB10_Msk      SYS_GPB_MFPH_PB10MFP_Msk       /*<! EBI_ADR17       PB10     MFP Mask */
#define EBI_ADR18_PB9_Msk       SYS_GPB_MFPH_PB9MFP_Msk        /*<! EBI_ADR18       PB9      MFP Mask */
#define EBI_ADR18_PF7_Msk       SYS_GPF_MFPL_PF7MFP_Msk        /*<! EBI_ADR18       PF7      MFP Mask */
#define EBI_ADR19_PF6_Msk       SYS_GPF_MFPL_PF6MFP_Msk        /*<! EBI_ADR19       PF6      MFP Mask */
#define EBI_ADR19_PB8_Msk       SYS_GPB_MFPH_PB8MFP_Msk        /*<! EBI_ADR19       PB8      MFP Mask */
#define EBI_ADR2_PB3_Msk        SYS_GPB_MFPL_PB3MFP_Msk        /*<! EBI_ADR2        PB3      MFP Mask */
#define EBI_ADR2_PH5_Msk        SYS_GPH_MFPL_PH5MFP_Msk        /*<! EBI_ADR2        PH5      MFP Mask */
#define EBI_ADR3_PH4_Msk        SYS_GPH_MFPL_PH4MFP_Msk        /*<! EBI_ADR3        PH4      MFP Mask */
#define EBI_ADR3_PB2_Msk        SYS_GPB_MFPL_PB2MFP_Msk        /*<! EBI_ADR3        PB2      MFP Mask */
#define EBI_ADR4_PC12_Msk       SYS_GPC_MFPH_PC12MFP_Msk       /*<! EBI_ADR4        PC12     MFP Mask */
#define EBI_ADR5_PC11_Msk       SYS_GPC_MFPH_PC11MFP_Msk       /*<! EBI_ADR5        PC11     MFP Mask */
#define EBI_ADR6_PC10_Msk       SYS_GPC_MFPH_PC10MFP_Msk       /*<! EBI_ADR6        PC10     MFP Mask */
#define EBI_ADR7_PC9_Msk        SYS_GPC_MFPH_PC9MFP_Msk        /*<! EBI_ADR7        PC9      MFP Mask */
#define EBI_ADR8_PB1_Msk        SYS_GPB_MFPL_PB1MFP_Msk        /*<! EBI_ADR8        PB1      MFP Mask */
#define EBI_ADR9_PB0_Msk        SYS_GPB_MFPL_PB0MFP_Msk        /*<! EBI_ADR9        PB0      MFP Mask */
#define EBI_ALE_PA8_Msk         SYS_GPA_MFPH_PA8MFP_Msk        /*<! EBI_ALE         PA8      MFP Mask */
#define EBI_ALE_PE2_Msk         SYS_GPE_MFPL_PE2MFP_Msk        /*<! EBI_ALE         PE2      MFP Mask */
#define EBI_MCLK_PE3_Msk        SYS_GPE_MFPL_PE3MFP_Msk        /*<! EBI_MCLK        PE3      MFP Mask */
#define EBI_MCLK_PA9_Msk        SYS_GPA_MFPH_PA9MFP_Msk        /*<! EBI_MCLK        PA9      MFP Mask */
#define EBI_nCS0_PB7_Msk        SYS_GPB_MFPL_PB7MFP_Msk        /*<! EBI_nCS0        PB7      MFP Mask */
#define EBI_nCS0_PF6_Msk        SYS_GPF_MFPL_PF6MFP_Msk        /*<! EBI_nCS0        PF6      MFP Mask */
#define EBI_nCS0_PD12_Msk       SYS_GPD_MFPH_PD12MFP_Msk       /*<! EBI_nCS0        PD12     MFP Mask */
#define EBI_nCS0_PD14_Msk       SYS_GPD_MFPH_PD14MFP_Msk       /*<! EBI_nCS0        PD14     MFP Mask */
#define EBI_nCS0_PF3_Msk        SYS_GPF_MFPL_PF3MFP_Msk        /*<! EBI_nCS0        PF3      MFP Mask */
#define EBI_nCS1_PF2_Msk        SYS_GPF_MFPL_PF2MFP_Msk        /*<! EBI_nCS1        PF2      MFP Mask */
#define EBI_nCS1_PD11_Msk       SYS_GPD_MFPH_PD11MFP_Msk       /*<! EBI_nCS1        PD11     MFP Mask */
#define EBI_nCS1_PB6_Msk        SYS_GPB_MFPL_PB6MFP_Msk        /*<! EBI_nCS1        PB6      MFP Mask */
#define EBI_nCS2_PD10_Msk       SYS_GPD_MFPH_PD10MFP_Msk       /*<! EBI_nCS2        PD10     MFP Mask */
#define EBI_nRD_PA11_Msk        SYS_GPA_MFPH_PA11MFP_Msk       /*<! EBI_nRD         PA11     MFP Mask */
#define EBI_nRD_PE5_Msk         SYS_GPE_MFPL_PE5MFP_Msk        /*<! EBI_nRD         PE5      MFP Mask */
#define EBI_nWR_PA10_Msk        SYS_GPA_MFPH_PA10MFP_Msk       /*<! EBI_nWR         PA10     MFP Mask */
#define EBI_nWR_PE4_Msk         SYS_GPE_MFPL_PE4MFP_Msk        /*<! EBI_nWR         PE4      MFP Mask */
#define EBI_nWRH_PB6_Msk        SYS_GPB_MFPL_PB6MFP_Msk        /*<! EBI_nWRH        PB6      MFP Mask */
#define EBI_nWRL_PB7_Msk        SYS_GPB_MFPL_PB7MFP_Msk        /*<! EBI_nWRL        PB7      MFP Mask */
#define ECAP0_IC0_PA10_Msk      SYS_GPA_MFPH_PA10MFP_Msk       /*<! ECAP0_IC0       PA10     MFP Mask */
#define ECAP0_IC0_PE8_Msk       SYS_GPE_MFPH_PE8MFP_Msk        /*<! ECAP0_IC0       PE8      MFP Mask */
#define ECAP0_IC1_PE9_Msk       SYS_GPE_MFPH_PE9MFP_Msk        /*<! ECAP0_IC1       PE9      MFP Mask */
#define ECAP0_IC1_PA9_Msk       SYS_GPA_MFPH_PA9MFP_Msk        /*<! ECAP0_IC1       PA9      MFP Mask */
#define ECAP0_IC2_PA8_Msk       SYS_GPA_MFPH_PA8MFP_Msk        /*<! ECAP0_IC2       PA8      MFP Mask */
#define ECAP0_IC2_PE10_Msk      SYS_GPE_MFPH_PE10MFP_Msk       /*<! ECAP0_IC2       PE10     MFP Mask */
#define ECAP1_IC0_PC10_Msk      SYS_GPC_MFPH_PC10MFP_Msk       /*<! ECAP1_IC0       PC10     MFP Mask */
#define ECAP1_IC0_PE13_Msk      SYS_GPE_MFPH_PE13MFP_Msk       /*<! ECAP1_IC0       PE13     MFP Mask */
#define ECAP1_IC1_PE12_Msk      SYS_GPE_MFPH_PE12MFP_Msk       /*<! ECAP1_IC1       PE12     MFP Mask */
#define ECAP1_IC1_PC11_Msk      SYS_GPC_MFPH_PC11MFP_Msk       /*<! ECAP1_IC1       PC11     MFP Mask */
#define ECAP1_IC2_PE11_Msk      SYS_GPE_MFPH_PE11MFP_Msk       /*<! ECAP1_IC2       PE11     MFP Mask */
#define ECAP1_IC2_PC12_Msk      SYS_GPC_MFPH_PC12MFP_Msk       /*<! ECAP1_IC2       PC12     MFP Mask */
#define I2C0_SCL_PB5_Msk        SYS_GPB_MFPL_PB5MFP_Msk        /*<! I2C0_SCL        PB5      MFP Mask */
#define I2C0_SCL_PC1_Msk        SYS_GPC_MFPL_PC1MFP_Msk        /*<! I2C0_SCL        PC1      MFP Mask */
#define I2C0_SCL_PF3_Msk        SYS_GPF_MFPL_PF3MFP_Msk        /*<! I2C0_SCL        PF3      MFP Mask */
#define I2C0_SCL_PE13_Msk       SYS_GPE_MFPH_PE13MFP_Msk       /*<! I2C0_SCL        PE13     MFP Mask */
#define I2C0_SCL_PD7_Msk        SYS_GPD_MFPL_PD7MFP_Msk        /*<! I2C0_SCL        PD7      MFP Mask */
#define I2C0_SCL_PA5_Msk        SYS_GPA_MFPL_PA5MFP_Msk        /*<! I2C0_SCL        PA5      MFP Mask */
#define I2C0_SCL_PC12_Msk       SYS_GPC_MFPH_PC12MFP_Msk       /*<! I2C0_SCL        PC12     MFP Mask */
#define I2C0_SDA_PB4_Msk        SYS_GPB_MFPL_PB4MFP_Msk        /*<! I2C0_SDA        PB4      MFP Mask */
#define I2C0_SDA_PC8_Msk        SYS_GPC_MFPH_PC8MFP_Msk        /*<! I2C0_SDA        PC8      MFP Mask */
#define I2C0_SDA_PC0_Msk        SYS_GPC_MFPL_PC0MFP_Msk        /*<! I2C0_SDA        PC0      MFP Mask */
#define I2C0_SDA_PD6_Msk        SYS_GPD_MFPL_PD6MFP_Msk        /*<! I2C0_SDA        PD6      MFP Mask */
#define I2C0_SDA_PC11_Msk       SYS_GPC_MFPH_PC11MFP_Msk       /*<! I2C0_SDA        PC11     MFP Mask */
#define I2C0_SDA_PA4_Msk        SYS_GPA_MFPL_PA4MFP_Msk        /*<! I2C0_SDA        PA4      MFP Mask */
#define I2C0_SDA_PF2_Msk        SYS_GPF_MFPL_PF2MFP_Msk        /*<! I2C0_SDA        PF2      MFP Mask */
#define I2C0_SMBAL_PG2_Msk      SYS_GPG_MFPL_PG2MFP_Msk        /*<! I2C0_SMBAL      PG2      MFP Mask */
#define I2C0_SMBAL_PC3_Msk      SYS_GPC_MFPL_PC3MFP_Msk        /*<! I2C0_SMBAL      PC3      MFP Mask */
#define I2C0_SMBSUS_PC2_Msk     SYS_GPC_MFPL_PC2MFP_Msk        /*<! I2C0_SMBSUS     PC2      MFP Mask */
#define I2C0_SMBSUS_PG3_Msk     SYS_GPG_MFPL_PG3MFP_Msk        /*<! I2C0_SMBSUS     PG3      MFP Mask */
#define I2C1_SCL_PA3_Msk        SYS_GPA_MFPL_PA3MFP_Msk        /*<! I2C1_SCL        PA3      MFP Mask */
#define I2C1_SCL_PG2_Msk        SYS_GPG_MFPL_PG2MFP_Msk        /*<! I2C1_SCL        PG2      MFP Mask */
#define I2C1_SCL_PB1_Msk        SYS_GPB_MFPL_PB1MFP_Msk        /*<! I2C1_SCL        PB1      MFP Mask */
#define I2C1_SCL_PB11_Msk       SYS_GPB_MFPH_PB11MFP_Msk       /*<! I2C1_SCL        PB11     MFP Mask */
#define I2C1_SCL_PD5_Msk        SYS_GPD_MFPL_PD5MFP_Msk        /*<! I2C1_SCL        PD5      MFP Mask */
#define I2C1_SCL_PA12_Msk       SYS_GPA_MFPH_PA12MFP_Msk       /*<! I2C1_SCL        PA12     MFP Mask */
#define I2C1_SCL_PC5_Msk        SYS_GPC_MFPL_PC5MFP_Msk        /*<! I2C1_SCL        PC5      MFP Mask */
#define I2C1_SCL_PA7_Msk        SYS_GPA_MFPL_PA7MFP_Msk        /*<! I2C1_SCL        PA7      MFP Mask */
#define I2C1_SCL_PF0_Msk        SYS_GPF_MFPL_PF0MFP_Msk        /*<! I2C1_SCL        PF0      MFP Mask */
#define I2C1_SCL_PE1_Msk        SYS_GPE_MFPL_PE1MFP_Msk        /*<! I2C1_SCL        PE1      MFP Mask */
#define I2C1_SDA_PB0_Msk        SYS_GPB_MFPL_PB0MFP_Msk        /*<! I2C1_SDA        PB0      MFP Mask */
#define I2C1_SDA_PA6_Msk        SYS_GPA_MFPL_PA6MFP_Msk        /*<! I2C1_SDA        PA6      MFP Mask */
#define I2C1_SDA_PA13_Msk       SYS_GPA_MFPH_PA13MFP_Msk       /*<! I2C1_SDA        PA13     MFP Mask */
#define I2C1_SDA_PG3_Msk        SYS_GPG_MFPL_PG3MFP_Msk        /*<! I2C1_SDA        PG3      MFP Mask */
#define I2C1_SDA_PE0_Msk        SYS_GPE_MFPL_PE0MFP_Msk        /*<! I2C1_SDA        PE0      MFP Mask */
#define I2C1_SDA_PC4_Msk        SYS_GPC_MFPL_PC4MFP_Msk        /*<! I2C1_SDA        PC4      MFP Mask */
#define I2C1_SDA_PA2_Msk        SYS_GPA_MFPL_PA2MFP_Msk        /*<! I2C1_SDA        PA2      MFP Mask */
#define I2C1_SDA_PB10_Msk       SYS_GPB_MFPH_PB10MFP_Msk       /*<! I2C1_SDA        PB10     MFP Mask */
#define I2C1_SDA_PF1_Msk        SYS_GPF_MFPL_PF1MFP_Msk        /*<! I2C1_SDA        PF1      MFP Mask */
#define I2C1_SDA_PD4_Msk        SYS_GPD_MFPL_PD4MFP_Msk        /*<! I2C1_SDA        PD4      MFP Mask */
#define I2C1_SMBAL_PB9_Msk      SYS_GPB_MFPH_PB9MFP_Msk        /*<! I2C1_SMBAL      PB9      MFP Mask */
#define I2C1_SMBAL_PC7_Msk      SYS_GPC_MFPL_PC7MFP_Msk        /*<! I2C1_SMBAL      PC7      MFP Mask */
#define I2C1_SMBAL_PH8_Msk      SYS_GPH_MFPH_PH8MFP_Msk        /*<! I2C1_SMBAL      PH8      MFP Mask */
#define I2C1_SMBSUS_PH9_Msk     SYS_GPH_MFPH_PH9MFP_Msk        /*<! I2C1_SMBSUS     PH9      MFP Mask */
#define I2C1_SMBSUS_PC6_Msk     SYS_GPC_MFPL_PC6MFP_Msk        /*<! I2C1_SMBSUS     PC6      MFP Mask */
#define I2C1_SMBSUS_PB8_Msk     SYS_GPB_MFPH_PB8MFP_Msk        /*<! I2C1_SMBSUS     PB8      MFP Mask */
#define I2C2_SCL_PB13_Msk       SYS_GPB_MFPH_PB13MFP_Msk       /*<! I2C2_SCL        PB13     MFP Mask */
#define I2C2_SCL_PA11_Msk       SYS_GPA_MFPH_PA11MFP_Msk       /*<! I2C2_SCL        PA11     MFP Mask */
#define I2C2_SCL_PH8_Msk        SYS_GPH_MFPH_PH8MFP_Msk        /*<! I2C2_SCL        PH8      MFP Mask */
#define I2C2_SCL_PD9_Msk        SYS_GPD_MFPH_PD9MFP_Msk        /*<! I2C2_SCL        PD9      MFP Mask */
#define I2C2_SCL_PD1_Msk        SYS_GPD_MFPL_PD1MFP_Msk        /*<! I2C2_SCL        PD1      MFP Mask */
#define I2C2_SCL_PA14_Msk       SYS_GPA_MFPH_PA14MFP_Msk       /*<! I2C2_SCL        PA14     MFP Mask */
#define I2C2_SCL_PA1_Msk        SYS_GPA_MFPL_PA1MFP_Msk        /*<! I2C2_SCL        PA1      MFP Mask */
#define I2C2_SDA_PA0_Msk        SYS_GPA_MFPL_PA0MFP_Msk        /*<! I2C2_SDA        PA0      MFP Mask */
#define I2C2_SDA_PB12_Msk       SYS_GPB_MFPH_PB12MFP_Msk       /*<! I2C2_SDA        PB12     MFP Mask */
#define I2C2_SDA_PA10_Msk       SYS_GPA_MFPH_PA10MFP_Msk       /*<! I2C2_SDA        PA10     MFP Mask */
#define I2C2_SDA_PA15_Msk       SYS_GPA_MFPH_PA15MFP_Msk       /*<! I2C2_SDA        PA15     MFP Mask */
#define I2C2_SDA_PH9_Msk        SYS_GPH_MFPH_PH9MFP_Msk        /*<! I2C2_SDA        PH9      MFP Mask */
#define I2C2_SDA_PD8_Msk        SYS_GPD_MFPH_PD8MFP_Msk        /*<! I2C2_SDA        PD8      MFP Mask */
#define I2C2_SDA_PD0_Msk        SYS_GPD_MFPL_PD0MFP_Msk        /*<! I2C2_SDA        PD0      MFP Mask */
#define I2C2_SMBAL_PB15_Msk     SYS_GPB_MFPH_PB15MFP_Msk       /*<! I2C2_SMBAL      PB15     MFP Mask */
#define I2C2_SMBSUS_PB14_Msk    SYS_GPB_MFPH_PB14MFP_Msk       /*<! I2C2_SMBSUS     PB14     MFP Mask */
#define I2S0_BCLK_PA12_Msk      SYS_GPA_MFPH_PA12MFP_Msk       /*<! I2S0_BCLK       PA12     MFP Mask */
#define I2S0_BCLK_PB5_Msk       SYS_GPB_MFPL_PB5MFP_Msk        /*<! I2S0_BCLK       PB5      MFP Mask */
#define I2S0_BCLK_PE8_Msk       SYS_GPE_MFPH_PE8MFP_Msk        /*<! I2S0_BCLK       PE8      MFP Mask */
#define I2S0_BCLK_PE1_Msk       SYS_GPE_MFPL_PE1MFP_Msk        /*<! I2S0_BCLK       PE1      MFP Mask */
#define I2S0_BCLK_PF10_Msk      SYS_GPF_MFPH_PF10MFP_Msk       /*<! I2S0_BCLK       PF10     MFP Mask */
#define I2S0_BCLK_PC4_Msk       SYS_GPC_MFPL_PC4MFP_Msk        /*<! I2S0_BCLK       PC4      MFP Mask */
#define I2S0_DI_PF8_Msk         SYS_GPF_MFPH_PF8MFP_Msk        /*<! I2S0_DI         PF8      MFP Mask */
#define I2S0_DI_PB3_Msk         SYS_GPB_MFPL_PB3MFP_Msk        /*<! I2S0_DI         PB3      MFP Mask */
#define I2S0_DI_PE10_Msk        SYS_GPE_MFPH_PE10MFP_Msk       /*<! I2S0_DI         PE10     MFP Mask */
#define I2S0_DI_PA14_Msk        SYS_GPA_MFPH_PA14MFP_Msk       /*<! I2S0_DI         PA14     MFP Mask */
#define I2S0_DI_PH8_Msk         SYS_GPH_MFPH_PH8MFP_Msk        /*<! I2S0_DI         PH8      MFP Mask */
#define I2S0_DI_PC2_Msk         SYS_GPC_MFPL_PC2MFP_Msk        /*<! I2S0_DI         PC2      MFP Mask */
#define I2S0_DO_PB2_Msk         SYS_GPB_MFPL_PB2MFP_Msk        /*<! I2S0_DO         PB2      MFP Mask */
#define I2S0_DO_PH9_Msk         SYS_GPH_MFPH_PH9MFP_Msk        /*<! I2S0_DO         PH9      MFP Mask */
#define I2S0_DO_PF7_Msk         SYS_GPF_MFPL_PF7MFP_Msk        /*<! I2S0_DO         PF7      MFP Mask */
#define I2S0_DO_PE11_Msk        SYS_GPE_MFPH_PE11MFP_Msk       /*<! I2S0_DO         PE11     MFP Mask */
#define I2S0_DO_PC1_Msk         SYS_GPC_MFPL_PC1MFP_Msk        /*<! I2S0_DO         PC1      MFP Mask */
#define I2S0_DO_PA15_Msk        SYS_GPA_MFPH_PA15MFP_Msk       /*<! I2S0_DO         PA15     MFP Mask */
#define I2S0_LRCK_PF6_Msk       SYS_GPF_MFPL_PF6MFP_Msk        /*<! I2S0_LRCK       PF6      MFP Mask */
#define I2S0_LRCK_PE12_Msk      SYS_GPE_MFPH_PE12MFP_Msk       /*<! I2S0_LRCK       PE12     MFP Mask */
#define I2S0_LRCK_PC0_Msk       SYS_GPC_MFPL_PC0MFP_Msk        /*<! I2S0_LRCK       PC0      MFP Mask */
#define I2S0_LRCK_PH10_Msk      SYS_GPH_MFPH_PH10MFP_Msk       /*<! I2S0_LRCK       PH10     MFP Mask */
#define I2S0_LRCK_PB1_Msk       SYS_GPB_MFPL_PB1MFP_Msk        /*<! I2S0_LRCK       PB1      MFP Mask */
#define I2S0_MCLK_PE9_Msk       SYS_GPE_MFPH_PE9MFP_Msk        /*<! I2S0_MCLK       PE9      MFP Mask */
#define I2S0_MCLK_PB4_Msk       SYS_GPB_MFPL_PB4MFP_Msk        /*<! I2S0_MCLK       PB4      MFP Mask */
#define I2S0_MCLK_PC3_Msk       SYS_GPC_MFPL_PC3MFP_Msk        /*<! I2S0_MCLK       PC3      MFP Mask */
#define I2S0_MCLK_PE0_Msk       SYS_GPE_MFPL_PE0MFP_Msk        /*<! I2S0_MCLK       PE0      MFP Mask */
#define I2S0_MCLK_PA13_Msk      SYS_GPA_MFPH_PA13MFP_Msk       /*<! I2S0_MCLK       PA13     MFP Mask */
#define I2S0_MCLK_PF9_Msk       SYS_GPF_MFPH_PF9MFP_Msk        /*<! I2S0_MCLK       PF9      MFP Mask */
#define ICE_CLK_PF1_Msk         SYS_GPF_MFPL_PF1MFP_Msk        /*<! ICE_CLK         PF1      MFP Mask */
#define ICE_DAT_PF0_Msk         SYS_GPF_MFPL_PF0MFP_Msk        /*<! ICE_DAT         PF0      MFP Mask */
#define INT0_PB5_Msk            SYS_GPB_MFPL_PB5MFP_Msk        /*<! INT0            PB5      MFP Mask */
#define INT0_PA6_Msk            SYS_GPA_MFPL_PA6MFP_Msk        /*<! INT0            PA6      MFP Mask */
#define INT1_PB4_Msk            SYS_GPB_MFPL_PB4MFP_Msk        /*<! INT1            PB4      MFP Mask */
#define INT1_PA7_Msk            SYS_GPA_MFPL_PA7MFP_Msk        /*<! INT1            PA7      MFP Mask */
#define INT2_PB3_Msk            SYS_GPB_MFPL_PB3MFP_Msk        /*<! INT2            PB3      MFP Mask */
#define INT2_PC6_Msk            SYS_GPC_MFPL_PC6MFP_Msk        /*<! INT2            PC6      MFP Mask */
#define INT3_PC7_Msk            SYS_GPC_MFPL_PC7MFP_Msk        /*<! INT3            PC7      MFP Mask */
#define INT3_PB2_Msk            SYS_GPB_MFPL_PB2MFP_Msk        /*<! INT3            PB2      MFP Mask */
#define INT4_PB6_Msk            SYS_GPB_MFPL_PB6MFP_Msk        /*<! INT4            PB6      MFP Mask */
#define INT4_PA8_Msk            SYS_GPA_MFPH_PA8MFP_Msk        /*<! INT4            PA8      MFP Mask */
#define INT5_PB7_Msk            SYS_GPB_MFPL_PB7MFP_Msk        /*<! INT5            PB7      MFP Mask */
#define INT5_PD12_Msk           SYS_GPD_MFPH_PD12MFP_Msk       /*<! INT5            PD12     MFP Mask */
#define INT6_PD11_Msk           SYS_GPD_MFPH_PD11MFP_Msk       /*<! INT6            PD11     MFP Mask */
#define INT6_PB8_Msk            SYS_GPB_MFPH_PB8MFP_Msk        /*<! INT6            PB8      MFP Mask */
#define INT7_PB9_Msk            SYS_GPB_MFPH_PB9MFP_Msk        /*<! INT7            PB9      MFP Mask */
#define INT7_PD10_Msk           SYS_GPD_MFPH_PD10MFP_Msk       /*<! INT7            PD10     MFP Mask */
#define EPWM0_BRAKE0_PE8_Msk    SYS_GPE_MFPH_PE8MFP_Msk        /*<! EPWM0_BRAKE0    PE8      MFP Mask */
#define EPWM0_BRAKE0_PB1_Msk    SYS_GPB_MFPL_PB1MFP_Msk        /*<! EPWM0_BRAKE0    PB1      MFP Mask */
#define EPWM0_BRAKE1_PB0_Msk    SYS_GPB_MFPL_PB0MFP_Msk        /*<! EPWM0_BRAKE1    PB0      MFP Mask */
#define EPWM0_BRAKE1_PE9_Msk    SYS_GPE_MFPH_PE9MFP_Msk        /*<! EPWM0_BRAKE1    PE9      MFP Mask */
#define EPWM0_CH0_PA5_Msk       SYS_GPA_MFPL_PA5MFP_Msk        /*<! EPWM0_CH0       PA5      MFP Mask */
#define EPWM0_CH0_PE7_Msk       SYS_GPE_MFPL_PE7MFP_Msk        /*<! EPWM0_CH0       PE7      MFP Mask */
#define EPWM0_CH0_PE8_Msk       SYS_GPE_MFPH_PE8MFP_Msk        /*<! EPWM0_CH0       PE8      MFP Mask */
#define EPWM0_CH0_PB5_Msk       SYS_GPB_MFPL_PB5MFP_Msk        /*<! EPWM0_CH0       PB5      MFP Mask */
#define EPWM0_CH1_PA4_Msk       SYS_GPA_MFPL_PA4MFP_Msk        /*<! EPWM0_CH1       PA4      MFP Mask */
#define EPWM0_CH1_PB4_Msk       SYS_GPB_MFPL_PB4MFP_Msk        /*<! EPWM0_CH1       PB4      MFP Mask */
#define EPWM0_CH1_PE9_Msk       SYS_GPE_MFPH_PE9MFP_Msk        /*<! EPWM0_CH1       PE9      MFP Mask */
#define EPWM0_CH1_PE6_Msk       SYS_GPE_MFPL_PE6MFP_Msk        /*<! EPWM0_CH1       PE6      MFP Mask */
#define EPWM0_CH2_PE5_Msk       SYS_GPE_MFPL_PE5MFP_Msk        /*<! EPWM0_CH2       PE5      MFP Mask */
#define EPWM0_CH2_PB3_Msk       SYS_GPB_MFPL_PB3MFP_Msk        /*<! EPWM0_CH2       PB3      MFP Mask */
#define EPWM0_CH2_PE10_Msk      SYS_GPE_MFPH_PE10MFP_Msk       /*<! EPWM0_CH2       PE10     MFP Mask */
#define EPWM0_CH2_PA3_Msk       SYS_GPA_MFPL_PA3MFP_Msk        /*<! EPWM0_CH2       PA3      MFP Mask */
#define EPWM0_CH3_PA2_Msk       SYS_GPA_MFPL_PA2MFP_Msk        /*<! EPWM0_CH3       PA2      MFP Mask */
#define EPWM0_CH3_PE11_Msk      SYS_GPE_MFPH_PE11MFP_Msk       /*<! EPWM0_CH3       PE11     MFP Mask */
#define EPWM0_CH3_PE4_Msk       SYS_GPE_MFPL_PE4MFP_Msk        /*<! EPWM0_CH3       PE4      MFP Mask */
#define EPWM0_CH3_PB2_Msk       SYS_GPB_MFPL_PB2MFP_Msk        /*<! EPWM0_CH3       PB2      MFP Mask */
#define EPWM0_CH4_PD14_Msk      SYS_GPD_MFPH_PD14MFP_Msk       /*<! EPWM0_CH4       PD14     MFP Mask */
#define EPWM0_CH4_PB1_Msk       SYS_GPB_MFPL_PB1MFP_Msk        /*<! EPWM0_CH4       PB1      MFP Mask */
#define EPWM0_CH4_PE3_Msk       SYS_GPE_MFPL_PE3MFP_Msk        /*<! EPWM0_CH4       PE3      MFP Mask */
#define EPWM0_CH4_PA1_Msk       SYS_GPA_MFPL_PA1MFP_Msk        /*<! EPWM0_CH4       PA1      MFP Mask */
#define EPWM0_CH4_PE12_Msk      SYS_GPE_MFPH_PE12MFP_Msk       /*<! EPWM0_CH4       PE12     MFP Mask */
#define EPWM0_CH5_PB0_Msk       SYS_GPB_MFPL_PB0MFP_Msk        /*<! EPWM0_CH5       PB0      MFP Mask */
#define EPWM0_CH5_PE2_Msk       SYS_GPE_MFPL_PE2MFP_Msk        /*<! EPWM0_CH5       PE2      MFP Mask */
#define EPWM0_CH5_PA0_Msk       SYS_GPA_MFPL_PA0MFP_Msk        /*<! EPWM0_CH5       PA0      MFP Mask */
#define EPWM0_CH5_PE13_Msk      SYS_GPE_MFPH_PE13MFP_Msk       /*<! EPWM0_CH5       PE13     MFP Mask */
#define EPWM0_CH5_PH11_Msk      SYS_GPH_MFPH_PH11MFP_Msk       /*<! EPWM0_CH5       PH11     MFP Mask */
#define EPWM0_SYNC_IN_PA15_Msk  SYS_GPA_MFPH_PA15MFP_Msk       /*<! EPWM0_SYNC_IN   PA15     MFP Mask */
#define EPWM0_SYNC_OUT_PF5_Msk  SYS_GPF_MFPL_PF5MFP_Msk        /*<! EPWM0_SYNC_OUT  PF5      MFP Mask */
#define EPWM0_SYNC_OUT_PA11_Msk SYS_GPA_MFPH_PA11MFP_Msk       /*<! EPWM0_SYNC_OUT  PA11     MFP Mask */
#define EPWM1_BRAKE0_PB7_Msk    SYS_GPB_MFPL_PB7MFP_Msk        /*<! EPWM1_BRAKE0    PB7      MFP Mask */
#define EPWM1_BRAKE0_PE10_Msk   SYS_GPE_MFPH_PE10MFP_Msk       /*<! EPWM1_BRAKE0    PE10     MFP Mask */
#define EPWM1_BRAKE1_PB6_Msk    SYS_GPB_MFPL_PB6MFP_Msk        /*<! EPWM1_BRAKE1    PB6      MFP Mask */
#define EPWM1_BRAKE1_PE11_Msk   SYS_GPE_MFPH_PE11MFP_Msk       /*<! EPWM1_BRAKE1    PE11     MFP Mask */
#define EPWM1_CH0_PC5_Msk       SYS_GPC_MFPL_PC5MFP_Msk        /*<! EPWM1_CH0       PC5      MFP Mask */
#define EPWM1_CH0_PE13_Msk      SYS_GPE_MFPH_PE13MFP_Msk       /*<! EPWM1_CH0       PE13     MFP Mask */
#define EPWM1_CH0_PC12_Msk      SYS_GPC_MFPH_PC12MFP_Msk       /*<! EPWM1_CH0       PC12     MFP Mask */
#define EPWM1_CH0_PB15_Msk      SYS_GPB_MFPH_PB15MFP_Msk       /*<! EPWM1_CH0       PB15     MFP Mask */
#define EPWM1_CH1_PB14_Msk      SYS_GPB_MFPH_PB14MFP_Msk       /*<! EPWM1_CH1       PB14     MFP Mask */
#define EPWM1_CH1_PC11_Msk      SYS_GPC_MFPH_PC11MFP_Msk       /*<! EPWM1_CH1       PC11     MFP Mask */
#define EPWM1_CH1_PC4_Msk       SYS_GPC_MFPL_PC4MFP_Msk        /*<! EPWM1_CH1       PC4      MFP Mask */
#define EPWM1_CH1_PC8_Msk       SYS_GPC_MFPH_PC8MFP_Msk        /*<! EPWM1_CH1       PC8      MFP Mask */
#define EPWM1_CH2_PC7_Msk       SYS_GPC_MFPL_PC7MFP_Msk        /*<! EPWM1_CH2       PC7      MFP Mask */
#define EPWM1_CH2_PC10_Msk      SYS_GPC_MFPH_PC10MFP_Msk       /*<! EPWM1_CH2       PC10     MFP Mask */
#define EPWM1_CH2_PC3_Msk       SYS_GPC_MFPL_PC3MFP_Msk        /*<! EPWM1_CH2       PC3      MFP Mask */
#define EPWM1_CH2_PB13_Msk      SYS_GPB_MFPH_PB13MFP_Msk       /*<! EPWM1_CH2       PB13     MFP Mask */
#define EPWM1_CH3_PB12_Msk      SYS_GPB_MFPH_PB12MFP_Msk       /*<! EPWM1_CH3       PB12     MFP Mask */
#define EPWM1_CH3_PC6_Msk       SYS_GPC_MFPL_PC6MFP_Msk        /*<! EPWM1_CH3       PC6      MFP Mask */
#define EPWM1_CH3_PC9_Msk       SYS_GPC_MFPH_PC9MFP_Msk        /*<! EPWM1_CH3       PC9      MFP Mask */
#define EPWM1_CH3_PC2_Msk       SYS_GPC_MFPL_PC2MFP_Msk        /*<! EPWM1_CH3       PC2      MFP Mask */
#define EPWM1_CH4_PB7_Msk       SYS_GPB_MFPL_PB7MFP_Msk        /*<! EPWM1_CH4       PB7      MFP Mask */
#define EPWM1_CH4_PB1_Msk       SYS_GPB_MFPL_PB1MFP_Msk        /*<! EPWM1_CH4       PB1      MFP Mask */
#define EPWM1_CH4_PC1_Msk       SYS_GPC_MFPL_PC1MFP_Msk        /*<! EPWM1_CH4       PC1      MFP Mask */
#define EPWM1_CH4_PA7_Msk       SYS_GPA_MFPL_PA7MFP_Msk        /*<! EPWM1_CH4       PA7      MFP Mask */
#define EPWM1_CH5_PA6_Msk       SYS_GPA_MFPL_PA6MFP_Msk        /*<! EPWM1_CH5       PA6      MFP Mask */
#define EPWM1_CH5_PC0_Msk       SYS_GPC_MFPL_PC0MFP_Msk        /*<! EPWM1_CH5       PC0      MFP Mask */
#define EPWM1_CH5_PB6_Msk       SYS_GPB_MFPL_PB6MFP_Msk        /*<! EPWM1_CH5       PB6      MFP Mask */
#define EPWM1_CH5_PB0_Msk       SYS_GPB_MFPL_PB0MFP_Msk        /*<! EPWM1_CH5       PB0      MFP Mask */
#define QEI0_A_PE3_Msk          SYS_GPE_MFPL_PE3MFP_Msk        /*<! QEI0_A          PE3      MFP Mask */
#define QEI0_A_PA4_Msk          SYS_GPA_MFPL_PA4MFP_Msk        /*<! QEI0_A          PA4      MFP Mask */
#define QEI0_A_PD11_Msk         SYS_GPD_MFPH_PD11MFP_Msk       /*<! QEI0_A          PD11     MFP Mask */
#define QEI0_B_PD10_Msk         SYS_GPD_MFPH_PD10MFP_Msk       /*<! QEI0_B          PD10     MFP Mask */
#define QEI0_B_PA3_Msk          SYS_GPA_MFPL_PA3MFP_Msk        /*<! QEI0_B          PA3      MFP Mask */
#define QEI0_B_PE2_Msk          SYS_GPE_MFPL_PE2MFP_Msk        /*<! QEI0_B          PE2      MFP Mask */
#define QEI0_INDEX_PE4_Msk      SYS_GPE_MFPL_PE4MFP_Msk        /*<! QEI0_INDEX      PE4      MFP Mask */
#define QEI0_INDEX_PA5_Msk      SYS_GPA_MFPL_PA5MFP_Msk        /*<! QEI0_INDEX      PA5      MFP Mask */
#define QEI0_INDEX_PD12_Msk     SYS_GPD_MFPH_PD12MFP_Msk       /*<! QEI0_INDEX      PD12     MFP Mask */
#define QEI1_A_PE6_Msk          SYS_GPE_MFPL_PE6MFP_Msk        /*<! QEI1_A          PE6      MFP Mask */
#define QEI1_A_PA13_Msk         SYS_GPA_MFPH_PA13MFP_Msk       /*<! QEI1_A          PA13     MFP Mask */
#define QEI1_A_PA9_Msk          SYS_GPA_MFPH_PA9MFP_Msk        /*<! QEI1_A          PA9      MFP Mask */
#define QEI1_B_PA14_Msk         SYS_GPA_MFPH_PA14MFP_Msk       /*<! QEI1_B          PA14     MFP Mask */
#define QEI1_B_PA8_Msk          SYS_GPA_MFPH_PA8MFP_Msk        /*<! QEI1_B          PA8      MFP Mask */
#define QEI1_B_PE5_Msk          SYS_GPE_MFPL_PE5MFP_Msk        /*<! QEI1_B          PE5      MFP Mask */
#define QEI1_INDEX_PE7_Msk      SYS_GPE_MFPL_PE7MFP_Msk        /*<! QEI1_INDEX      PE7      MFP Mask */
#define QEI1_INDEX_PA10_Msk     SYS_GPA_MFPH_PA10MFP_Msk       /*<! QEI1_INDEX      PA10     MFP Mask */
#define QEI1_INDEX_PA12_Msk     SYS_GPA_MFPH_PA12MFP_Msk       /*<! QEI1_INDEX      PA12     MFP Mask */
#define SC0_CLK_PF6_Msk         SYS_GPF_MFPL_PF6MFP_Msk        /*<! SC0_CLK         PF6      MFP Mask */
#define SC0_CLK_PE2_Msk         SYS_GPE_MFPL_PE2MFP_Msk        /*<! SC0_CLK         PE2      MFP Mask */
#define SC0_CLK_PA0_Msk         SYS_GPA_MFPL_PA0MFP_Msk        /*<! SC0_CLK         PA0      MFP Mask */
#define SC0_CLK_PB5_Msk         SYS_GPB_MFPL_PB5MFP_Msk        /*<! SC0_CLK         PB5      MFP Mask */
#define SC0_DAT_PE3_Msk         SYS_GPE_MFPL_PE3MFP_Msk        /*<! SC0_DAT         PE3      MFP Mask */
#define SC0_DAT_PB4_Msk         SYS_GPB_MFPL_PB4MFP_Msk        /*<! SC0_DAT         PB4      MFP Mask */
#define SC0_DAT_PA1_Msk         SYS_GPA_MFPL_PA1MFP_Msk        /*<! SC0_DAT         PA1      MFP Mask */
#define SC0_DAT_PF7_Msk         SYS_GPF_MFPL_PF7MFP_Msk        /*<! SC0_DAT         PF7      MFP Mask */
#define SC0_PWR_PE5_Msk         SYS_GPE_MFPL_PE5MFP_Msk        /*<! SC0_PWR         PE5      MFP Mask */
#define SC0_PWR_PA3_Msk         SYS_GPA_MFPL_PA3MFP_Msk        /*<! SC0_PWR         PA3      MFP Mask */
#define SC0_PWR_PB2_Msk         SYS_GPB_MFPL_PB2MFP_Msk        /*<! SC0_PWR         PB2      MFP Mask */
#define SC0_PWR_PF9_Msk         SYS_GPF_MFPH_PF9MFP_Msk        /*<! SC0_PWR         PF9      MFP Mask */
#define SC0_RST_PF8_Msk         SYS_GPF_MFPH_PF8MFP_Msk        /*<! SC0_RST         PF8      MFP Mask */
#define SC0_RST_PE4_Msk         SYS_GPE_MFPL_PE4MFP_Msk        /*<! SC0_RST         PE4      MFP Mask */
#define SC0_RST_PA2_Msk         SYS_GPA_MFPL_PA2MFP_Msk        /*<! SC0_RST         PA2      MFP Mask */
#define SC0_RST_PB3_Msk         SYS_GPB_MFPL_PB3MFP_Msk        /*<! SC0_RST         PB3      MFP Mask */
#define SC0_nCD_PE6_Msk         SYS_GPE_MFPL_PE6MFP_Msk        /*<! SC0_nCD         PE6      MFP Mask */
#define SC0_nCD_PF10_Msk        SYS_GPF_MFPH_PF10MFP_Msk       /*<! SC0_nCD         PF10     MFP Mask */
#define SC0_nCD_PA4_Msk         SYS_GPA_MFPL_PA4MFP_Msk        /*<! SC0_nCD         PA4      MFP Mask */
#define SC0_nCD_PC12_Msk        SYS_GPC_MFPH_PC12MFP_Msk       /*<! SC0_nCD         PC12     MFP Mask */
#define SC1_CLK_PC0_Msk         SYS_GPC_MFPL_PC0MFP_Msk        /*<! SC1_CLK         PC0      MFP Mask */
#define SC1_CLK_PB12_Msk        SYS_GPB_MFPH_PB12MFP_Msk       /*<! SC1_CLK         PB12     MFP Mask */
#define SC1_CLK_PD4_Msk         SYS_GPD_MFPL_PD4MFP_Msk        /*<! SC1_CLK         PD4      MFP Mask */
#define SC1_DAT_PD5_Msk         SYS_GPD_MFPL_PD5MFP_Msk        /*<! SC1_DAT         PD5      MFP Mask */
#define SC1_DAT_PB13_Msk        SYS_GPB_MFPH_PB13MFP_Msk       /*<! SC1_DAT         PB13     MFP Mask */
#define SC1_DAT_PC1_Msk         SYS_GPC_MFPL_PC1MFP_Msk        /*<! SC1_DAT         PC1      MFP Mask */
#define SC1_PWR_PB15_Msk        SYS_GPB_MFPH_PB15MFP_Msk       /*<! SC1_PWR         PB15     MFP Mask */
#define SC1_PWR_PC3_Msk         SYS_GPC_MFPL_PC3MFP_Msk        /*<! SC1_PWR         PC3      MFP Mask */
#define SC1_PWR_PD7_Msk         SYS_GPD_MFPL_PD7MFP_Msk        /*<! SC1_PWR         PD7      MFP Mask */
#define SC1_RST_PD6_Msk         SYS_GPD_MFPL_PD6MFP_Msk        /*<! SC1_RST         PD6      MFP Mask */
#define SC1_RST_PB14_Msk        SYS_GPB_MFPH_PB14MFP_Msk       /*<! SC1_RST         PB14     MFP Mask */
#define SC1_RST_PC2_Msk         SYS_GPC_MFPL_PC2MFP_Msk        /*<! SC1_RST         PC2      MFP Mask */
#define SC1_nCD_PD3_Msk         SYS_GPD_MFPL_PD3MFP_Msk        /*<! SC1_nCD         PD3      MFP Mask */
#define SC1_nCD_PC4_Msk         SYS_GPC_MFPL_PC4MFP_Msk        /*<! SC1_nCD         PC4      MFP Mask */
#define SC1_nCD_PD14_Msk        SYS_GPD_MFPH_PD14MFP_Msk       /*<! SC1_nCD         PD14     MFP Mask */
#define SC2_CLK_PD0_Msk         SYS_GPD_MFPL_PD0MFP_Msk        /*<! SC2_CLK         PD0      MFP Mask */
#define SC2_CLK_PA15_Msk        SYS_GPA_MFPH_PA15MFP_Msk       /*<! SC2_CLK         PA15     MFP Mask */
#define SC2_CLK_PE0_Msk         SYS_GPE_MFPL_PE0MFP_Msk        /*<! SC2_CLK         PE0      MFP Mask */
#define SC2_CLK_PA8_Msk         SYS_GPA_MFPH_PA8MFP_Msk        /*<! SC2_CLK         PA8      MFP Mask */
#define SC2_CLK_PA6_Msk         SYS_GPA_MFPL_PA6MFP_Msk        /*<! SC2_CLK         PA6      MFP Mask */
#define SC2_DAT_PE1_Msk         SYS_GPE_MFPL_PE1MFP_Msk        /*<! SC2_DAT         PE1      MFP Mask */
#define SC2_DAT_PD1_Msk         SYS_GPD_MFPL_PD1MFP_Msk        /*<! SC2_DAT         PD1      MFP Mask */
#define SC2_DAT_PA9_Msk         SYS_GPA_MFPH_PA9MFP_Msk        /*<! SC2_DAT         PA9      MFP Mask */
#define SC2_DAT_PA14_Msk        SYS_GPA_MFPH_PA14MFP_Msk       /*<! SC2_DAT         PA14     MFP Mask */
#define SC2_DAT_PA7_Msk         SYS_GPA_MFPL_PA7MFP_Msk        /*<! SC2_DAT         PA7      MFP Mask */
#define SC2_PWR_PD3_Msk         SYS_GPD_MFPL_PD3MFP_Msk        /*<! SC2_PWR         PD3      MFP Mask */
#define SC2_PWR_PA11_Msk        SYS_GPA_MFPH_PA11MFP_Msk       /*<! SC2_PWR         PA11     MFP Mask */
#define SC2_PWR_PA12_Msk        SYS_GPA_MFPH_PA12MFP_Msk       /*<! SC2_PWR         PA12     MFP Mask */
#define SC2_PWR_PH8_Msk         SYS_GPH_MFPH_PH8MFP_Msk        /*<! SC2_PWR         PH8      MFP Mask */
#define SC2_PWR_PC7_Msk         SYS_GPC_MFPL_PC7MFP_Msk        /*<! SC2_PWR         PC7      MFP Mask */
#define SC2_RST_PD2_Msk         SYS_GPD_MFPL_PD2MFP_Msk        /*<! SC2_RST         PD2      MFP Mask */
#define SC2_RST_PC6_Msk         SYS_GPC_MFPL_PC6MFP_Msk        /*<! SC2_RST         PC6      MFP Mask */
#define SC2_RST_PH9_Msk         SYS_GPH_MFPH_PH9MFP_Msk        /*<! SC2_RST         PH9      MFP Mask */
#define SC2_RST_PA10_Msk        SYS_GPA_MFPH_PA10MFP_Msk       /*<! SC2_RST         PA10     MFP Mask */
#define SC2_RST_PA13_Msk        SYS_GPA_MFPH_PA13MFP_Msk       /*<! SC2_RST         PA13     MFP Mask */
#define SC2_nCD_PH10_Msk        SYS_GPH_MFPH_PH10MFP_Msk       /*<! SC2_nCD         PH10     MFP Mask */
#define SC2_nCD_PA5_Msk         SYS_GPA_MFPL_PA5MFP_Msk        /*<! SC2_nCD         PA5      MFP Mask */
#define SC2_nCD_PC13_Msk        SYS_GPC_MFPH_PC13MFP_Msk       /*<! SC2_nCD         PC13     MFP Mask */
#define SC2_nCD_PD13_Msk        SYS_GPD_MFPH_PD13MFP_Msk       /*<! SC2_nCD         PD13     MFP Mask */
#define SD0_CLK_PE6_Msk         SYS_GPE_MFPL_PE6MFP_Msk        /*<! SD0_CLK         PE6      MFP Mask */
#define SD0_CLK_PB1_Msk         SYS_GPB_MFPL_PB1MFP_Msk        /*<! SD0_CLK         PB1      MFP Mask */
#define SD0_CMD_PB0_Msk         SYS_GPB_MFPL_PB0MFP_Msk        /*<! SD0_CMD         PB0      MFP Mask */
#define SD0_CMD_PE7_Msk         SYS_GPE_MFPL_PE7MFP_Msk        /*<! SD0_CMD         PE7      MFP Mask */
#define SD0_DAT0_PB2_Msk        SYS_GPB_MFPL_PB2MFP_Msk        /*<! SD0_DAT0        PB2      MFP Mask */
#define SD0_DAT0_PE2_Msk        SYS_GPE_MFPL_PE2MFP_Msk        /*<! SD0_DAT0        PE2      MFP Mask */
#define SD0_DAT1_PE3_Msk        SYS_GPE_MFPL_PE3MFP_Msk        /*<! SD0_DAT1        PE3      MFP Mask */
#define SD0_DAT1_PB3_Msk        SYS_GPB_MFPL_PB3MFP_Msk        /*<! SD0_DAT1        PB3      MFP Mask */
#define SD0_DAT2_PB4_Msk        SYS_GPB_MFPL_PB4MFP_Msk        /*<! SD0_DAT2        PB4      MFP Mask */
#define SD0_DAT2_PE4_Msk        SYS_GPE_MFPL_PE4MFP_Msk        /*<! SD0_DAT2        PE4      MFP Mask */
#define SD0_DAT3_PE5_Msk        SYS_GPE_MFPL_PE5MFP_Msk        /*<! SD0_DAT3        PE5      MFP Mask */
#define SD0_DAT3_PB5_Msk        SYS_GPB_MFPL_PB5MFP_Msk        /*<! SD0_DAT3        PB5      MFP Mask */
#define SD0_nCD_PB12_Msk        SYS_GPB_MFPH_PB12MFP_Msk       /*<! SD0_nCD         PB12     MFP Mask */
#define SD0_nCD_PD13_Msk        SYS_GPD_MFPH_PD13MFP_Msk       /*<! SD0_nCD         PD13     MFP Mask */
#define QSPI0_CLK_PF2_Msk       SYS_GPF_MFPL_PF2MFP_Msk        /*<! QSPI0_CLK       PF2      MFP Mask */
#define QSPI0_CLK_PH8_Msk       SYS_GPH_MFPH_PH8MFP_Msk        /*<! QSPI0_CLK       PH8      MFP Mask */
#define QSPI0_CLK_PA2_Msk       SYS_GPA_MFPL_PA2MFP_Msk        /*<! QSPI0_CLK       PA2      MFP Mask */
#define QSPI0_CLK_PC2_Msk       SYS_GPC_MFPL_PC2MFP_Msk        /*<! QSPI0_CLK       PC2      MFP Mask */
#define QSPI0_MISO0_PC1_Msk     SYS_GPC_MFPL_PC1MFP_Msk        /*<! QSPI0_MISO0     PC1      MFP Mask */
#define QSPI0_MISO0_PE1_Msk     SYS_GPE_MFPL_PE1MFP_Msk        /*<! QSPI0_MISO0     PE1      MFP Mask */
#define QSPI0_MISO0_PA1_Msk     SYS_GPA_MFPL_PA1MFP_Msk        /*<! QSPI0_MISO0     PA1      MFP Mask */
#define QSPI0_MISO1_PC5_Msk     SYS_GPC_MFPL_PC5MFP_Msk        /*<! QSPI0_MISO1     PC5      MFP Mask */
#define QSPI0_MISO1_PH10_Msk    SYS_GPH_MFPH_PH10MFP_Msk       /*<! QSPI0_MISO1     PH10     MFP Mask */
#define QSPI0_MISO1_PA5_Msk     SYS_GPA_MFPL_PA5MFP_Msk        /*<! QSPI0_MISO1     PA5      MFP Mask */
#define QSPI0_MOSI0_PC0_Msk     SYS_GPC_MFPL_PC0MFP_Msk        /*<! QSPI0_MOSI0     PC0      MFP Mask */
#define QSPI0_MOSI0_PE0_Msk     SYS_GPE_MFPL_PE0MFP_Msk        /*<! QSPI0_MOSI0     PE0      MFP Mask */
#define QSPI0_MOSI0_PA0_Msk     SYS_GPA_MFPL_PA0MFP_Msk        /*<! QSPI0_MOSI0     PA0      MFP Mask */
#define QSPI0_MOSI1_PA4_Msk     SYS_GPA_MFPL_PA4MFP_Msk        /*<! QSPI0_MOSI1     PA4      MFP Mask */
#define QSPI0_MOSI1_PH11_Msk    SYS_GPH_MFPH_PH11MFP_Msk       /*<! QSPI0_MOSI1     PH11     MFP Mask */
#define QSPI0_MOSI1_PC4_Msk     SYS_GPC_MFPL_PC4MFP_Msk        /*<! QSPI0_MOSI1     PC4      MFP Mask */
#define QSPI0_SS_PH9_Msk        SYS_GPH_MFPH_PH9MFP_Msk        /*<! QSPI0_SS        PH9      MFP Mask */
#define QSPI0_SS_PA3_Msk        SYS_GPA_MFPL_PA3MFP_Msk        /*<! QSPI0_SS        PA3      MFP Mask */
#define QSPI0_SS_PC3_Msk        SYS_GPC_MFPL_PC3MFP_Msk        /*<! QSPI0_SS        PC3      MFP Mask */
#define SPI0_CLK_PD2_Msk        SYS_GPD_MFPL_PD2MFP_Msk        /*<! SPI0_CLK        PD2      MFP Mask */
#define SPI0_CLK_PF8_Msk        SYS_GPF_MFPH_PF8MFP_Msk        /*<! SPI0_CLK        PF8      MFP Mask */
#define SPI0_CLK_PA2_Msk        SYS_GPA_MFPL_PA2MFP_Msk        /*<! SPI0_CLK        PA2      MFP Mask */
#define SPI0_CLK_PB14_Msk       SYS_GPB_MFPH_PB14MFP_Msk       /*<! SPI0_CLK        PB14     MFP Mask */
#define SPI0_I2SMCLK_PD13_Msk   SYS_GPD_MFPH_PD13MFP_Msk       /*<! SPI0_I2SMCLK    PD13     MFP Mask */
#define SPI0_I2SMCLK_PA4_Msk    SYS_GPA_MFPL_PA4MFP_Msk        /*<! SPI0_I2SMCLK    PA4      MFP Mask */
#define SPI0_I2SMCLK_PB11_Msk   SYS_GPB_MFPH_PB11MFP_Msk       /*<! SPI0_I2SMCLK    PB11     MFP Mask */
#define SPI0_I2SMCLK_PB0_Msk    SYS_GPB_MFPL_PB0MFP_Msk        /*<! SPI0_I2SMCLK    PB0      MFP Mask */
#define SPI0_I2SMCLK_PD14_Msk   SYS_GPD_MFPH_PD14MFP_Msk       /*<! SPI0_I2SMCLK    PD14     MFP Mask */
#define SPI0_I2SMCLK_PF10_Msk   SYS_GPF_MFPH_PF10MFP_Msk       /*<! SPI0_I2SMCLK    PF10     MFP Mask */
#define SPI0_MISO_PF7_Msk       SYS_GPF_MFPL_PF7MFP_Msk        /*<! SPI0_MISO       PF7      MFP Mask */
#define SPI0_MISO_PB13_Msk      SYS_GPB_MFPH_PB13MFP_Msk       /*<! SPI0_MISO       PB13     MFP Mask */
#define SPI0_MISO_PA1_Msk       SYS_GPA_MFPL_PA1MFP_Msk        /*<! SPI0_MISO       PA1      MFP Mask */
#define SPI0_MISO_PD1_Msk       SYS_GPD_MFPL_PD1MFP_Msk        /*<! SPI0_MISO       PD1      MFP Mask */
#define SPI0_MOSI_PA0_Msk       SYS_GPA_MFPL_PA0MFP_Msk        /*<! SPI0_MOSI       PA0      MFP Mask */
#define SPI0_MOSI_PB12_Msk      SYS_GPB_MFPH_PB12MFP_Msk       /*<! SPI0_MOSI       PB12     MFP Mask */
#define SPI0_MOSI_PD0_Msk       SYS_GPD_MFPL_PD0MFP_Msk        /*<! SPI0_MOSI       PD0      MFP Mask */
#define SPI0_MOSI_PF6_Msk       SYS_GPF_MFPL_PF6MFP_Msk        /*<! SPI0_MOSI       PF6      MFP Mask */
#define SPI0_SS_PB15_Msk        SYS_GPB_MFPH_PB15MFP_Msk       /*<! SPI0_SS         PB15     MFP Mask */
#define SPI0_SS_PA3_Msk         SYS_GPA_MFPL_PA3MFP_Msk        /*<! SPI0_SS         PA3      MFP Mask */
#define SPI0_SS_PD3_Msk         SYS_GPD_MFPL_PD3MFP_Msk        /*<! SPI0_SS         PD3      MFP Mask */
#define SPI0_SS_PF9_Msk         SYS_GPF_MFPH_PF9MFP_Msk        /*<! SPI0_SS         PF9      MFP Mask */
#define SPI1_CLK_PB3_Msk        SYS_GPB_MFPL_PB3MFP_Msk        /*<! SPI1_CLK        PB3      MFP Mask */
#define SPI1_CLK_PH6_Msk        SYS_GPH_MFPL_PH6MFP_Msk        /*<! SPI1_CLK        PH6      MFP Mask */
#define SPI1_CLK_PH8_Msk        SYS_GPH_MFPH_PH8MFP_Msk        /*<! SPI1_CLK        PH8      MFP Mask */
#define SPI1_CLK_PC1_Msk        SYS_GPC_MFPL_PC1MFP_Msk        /*<! SPI1_CLK        PC1      MFP Mask */
#define SPI1_CLK_PD5_Msk        SYS_GPD_MFPL_PD5MFP_Msk        /*<! SPI1_CLK        PD5      MFP Mask */
#define SPI1_CLK_PA7_Msk        SYS_GPA_MFPL_PA7MFP_Msk        /*<! SPI1_CLK        PA7      MFP Mask */
#define SPI1_I2SMCLK_PB1_Msk    SYS_GPB_MFPL_PB1MFP_Msk        /*<! SPI1_I2SMCLK    PB1      MFP Mask */
#define SPI1_I2SMCLK_PH10_Msk   SYS_GPH_MFPH_PH10MFP_Msk       /*<! SPI1_I2SMCLK    PH10     MFP Mask */
#define SPI1_I2SMCLK_PC4_Msk    SYS_GPC_MFPL_PC4MFP_Msk        /*<! SPI1_I2SMCLK    PC4      MFP Mask */
#define SPI1_I2SMCLK_PD13_Msk   SYS_GPD_MFPH_PD13MFP_Msk       /*<! SPI1_I2SMCLK    PD13     MFP Mask */
#define SPI1_I2SMCLK_PA5_Msk    SYS_GPA_MFPL_PA5MFP_Msk        /*<! SPI1_I2SMCLK    PA5      MFP Mask */
#define SPI1_MISO_PD7_Msk       SYS_GPD_MFPL_PD7MFP_Msk        /*<! SPI1_MISO       PD7      MFP Mask */
#define SPI1_MISO_PC7_Msk       SYS_GPC_MFPL_PC7MFP_Msk        /*<! SPI1_MISO       PC7      MFP Mask */
#define SPI1_MISO_PB5_Msk       SYS_GPB_MFPL_PB5MFP_Msk        /*<! SPI1_MISO       PB5      MFP Mask */
#define SPI1_MISO_PE1_Msk       SYS_GPE_MFPL_PE1MFP_Msk        /*<! SPI1_MISO       PE1      MFP Mask */
#define SPI1_MISO_PH4_Msk       SYS_GPH_MFPL_PH4MFP_Msk        /*<! SPI1_MISO       PH4      MFP Mask */
#define SPI1_MISO_PC3_Msk       SYS_GPC_MFPL_PC3MFP_Msk        /*<! SPI1_MISO       PC3      MFP Mask */
#define SPI1_MOSI_PD6_Msk       SYS_GPD_MFPL_PD6MFP_Msk        /*<! SPI1_MOSI       PD6      MFP Mask */
#define SPI1_MOSI_PE0_Msk       SYS_GPE_MFPL_PE0MFP_Msk        /*<! SPI1_MOSI       PE0      MFP Mask */
#define SPI1_MOSI_PB4_Msk       SYS_GPB_MFPL_PB4MFP_Msk        /*<! SPI1_MOSI       PB4      MFP Mask */
#define SPI1_MOSI_PC6_Msk       SYS_GPC_MFPL_PC6MFP_Msk        /*<! SPI1_MOSI       PC6      MFP Mask */
#define SPI1_MOSI_PC2_Msk       SYS_GPC_MFPL_PC2MFP_Msk        /*<! SPI1_MOSI       PC2      MFP Mask */
#define SPI1_MOSI_PH5_Msk       SYS_GPH_MFPL_PH5MFP_Msk        /*<! SPI1_MOSI       PH5      MFP Mask */
#define SPI1_SS_PB2_Msk         SYS_GPB_MFPL_PB2MFP_Msk        /*<! SPI1_SS         PB2      MFP Mask */
#define SPI1_SS_PH9_Msk         SYS_GPH_MFPH_PH9MFP_Msk        /*<! SPI1_SS         PH9      MFP Mask */
#define SPI1_SS_PD4_Msk         SYS_GPD_MFPL_PD4MFP_Msk        /*<! SPI1_SS         PD4      MFP Mask */
#define SPI1_SS_PC0_Msk         SYS_GPC_MFPL_PC0MFP_Msk        /*<! SPI1_SS         PC0      MFP Mask */
#define SPI1_SS_PA6_Msk         SYS_GPA_MFPL_PA6MFP_Msk        /*<! SPI1_SS         PA6      MFP Mask */
#define SPI1_SS_PH7_Msk         SYS_GPH_MFPL_PH7MFP_Msk        /*<! SPI1_SS         PH7      MFP Mask */
#define SPI2_CLK_PE8_Msk        SYS_GPE_MFPH_PE8MFP_Msk        /*<! SPI2_CLK        PE8      MFP Mask */
#define SPI2_CLK_PG3_Msk        SYS_GPG_MFPL_PG3MFP_Msk        /*<! SPI2_CLK        PG3      MFP Mask */
#define SPI2_CLK_PA10_Msk       SYS_GPA_MFPH_PA10MFP_Msk       /*<! SPI2_CLK        PA10     MFP Mask */
#define SPI2_CLK_PA13_Msk       SYS_GPA_MFPH_PA13MFP_Msk       /*<! SPI2_CLK        PA13     MFP Mask */
#define SPI2_I2SMCLK_PC13_Msk   SYS_GPC_MFPH_PC13MFP_Msk       /*<! SPI2_I2SMCLK    PC13     MFP Mask */
#define SPI2_I2SMCLK_PE12_Msk   SYS_GPE_MFPH_PE12MFP_Msk       /*<! SPI2_I2SMCLK    PE12     MFP Mask */
#define SPI2_MISO_PG4_Msk       SYS_GPG_MFPL_PG4MFP_Msk        /*<! SPI2_MISO       PG4      MFP Mask */
#define SPI2_MISO_PA9_Msk       SYS_GPA_MFPH_PA9MFP_Msk        /*<! SPI2_MISO       PA9      MFP Mask */
#define SPI2_MISO_PA14_Msk      SYS_GPA_MFPH_PA14MFP_Msk       /*<! SPI2_MISO       PA14     MFP Mask */
#define SPI2_MISO_PE9_Msk       SYS_GPE_MFPH_PE9MFP_Msk        /*<! SPI2_MISO       PE9      MFP Mask */
#define SPI2_MOSI_PE10_Msk      SYS_GPE_MFPH_PE10MFP_Msk       /*<! SPI2_MOSI       PE10     MFP Mask */
#define SPI2_MOSI_PA15_Msk      SYS_GPA_MFPH_PA15MFP_Msk       /*<! SPI2_MOSI       PA15     MFP Mask */
#define SPI2_MOSI_PA8_Msk       SYS_GPA_MFPH_PA8MFP_Msk        /*<! SPI2_MOSI       PA8      MFP Mask */
#define SPI2_MOSI_PF11_Msk      SYS_GPF_MFPH_PF11MFP_Msk       /*<! SPI2_MOSI       PF11     MFP Mask */
#define SPI2_SS_PG2_Msk         SYS_GPG_MFPL_PG2MFP_Msk        /*<! SPI2_SS         PG2      MFP Mask */
#define SPI2_SS_PE11_Msk        SYS_GPE_MFPH_PE11MFP_Msk       /*<! SPI2_SS         PE11     MFP Mask */
#define SPI2_SS_PA11_Msk        SYS_GPA_MFPH_PA11MFP_Msk       /*<! SPI2_SS         PA11     MFP Mask */
#define SPI2_SS_PA12_Msk        SYS_GPA_MFPH_PA12MFP_Msk       /*<! SPI2_SS         PA12     MFP Mask */
#define SPI3_CLK_PB11_Msk       SYS_GPB_MFPH_PB11MFP_Msk       /*<! SPI3_CLK        PB11     MFP Mask */
#define SPI3_CLK_PE4_Msk        SYS_GPE_MFPL_PE4MFP_Msk        /*<! SPI3_CLK        PE4      MFP Mask */
#define SPI3_CLK_PC10_Msk       SYS_GPC_MFPH_PC10MFP_Msk       /*<! SPI3_CLK        PC10     MFP Mask */
#define SPI3_I2SMCLK_PE6_Msk    SYS_GPE_MFPL_PE6MFP_Msk        /*<! SPI3_I2SMCLK    PE6      MFP Mask */
#define SPI3_I2SMCLK_PB1_Msk    SYS_GPB_MFPL_PB1MFP_Msk        /*<! SPI3_I2SMCLK    PB1      MFP Mask */
#define SPI3_I2SMCLK_PD14_Msk   SYS_GPD_MFPH_PD14MFP_Msk       /*<! SPI3_I2SMCLK    PD14     MFP Mask */
#define SPI3_MISO_PC12_Msk      SYS_GPC_MFPH_PC12MFP_Msk       /*<! SPI3_MISO       PC12     MFP Mask */
#define SPI3_MISO_PB9_Msk       SYS_GPB_MFPH_PB9MFP_Msk        /*<! SPI3_MISO       PB9      MFP Mask */
#define SPI3_MISO_PE3_Msk       SYS_GPE_MFPL_PE3MFP_Msk        /*<! SPI3_MISO       PE3      MFP Mask */
#define SPI3_MOSI_PB8_Msk       SYS_GPB_MFPH_PB8MFP_Msk        /*<! SPI3_MOSI       PB8      MFP Mask */
#define SPI3_MOSI_PE2_Msk       SYS_GPE_MFPL_PE2MFP_Msk        /*<! SPI3_MOSI       PE2      MFP Mask */
#define SPI3_MOSI_PC11_Msk      SYS_GPC_MFPH_PC11MFP_Msk       /*<! SPI3_MOSI       PC11     MFP Mask */
#define SPI3_SS_PE5_Msk         SYS_GPE_MFPL_PE5MFP_Msk        /*<! SPI3_SS         PE5      MFP Mask */
#define SPI3_SS_PB10_Msk        SYS_GPB_MFPH_PB10MFP_Msk       /*<! SPI3_SS         PB10     MFP Mask */
#define SPI3_SS_PC9_Msk         SYS_GPC_MFPH_PC9MFP_Msk        /*<! SPI3_SS         PC9      MFP Mask */
#define TAMPER0_PF6_Msk         SYS_GPF_MFPL_PF6MFP_Msk        /*<! TAMPER0         PF6      MFP Mask */
#define TAMPER1_PF7_Msk         SYS_GPF_MFPL_PF7MFP_Msk        /*<! TAMPER1         PF7      MFP Mask */
#define TAMPER2_PF8_Msk         SYS_GPF_MFPH_PF8MFP_Msk        /*<! TAMPER2         PF8      MFP Mask */
#define TAMPER3_PF9_Msk         SYS_GPF_MFPH_PF9MFP_Msk        /*<! TAMPER3         PF9      MFP Mask */
#define TAMPER4_PF10_Msk        SYS_GPF_MFPH_PF10MFP_Msk       /*<! TAMPER4         PF10     MFP Mask */
#define TAMPER5_PF11_Msk        SYS_GPF_MFPH_PF11MFP_Msk       /*<! TAMPER5         PF11     MFP Mask */
#define TM0_PC7_Msk             SYS_GPC_MFPL_PC7MFP_Msk        /*<! TM0             PC7      MFP Mask */
#define TM0_PB5_Msk             SYS_GPB_MFPL_PB5MFP_Msk        /*<! TM0             PB5      MFP Mask */
#define TM0_PG2_Msk             SYS_GPG_MFPL_PG2MFP_Msk        /*<! TM0             PG2      MFP Mask */
#define TM0_EXT_PA11_Msk        SYS_GPA_MFPH_PA11MFP_Msk       /*<! TM0_EXT         PA11     MFP Mask */
#define TM0_EXT_PB15_Msk        SYS_GPB_MFPH_PB15MFP_Msk       /*<! TM0_EXT         PB15     MFP Mask */
#define TM1_PG3_Msk             SYS_GPG_MFPL_PG3MFP_Msk        /*<! TM1             PG3      MFP Mask */
#define TM1_PB4_Msk             SYS_GPB_MFPL_PB4MFP_Msk        /*<! TM1             PB4      MFP Mask */
#define TM1_PC6_Msk             SYS_GPC_MFPL_PC6MFP_Msk        /*<! TM1             PC6      MFP Mask */
#define TM1_EXT_PA10_Msk        SYS_GPA_MFPH_PA10MFP_Msk       /*<! TM1_EXT         PA10     MFP Mask */
#define TM1_EXT_PB14_Msk        SYS_GPB_MFPH_PB14MFP_Msk       /*<! TM1_EXT         PB14     MFP Mask */
#define TM2_PG4_Msk             SYS_GPG_MFPL_PG4MFP_Msk        /*<! TM2             PG4      MFP Mask */
#define TM2_PD0_Msk             SYS_GPD_MFPL_PD0MFP_Msk        /*<! TM2             PD0      MFP Mask */
#define TM2_PB3_Msk             SYS_GPB_MFPL_PB3MFP_Msk        /*<! TM2             PB3      MFP Mask */
#define TM2_PA7_Msk             SYS_GPA_MFPL_PA7MFP_Msk        /*<! TM2             PA7      MFP Mask */
#define TM2_EXT_PB13_Msk        SYS_GPB_MFPH_PB13MFP_Msk       /*<! TM2_EXT         PB13     MFP Mask */
#define TM2_EXT_PA9_Msk         SYS_GPA_MFPH_PA9MFP_Msk        /*<! TM2_EXT         PA9      MFP Mask */
#define TM3_PA6_Msk             SYS_GPA_MFPL_PA6MFP_Msk        /*<! TM3             PA6      MFP Mask */
#define TM3_PF11_Msk            SYS_GPF_MFPH_PF11MFP_Msk       /*<! TM3             PF11     MFP Mask */
#define TM3_PB2_Msk             SYS_GPB_MFPL_PB2MFP_Msk        /*<! TM3             PB2      MFP Mask */
#define TM3_EXT_PA8_Msk         SYS_GPA_MFPH_PA8MFP_Msk        /*<! TM3_EXT         PA8      MFP Mask */
#define TM3_EXT_PB12_Msk        SYS_GPB_MFPH_PB12MFP_Msk       /*<! TM3_EXT         PB12     MFP Mask */
#define TRACE_CLK_PE12_Msk      SYS_GPE_MFPH_PE8MFP_Msk        /*<! TRACE_CLK       PE12     MFP Mask */
#define TRACE_DATA0_PE11_Msk    SYS_GPE_MFPH_PE9MFP_Msk        /*<! TRACE_DATA0     PE11     MFP Mask */
#define TRACE_DATA1_PE10_Msk    SYS_GPE_MFPH_PE10MFP_Msk       /*<! TRACE_DATA1     PE10     MFP Mask */
#define TRACE_DATA2_PE9_Msk     SYS_GPE_MFPH_PE11MFP_Msk       /*<! TRACE_DATA2     PE9      MFP Mask */
#define TRACE_DATA3_PE8_Msk     SYS_GPE_MFPH_PE12MFP_Msk       /*<! TRACE_DATA3     PE8      MFP Mask */
#define UART0_RXD_PD2_Msk       SYS_GPD_MFPL_PD2MFP_Msk        /*<! UART0_RXD       PD2      MFP Mask */
#define UART0_RXD_PB8_Msk       SYS_GPB_MFPH_PB8MFP_Msk        /*<! UART0_RXD       PB8      MFP Mask */
#define UART0_RXD_PA0_Msk       SYS_GPA_MFPL_PA0MFP_Msk        /*<! UART0_RXD       PA0      MFP Mask */
#define UART0_RXD_PA6_Msk       SYS_GPA_MFPL_PA6MFP_Msk        /*<! UART0_RXD       PA6      MFP Mask */
#define UART0_RXD_PB12_Msk      SYS_GPB_MFPH_PB12MFP_Msk       /*<! UART0_RXD       PB12     MFP Mask */
#define UART0_RXD_PA15_Msk      SYS_GPA_MFPH_PA15MFP_Msk       /*<! UART0_RXD       PA15     MFP Mask */
#define UART0_RXD_PC11_Msk      SYS_GPC_MFPH_PC11MFP_Msk       /*<! UART0_RXD       PC11     MFP Mask */
#define UART0_RXD_PH11_Msk      SYS_GPH_MFPH_PH11MFP_Msk       /*<! UART0_RXD       PH11     MFP Mask */
#define UART0_RXD_PF2_Msk       SYS_GPF_MFPL_PF2MFP_Msk        /*<! UART0_RXD       PF2      MFP Mask */
#define UART0_TXD_PA7_Msk       SYS_GPA_MFPL_PA7MFP_Msk        /*<! UART0_TXD       PA7      MFP Mask */
#define UART0_TXD_PD3_Msk       SYS_GPD_MFPL_PD3MFP_Msk        /*<! UART0_TXD       PD3      MFP Mask */
#define UART0_TXD_PF3_Msk       SYS_GPF_MFPL_PF3MFP_Msk        /*<! UART0_TXD       PF3      MFP Mask */
#define UART0_TXD_PC12_Msk      SYS_GPC_MFPH_PC12MFP_Msk       /*<! UART0_TXD       PC12     MFP Mask */
#define UART0_TXD_PH10_Msk      SYS_GPH_MFPH_PH10MFP_Msk       /*<! UART0_TXD       PH10     MFP Mask */
#define UART0_TXD_PA1_Msk       SYS_GPA_MFPL_PA1MFP_Msk        /*<! UART0_TXD       PA1      MFP Mask */
#define UART0_TXD_PB9_Msk       SYS_GPB_MFPH_PB9MFP_Msk        /*<! UART0_TXD       PB9      MFP Mask */
#define UART0_TXD_PB13_Msk      SYS_GPB_MFPH_PB13MFP_Msk       /*<! UART0_TXD       PB13     MFP Mask */
#define UART0_TXD_PA14_Msk      SYS_GPA_MFPH_PA14MFP_Msk       /*<! UART0_TXD       PA14     MFP Mask */
#define UART0_nCTS_PA5_Msk      SYS_GPA_MFPL_PA5MFP_Msk        /*<! UART0_nCTS      PA5      MFP Mask */
#define UART0_nCTS_PB11_Msk     SYS_GPB_MFPH_PB11MFP_Msk       /*<! UART0_nCTS      PB11     MFP Mask */
#define UART0_nCTS_PB15_Msk     SYS_GPB_MFPH_PB15MFP_Msk       /*<! UART0_nCTS      PB15     MFP Mask */
#define UART0_nCTS_PC7_Msk      SYS_GPC_MFPL_PC7MFP_Msk        /*<! UART0_nCTS      PC7      MFP Mask */
#define UART0_nRTS_PB14_Msk     SYS_GPB_MFPH_PB14MFP_Msk       /*<! UART0_nRTS      PB14     MFP Mask */
#define UART0_nRTS_PB10_Msk     SYS_GPB_MFPH_PB10MFP_Msk       /*<! UART0_nRTS      PB10     MFP Mask */
#define UART0_nRTS_PC6_Msk      SYS_GPC_MFPL_PC6MFP_Msk        /*<! UART0_nRTS      PC6      MFP Mask */
#define UART0_nRTS_PA4_Msk      SYS_GPA_MFPL_PA4MFP_Msk        /*<! UART0_nRTS      PA4      MFP Mask */
#define UART1_RXD_PF1_Msk       SYS_GPF_MFPL_PF1MFP_Msk        /*<! UART1_RXD       PF1      MFP Mask */
#define UART1_RXD_PA8_Msk       SYS_GPA_MFPH_PA8MFP_Msk        /*<! UART1_RXD       PA8      MFP Mask */
#define UART1_RXD_PA2_Msk       SYS_GPA_MFPL_PA2MFP_Msk        /*<! UART1_RXD       PA2      MFP Mask */
#define UART1_RXD_PB2_Msk       SYS_GPB_MFPL_PB2MFP_Msk        /*<! UART1_RXD       PB2      MFP Mask */
#define UART1_RXD_PB6_Msk       SYS_GPB_MFPL_PB6MFP_Msk        /*<! UART1_RXD       PB6      MFP Mask */
#define UART1_RXD_PD6_Msk       SYS_GPD_MFPL_PD6MFP_Msk        /*<! UART1_RXD       PD6      MFP Mask */
#define UART1_RXD_PD10_Msk      SYS_GPD_MFPH_PD10MFP_Msk       /*<! UART1_RXD       PD10     MFP Mask */
#define UART1_RXD_PH9_Msk       SYS_GPH_MFPH_PH9MFP_Msk        /*<! UART1_RXD       PH9      MFP Mask */
#define UART1_RXD_PC8_Msk       SYS_GPC_MFPH_PC8MFP_Msk        /*<! UART1_RXD       PC8      MFP Mask */
#define UART1_TXD_PB3_Msk       SYS_GPB_MFPL_PB3MFP_Msk        /*<! UART1_TXD       PB3      MFP Mask */
#define UART1_TXD_PA3_Msk       SYS_GPA_MFPL_PA3MFP_Msk        /*<! UART1_TXD       PA3      MFP Mask */
#define UART1_TXD_PE13_Msk      SYS_GPE_MFPH_PE13MFP_Msk       /*<! UART1_TXD       PE13     MFP Mask */
#define UART1_TXD_PA9_Msk       SYS_GPA_MFPH_PA9MFP_Msk        /*<! UART1_TXD       PA9      MFP Mask */
#define UART1_TXD_PF0_Msk       SYS_GPF_MFPL_PF0MFP_Msk        /*<! UART1_TXD       PF0      MFP Mask */
#define UART1_TXD_PD11_Msk      SYS_GPD_MFPH_PD11MFP_Msk       /*<! UART1_TXD       PD11     MFP Mask */
#define UART1_TXD_PD7_Msk       SYS_GPD_MFPL_PD7MFP_Msk        /*<! UART1_TXD       PD7      MFP Mask */
#define UART1_TXD_PB7_Msk       SYS_GPB_MFPL_PB7MFP_Msk        /*<! UART1_TXD       PB7      MFP Mask */
#define UART1_TXD_PH8_Msk       SYS_GPH_MFPH_PH8MFP_Msk        /*<! UART1_TXD       PH8      MFP Mask */
#define UART1_nCTS_PE11_Msk     SYS_GPE_MFPH_PE11MFP_Msk       /*<! UART1_nCTS      PE11     MFP Mask */
#define UART1_nCTS_PB9_Msk      SYS_GPB_MFPH_PB9MFP_Msk        /*<! UART1_nCTS      PB9      MFP Mask */
#define UART1_nCTS_PA1_Msk      SYS_GPA_MFPL_PA1MFP_Msk        /*<! UART1_nCTS      PA1      MFP Mask */
#define UART1_nRTS_PA0_Msk      SYS_GPA_MFPL_PA0MFP_Msk        /*<! UART1_nRTS      PA0      MFP Mask */
#define UART1_nRTS_PE12_Msk     SYS_GPE_MFPH_PE12MFP_Msk       /*<! UART1_nRTS      PE12     MFP Mask */
#define UART1_nRTS_PB8_Msk      SYS_GPB_MFPH_PB8MFP_Msk        /*<! UART1_nRTS      PB8      MFP Mask */
#define UART2_RXD_PB0_Msk       SYS_GPB_MFPL_PB0MFP_Msk        /*<! UART2_RXD       PB0      MFP Mask */
#define UART2_RXD_PE15_Msk      SYS_GPE_MFPH_PE15MFP_Msk       /*<! UART2_RXD       PE15     MFP Mask */
#define UART2_RXD_PD12_Msk      SYS_GPD_MFPH_PD12MFP_Msk       /*<! UART2_RXD       PD12     MFP Mask */
#define UART2_RXD_PF5_Msk       SYS_GPF_MFPL_PF5MFP_Msk        /*<! UART2_RXD       PF5      MFP Mask */
#define UART2_RXD_PC0_Msk       SYS_GPC_MFPL_PC0MFP_Msk        /*<! UART2_RXD       PC0      MFP Mask */
#define UART2_RXD_PC4_Msk       SYS_GPC_MFPL_PC4MFP_Msk        /*<! UART2_RXD       PC4      MFP Mask */
#define UART2_RXD_PE9_Msk       SYS_GPE_MFPH_PE9MFP_Msk        /*<! UART2_RXD       PE9      MFP Mask */
#define UART2_TXD_PE8_Msk       SYS_GPE_MFPH_PE8MFP_Msk        /*<! UART2_TXD       PE8      MFP Mask */
#define UART2_TXD_PF4_Msk       SYS_GPF_MFPL_PF4MFP_Msk        /*<! UART2_TXD       PF4      MFP Mask */
#define UART2_TXD_PC13_Msk      SYS_GPC_MFPH_PC13MFP_Msk       /*<! UART2_TXD       PC13     MFP Mask */
#define UART2_TXD_PC1_Msk       SYS_GPC_MFPL_PC1MFP_Msk        /*<! UART2_TXD       PC1      MFP Mask */
#define UART2_TXD_PE14_Msk      SYS_GPE_MFPH_PE14MFP_Msk       /*<! UART2_TXD       PE14     MFP Mask */
#define UART2_TXD_PC5_Msk       SYS_GPC_MFPL_PC5MFP_Msk        /*<! UART2_TXD       PC5      MFP Mask */
#define UART2_TXD_PB1_Msk       SYS_GPB_MFPL_PB1MFP_Msk        /*<! UART2_TXD       PB1      MFP Mask */
#define UART2_nCTS_PF5_Msk      SYS_GPF_MFPL_PF5MFP_Msk        /*<! UART2_nCTS      PF5      MFP Mask */
#define UART2_nCTS_PD9_Msk      SYS_GPD_MFPH_PD9MFP_Msk        /*<! UART2_nCTS      PD9      MFP Mask */
#define UART2_nCTS_PC2_Msk      SYS_GPC_MFPL_PC2MFP_Msk        /*<! UART2_nCTS      PC2      MFP Mask */
#define UART2_nRTS_PF4_Msk      SYS_GPF_MFPL_PF4MFP_Msk        /*<! UART2_nRTS      PF4      MFP Mask */
#define UART2_nRTS_PD8_Msk      SYS_GPD_MFPH_PD8MFP_Msk        /*<! UART2_nRTS      PD8      MFP Mask */
#define UART2_nRTS_PC3_Msk      SYS_GPC_MFPL_PC3MFP_Msk        /*<! UART2_nRTS      PC3      MFP Mask */
#define UART3_RXD_PD0_Msk       SYS_GPD_MFPL_PD0MFP_Msk        /*<! UART3_RXD       PD0      MFP Mask */
#define UART3_RXD_PE11_Msk      SYS_GPE_MFPH_PE11MFP_Msk       /*<! UART3_RXD       PE11     MFP Mask */
#define UART3_RXD_PC9_Msk       SYS_GPC_MFPH_PC9MFP_Msk        /*<! UART3_RXD       PC9      MFP Mask */
#define UART3_RXD_PE0_Msk       SYS_GPE_MFPL_PE0MFP_Msk        /*<! UART3_RXD       PE0      MFP Mask */
#define UART3_RXD_PC2_Msk       SYS_GPC_MFPL_PC2MFP_Msk        /*<! UART3_RXD       PC2      MFP Mask */
#define UART3_RXD_PB14_Msk      SYS_GPB_MFPH_PB14MFP_Msk       /*<! UART3_RXD       PB14     MFP Mask */
#define UART3_TXD_PD1_Msk       SYS_GPD_MFPL_PD1MFP_Msk        /*<! UART3_TXD       PD1      MFP Mask */
#define UART3_TXD_PC10_Msk      SYS_GPC_MFPH_PC10MFP_Msk       /*<! UART3_TXD       PC10     MFP Mask */
#define UART3_TXD_PB15_Msk      SYS_GPB_MFPH_PB15MFP_Msk       /*<! UART3_TXD       PB15     MFP Mask */
#define UART3_TXD_PC3_Msk       SYS_GPC_MFPL_PC3MFP_Msk        /*<! UART3_TXD       PC3      MFP Mask */
#define UART3_TXD_PE1_Msk       SYS_GPE_MFPL_PE1MFP_Msk        /*<! UART3_TXD       PE1      MFP Mask */
#define UART3_TXD_PE10_Msk      SYS_GPE_MFPH_PE10MFP_Msk       /*<! UART3_TXD       PE10     MFP Mask */
#define UART3_nCTS_PB12_Msk     SYS_GPB_MFPH_PB12MFP_Msk       /*<! UART3_nCTS      PB12     MFP Mask */
#define UART3_nCTS_PH9_Msk      SYS_GPH_MFPH_PH9MFP_Msk        /*<! UART3_nCTS      PH9      MFP Mask */
#define UART3_nCTS_PD2_Msk      SYS_GPD_MFPL_PD2MFP_Msk        /*<! UART3_nCTS      PD2      MFP Mask */
#define UART3_nRTS_PB13_Msk     SYS_GPB_MFPH_PB13MFP_Msk       /*<! UART3_nRTS      PB13     MFP Mask */
#define UART3_nRTS_PH8_Msk      SYS_GPH_MFPH_PH8MFP_Msk        /*<! UART3_nRTS      PH8      MFP Mask */
#define UART3_nRTS_PD3_Msk      SYS_GPD_MFPL_PD3MFP_Msk        /*<! UART3_nRTS      PD3      MFP Mask */
#define UART4_RXD_PA13_Msk      SYS_GPA_MFPH_PA13MFP_Msk       /*<! UART4_RXD       PA13     MFP Mask */
#define UART4_RXD_PC6_Msk       SYS_GPC_MFPL_PC6MFP_Msk        /*<! UART4_RXD       PC6      MFP Mask */
#define UART4_RXD_PC4_Msk       SYS_GPC_MFPL_PC4MFP_Msk        /*<! UART4_RXD       PC4      MFP Mask */
#define UART4_RXD_PB10_Msk      SYS_GPB_MFPH_PB10MFP_Msk       /*<! UART4_RXD       PB10     MFP Mask */
#define UART4_RXD_PH11_Msk      SYS_GPH_MFPH_PH11MFP_Msk       /*<! UART4_RXD       PH11     MFP Mask */
#define UART4_RXD_PA2_Msk       SYS_GPA_MFPL_PA2MFP_Msk        /*<! UART4_RXD       PA2      MFP Mask */
#define UART4_RXD_PF6_Msk       SYS_GPF_MFPL_PF6MFP_Msk        /*<! UART4_RXD       PF6      MFP Mask */
#define UART4_TXD_PH10_Msk      SYS_GPH_MFPH_PH10MFP_Msk       /*<! UART4_TXD       PH10     MFP Mask */
#define UART4_TXD_PA3_Msk       SYS_GPA_MFPL_PA3MFP_Msk        /*<! UART4_TXD       PA3      MFP Mask */
#define UART4_TXD_PA12_Msk      SYS_GPA_MFPH_PA12MFP_Msk       /*<! UART4_TXD       PA12     MFP Mask */
#define UART4_TXD_PC7_Msk       SYS_GPC_MFPL_PC7MFP_Msk        /*<! UART4_TXD       PC7      MFP Mask */
#define UART4_TXD_PB11_Msk      SYS_GPB_MFPH_PB11MFP_Msk       /*<! UART4_TXD       PB11     MFP Mask */
#define UART4_TXD_PF7_Msk       SYS_GPF_MFPL_PF7MFP_Msk        /*<! UART4_TXD       PF7      MFP Mask */
#define UART4_TXD_PC5_Msk       SYS_GPC_MFPL_PC5MFP_Msk        /*<! UART4_TXD       PC5      MFP Mask */
#define UART4_nCTS_PE1_Msk      SYS_GPE_MFPL_PE1MFP_Msk        /*<! UART4_nCTS      PE1      MFP Mask */
#define UART4_nCTS_PC8_Msk      SYS_GPC_MFPH_PC8MFP_Msk        /*<! UART4_nCTS      PC8      MFP Mask */
#define UART4_nRTS_PE0_Msk      SYS_GPE_MFPL_PE0MFP_Msk        /*<! UART4_nRTS      PE0      MFP Mask */
#define UART4_nRTS_PE13_Msk     SYS_GPE_MFPH_PE13MFP_Msk       /*<! UART4_nRTS      PE13     MFP Mask */
#define UART5_RXD_PB4_Msk       SYS_GPB_MFPL_PB4MFP_Msk        /*<! UART5_RXD       PB4      MFP Mask */
#define UART5_RXD_PA4_Msk       SYS_GPA_MFPL_PA4MFP_Msk        /*<! UART5_RXD       PA4      MFP Mask */
#define UART5_RXD_PE6_Msk       SYS_GPE_MFPL_PE6MFP_Msk        /*<! UART5_RXD       PE6      MFP Mask */
#define UART5_TXD_PB5_Msk       SYS_GPB_MFPL_PB5MFP_Msk        /*<! UART5_TXD       PB5      MFP Mask */
#define UART5_TXD_PE7_Msk       SYS_GPE_MFPL_PE7MFP_Msk        /*<! UART5_TXD       PE7      MFP Mask */
#define UART5_TXD_PA5_Msk       SYS_GPA_MFPL_PA5MFP_Msk        /*<! UART5_TXD       PA5      MFP Mask */
#define UART5_nCTS_PB2_Msk      SYS_GPB_MFPL_PB2MFP_Msk        /*<! UART5_nCTS      PB2      MFP Mask */
#define UART5_nRTS_PB3_Msk      SYS_GPB_MFPL_PB3MFP_Msk        /*<! UART5_nRTS      PB3      MFP Mask */
#define USB_D_P_PA14_Msk        SYS_GPA_MFPH_PA14MFP_Msk       /*<! USB_D_P         PA14     MFP Mask */
#define USB_D_N_PA13_Msk        SYS_GPA_MFPH_PA13MFP_Msk       /*<! USB_D_N         PA13     MFP Mask */
#define USB_OTG_ID_PA15_Msk     SYS_GPA_MFPH_PA15MFP_Msk       /*<! USB_OTG_ID      PA15     MFP Mask */
#define USB_VBUS_PA12_Msk       SYS_GPA_MFPH_PA12MFP_Msk       /*<! USB_VBUS        PA12     MFP Mask */
#define USB_VBUS_EN_PB6_Msk     SYS_GPB_MFPL_PB6MFP_Msk        /*<! USB_VBUS_EN     PB6      MFP Mask */
#define USB_VBUS_EN_PB15_Msk    SYS_GPB_MFPH_PB15MFP_Msk       /*<! USB_VBUS_EN     PB15     MFP Mask */
#define USB_VBUS_ST_PB14_Msk    SYS_GPB_MFPH_PB14MFP_Msk       /*<! USB_VBUS_ST     PB14     MFP Mask */
#define USB_VBUS_ST_PB7_Msk     SYS_GPB_MFPL_PB7MFP_Msk        /*<! USB_VBUS_ST     PB7      MFP Mask */
#define USB_VBUS_ST_PD4_Msk     SYS_GPD_MFPL_PD4MFP_Msk        /*<! USB_VBUS_ST     PD4      MFP Mask */
#define USCI0_CLK_PD0_Msk       SYS_GPD_MFPL_PD0MFP_Msk        /*<! USCI0_CLK       PD0      MFP Mask */
#define USCI0_CLK_PA11_Msk      SYS_GPA_MFPH_PA11MFP_Msk       /*<! USCI0_CLK       PA11     MFP Mask */
#define USCI0_CLK_PE2_Msk       SYS_GPE_MFPL_PE2MFP_Msk        /*<! USCI0_CLK       PE2      MFP Mask */
#define USCI0_CLK_PB12_Msk      SYS_GPB_MFPH_PB12MFP_Msk       /*<! USCI0_CLK       PB12     MFP Mask */
#define USCI0_CTL0_PD4_Msk      SYS_GPD_MFPL_PD4MFP_Msk        /*<! USCI0_CTL0      PD4      MFP Mask */
#define USCI0_CTL0_PE6_Msk      SYS_GPE_MFPL_PE6MFP_Msk        /*<! USCI0_CTL0      PE6      MFP Mask */
#define USCI0_CTL0_PC13_Msk     SYS_GPC_MFPH_PC13MFP_Msk       /*<! USCI0_CTL0      PC13     MFP Mask */
#define USCI0_CTL0_PD14_Msk     SYS_GPD_MFPH_PD14MFP_Msk       /*<! USCI0_CTL0      PD14     MFP Mask */
#define USCI0_CTL1_PD3_Msk      SYS_GPD_MFPL_PD3MFP_Msk        /*<! USCI0_CTL1      PD3      MFP Mask */
#define USCI0_CTL1_PE5_Msk      SYS_GPE_MFPL_PE5MFP_Msk        /*<! USCI0_CTL1      PE5      MFP Mask */
#define USCI0_CTL1_PB15_Msk     SYS_GPB_MFPH_PB15MFP_Msk       /*<! USCI0_CTL1      PB15     MFP Mask */
#define USCI0_CTL1_PA8_Msk      SYS_GPA_MFPH_PA8MFP_Msk        /*<! USCI0_CTL1      PA8      MFP Mask */
#define USCI0_DAT0_PE3_Msk      SYS_GPE_MFPL_PE3MFP_Msk        /*<! USCI0_DAT0      PE3      MFP Mask */
#define USCI0_DAT0_PB13_Msk     SYS_GPB_MFPH_PB13MFP_Msk       /*<! USCI0_DAT0      PB13     MFP Mask */
#define USCI0_DAT0_PD1_Msk      SYS_GPD_MFPL_PD1MFP_Msk        /*<! USCI0_DAT0      PD1      MFP Mask */
#define USCI0_DAT0_PA10_Msk     SYS_GPA_MFPH_PA10MFP_Msk       /*<! USCI0_DAT0      PA10     MFP Mask */
#define USCI0_DAT1_PE4_Msk      SYS_GPE_MFPL_PE4MFP_Msk        /*<! USCI0_DAT1      PE4      MFP Mask */
#define USCI0_DAT1_PD2_Msk      SYS_GPD_MFPL_PD2MFP_Msk        /*<! USCI0_DAT1      PD2      MFP Mask */
#define USCI0_DAT1_PB14_Msk     SYS_GPB_MFPH_PB14MFP_Msk       /*<! USCI0_DAT1      PB14     MFP Mask */
#define USCI0_DAT1_PA9_Msk      SYS_GPA_MFPH_PA9MFP_Msk        /*<! USCI0_DAT1      PA9      MFP Mask */
#define USCI1_CLK_PE12_Msk      SYS_GPE_MFPH_PE12MFP_Msk       /*<! USCI1_CLK       PE12     MFP Mask */
#define USCI1_CLK_PD7_Msk       SYS_GPD_MFPL_PD7MFP_Msk        /*<! USCI1_CLK       PD7      MFP Mask */
#define USCI1_CLK_PB8_Msk       SYS_GPB_MFPH_PB8MFP_Msk        /*<! USCI1_CLK       PB8      MFP Mask */
#define USCI1_CLK_PB1_Msk       SYS_GPB_MFPL_PB1MFP_Msk        /*<! USCI1_CLK       PB1      MFP Mask */
#define USCI1_CTL0_PB10_Msk     SYS_GPB_MFPH_PB10MFP_Msk       /*<! USCI1_CTL0      PB10     MFP Mask */
#define USCI1_CTL0_PB5_Msk      SYS_GPB_MFPL_PB5MFP_Msk        /*<! USCI1_CTL0      PB5      MFP Mask */
#define USCI1_CTL0_PE9_Msk      SYS_GPE_MFPH_PE9MFP_Msk        /*<! USCI1_CTL0      PE9      MFP Mask */
#define USCI1_CTL0_PD3_Msk      SYS_GPD_MFPL_PD3MFP_Msk        /*<! USCI1_CTL0      PD3      MFP Mask */
#define USCI1_CTL1_PD4_Msk      SYS_GPD_MFPL_PD4MFP_Msk        /*<! USCI1_CTL1      PD4      MFP Mask */
#define USCI1_CTL1_PE8_Msk      SYS_GPE_MFPH_PE8MFP_Msk        /*<! USCI1_CTL1      PE8      MFP Mask */
#define USCI1_CTL1_PB9_Msk      SYS_GPB_MFPH_PB9MFP_Msk        /*<! USCI1_CTL1      PB9      MFP Mask */
#define USCI1_CTL1_PB4_Msk      SYS_GPB_MFPL_PB4MFP_Msk        /*<! USCI1_CTL1      PB4      MFP Mask */
#define USCI1_DAT0_PB2_Msk      SYS_GPB_MFPL_PB2MFP_Msk        /*<! USCI1_DAT0      PB2      MFP Mask */
#define USCI1_DAT0_PB7_Msk      SYS_GPB_MFPL_PB7MFP_Msk        /*<! USCI1_DAT0      PB7      MFP Mask */
#define USCI1_DAT0_PE10_Msk     SYS_GPE_MFPH_PE10MFP_Msk       /*<! USCI1_DAT0      PE10     MFP Mask */
#define USCI1_DAT0_PD5_Msk      SYS_GPD_MFPL_PD5MFP_Msk        /*<! USCI1_DAT0      PD5      MFP Mask */
#define USCI1_DAT1_PD6_Msk      SYS_GPD_MFPL_PD6MFP_Msk        /*<! USCI1_DAT1      PD6      MFP Mask */
#define USCI1_DAT1_PB3_Msk      SYS_GPB_MFPL_PB3MFP_Msk        /*<! USCI1_DAT1      PB3      MFP Mask */
#define USCI1_DAT1_PE11_Msk     SYS_GPE_MFPH_PE11MFP_Msk       /*<! USCI1_DAT1      PE11     MFP Mask */
#define USCI1_DAT1_PB6_Msk      SYS_GPB_MFPL_PB6MFP_Msk        /*<! USCI1_DAT1      PB6      MFP Mask */
#define X32_IN_PF5_Msk          SYS_GPF_MFPL_PF5MFP_Msk        /*<! X32_IN          PF5      MFP Mask */
#define X32_OUT_PF4_Msk         SYS_GPF_MFPL_PF4MFP_Msk        /*<! X32_OUT         PF4      MFP Mask */
#define XT1_IN_PF3_Msk          SYS_GPF_MFPL_PF3MFP_Msk        /*<! XT1_IN          PF3      MFP Mask */
#define XT1_OUT_PF2_Msk         SYS_GPF_MFPL_PF2MFP_Msk        /*<! XT1_OUT         PF2      MFP Mask */



/*@}*/ /* end of group SYS_EXPORTED_CONSTANTS */

/** @addtogroup SYS_EXPORTED_FUNCTIONS SYS Exported Functions
  @{
*/


/**
  * @brief      Clear Brown-out detector interrupt flag
  * @param      None
  * @return     None
  * @details    This macro clear Brown-out detector interrupt flag.
  */
#define SYS_CLEAR_BOD_INT_FLAG()        (SYS->BODCTL |= SYS_BODCTL_BODIF_Msk)

/**
  * @brief      Set Brown-out detector function to normal mode
  * @param      None
  * @return     None
  * @details    This macro set Brown-out detector to normal mode.
  *             The register write-protection function should be disabled before using this macro.
  */
#define SYS_CLEAR_BOD_LPM()             (SYS->BODCTL &= ~SYS_BODCTL_BODLPM_Msk)

/**
  * @brief      Disable Brown-out detector function
  * @param      None
  * @return     None
  * @details    This macro disable Brown-out detector function.
  *             The register write-protection function should be disabled before using this macro.
  */
#define SYS_DISABLE_BOD()               (SYS->BODCTL &= ~SYS_BODCTL_BODEN_Msk)

/**
  * @brief      Enable Brown-out detector function
  * @param      None
  * @return     None
  * @details    This macro enable Brown-out detector function.
  *             The register write-protection function should be disabled before using this macro.
  */
#define SYS_ENABLE_BOD()                (SYS->BODCTL |= SYS_BODCTL_BODEN_Msk)

/**
  * @brief      Get Brown-out detector interrupt flag
  * @param      None
  * @retval     0   Brown-out detect interrupt flag is not set.
  * @retval     >=1 Brown-out detect interrupt flag is set.
  * @details    This macro get Brown-out detector interrupt flag.
  */
#define SYS_GET_BOD_INT_FLAG()          (SYS->BODCTL & SYS_BODCTL_BODIF_Msk)

/**
  * @brief      Get Brown-out detector status
  * @param      None
  * @retval     0   System voltage is higher than BOD threshold voltage setting or BOD function is disabled.
  * @retval     >=1 System voltage is lower than BOD threshold voltage setting.
  * @details    This macro get Brown-out detector output status.
  *             If the BOD function is disabled, this function always return 0.
  */
#define SYS_GET_BOD_OUTPUT()            (SYS->BODCTL & SYS_BODCTL_BODOUT_Msk)

/**
  * @brief      Enable Brown-out detector interrupt function
  * @param      None
  * @return     None
  * @details    This macro enable Brown-out detector interrupt function.
  *             The register write-protection function should be disabled before using this macro.
  */
#define SYS_DISABLE_BOD_RST()           (SYS->BODCTL &= ~SYS_BODCTL_BODRSTEN_Msk)

/**
  * @brief      Enable Brown-out detector reset function
  * @param      None
  * @return     None
  * @details    This macro enable Brown-out detect reset function.
  *             The register write-protection function should be disabled before using this macro.
  */
#define SYS_ENABLE_BOD_RST()            (SYS->BODCTL |= SYS_BODCTL_BODRSTEN_Msk)

/**
  * @brief      Set Brown-out detector function low power mode
  * @param      None
  * @return     None
  * @details    This macro set Brown-out detector to low power mode.
  *             The register write-protection function should be disabled before using this macro.
  */
#define SYS_SET_BOD_LPM()               (SYS->BODCTL |= SYS_BODCTL_BODLPM_Msk)

/**
  * @brief      Set Brown-out detector voltage level
  * @param[in]  u32Level is Brown-out voltage level. Including :
  *             - \ref SYS_BODCTL_BODVL_1_6V
  *             - \ref SYS_BODCTL_BODVL_1_8V
  *             - \ref SYS_BODCTL_BODVL_2_0V
  *             - \ref SYS_BODCTL_BODVL_2_2V
  *             - \ref SYS_BODCTL_BODVL_2_4V
  *             - \ref SYS_BODCTL_BODVL_2_6V
  *             - \ref SYS_BODCTL_BODVL_2_8V
  *             - \ref SYS_BODCTL_BODVL_3_0V
  * @return     None
  * @details    This macro set Brown-out detector voltage level.
  *             The write-protection function should be disabled before using this macro.
  */
#define SYS_SET_BOD_LEVEL(u32Level)     (SYS->BODCTL = (SYS->BODCTL & ~SYS_BODCTL_BODVL_Msk) | (u32Level))

/**
  * @brief      Get reset source is from Brown-out detector reset
  * @param      None
  * @retval     0   Previous reset source is not from Brown-out detector reset
  * @retval     >=1 Previous reset source is from Brown-out detector reset
  * @details    This macro get previous reset source is from Brown-out detect reset or not.
  */
#define SYS_IS_BOD_RST()                (SYS->RSTSTS & SYS_RSTSTS_BODRF_Msk)

/**
  * @brief      Get reset source is from CPU reset
  * @param      None
  * @retval     0   Previous reset source is not from CPU reset
  * @retval     >=1 Previous reset source is from CPU reset
  * @details    This macro get previous reset source is from CPU reset.
  */
#define SYS_IS_CPU_RST()                (SYS->RSTSTS & SYS_RSTSTS_CPURF_Msk)

/**
  * @brief      Get reset source is from LVR Reset
  * @param      None
  * @retval     0   Previous reset source is not from Low-Voltage-Reset
  * @retval     >=1 Previous reset source is from Low-Voltage-Reset
  * @details    This macro get previous reset source is from Low-Voltage-Reset.
  */
#define SYS_IS_LVR_RST()                (SYS->RSTSTS & SYS_RSTSTS_LVRF_Msk)

/**
  * @brief      Get reset source is from Power-on Reset
  * @param      None
  * @retval     0   Previous reset source is not from Power-on Reset
  * @retval     >=1 Previous reset source is from Power-on Reset
  * @details    This macro get previous reset source is from Power-on Reset.
  */
#define SYS_IS_POR_RST()                (SYS->RSTSTS & SYS_RSTSTS_PORF_Msk)

/**
  * @brief      Get reset source is from reset pin reset
  * @param      None
  * @retval     0   Previous reset source is not from reset pin reset
  * @retval     >=1 Previous reset source is from reset pin reset
  * @details    This macro get previous reset source is from reset pin reset.
  */
#define SYS_IS_RSTPIN_RST()             (SYS->RSTSTS & SYS_RSTSTS_PINRF_Msk)

/**
  * @brief      Get reset source is from system reset
  * @param      None
  * @retval     0   Previous reset source is not from system reset
  * @retval     >=1 Previous reset source is from system reset
  * @details    This macro get previous reset source is from system reset.
  */
#define SYS_IS_SYSTEM_RST()             (SYS->RSTSTS & SYS_RSTSTS_SYSRF_Msk)

/**
  * @brief      Get reset source is from window watch dog reset
  * @param      None
  * @retval     0   Previous reset source is not from window watch dog reset
  * @retval     >=1 Previous reset source is from window watch dog reset
  * @details    This macro get previous reset source is from window watch dog reset.
  */
#define SYS_IS_WDT_RST()                (SYS->RSTSTS & SYS_RSTSTS_WDTRF_Msk)

/**
  * @brief      Disable Low-Voltage-Reset function
  * @param      None
  * @return     None
  * @details    This macro disable Low-Voltage-Reset function.
  *             The register write-protection function should be disabled before using this macro.
  */
#define SYS_DISABLE_LVR()               (SYS->BODCTL &= ~SYS_BODCTL_LVREN_Msk)

/**
  * @brief      Enable Low-Voltage-Reset function
  * @param      None
  * @return     None
  * @details    This macro enable Low-Voltage-Reset function.
  *             The register write-protection function should be disabled before using this macro.
  */
#define SYS_ENABLE_LVR()                (SYS->BODCTL |= SYS_BODCTL_LVREN_Msk)

/**
  * @brief      Disable Power-on Reset function
  * @param      None
  * @return     None
  * @details    This macro disable Power-on Reset function.
  *             The register write-protection function should be disabled before using this macro.
  */
#define SYS_DISABLE_POR()               (SYS->PORCTL0 = 0x5AA5)

/**
  * @brief      Enable Power-on Reset function
  * @param      None
  * @return     None
  * @details    This macro enable Power-on Reset function.
  *             The register write-protection function should be disabled before using this macro.
  */
#define SYS_ENABLE_POR()                (SYS->PORCTL0 = 0)

/**
  * @brief      Clear reset source flag
  * @param[in]  u32RstSrc is reset source. Including :
  *             - \ref SYS_RSTSTS_PORF_Msk
  *             - \ref SYS_RSTSTS_PINRF_Msk
  *             - \ref SYS_RSTSTS_WDTRF_Msk
  *             - \ref SYS_RSTSTS_LVRF_Msk
  *             - \ref SYS_RSTSTS_BODRF_Msk
  *             - \ref SYS_RSTSTS_SYSRF_Msk
  *             - \ref SYS_RSTSTS_CPURF_Msk
  *             - \ref SYS_RSTSTS_CPULKRF_Msk
  * @return     None
  * @details    This macro clear reset source flag.
  */
#define SYS_CLEAR_RST_SOURCE(u32RstSrc) ((SYS->RSTSTS) = (u32RstSrc) )


/*---------------------------------------------------------------------------------------------------------*/
/* static inline functions                                                                                 */
/*---------------------------------------------------------------------------------------------------------*/
/* Declare these inline functions here to avoid MISRA C 2004 rule 8.1 error */
__STATIC_INLINE void SYS_UnlockReg(void);
__STATIC_INLINE void SYS_LockReg(void);


/**
  * @brief      Disable register write-protection function
  * @param      None
  * @return     None
  * @details    This function disable register write-protection function.
  *             To unlock the protected register to allow write access.
  */
__STATIC_INLINE void SYS_UnlockReg(void)
{
    do
    {
        SYS->REGLCTL = 0x59UL;
        SYS->REGLCTL = 0x16UL;
        SYS->REGLCTL = 0x88UL;
    }
    while(SYS->REGLCTL == 0UL);
}

/**
  * @brief      Enable register write-protection function
  * @param      None
  * @return     None
  * @details    This function is used to enable register write-protection function.
  *             To lock the protected register to forbid write access.
  */
__STATIC_INLINE void SYS_LockReg(void)
{
    SYS->REGLCTL = 0UL;
}


void SYS_ClearResetSrc(uint32_t u32Src);
uint32_t SYS_GetBODStatus(void);
uint32_t SYS_GetResetSrc(void);
uint32_t SYS_IsRegLocked(void);
uint32_t SYS_ReadPDID(void);
void SYS_ResetChip(void);
void SYS_ResetCPU(void);
void SYS_ResetModule(uint32_t u32ModuleIndex);
void SYS_EnableBOD(int32_t i32Mode, uint32_t u32BODLevel);
void SYS_DisableBOD(void);
void SYS_SetPowerLevel(uint32_t u32PowerLevel);
uint32_t SYS_SetPowerRegulator(uint32_t u32PowerRegulator);
void SYS_SetSSRAMPowerMode(uint32_t u32SRAMSel, uint32_t u32PowerMode);
void SYS_SetPSRAMPowerMode(uint32_t u32SRAMSel, uint32_t u32PowerMode);


/*@}*/ /* end of group SYS_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group SYS_Driver */

/*@}*/ /* end of group Standard_Driver */


#ifdef __cplusplus
}
#endif

#endif /* __SYS_H__ */


/*** (C) COPYRIGHT 2016 Nuvoton Technology Corp. ***/
