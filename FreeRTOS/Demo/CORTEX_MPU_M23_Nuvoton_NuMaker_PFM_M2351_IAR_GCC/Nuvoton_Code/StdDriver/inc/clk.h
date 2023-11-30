/**************************************************************************//**
 * @file     clk.h
 * @version  V3.0
 * @brief    M2351 series Clock Controller (CLK) driver header file
 *
 * @note
 * Copyright (C) 2016 Nuvoton Technology Corp. All rights reserved.
 *
 ******************************************************************************/
#ifndef __CLK_H__
#define __CLK_H__


#ifdef __cplusplus
extern "C"
{
#endif



/** @addtogroup Standard_Driver Standard Driver
  @{
*/

/** @addtogroup CLK_Driver CLK Driver
  @{
*/

/** @addtogroup CLK_EXPORTED_CONSTANTS CLK Exported Constants
  @{
*/


#define FREQ_2MHZ          2000000UL
#define FREQ_8MHZ          8000000UL
#define FREQ_24MHZ         24000000UL
#define FREQ_48MHZ         48000000UL
#define FREQ_64MHZ         64000000UL
#define FREQ_96MHZ         96000000UL
#define FREQ_144MHZ        144000000UL
#define FREQ_200MHZ        200000000UL



/*---------------------------------------------------------------------------------------------------------*/
/*  CLKSEL0 constant definitions.                                                                          */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_CLKSEL0_HCLKSEL_HXT         (0x00UL<<CLK_CLKSEL0_HCLKSEL_Pos) /*!< Setting HCLK clock source as HXT */
#define CLK_CLKSEL0_HCLKSEL_LXT         (0x01UL<<CLK_CLKSEL0_HCLKSEL_Pos) /*!< Setting HCLK clock source as LXT */
#define CLK_CLKSEL0_HCLKSEL_PLL         (0x02UL<<CLK_CLKSEL0_HCLKSEL_Pos) /*!< Setting HCLK clock source as PLL */
#define CLK_CLKSEL0_HCLKSEL_LIRC        (0x03UL<<CLK_CLKSEL0_HCLKSEL_Pos) /*!< Setting HCLK clock source as LIRC */
#define CLK_CLKSEL0_HCLKSEL_HIRC48      (0x05UL<<CLK_CLKSEL0_HCLKSEL_Pos) /*!< Setting HCLK clock source as HIRC48 */
#define CLK_CLKSEL0_HCLKSEL_HIRC        (0x07UL<<CLK_CLKSEL0_HCLKSEL_Pos) /*!< Setting HCLK clock source as HIRC */

#define CLK_CLKSEL0_STCLKSEL_HXT        (0x00UL<<CLK_CLKSEL0_STCLKSEL_Pos) /*!< Setting SysTick clock source as HXT */
#define CLK_CLKSEL0_STCLKSEL_LXT        (0x01UL<<CLK_CLKSEL0_STCLKSEL_Pos) /*!< Setting SysTick clock source as LXT */
#define CLK_CLKSEL0_STCLKSEL_HXT_DIV2   (0x02UL<<CLK_CLKSEL0_STCLKSEL_Pos) /*!< Setting SysTick clock source as HXT */
#define CLK_CLKSEL0_STCLKSEL_HCLK_DIV2  (0x03UL<<CLK_CLKSEL0_STCLKSEL_Pos) /*!< Setting SysTick clock source as HCLK/2 */
#define CLK_CLKSEL0_STCLKSEL_HIRC_DIV2  (0x07UL<<CLK_CLKSEL0_STCLKSEL_Pos) /*!< Setting SysTick clock source as HIRC/2 */
#define CLK_CLKSEL0_STCLKSEL_HCLK       (0x01UL<<SysTick_CTRL_CLKSOURCE_Pos) /*!< Setting SysTick clock source as HCLK */

#define CLK_CLKSEL0_SDH0SEL_HXT         (0x00UL<<CLK_CLKSEL0_SDH0SEL_Pos) /*!< Setting SDH0 clock source as HXT */
#define CLK_CLKSEL0_SDH0SEL_PLL         (0x01UL<<CLK_CLKSEL0_SDH0SEL_Pos) /*!< Setting SDH0 clock source as PLL */
#define CLK_CLKSEL0_SDH0SEL_HCLK        (0x02UL<<CLK_CLKSEL0_SDH0SEL_Pos) /*!< Setting SDH0 clock source as HCLK */
#define CLK_CLKSEL0_SDH0SEL_HIRC        (0x03UL<<CLK_CLKSEL0_SDH0SEL_Pos) /*!< Setting SDH0 clock source as HIRC */

#define CLK_CLKSEL0_USBSEL_HIRC48       (0x00UL<<CLK_CLKSEL0_USBSEL_Pos)  /*!< Setting USB clock source as HIRC48 */
#define CLK_CLKSEL0_USBSEL_PLL          (0x01UL<<CLK_CLKSEL0_USBSEL_Pos)  /*!< Setting USB clock source as PLL */


/*---------------------------------------------------------------------------------------------------------*/
/*  CLKSEL1 constant definitions.                                                                          */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_CLKSEL1_WDTSEL_LXT           (0x1UL<<CLK_CLKSEL1_WDTSEL_Pos)  /*!< Setting WDT clock source as LXT */
#define CLK_CLKSEL1_WDTSEL_HCLK_DIV2048  (0x2UL<<CLK_CLKSEL1_WDTSEL_Pos)  /*!< Setting WDT clock source as HCLK/2048 */
#define CLK_CLKSEL1_WDTSEL_LIRC          (0x3UL<<CLK_CLKSEL1_WDTSEL_Pos)  /*!< Setting WDT clock source as LIRC */

#define CLK_CLKSEL1_TMR0SEL_HXT          (0x0UL<<CLK_CLKSEL1_TMR0SEL_Pos) /*!< Setting Timer 0 clock source as HXT */
#define CLK_CLKSEL1_TMR0SEL_LXT          (0x1UL<<CLK_CLKSEL1_TMR0SEL_Pos) /*!< Setting Timer 0 clock source as LXT */
#define CLK_CLKSEL1_TMR0SEL_PCLK0        (0x2UL<<CLK_CLKSEL1_TMR0SEL_Pos) /*!< Setting Timer 0 clock source as PCLK0 */
#define CLK_CLKSEL1_TMR0SEL_EXT_TRG      (0x3UL<<CLK_CLKSEL1_TMR0SEL_Pos) /*!< Setting Timer 0 clock source as external trigger */
#define CLK_CLKSEL1_TMR0SEL_LIRC         (0x5UL<<CLK_CLKSEL1_TMR0SEL_Pos) /*!< Setting Timer 0 clock source as LIRC */
#define CLK_CLKSEL1_TMR0SEL_HIRC         (0x7UL<<CLK_CLKSEL1_TMR0SEL_Pos) /*!< Setting Timer 0 clock source as HIRC */

#define CLK_CLKSEL1_TMR1SEL_HXT          (0x0UL<<CLK_CLKSEL1_TMR1SEL_Pos) /*!< Setting Timer 1 clock source as HXT */
#define CLK_CLKSEL1_TMR1SEL_LXT          (0x1UL<<CLK_CLKSEL1_TMR1SEL_Pos) /*!< Setting Timer 1 clock source as LXT */
#define CLK_CLKSEL1_TMR1SEL_PCLK0        (0x2UL<<CLK_CLKSEL1_TMR1SEL_Pos) /*!< Setting Timer 1 clock source as PCLK0 */
#define CLK_CLKSEL1_TMR1SEL_EXT_TRG      (0x3UL<<CLK_CLKSEL1_TMR1SEL_Pos) /*!< Setting Timer 1 clock source as external trigger */
#define CLK_CLKSEL1_TMR1SEL_LIRC         (0x5UL<<CLK_CLKSEL1_TMR1SEL_Pos) /*!< Setting Timer 1 clock source as LIRC */
#define CLK_CLKSEL1_TMR1SEL_HIRC         (0x7UL<<CLK_CLKSEL1_TMR1SEL_Pos) /*!< Setting Timer 1 clock source as HIRC */

#define CLK_CLKSEL1_TMR2SEL_HXT          (0x0UL<<CLK_CLKSEL1_TMR2SEL_Pos) /*!< Setting Timer 2 clock source as HXT */
#define CLK_CLKSEL1_TMR2SEL_LXT          (0x1UL<<CLK_CLKSEL1_TMR2SEL_Pos) /*!< Setting Timer 2 clock source as LXT */
#define CLK_CLKSEL1_TMR2SEL_PCLK1        (0x2UL<<CLK_CLKSEL1_TMR2SEL_Pos) /*!< Setting Timer 2 clock source as PCLK1 */
#define CLK_CLKSEL1_TMR2SEL_EXT_TRG      (0x3UL<<CLK_CLKSEL1_TMR2SEL_Pos) /*!< Setting Timer 2 clock source as external trigger */
#define CLK_CLKSEL1_TMR2SEL_LIRC         (0x5UL<<CLK_CLKSEL1_TMR2SEL_Pos) /*!< Setting Timer 2 clock source as LIRC */
#define CLK_CLKSEL1_TMR2SEL_HIRC         (0x7UL<<CLK_CLKSEL1_TMR2SEL_Pos) /*!< Setting Timer 2 clock source as HIRC */

#define CLK_CLKSEL1_TMR3SEL_HXT          (0x0UL<<CLK_CLKSEL1_TMR3SEL_Pos) /*!< Setting Timer 3 clock source as HXT */
#define CLK_CLKSEL1_TMR3SEL_LXT          (0x1UL<<CLK_CLKSEL1_TMR3SEL_Pos) /*!< Setting Timer 3 clock source as LXT */
#define CLK_CLKSEL1_TMR3SEL_PCLK1        (0x2UL<<CLK_CLKSEL1_TMR3SEL_Pos) /*!< Setting Timer 3 clock source as PCLK1 */
#define CLK_CLKSEL1_TMR3SEL_EXT_TRG      (0x3UL<<CLK_CLKSEL1_TMR3SEL_Pos) /*!< Setting Timer 3 clock source as external trigger */
#define CLK_CLKSEL1_TMR3SEL_LIRC         (0x5UL<<CLK_CLKSEL1_TMR3SEL_Pos) /*!< Setting Timer 3 clock source as LIRC */
#define CLK_CLKSEL1_TMR3SEL_HIRC         (0x7UL<<CLK_CLKSEL1_TMR3SEL_Pos) /*!< Setting Timer 3 clock source as HIRC */

#define CLK_CLKSEL1_UART0SEL_HXT         (0x0UL<<CLK_CLKSEL1_UART0SEL_Pos) /*!< Setting UART0 clock source as HXT */
#define CLK_CLKSEL1_UART0SEL_PLL         (0x1UL<<CLK_CLKSEL1_UART0SEL_Pos) /*!< Setting UART0 clock source as PLL */
#define CLK_CLKSEL1_UART0SEL_LXT         (0x2UL<<CLK_CLKSEL1_UART0SEL_Pos) /*!< Setting UART0 clock source as LXT */
#define CLK_CLKSEL1_UART0SEL_HIRC        (0x3UL<<CLK_CLKSEL1_UART0SEL_Pos) /*!< Setting UART0 clock source as HIRC */

#define CLK_CLKSEL1_UART1SEL_HXT         (0x0UL<<CLK_CLKSEL1_UART1SEL_Pos) /*!< Setting UART1 clock source as HXT */
#define CLK_CLKSEL1_UART1SEL_PLL         (0x1UL<<CLK_CLKSEL1_UART1SEL_Pos) /*!< Setting UART1 clock source as PLL */
#define CLK_CLKSEL1_UART1SEL_LXT         (0x2UL<<CLK_CLKSEL1_UART1SEL_Pos) /*!< Setting UART1 clock source as LXT */
#define CLK_CLKSEL1_UART1SEL_HIRC        (0x3UL<<CLK_CLKSEL1_UART1SEL_Pos) /*!< Setting UART1 clock source as HIRC */

#define CLK_CLKSEL1_CLKOSEL_HXT          (0x0UL<<CLK_CLKSEL1_CLKOSEL_Pos) /*!< Setting CLKO clock source as HXT */
#define CLK_CLKSEL1_CLKOSEL_LXT          (0x1UL<<CLK_CLKSEL1_CLKOSEL_Pos) /*!< Setting CLKO clock source as LXT */
#define CLK_CLKSEL1_CLKOSEL_HCLK         (0x2UL<<CLK_CLKSEL1_CLKOSEL_Pos) /*!< Setting CLKO clock source as HCLK */
#define CLK_CLKSEL1_CLKOSEL_HIRC         (0x3UL<<CLK_CLKSEL1_CLKOSEL_Pos) /*!< Setting CLKO clock source as HIRC */

#define CLK_CLKSEL1_WWDTSEL_HCLK_DIV2048 (0x2UL<<CLK_CLKSEL1_WWDTSEL_Pos) /*!< Setting WWDT clock source as HCLK/2048 */
#define CLK_CLKSEL1_WWDTSEL_LIRC         (0x3UL<<CLK_CLKSEL1_WWDTSEL_Pos) /*!< Setting WWDT clock source as LIRC */


/*---------------------------------------------------------------------------------------------------------*/
/*  CLKSEL2 constant definitions.                                                                          */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_CLKSEL2_EPWM0SEL_PCLK0       (0x1UL<<CLK_CLKSEL2_EPWM0SEL_Pos) /*!< Setting EPWM0 clock source as PCLK0 */
#define CLK_CLKSEL2_EPWM1SEL_PCLK1       (0x1UL<<CLK_CLKSEL2_EPWM1SEL_Pos) /*!< Setting EPWM1 clock source as PCLK1 */

#define CLK_CLKSEL2_BPWM0SEL_PCLK0       (0x1UL<<CLK_CLKSEL2_BPWM0SEL_Pos) /*!< Setting BPWM0 clock source as PCLK0 */
#define CLK_CLKSEL2_BPWM1SEL_PCLK1       (0x1UL<<CLK_CLKSEL2_BPWM1SEL_Pos) /*!< Setting BPWM1 clock source as PCLK1 */

#define CLK_CLKSEL2_QSPI0SEL_HXT         (0x0UL<<CLK_CLKSEL2_QSPI0SEL_Pos) /*!< Setting QSPI0 clock source as HXT */
#define CLK_CLKSEL2_QSPI0SEL_PLL         (0x1UL<<CLK_CLKSEL2_QSPI0SEL_Pos) /*!< Setting QSPI0 clock source as PLL */
#define CLK_CLKSEL2_QSPI0SEL_PCLK0       (0x2UL<<CLK_CLKSEL2_QSPI0SEL_Pos) /*!< Setting QSPI0 clock source as PCLK0 */
#define CLK_CLKSEL2_QSPI0SEL_HIRC        (0x3UL<<CLK_CLKSEL2_QSPI0SEL_Pos) /*!< Setting QSPI0 clock source as HIRC */

#define CLK_CLKSEL2_SPI0SEL_HXT          (0x0UL<<CLK_CLKSEL2_SPI0SEL_Pos) /*!< Setting SPI0 clock source as HXT */
#define CLK_CLKSEL2_SPI0SEL_PLL          (0x1UL<<CLK_CLKSEL2_SPI0SEL_Pos) /*!< Setting SPI0 clock source as PLL */
#define CLK_CLKSEL2_SPI0SEL_PCLK1        (0x2UL<<CLK_CLKSEL2_SPI0SEL_Pos) /*!< Setting SPI0 clock source as PCLK1 */
#define CLK_CLKSEL2_SPI0SEL_HIRC         (0x3UL<<CLK_CLKSEL2_SPI0SEL_Pos) /*!< Setting SPI0 clock source as HIRC */

#define CLK_CLKSEL2_SPI1SEL_HXT          (0x0UL<<CLK_CLKSEL2_SPI1SEL_Pos) /*!< Setting SPI1 clock source as HXT */
#define CLK_CLKSEL2_SPI1SEL_PLL          (0x1UL<<CLK_CLKSEL2_SPI1SEL_Pos) /*!< Setting SPI1 clock source as PLL */
#define CLK_CLKSEL2_SPI1SEL_PCLK0        (0x2UL<<CLK_CLKSEL2_SPI1SEL_Pos) /*!< Setting SPI1 clock source as PCLK0 */
#define CLK_CLKSEL2_SPI1SEL_HIRC         (0x3UL<<CLK_CLKSEL2_SPI1SEL_Pos) /*!< Setting SPI1 clock source as HIRC */

#define CLK_CLKSEL2_SPI2SEL_HXT          (0x0UL<<CLK_CLKSEL2_SPI2SEL_Pos) /*!< Setting SPI2 clock source as HXT */
#define CLK_CLKSEL2_SPI2SEL_PLL          (0x1UL<<CLK_CLKSEL2_SPI2SEL_Pos) /*!< Setting SPI2 clock source as PLL */
#define CLK_CLKSEL2_SPI2SEL_PCLK1        (0x2UL<<CLK_CLKSEL2_SPI2SEL_Pos) /*!< Setting SPI2 clock source as PCLK1 */
#define CLK_CLKSEL2_SPI2SEL_HIRC         (0x3UL<<CLK_CLKSEL2_SPI2SEL_Pos) /*!< Setting SPI2 clock source as HIRC */

#define CLK_CLKSEL2_SPI3SEL_HXT          (0x0UL<<CLK_CLKSEL2_SPI3SEL_Pos) /*!< Setting SPI3 clock source as HXT */
#define CLK_CLKSEL2_SPI3SEL_PLL          (0x1UL<<CLK_CLKSEL2_SPI3SEL_Pos) /*!< Setting SPI3 clock source as PLL */
#define CLK_CLKSEL2_SPI3SEL_PCLK0        (0x2UL<<CLK_CLKSEL2_SPI3SEL_Pos) /*!< Setting SPI3 clock source as PCLK0 */
#define CLK_CLKSEL2_SPI3SEL_HIRC         (0x3UL<<CLK_CLKSEL2_SPI3SEL_Pos) /*!< Setting SPI3 clock source as HIRC */


/*---------------------------------------------------------------------------------------------------------*/
/*  CLKSEL3 constant definitions.                                                                          */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_CLKSEL3_SC0SEL_HXT          (0x0UL<<CLK_CLKSEL3_SC0SEL_Pos) /*!< Setting SC0 clock source as HXT */
#define CLK_CLKSEL3_SC0SEL_PLL          (0x1UL<<CLK_CLKSEL3_SC0SEL_Pos) /*!< Setting SC0 clock source as PLL */
#define CLK_CLKSEL3_SC0SEL_PCLK0        (0x2UL<<CLK_CLKSEL3_SC0SEL_Pos) /*!< Setting SC0 clock source as PCLK0 */
#define CLK_CLKSEL3_SC0SEL_HIRC         (0x3UL<<CLK_CLKSEL3_SC0SEL_Pos) /*!< Setting SC0 clock source as HIRC */

#define CLK_CLKSEL3_SC1SEL_HXT          (0x0UL<<CLK_CLKSEL3_SC1SEL_Pos) /*!< Setting SC1 clock source as HXT */
#define CLK_CLKSEL3_SC1SEL_PLL          (0x1UL<<CLK_CLKSEL3_SC1SEL_Pos) /*!< Setting SC1 clock source as PLL */
#define CLK_CLKSEL3_SC1SEL_PCLK1        (0x2UL<<CLK_CLKSEL3_SC1SEL_Pos) /*!< Setting SC1 clock source as PCLK1 */
#define CLK_CLKSEL3_SC1SEL_HIRC         (0x3UL<<CLK_CLKSEL3_SC1SEL_Pos) /*!< Setting SC1 clock source as HIRC */

#define CLK_CLKSEL3_SC2SEL_HXT          (0x0UL<<CLK_CLKSEL3_SC2SEL_Pos) /*!< Setting SC2 clock source as HXT */
#define CLK_CLKSEL3_SC2SEL_PLL          (0x1UL<<CLK_CLKSEL3_SC2SEL_Pos) /*!< Setting SC2 clock source as PLL */
#define CLK_CLKSEL3_SC2SEL_PCLK0        (0x2UL<<CLK_CLKSEL3_SC2SEL_Pos) /*!< Setting SC2 clock source as PCLK1 */
#define CLK_CLKSEL3_SC2SEL_HIRC         (0x3UL<<CLK_CLKSEL3_SC2SEL_Pos) /*!< Setting SC2 clock source as HIRC */

#define CLK_CLKSEL3_RTCSEL_LXT          (0x0UL<<CLK_CLKSEL3_RTCSEL_Pos)  /*!< Setting RTC clock source as LXT */
#define CLK_CLKSEL3_RTCSEL_LIRC         (0x1UL<<CLK_CLKSEL3_RTCSEL_Pos)  /*!< Setting RTC clock source as LIRC */

#define CLK_CLKSEL3_I2S0SEL_HXT         (0x0UL<<CLK_CLKSEL3_I2S0SEL_Pos) /*!< Setting I2S0 clock source as HXT */
#define CLK_CLKSEL3_I2S0SEL_PLL         (0x1UL<<CLK_CLKSEL3_I2S0SEL_Pos) /*!< Setting I2S0 clock source as PLL */
#define CLK_CLKSEL3_I2S0SEL_PCLK0       (0x2UL<<CLK_CLKSEL3_I2S0SEL_Pos) /*!< Setting I2S0 clock source as PCLK0 */
#define CLK_CLKSEL3_I2S0SEL_HIRC        (0x3UL<<CLK_CLKSEL3_I2S0SEL_Pos) /*!< Setting I2S0 clock source as HIRC */

#define CLK_CLKSEL3_UART2SEL_HXT        (0x0UL<<CLK_CLKSEL3_UART2SEL_Pos) /*!< Setting UART2 clock source as HXT */
#define CLK_CLKSEL3_UART2SEL_PLL        (0x1UL<<CLK_CLKSEL3_UART2SEL_Pos) /*!< Setting UART2 clock source as PLL */
#define CLK_CLKSEL3_UART2SEL_LXT        (0x2UL<<CLK_CLKSEL3_UART2SEL_Pos) /*!< Setting UART2 clock source as LXT */
#define CLK_CLKSEL3_UART2SEL_HIRC       (0x3UL<<CLK_CLKSEL3_UART2SEL_Pos) /*!< Setting UART2 clock source as HIRC */

#define CLK_CLKSEL3_UART3SEL_HXT        (0x0UL<<CLK_CLKSEL3_UART3SEL_Pos) /*!< Setting UART3 clock source as HXT */
#define CLK_CLKSEL3_UART3SEL_PLL        (0x1UL<<CLK_CLKSEL3_UART3SEL_Pos) /*!< Setting UART3 clock source as PLL */
#define CLK_CLKSEL3_UART3SEL_LXT        (0x2UL<<CLK_CLKSEL3_UART3SEL_Pos) /*!< Setting UART3 clock source as LXT */
#define CLK_CLKSEL3_UART3SEL_HIRC       (0x3UL<<CLK_CLKSEL3_UART3SEL_Pos) /*!< Setting UART3 clock source as HIRC */

#define CLK_CLKSEL3_UART4SEL_HXT        (0x0UL<<CLK_CLKSEL3_UART4SEL_Pos) /*!< Setting UART4 clock source as HXT */
#define CLK_CLKSEL3_UART4SEL_PLL        (0x1UL<<CLK_CLKSEL3_UART4SEL_Pos) /*!< Setting UART4 clock source as PLL */
#define CLK_CLKSEL3_UART4SEL_LXT        (0x2UL<<CLK_CLKSEL3_UART4SEL_Pos) /*!< Setting UART4 clock source as LXT */
#define CLK_CLKSEL3_UART4SEL_HIRC       (0x3UL<<CLK_CLKSEL3_UART4SEL_Pos) /*!< Setting UART4 clock source as HIRC */

#define CLK_CLKSEL3_UART5SEL_HXT        (0x0UL<<CLK_CLKSEL3_UART5SEL_Pos) /*!< Setting UART5 clock source as HXT */
#define CLK_CLKSEL3_UART5SEL_PLL        (0x1UL<<CLK_CLKSEL3_UART5SEL_Pos) /*!< Setting UART5 clock source as PLL */
#define CLK_CLKSEL3_UART5SEL_LXT        (0x2UL<<CLK_CLKSEL3_UART5SEL_Pos) /*!< Setting UART5 clock source as LXT */
#define CLK_CLKSEL3_UART5SEL_HIRC       (0x3UL<<CLK_CLKSEL3_UART5SEL_Pos) /*!< Setting UART5 clock source as HIRC */


/*---------------------------------------------------------------------------------------------------------*/
/*  CLKDIV0 constant definitions.                                                                          */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_CLKDIV0_HCLK(x)     (((x)-1UL) << CLK_CLKDIV0_HCLKDIV_Pos)  /*!< CLKDIV0 Setting for HCLK clock divider. It could be 1~16 */
#define CLK_CLKDIV0_USB(x)      (((x)-1UL) << CLK_CLKDIV0_USBDIV_Pos)   /*!< CLKDIV0 Setting for USB clock divider. It could be 1~16 */
#define CLK_CLKDIV0_UART0(x)    (((x)-1UL) << CLK_CLKDIV0_UART0DIV_Pos) /*!< CLKDIV0 Setting for UART0 clock divider. It could be 1~16 */
#define CLK_CLKDIV0_UART1(x)    (((x)-1UL) << CLK_CLKDIV0_UART1DIV_Pos) /*!< CLKDIV0 Setting for UART1 clock divider. It could be 1~16 */
#define CLK_CLKDIV0_EADC(x)     (((x)-1UL) << CLK_CLKDIV0_EADCDIV_Pos)  /*!< CLKDIV0 Setting for EADC clock divider. It could be 1~256 */
#define CLK_CLKDIV0_SDH0(x)     (((x)-1UL) << CLK_CLKDIV0_SDH0DIV_Pos)  /*!< CLKDIV0 Setting for SDH0 clock divider. It could be 1~256 */


/*---------------------------------------------------------------------------------------------------------*/
/*  CLKDIV1 constant definitions.                                                                          */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_CLKDIV1_SC0(x)      (((x)-1UL) << CLK_CLKDIV1_SC0DIV_Pos)  /*!< CLKDIV1 Setting for SC0 clock divider. It could be 1~256 */
#define CLK_CLKDIV1_SC1(x)      (((x)-1UL) << CLK_CLKDIV1_SC1DIV_Pos)  /*!< CLKDIV1 Setting for SC1 clock divider. It could be 1~256 */
#define CLK_CLKDIV1_SC2(x)      (((x)-1UL) << CLK_CLKDIV1_SC2DIV_Pos)  /*!< CLKDIV1 Setting for SC2 clock divider. It could be 1~256 */


/*---------------------------------------------------------------------------------------------------------*/
/*  CLKDIV4 constant definitions.                                                                          */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_CLKDIV4_UART2(x)     (((x)-1UL) << CLK_CLKDIV4_UART2DIV_Pos)  /*!< CLKDIV4 Setting for UART2 clock divider. It could be 1~16 */
#define CLK_CLKDIV4_UART3(x)     (((x)-1UL) << CLK_CLKDIV4_UART3DIV_Pos)  /*!< CLKDIV4 Setting for UART3 clock divider. It could be 1~16 */
#define CLK_CLKDIV4_UART4(x)     (((x)-1UL) << CLK_CLKDIV4_UART4DIV_Pos)  /*!< CLKDIV4 Setting for UART4 clock divider. It could be 1~16 */
#define CLK_CLKDIV4_UART5(x)     (((x)-1UL) << CLK_CLKDIV4_UART5DIV_Pos)  /*!< CLKDIV4 Setting for UART5 clock divider. It could be 1~16 */


/*---------------------------------------------------------------------------------------------------------*/
/*  PCLKDIV constant definitions.                                                                          */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_PCLKDIV_APB0DIV_HCLK            (0x0UL << CLK_PCLKDIV_APB0DIV_Pos)  /*!< PCLKDIV Setting for PCLK0 = HCLK */
#define CLK_PCLKDIV_APB0DIV_HCLK_DIV2       (0x1UL << CLK_PCLKDIV_APB0DIV_Pos)  /*!< PCLKDIV Setting for PCLK0 = 1/2 HCLK */
#define CLK_PCLKDIV_APB0DIV_HCLK_DIV4       (0x2UL << CLK_PCLKDIV_APB0DIV_Pos)  /*!< PCLKDIV Setting for PCLK0 = 1/4 HCLK  */
#define CLK_PCLKDIV_APB0DIV_HCLK_DIV8       (0x3UL << CLK_PCLKDIV_APB0DIV_Pos)  /*!< PCLKDIV Setting for PCLK0 = 1/8 HCLK */
#define CLK_PCLKDIV_APB0DIV_HCLK_DIV16      (0x4UL << CLK_PCLKDIV_APB0DIV_Pos)  /*!< PCLKDIV Setting for PCLK0 = 1/16 HCLK */
#define CLK_PCLKDIV_APB0DIV_HCLK_DIV32      (0x5UL << CLK_PCLKDIV_APB0DIV_Pos)  /*!< PCLKDIV Setting for PCLK0 = 1/32 HCLK */

#define CLK_PCLKDIV_APB1DIV_HCLK            (0x0UL << CLK_PCLKDIV_APB1DIV_Pos)  /*!< PCLKDIV Setting for PCLK1 = HCLK */
#define CLK_PCLKDIV_APB1DIV_HCLK_DIV2       (0x1UL << CLK_PCLKDIV_APB1DIV_Pos)  /*!< PCLKDIV Setting for PCLK1 = 1/2 HCLK */
#define CLK_PCLKDIV_APB1DIV_HCLK_DIV4       (0x2UL << CLK_PCLKDIV_APB1DIV_Pos)  /*!< PCLKDIV Setting for PCLK1 = 1/4 HCLK */
#define CLK_PCLKDIV_APB1DIV_HCLK_DIV8       (0x3UL << CLK_PCLKDIV_APB1DIV_Pos)  /*!< PCLKDIV Setting for PCLK1 = 1/8 HCLK */
#define CLK_PCLKDIV_APB1DIV_HCLK_DIV16      (0x4UL << CLK_PCLKDIV_APB1DIV_Pos)  /*!< PCLKDIV Setting for PCLK1 = 1/16 HCLK */
#define CLK_PCLKDIV_APB1DIV_HCLK_DIV32      (0x5UL << CLK_PCLKDIV_APB1DIV_Pos)  /*!< PCLKDIV Setting for PCLK1 = 1/32 HCLK */


/*---------------------------------------------------------------------------------------------------------*/
/*  PLLCTL constant definitions. PLL = FIN * (2*NF) / NR / NO                                              */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_PLLCTL_PLLSRC_HXT   0x00000000UL    /*!< For PLL clock source is HXT.  2MHz < FIN/NR < 8MHz */
#define CLK_PLLCTL_PLLSRC_HIRC  0x00080000UL    /*!< For PLL clock source is HIRC. 2MHz < FIN/NR < 8MHz */

#define CLK_PLLCTL_NF(x)        ((x)-2UL)         /*!< x must be constant and 2 <= x <= 513. 96MHz < FIN*(2*NF)/NR < 200MHz */
#define CLK_PLLCTL_NR(x)        (((x)-1UL)<<9)    /*!< x must be constant and 2 <= x <= 33.  2MHz < FIN/NR < 8MHz */

#define CLK_PLLCTL_NO_1         0x0000UL        /*!< For output divider is 1 */
#define CLK_PLLCTL_NO_2         0x4000UL        /*!< For output divider is 2 */
#define CLK_PLLCTL_NO_4         0xC000UL        /*!< For output divider is 4 */

#define CLK_PLLCTL_48MHz_HXT    (CLK_PLLCTL_PLLSRC_HXT  | CLK_PLLCTL_NR(2UL) | CLK_PLLCTL_NF(16UL) | CLK_PLLCTL_NO_4) /*!< Predefined PLLCTL setting for 48MHz PLL output with HXT */
#define CLK_PLLCTL_48MHz_HIRC   (CLK_PLLCTL_PLLSRC_HIRC | CLK_PLLCTL_NR(2UL) | CLK_PLLCTL_NF(16UL) | CLK_PLLCTL_NO_4) /*!< Predefined PLLCTL setting for 48MHz PLL output with HIRC */

#define CLK_PLLCTL_64MHz_HXT    (CLK_PLLCTL_PLLSRC_HXT  | CLK_PLLCTL_NR(3UL) | CLK_PLLCTL_NF(16UL) | CLK_PLLCTL_NO_2) /*!< Predefined PLLCTL setting for 64MHz PLL output with HXT */
#define CLK_PLLCTL_64MHz_HIRC   (CLK_PLLCTL_PLLSRC_HIRC | CLK_PLLCTL_NR(3UL) | CLK_PLLCTL_NF(16UL) | CLK_PLLCTL_NO_2) /*!< Predefined PLLCTL setting for 64Hz PLL output with HIRC */

#define CLK_PLLCTL_96MHz_HXT    (CLK_PLLCTL_PLLSRC_HXT  | CLK_PLLCTL_NR(2UL) | CLK_PLLCTL_NF(16UL) | CLK_PLLCTL_NO_2) /*!< Predefined PLLCTL setting for 96MHz PLL output with HXT */
#define CLK_PLLCTL_96MHz_HIRC   (CLK_PLLCTL_PLLSRC_HIRC | CLK_PLLCTL_NR(2UL) | CLK_PLLCTL_NF(16UL) | CLK_PLLCTL_NO_2) /*!< Predefined PLLCTL setting for 96MHz PLL output with HIRC */

#define CLK_PLLCTL_128MHz_HXT    (CLK_PLLCTL_PLLSRC_HXT  | CLK_PLLCTL_NR(3UL) | CLK_PLLCTL_NF(16UL) | CLK_PLLCTL_NO_1) /*!< Predefined PLLCTL setting for 128MHz PLL output with HXT */
#define CLK_PLLCTL_128MHz_HIRC   (CLK_PLLCTL_PLLSRC_HIRC | CLK_PLLCTL_NR(3UL) | CLK_PLLCTL_NF(16UL) | CLK_PLLCTL_NO_1) /*!< Predefined PLLCTL setting for 128MHz PLL output with HIRC */


/*---------------------------------------------------------------------------------------------------------*/
/*  MODULE constant definitions.                                                                           */
/*---------------------------------------------------------------------------------------------------------*/
/* APBCLK(31:30)|CLKSEL(29:28)|CLKSEL_Msk(27:25) |CLKSEL_Pos(24:20)|CLKDIV(19:18)|CLKDIV_Msk(17:10)|CLKDIV_Pos(9:5)|IP_EN_Pos(4:0) */

#define MODULE_APBCLK(x)        (((x) >>30) & 0x3UL)    /*!< Calculate AHBCLK/APBCLK offset on MODULE index, 0x0:AHBCLK, 0x1:APBCLK0, 0x2:APBCLK1 */
#define MODULE_CLKSEL(x)        (((x) >>28) & 0x3UL)    /*!< Calculate CLKSEL offset on MODULE index, 0x0:CLKSEL0, 0x1:CLKSEL1, 0x2:CLKSEL2, 0x3:CLKSEL3 */
#define MODULE_CLKSEL_Msk(x)    (((x) >>25) & 0x7UL)    /*!< Calculate CLKSEL mask offset on MODULE index */
#define MODULE_CLKSEL_Pos(x)    (((x) >>20) & 0x1fUL)   /*!< Calculate CLKSEL position offset on MODULE index */
#define MODULE_CLKDIV(x)        (((x) >>18) & 0x3UL)    /*!< Calculate APBCLK CLKDIV on MODULE index, 0x0:CLKDIV0, 0x1:CLKDIV1, 0x4:CLKDIV4 */
#define MODULE_CLKDIV_Msk(x)    (((x) >>10) & 0xffUL)   /*!< Calculate CLKDIV mask offset on MODULE index */
#define MODULE_CLKDIV_Pos(x)    (((x) >>5 ) & 0x1fUL)   /*!< Calculate CLKDIV position offset on MODULE index */
#define MODULE_IP_EN_Pos(x)     (((x) >>0 ) & 0x1fUL)   /*!< Calculate APBCLK offset on MODULE index */
#define MODULE_NoMsk            0x0UL                     /*!< Not mask on MODULE index */
#define NA                      MODULE_NoMsk              /*!< Not Available */

#define MODULE_APBCLK_ENC(x)        (((x) & 0x03UL) << 30)   /*!< MODULE index, 0x0:AHBCLK, 0x1:APBCLK0, 0x2:APBCLK1 */
#define MODULE_CLKSEL_ENC(x)        (((x) & 0x03UL) << 28)   /*!< CLKSEL offset on MODULE index, 0x0:CLKSEL0, 0x1:CLKSEL1, 0x2:CLKSEL2, 0x3:CLKSEL3 */
#define MODULE_CLKSEL_Msk_ENC(x)    (((x) & 0x07UL) << 25)   /*!< CLKSEL mask offset on MODULE index */
#define MODULE_CLKSEL_Pos_ENC(x)    (((x) & 0x1fUL) << 20)   /*!< CLKSEL position offset on MODULE index */
#define MODULE_CLKDIV_ENC(x)        (((x) & 0x03UL) << 18)   /*!< APBCLK CLKDIV on MODULE index, 0x0:CLKDIV, 0x1:CLKDIV1, 0x4:CLKDIV4 */
#define MODULE_CLKDIV_Msk_ENC(x)    (((x) & 0xffUL) << 10)   /*!< CLKDIV mask offset on MODULE index */
#define MODULE_CLKDIV_Pos_ENC(x)    (((x) & 0x1fUL) <<  5)   /*!< CLKDIV position offset on MODULE index */
#define MODULE_IP_EN_Pos_ENC(x)     (((x) & 0x1fUL) <<  0)   /*!< AHBCLK/APBCLK offset on MODULE index */


/* AHBCLK */
#define PDMA0_MODULE   (MODULE_APBCLK_ENC( 0UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_AHBCLK_PDMA0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< PDMA Module */

#define PDMA1_MODULE   (MODULE_APBCLK_ENC( 0UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_AHBCLK_PDMA1CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< PDMA Module */

#define ISP_MODULE     (MODULE_APBCLK_ENC( 0UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_AHBCLK_ISPCKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< ISP Module */

#define EBI_MODULE     (MODULE_APBCLK_ENC( 0UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_AHBCLK_EBICKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< EBI Module */

#define SDH0_MODULE    (MODULE_APBCLK_ENC( 0UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_AHBCLK_SDH0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 0UL)|MODULE_CLKSEL_Msk_ENC(   3UL)|MODULE_CLKSEL_Pos_ENC(20UL)|\
                        MODULE_CLKDIV_ENC( 0UL)|MODULE_CLKDIV_Msk_ENC(0xFFUL)|MODULE_CLKDIV_Pos_ENC(24UL))/*!< SDH0 Module */

#define CRC_MODULE     (MODULE_APBCLK_ENC( 0UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_AHBCLK_CRCCKEN_Pos)|\
                        MODULE_CLKSEL_ENC( NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC( NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))     /*!< CRC Module */

#define CRPT_MODULE    (MODULE_APBCLK_ENC( 0UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_AHBCLK_CRPTCKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< CRPT Module */

#define USBH_MODULE    (MODULE_APBCLK_ENC( 0UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_AHBCLK_USBHCKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 0UL)|MODULE_CLKSEL_Msk_ENC(  1UL)|MODULE_CLKSEL_Pos_ENC( 8UL)|\
                        MODULE_CLKDIV_ENC( 0UL)|MODULE_CLKDIV_Msk_ENC(0xFUL)|MODULE_CLKDIV_Pos_ENC( 4UL))  /*!< USBH Module */

/* APBCLK0 */
#define WDT_MODULE     (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_WDTCKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 1UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC( 0UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(  NA)|MODULE_CLKDIV_Pos_ENC( NA))    /*!< WDT Module */

#define WWDT_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_WDTCKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 1UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC(30UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(  NA)|MODULE_CLKDIV_Pos_ENC(NA))     /*!< WWDT Module */

#define RTC_MODULE     (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_RTCCKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 3UL)|MODULE_CLKSEL_Msk_ENC( 1UL)|MODULE_CLKSEL_Pos_ENC( 8UL)|\
                        MODULE_CLKDIV_ENC( NA)|MODULE_CLKDIV_Msk_ENC(   NA)|MODULE_CLKDIV_Pos_ENC(NA))     /*!< RTC Module */

#define TMR0_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_TMR0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 1UL)|MODULE_CLKSEL_Msk_ENC( 7UL)|MODULE_CLKSEL_Pos_ENC( 8UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(  NA)|MODULE_CLKDIV_Pos_ENC(  NA))    /*!< TMR0 Module */

#define TMR1_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_TMR1CKEN_Pos) |\
                        MODULE_CLKSEL_ENC( 1UL)|MODULE_CLKSEL_Msk_ENC( 7UL)|MODULE_CLKSEL_Pos_ENC(12UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(   NA))     /*!< TMR1 Module */

#define TMR2_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_TMR2CKEN_Pos) |\
                        MODULE_CLKSEL_ENC( 1UL)|MODULE_CLKSEL_Msk_ENC( 7UL)|MODULE_CLKSEL_Pos_ENC(16UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(    NA))    /*!< TMR2 Module */

#define TMR3_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_TMR3CKEN_Pos) |\
                        MODULE_CLKSEL_ENC( 1UL)|MODULE_CLKSEL_Msk_ENC( 7UL)|MODULE_CLKSEL_Pos_ENC(20UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(   NA))     /*!< TMR3 Module */

#define CLKO_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_CLKOCKEN_Pos) |\
                        MODULE_CLKSEL_ENC( 1UL)|MODULE_CLKSEL_Msk_ENC(3UL)|MODULE_CLKSEL_Pos_ENC(28UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(   NA))     /*!< CLKO Module */

#define ACMP01_MODULE  (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_ACMP01CKEN_Pos) |\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))        /*!< ACMP01 Module */

#define I2C0_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_I2C0CKEN_Pos) |\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))        /*!< I2C0 Module */

#define I2C1_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_I2C1CKEN_Pos) |\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))        /*!< I2C1 Module */

#define I2C2_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_I2C2CKEN_Pos) |\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))        /*!< I2C2 Module */

#define QSPI0_MODULE   (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_QSPI0CKEN_Pos) |\
                        MODULE_CLKSEL_ENC( 2UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC( 2UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(  NA)|MODULE_CLKDIV_Pos_ENC(  NA))    /*!< QSPI0 Module */

#define SPI0_MODULE    (MODULE_APBCLK_ENC(1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_SPI0CKEN_Pos) |\
                        MODULE_CLKSEL_ENC(2UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC( 4UL)|\
                        MODULE_CLKDIV_ENC(NA)|MODULE_CLKDIV_Msk_ENC(   NA)|MODULE_CLKDIV_Pos_ENC(  NA))     /*!< SPI0 Module */

#define SPI1_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_SPI1CKEN_Pos) |\
                        MODULE_CLKSEL_ENC( 2UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC( 6UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(  NA)|MODULE_CLKDIV_Pos_ENC(  NA))    /*!< SPI1 Module */

#define SPI2_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_SPI2CKEN_Pos) |\
                        MODULE_CLKSEL_ENC( 2UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC(10UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(  NA)|MODULE_CLKDIV_Pos_ENC(  NA))    /*!< SPI2 Module */

#define UART0_MODULE   (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_UART0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 1UL)|MODULE_CLKSEL_Msk_ENC(   3UL)|MODULE_CLKSEL_Pos_ENC(24UL)|\
                        MODULE_CLKDIV_ENC( 0UL)|MODULE_CLKDIV_Msk_ENC(0x0FUL)|MODULE_CLKDIV_Pos_ENC( 8UL))    /*!< UART0 Module */

#define UART1_MODULE   (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_UART1CKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 1UL)|MODULE_CLKSEL_Msk_ENC(   3UL)|MODULE_CLKSEL_Pos_ENC(26UL)|\
                        MODULE_CLKDIV_ENC( 0UL)|MODULE_CLKDIV_Msk_ENC(0x0FUL)|MODULE_CLKDIV_Pos_ENC(12UL))  /*!< UART1 Module */

#define UART2_MODULE   (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_UART2CKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 3UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC(24UL)|\
                        MODULE_CLKDIV_ENC( 3UL)|MODULE_CLKDIV_Msk_ENC(0x0FUL)|MODULE_CLKDIV_Pos_ENC( 0UL))  /*!< UART2 Module */

#define UART3_MODULE   (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_UART3CKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 3UL)|MODULE_CLKSEL_Msk_ENC(   3UL)|MODULE_CLKSEL_Pos_ENC(26UL)|\
                        MODULE_CLKDIV_ENC( 3UL)|MODULE_CLKDIV_Msk_ENC(0x0FUL)|MODULE_CLKDIV_Pos_ENC( 4UL))  /*!< UART3 Module */

#define UART4_MODULE   (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_UART4CKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 3UL)|MODULE_CLKSEL_Msk_ENC(   3UL)|MODULE_CLKSEL_Pos_ENC(28UL)|\
                        MODULE_CLKDIV_ENC( 3UL)|MODULE_CLKDIV_Msk_ENC(0x0FUL)|MODULE_CLKDIV_Pos_ENC( 8UL))  /*!< UART4 Module */

#define UART5_MODULE   (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_UART5CKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 3UL)|MODULE_CLKSEL_Msk_ENC(   3UL)|MODULE_CLKSEL_Pos_ENC(30UL)|\
                        MODULE_CLKDIV_ENC( 3UL)|MODULE_CLKDIV_Msk_ENC(0x0FUL)|MODULE_CLKDIV_Pos_ENC(12UL))  /*!< UART5 Module */

#define CAN0_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_CAN0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))        /*!< CAN0 Module */

#define OTG_MODULE     (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_OTGCKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 0UL)|MODULE_CLKSEL_Msk_ENC(  1UL)|MODULE_CLKSEL_Pos_ENC( 8UL)|\
                        MODULE_CLKDIV_ENC( 0UL)|MODULE_CLKDIV_Msk_ENC(0x0FUL)|MODULE_CLKDIV_Pos_ENC( 4UL))  /*!< OTG Module */

#define USBD_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_USBDCKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 0UL)|MODULE_CLKSEL_Msk_ENC(  1UL)|MODULE_CLKSEL_Pos_ENC( 8UL)|\
                        MODULE_CLKDIV_ENC( 0UL)|MODULE_CLKDIV_Msk_ENC(0x0FUL)|MODULE_CLKDIV_Pos_ENC(4UL))   /*!< USBD Module */

#define EADC_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_EADCCKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(    NA)|MODULE_CLKSEL_Pos_ENC(  NA)|\
                        MODULE_CLKDIV_ENC( 0UL)|MODULE_CLKDIV_Msk_ENC(0xFFUL)|MODULE_CLKDIV_Pos_ENC(16UL))  /*!< EADC Module */

#define I2S0_MODULE    (MODULE_APBCLK_ENC( 1UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK0_I2S0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC( 3UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC(16UL)|\
                        MODULE_CLKDIV_ENC( NA)|MODULE_CLKDIV_Msk_ENC(   NA)|MODULE_CLKDIV_Pos_ENC(  NA))    /*!< I2S0 Module */

/* APBCLK1 */
#define SC0_MODULE     (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_SC0CKEN_Pos)  |\
                        MODULE_CLKSEL_ENC( 3UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC( 0UL)|\
                        MODULE_CLKDIV_ENC( 1UL)|MODULE_CLKDIV_Msk_ENC(0xFFUL)|MODULE_CLKDIV_Pos_ENC( 0UL))    /*!< SC0 Module */

#define SC1_MODULE     (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_SC1CKEN_Pos)  |\
                        MODULE_CLKSEL_ENC( 3UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC( 2UL)|\
                        MODULE_CLKDIV_ENC( 1UL)|MODULE_CLKDIV_Msk_ENC(0xFFUL)|MODULE_CLKDIV_Pos_ENC( 8UL))    /*!< SC1 Module */

#define SC2_MODULE     (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_SC2CKEN_Pos)  |\
                        MODULE_CLKSEL_ENC( 3UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC( 4UL)|\
                        MODULE_CLKDIV_ENC( 1UL)|MODULE_CLKDIV_Msk_ENC(0xFFUL)|MODULE_CLKDIV_Pos_ENC(16UL))    /*!< SC2 Module */

#define SPI3_MODULE    (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_SPI3CKEN_Pos)  |\
                        MODULE_CLKSEL_ENC( 2UL)|MODULE_CLKSEL_Msk_ENC( 3UL)|MODULE_CLKSEL_Pos_ENC(12UL)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< SPI3 Module */

#define USCI0_MODULE   (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_USCI0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< USCI0 Module */

#define USCI1_MODULE   (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_USCI1CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< USCI1 Module */

#define DAC_MODULE     (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_DACCKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< DAC Module */

#define EPWM0_MODULE   (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_EPWM0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< EPWM0 Module */

#define EPWM1_MODULE   (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_EPWM1CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< EPWM1 Module */

#define BPWM0_MODULE   (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_BPWM0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< BPWM0 Module */

#define BPWM1_MODULE   (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_BPWM1CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< BPWM1 Module */

#define QEI0_MODULE    (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_QEI0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< QEI0 Module */

#define QEI1_MODULE    (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_QEI1CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< QEI1 Module */

#define TRNG_MODULE     (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_TRNGCKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< TRNG Module */

#define ECAP0_MODULE   (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_ECAP0CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< ECAP0 Module */

#define ECAP1_MODULE   (MODULE_APBCLK_ENC( 2UL)|MODULE_IP_EN_Pos_ENC((uint32_t)CLK_APBCLK1_ECAP1CKEN_Pos)|\
                        MODULE_CLKSEL_ENC(  NA)|MODULE_CLKSEL_Msk_ENC(NA)|MODULE_CLKSEL_Pos_ENC(NA)|\
                        MODULE_CLKDIV_ENC(  NA)|MODULE_CLKDIV_Msk_ENC(NA)|MODULE_CLKDIV_Pos_ENC(NA))      /*!< ECAP1 Module */


/*---------------------------------------------------------------------------------------------------------*/
/*  PDMSEL constant definitions.                                                                           */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_PMUCTL_PDMSEL_PD          (0x0UL << CLK_PMUCTL_PDMSEL_Pos)        /*!< Select Power-down mode is Power-down mode */
#define CLK_PMUCTL_PDMSEL_LLPD        (0x1UL << CLK_PMUCTL_PDMSEL_Pos)        /*!< Select Power-down mode is Low leakage Power-down mode */
#define CLK_PMUCTL_PDMSEL_FWPD        (0x2UL << CLK_PMUCTL_PDMSEL_Pos)        /*!< Select Power-down mode is Fast Wake-up Power-down mode */
#define CLK_PMUCTL_PDMSEL_ULLPD       (0x3UL << CLK_PMUCTL_PDMSEL_Pos)        /*!< Select Power-down mode is Ultra Low leakage Power-down mode */
#define CLK_PMUCTL_PDMSEL_SPD         (0x4UL << CLK_PMUCTL_PDMSEL_Pos)        /*!< Select Power-down mode is Standby Power-down mode */
#define CLK_PMUCTL_PDMSEL_DPD         (0x6UL << CLK_PMUCTL_PDMSEL_Pos)        /*!< Select Power-down mode is Deep Power-down mode */

/*---------------------------------------------------------------------------------------------------------*/
/*  WKTMRIS constant definitions.                                                                          */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_PMUCTL_WKTMRIS_128          (0x0UL << CLK_PMUCTL_WKTMRIS_Pos)     /*!< Select Wake-up Timer Time-out Interval is 128 LIRC clocks (12.8 ms) */
#define CLK_PMUCTL_WKTMRIS_256          (0x1UL << CLK_PMUCTL_WKTMRIS_Pos)     /*!< Select Wake-up Timer Time-out Interval is 256 LIRC clocks (25.6 ms) */
#define CLK_PMUCTL_WKTMRIS_512          (0x2UL << CLK_PMUCTL_WKTMRIS_Pos)     /*!< Select Wake-up Timer Time-out Interval is 512 LIRC clocks (51.2 ms) */
#define CLK_PMUCTL_WKTMRIS_1024         (0x3UL << CLK_PMUCTL_WKTMRIS_Pos)     /*!< Select Wake-up Timer Time-out Interval is 1024 LIRC clocks (102.4ms) */
#define CLK_PMUCTL_WKTMRIS_4096         (0x4UL << CLK_PMUCTL_WKTMRIS_Pos)     /*!< Select Wake-up Timer Time-out Interval is 4096 LIRC clocks (409.6ms) */
#define CLK_PMUCTL_WKTMRIS_8192         (0x5UL << CLK_PMUCTL_WKTMRIS_Pos)     /*!< Select Wake-up Timer Time-out Interval is 8192 LIRC clocks (819.2ms) */
#define CLK_PMUCTL_WKTMRIS_16384        (0x6UL << CLK_PMUCTL_WKTMRIS_Pos)     /*!< Select Wake-up Timer Time-out Interval is 16384 LIRC clocks (1638.4ms) */
#define CLK_PMUCTL_WKTMRIS_65536        (0x7UL << CLK_PMUCTL_WKTMRIS_Pos)     /*!< Select Wake-up Timer Time-out Interval is 65536 LIRC clocks (6553.6ms) */

/*---------------------------------------------------------------------------------------------------------*/
/*  SWKDBCLKSEL constant definitions.                                                                      */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_SWKDBCTL_SWKDBCLKSEL_1          (0x0UL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 1 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_2          (0x1UL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 2 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_4          (0x2UL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 4 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_8          (0x3UL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 8 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_16         (0x4UL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 16 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_32         (0x5UL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 32 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_64         (0x6UL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 64 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_128        (0x7UL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 128 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_256        (0x8UL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 256 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_2x256      (0x9UL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 2x256 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_4x256      (0xaUL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 4x256 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_8x256      (0xbUL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 8x256 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_16x256     (0xcUL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 16x256 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_32x256     (0xdUL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 32x256 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_64x256     (0xeUL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 64x256 clocks */
#define CLK_SWKDBCTL_SWKDBCLKSEL_128x256    (0xfUL << CLK_SWKDBCTL_SWKDBCLKSEL_Pos)     /*!< Select Standby Power-down Pin De-bounce Sampling Cycle is 128x256 clocks */

/*---------------------------------------------------------------------------------------------------------*/
/*  DPD Pin Rising/Falling Edge Wake-up Enable constant definitions.                                       */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_DPDWKPIN_DISABLE     (0x0UL << CLK_PMUCTL_WKPINEN_Pos)     /*!< Disable Wake-up pin at Deep Power-down mode */
#define CLK_DPDWKPIN_RISING      (0x1UL << CLK_PMUCTL_WKPINEN_Pos)     /*!< Enable Wake-up pin rising edge at Deep Power-down mode */
#define CLK_DPDWKPIN_FALLING     (0x2UL << CLK_PMUCTL_WKPINEN_Pos)     /*!< Enable Wake-up pin falling edge at Deep Power-down mode */
#define CLK_DPDWKPIN_BOTHEDGE    (0x3UL << CLK_PMUCTL_WKPINEN_Pos)     /*!< Enable Wake-up pin both edge at Deep Power-down mode */

/*---------------------------------------------------------------------------------------------------------*/
/*  SPD Pin Rising/Falling Edge Wake-up Enable constant definitions.                                       */
/*---------------------------------------------------------------------------------------------------------*/
#define CLK_SPDWKPIN_ENABLE         (0x1UL << 0)     /*!< Enable Standby Power-down Pin Wake-up */
#define CLK_SPDWKPIN_RISING         (0x1UL << 1)     /*!< Standby Power-down Wake-up on Standby Power-down Pin rising edge */
#define CLK_SPDWKPIN_FALLING        (0x1UL << 2)     /*!< Standby Power-down Wake-up on Standby Power-down Pin falling edge */
#define CLK_SPDWKPIN_DEBOUNCEEN     (0x1UL << 8)     /*!< Enable Standby power-down pin De-bounce function */
#define CLK_SPDWKPIN_DEBOUNCEDIS    (0x0UL << 8)     /*!< Disable Standby power-down pin De-bounce function */

#define CLK_DISABLE_WKTMR(void)       (CLK->PMUCTL &= ~CLK_PMUCTL_WKTMREN_Msk)    /*!< Disable Wake-up timer at Standby or Deep Power-down mode \hideinitializer */
#define CLK_ENABLE_WKTMR(void)        (CLK->PMUCTL |= CLK_PMUCTL_WKTMREN_Msk)     /*!< Enable Wake-up timer at Standby or Deep Power-down mode \hideinitializer */
#define CLK_DISABLE_DPDWKPIN(void)    (CLK->PMUCTL &= ~CLK_PMUCTL_WKPINEN_Msk)    /*!< Disable Wake-up pin at Deep Power-down mode \hideinitializer */
#define CLK_DISABLE_SPDACMP(void)     (CLK->PMUCTL &= ~CLK_PMUCTL_ACMPSPWK_Msk)   /*!< Disable ACMP wake-up at Standby Power-down mode \hideinitializer */
#define CLK_ENABLE_SPDACMP(void)      (CLK->PMUCTL |= CLK_PMUCTL_ACMPSPWK_Msk)    /*!< Enable ACMP wake-up at Standby Power-down mode \hideinitializer */
#define CLK_DISABLE_RTCWK(void)       (CLK->PMUCTL &= ~CLK_PMUCTL_RTCWKEN_Msk)    /*!< Disable RTC Wake-up at Standby or Deep Power-down mode \hideinitializer */
#define CLK_ENABLE_RTCWK(void)        (CLK->PMUCTL |= CLK_PMUCTL_RTCWKEN_Msk)     /*!< Enable RTC Wake-up at Standby or Deep Power-down mode \hideinitializer */


/*@}*/ /* end of group CLK_EXPORTED_CONSTANTS */

/** @addtogroup CLK_EXPORTED_FUNCTIONS CLK Exported Functions
  @{
*/


/**
 * @brief       Set Wake-up Timer Time-out Interval
 *
 * @param[in]   u32Interval  The Wake-up Timer Time-out Interval selection. It could be
 *                             - \ref CLK_PMUCTL_WKTMRIS_128
 *                             - \ref CLK_PMUCTL_WKTMRIS_256
 *                             - \ref CLK_PMUCTL_WKTMRIS_512
 *                             - \ref CLK_PMUCTL_WKTMRIS_1024
 *                             - \ref CLK_PMUCTL_WKTMRIS_4096
 *                             - \ref CLK_PMUCTL_WKTMRIS_8192
 *                             - \ref CLK_PMUCTL_WKTMRIS_16384
 *                             - \ref CLK_PMUCTL_WKTMRIS_65536
 *
 * @return      None
 *
 * @details     This function set Wake-up Timer Time-out Interval.
 *
 *
 */
#define CLK_SET_WKTMR_INTERVAL(u32Interval)   (CLK->PMUCTL = (CLK->PMUCTL & (~CLK_PMUCTL_WKTMRIS_Msk)) | (u32Interval))

/**
 * @brief       Set De-bounce Sampling Cycle Time
 *
 * @param[in]   u32CycleSel   The de-bounce sampling cycle selection. It could be
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_1
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_2
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_4
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_8
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_16
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_32
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_64
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_128
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_256
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_2x256
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_4x256
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_8x256
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_16x256
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_32x256
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_64x256
 *                             - \ref CLK_SWKDBCTL_SWKDBCLKSEL_128x256
 *
 * @return      None
 *
 * @details     This function set Set De-bounce Sampling Cycle Time for Standby Power-down pin wake-up.
 *
 *
 */
#define CLK_SET_SPDDEBOUNCETIME(u32CycleSel)    (CLK->SWKDBCTL = (u32CycleSel))

/*---------------------------------------------------------------------------------------------------------*/
/* static inline functions                                                                                 */
/*---------------------------------------------------------------------------------------------------------*/
/* Declare these inline functions here to avoid MISRA C 2004 rule 8.1 error */
__STATIC_INLINE void CLK_SysTickDelay(uint32_t us);
__STATIC_INLINE void CLK_SysTickLongDelay(uint32_t us);


/**
  * @brief      This function execute delay function.
  * @param[in]  us  Delay time. The Max value is (2^24-1) / CPU Clock(MHz). Ex:
  *                             64MHz => 262143us, 48MHz => 349525us ...
  * @return     None
  * @details    Use the SysTick to generate the delay time and the UNIT is in us.
  *             The SysTick clock source is from HCLK, i.e the same as system core clock.
  *             User can use SystemCoreClockUpdate() to calculate CyclesPerUs automatically before using this function.
  */
__STATIC_INLINE void CLK_SysTickDelay(uint32_t us)
{
    SysTick->LOAD = us * CyclesPerUs;
    SysTick->VAL  = (0x0UL);
    SysTick->CTRL = SysTick_CTRL_CLKSOURCE_Msk | SysTick_CTRL_ENABLE_Msk;

    /* Waiting for down-count to zero */
    while((SysTick->CTRL & SysTick_CTRL_COUNTFLAG_Msk) == 0UL)
    {
    }

    /* Disable SysTick counter */
    SysTick->CTRL = 0UL;
}


#if defined (__ARM_FEATURE_CMSE) && (__ARM_FEATURE_CMSE == 3L)

__STATIC_INLINE void CLK_SysTickDelay_NS(uint32_t us);

/**
  * @brief      This function execute delay function.
  * @param[in]  us  Delay time. The Max value is (2^24-1) / CPU Clock(MHz). Ex:
  *                             64MHz => 262143us, 48MHz => 349525us ...
  * @return     None
  * @details    Use the SysTick to generate the delay time and the UNIT is in us.
  *             The SysTick clock source is from HCLK, i.e the same as system core clock.
  *             User can use SystemCoreClockUpdate() to calculate CyclesPerUs automatically before using this function.
  */
__STATIC_INLINE void CLK_SysTickDelay_NS(uint32_t us)
{
    SysTick_NS->LOAD = us * CyclesPerUs;
    SysTick_NS->VAL  = (0x00UL);
    SysTick_NS->CTRL = SysTick_CTRL_CLKSOURCE_Msk | SysTick_CTRL_ENABLE_Msk;

    /* Waiting for down-count to zero */
    while((SysTick_NS->CTRL & SysTick_CTRL_COUNTFLAG_Msk) == 0UL);

    /* Disable SysTick counter */
    SysTick_NS->CTRL = 0UL;
}
#endif /* defined (__ARM_FEATURE_CMSE) && (__ARM_FEATURE_CMSE == 3L) */




/**
  * @brief      This function execute long delay function.
  * @param[in]  us  Delay time.
  * @return     None
  * @details    Use the SysTick to generate the long delay time and the UNIT is in us.
  *             The SysTick clock source is from HCLK, i.e the same as system core clock.
  *             User can use SystemCoreClockUpdate() to calculate CyclesPerUs automatically before using this function.
  */
__STATIC_INLINE void CLK_SysTickLongDelay(uint32_t us)
{
    uint32_t u32Delay;

    /* It should <= 65536us for each delay loop */
    u32Delay = 65536UL;

    do
    {
        if(us > u32Delay)
        {
            us -= u32Delay;
        }
        else
        {
            u32Delay = us;
            us = 0UL;
        }

        SysTick->LOAD = u32Delay * CyclesPerUs;
        SysTick->VAL  = (0x0UL);
        SysTick->CTRL = SysTick_CTRL_CLKSOURCE_Msk | SysTick_CTRL_ENABLE_Msk;

        /* Waiting for down-count to zero */
        while((SysTick->CTRL & SysTick_CTRL_COUNTFLAG_Msk) == 0UL);

        /* Disable SysTick counter */
        SysTick->CTRL = 0UL;

    }
    while(us > 0UL);

}

#if defined (__ARM_FEATURE_CMSE) && (__ARM_FEATURE_CMSE == 3L)

__STATIC_INLINE void CLK_SysTickLongDelay_NS(uint32_t us);

/**
  * @brief      This function execute long delay function.
  * @param[in]  us  Delay time.
  * @return     None
  * @details    Use the SysTick to generate the long delay time and the UNIT is in us.
  *             The SysTick clock source is from HCLK, i.e the same as system core clock.
  *             User can use SystemCoreClockUpdate() to calculate CyclesPerUs automatically before using this function.
  */
__STATIC_INLINE void CLK_SysTickLongDelay_NS(uint32_t us)
{
    uint32_t u32Delay;

    /* It should <= 65536us for each delay loop */
    u32Delay = 65536UL;

    do
    {
        if(us > u32Delay)
        {
            us -= u32Delay;
        }
        else
        {
            u32Delay = us;
            us = 0UL;
        }

        SysTick_NS->LOAD = u32Delay * CyclesPerUs;
        SysTick_NS->VAL  = (0x0UL);
        SysTick_NS->CTRL = SysTick_CTRL_CLKSOURCE_Msk | SysTick_CTRL_ENABLE_Msk;

        /* Waiting for down-count to zero */
        while((SysTick_NS->CTRL & SysTick_CTRL_COUNTFLAG_Msk) == 0UL);

        /* Disable SysTick counter */
        SysTick_NS->CTRL = 0UL;

    }
    while(us > 0UL);

}

#endif /* defined (__ARM_FEATURE_CMSE) && (__ARM_FEATURE_CMSE == 3L) */


void CLK_DisableCKO(void);
void CLK_EnableCKO(uint32_t u32ClkSrc, uint32_t u32ClkDiv, uint32_t u32ClkDivBy1En);
void CLK_PowerDown(void);
void CLK_Idle(void);
uint32_t CLK_GetHXTFreq(void);
uint32_t CLK_GetLXTFreq(void);
uint32_t CLK_GetHCLKFreq(void);
uint32_t CLK_GetPCLK0Freq(void);
uint32_t CLK_GetPCLK1Freq(void);
uint32_t CLK_GetCPUFreq(void);
uint32_t CLK_SetCoreClock(uint32_t u32Hclk);
void CLK_SetHCLK(uint32_t u32ClkSrc, uint32_t u32ClkDiv);
void CLK_SetModuleClock(uint32_t u32ModuleIdx, uint32_t u32ClkSrc, uint32_t u32ClkDiv);
void CLK_SetSysTickClockSrc(uint32_t u32ClkSrc);
void CLK_EnableXtalRC(uint32_t u32ClkMask);
void CLK_DisableXtalRC(uint32_t u32ClkMask);
void CLK_EnableModuleClock(uint32_t u32ModuleIdx);
void CLK_DisableModuleClock(uint32_t u32ModuleIdx);
uint32_t CLK_EnablePLL(uint32_t u32PllClkSrc, uint32_t u32PllFreq);
void CLK_DisablePLL(void);
uint32_t CLK_WaitClockReady(uint32_t u32ClkMask);
void CLK_EnableSysTick(uint32_t u32ClkSrc, uint32_t u32Count);
void CLK_DisableSysTick(void);
void CLK_SetPowerDownMode(uint32_t u32PDMode);
void CLK_EnableDPDWKPin(uint32_t u32TriggerType);
uint32_t CLK_GetPMUWKSrc(void);
void CLK_EnableSPDWKPin(uint32_t u32Port, uint32_t u32Pin, uint32_t u32TriggerType, uint32_t u32DebounceEn);
uint32_t CLK_GetPLLClockFreq(void);
uint32_t CLK_GetModuleClockSource(uint32_t u32ModuleIdx);
uint32_t CLK_GetModuleClockDivider(uint32_t u32ModuleIdx);



/*@}*/ /* end of group CLK_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group CLK_Driver */

/*@}*/ /* end of group Standard_Driver */


#ifdef __cplusplus
}
#endif


#endif /* __CLK_H__ */



/*** (C) COPYRIGHT 2016 Nuvoton Technology Corp. ***/
