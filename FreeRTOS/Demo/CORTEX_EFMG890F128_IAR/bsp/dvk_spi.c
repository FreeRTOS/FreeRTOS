/**************************************************************************//**
 * @file
 * @brief SPI implementation of Board Control interface
 *        This implementation use the USART2 SPI interface to control board
 *        control registers. It works
 * @author Energy Micro AS
 * @version 1.0.1
 ******************************************************************************
 * @section License
 * <b>(C) Copyright 2009 Energy Micro AS, http://www.energymicro.com</b>
 ******************************************************************************
 *
 * This source code is the property of Energy Micro AS. The source and compiled
 * code may only be used on Energy Micro "EFM32" microcontrollers.
 *
 * This copyright notice may not be removed from the source code nor changed.
 *
 * DISCLAIMER OF WARRANTY/LIMITATION OF REMEDIES: Energy Micro AS has no
 * obligation to support this Software. Energy Micro AS is providing the
 * Software "AS IS", with no express or implied warranties of any kind,
 * including, but not limited to, any implied warranties of merchantability
 * or fitness for any particular purpose or warranties against infringement
 * of any proprietary rights of a third party.
 *
 * Energy Micro AS will not be liable for any consequential, incidental, or
 * special damages, or any other relief, or for any claim by any third party,
 * arising from your use of this Software.
 *
 *****************************************************************************/

#include "efm32.h"
#include "dvk.h"
#include "dvk_bcregisters.h"

#define clear_bit(reg, bit)    (reg &= ~(1 << bit))

static volatile uint16_t *lastAddr = 0;

/**************************************************************************//**
 * @brief  Initializes USART2 SPI interface for access to FPGA registers
 *         for board control
 *****************************************************************************/
static void spiInit(void)
{
  USART_TypeDef  *usart = USART2;
  GPIO_TypeDef   *gpio  = GPIO;
  uint32_t       clk, spidiv;
  const uint32_t baudrate = 7000000;
  const uint32_t div      = (2 * baudrate / 256);

  /* Configure SPI bus connect pins */
  gpio->P[2].MODEH &= ~(_GPIO_P_MODEH_MODE13_MASK);
  gpio->P[2].MODEH |= (GPIO_P_MODEH_MODE13_PUSHPULL);
  gpio->P[2].DOUT &= ~(1UL << 13);

  /* Configure SPI pins */
  gpio->P[2].MODEL &= ~(_GPIO_P_MODEL_MODE2_MASK |
                        _GPIO_P_MODEL_MODE3_MASK |
                        _GPIO_P_MODEL_MODE4_MASK |
                        _GPIO_P_MODEL_MODE5_MASK);
  gpio->P[2].MODEL |= (GPIO_P_MODEL_MODE2_PUSHPULL |
                       GPIO_P_MODEL_MODE3_PUSHPULL |
                       GPIO_P_MODEL_MODE4_PUSHPULL |
                       GPIO_P_MODEL_MODE5_PUSHPULL);
  gpio->P[2].DOUT |= (1UL << 5);

  /* Configure USART2 as SPI master with manual CS */
  /* Get peripheral clock - ensure updated SystemCoreClock */
  SystemCoreClockUpdate();
  clk = (SystemCoreClock >> ((CMU->HFPERCLKDIV & _CMU_HFPERCLKDIV_HFPERCLKDIV_MASK) >>
                             _CMU_HFPERCLKDIV_HFPERCLKDIV_SHIFT));
  /* Drive spi at max 7Mhz or half clockrate if core freq < 14Mhz */
  if (clk < 14000000)
  {
    spidiv = 0;
  }
  else
  {
    spidiv = (clk) / (div) - 256;
  }

  /* Never allow higher frequency than specified, round up 1/4 div */
  if (spidiv & 0x3f) spidiv += 0x40;

  usart->CLKDIV = spidiv;
  usart->CTRL   = USART_CTRL_SYNC;
  usart->CMD    = USART_CMD_CLEARRX | USART_CMD_CLEARTX;
  usart->ROUTE  = USART_ROUTE_TXPEN | USART_ROUTE_RXPEN | USART_ROUTE_CLKPEN;
  usart->CMD    = USART_CMD_MASTEREN | USART_CMD_TXEN | USART_CMD_RXEN;
}

/**************************************************************************//**
 * @brief  Disables GPIO pins and USART2 from FPGA register access
 *****************************************************************************/
static void spiDisable(void)
{
  USART_TypeDef *usart = USART2;
  GPIO_TypeDef  *gpio  = GPIO;

  /* Disable USART2 */
  usart->CTRL  = _USART_CTRL_RESETVALUE;
  usart->ROUTE = _USART_ROUTE_RESETVALUE;
  usart->CMD   = USART_CMD_MASTERDIS | USART_CMD_TXDIS | USART_CMD_RXDIS;

  /* Disable SPI pins */
  gpio->P[2].MODEH &= ~(_GPIO_P_MODEH_MODE13_MASK);
  gpio->P[2].MODEL &= ~(_GPIO_P_MODEL_MODE2_MASK |
                        _GPIO_P_MODEL_MODE3_MASK |
                        _GPIO_P_MODEL_MODE4_MASK |
                        _GPIO_P_MODEL_MODE5_MASK);
}

/**************************************************************************//**
 * @brief  Performs USART2 SPI Transfer
 *****************************************************************************/
static uint16_t spiAccess(uint8_t spiadr, uint8_t rw, uint16_t spidata)
{
  USART_TypeDef *usart = USART2;
  GPIO_TypeDef  *gpio  = GPIO;
  uint16_t      tmp;

  clear_bit(gpio->P[2].DOUT, 5);

  /* SPI address */
  usart->TXDATA = (spiadr & 0x3) | rw << 3;
  while (!(usart->STATUS & USART_STATUS_TXC)) ;
  tmp = (usart->RXDATA) << 0;

  /* SPI data LSB */
  usart->TXDATA = spidata & 0xFF;
  while (!(usart->STATUS & USART_STATUS_TXC)) ;
  tmp = (usart->RXDATA);

  /* SPI data MSB */
  usart->TXDATA = spidata >> 8;
  while (!(usart->STATUS & USART_STATUS_TXC)) ;
  tmp |= (usart->RXDATA) << 8;

  gpio->P[2].DOUT |= (1 << 5);

  return tmp;
}

/**************************************************************************//**
 * @brief  Performs USART2 SPI write to FPGA register
 * @param spiadr Address of register
 * @param spidata Data to write
 *****************************************************************************/
static void spiWrite(uint8_t spiadr, uint16_t spidata)
{
  spiAccess(spiadr, 0, spidata);
}

/**************************************************************************//**
 * @brief  Performs USART2 SPI read from FPGA register
 * @param spiadr Address of register
 * @param spidata Dummy data
 *****************************************************************************/
static uint16_t spiRead(uint8_t spiadr, uint16_t spidata)
{
  return spiAccess(spiadr, 1, spidata);
}

/**************************************************************************//**
 * @brief  Initializes DVK register access
 *****************************************************************************/
void DVK_SPI_init(void)
{
  uint16_t spiMagic;

  spiInit();
  /* Read "board control Magic" register to verify SPI is up and running */
  /*  if not FPGA is configured to be in EBI mode  */

  spiMagic = DVK_SPI_readRegister(BC_MAGIC);
  if (spiMagic != BC_MAGIC_VALUE)
  {
    /* Development Kit is configured to use EBI mode, restart of kit required */
    /* to use USART2-SPI for configuration */
    spiDisable();
    while (1) ;
  }
}

/**************************************************************************//**
 * @brief  Disable and free up resources used by SPI board control access
 *****************************************************************************/
void DVK_SPI_disable(void)
{
  spiDisable();
}

/**************************************************************************//**
 * @brief  Perform read from DVK board control register
 * @param  addr Address of register to read from
 *****************************************************************************/
uint16_t DVK_SPI_readRegister(volatile uint16_t *addr)
{
  uint16_t data;

  if (addr != lastAddr)
  {
    spiWrite(0x00, 0xFFFF & ((uint32_t) addr));             /*LSBs of address*/
    spiWrite(0x01, 0xFF & ((uint32_t) addr >> 16));         /*MSBs of address*/
    spiWrite(0x02, (0x0C000000 & (uint32_t) addr) >> 26);   /*Chip select*/
  }
  /* Read twice */
  data     = spiRead(0x03, 0);
  data     = spiRead(0x03, 0);
  lastAddr = addr;
  return data;
}

/**************************************************************************//**
 * @brief  Perform write to DVK board control register
 * @param addr Address of register to write to
 * @param data 16-bit to  write into register
 *****************************************************************************/
void DVK_SPI_writeRegister(volatile uint16_t *addr, uint16_t data)
{
  if (addr != lastAddr)
  {
    spiWrite(0x00, 0xFFFF & ((uint32_t) addr));             /*LSBs of address*/
    spiWrite(0x01, 0xFF & ((uint32_t) addr >> 16));         /*MSBs of address*/
    spiWrite(0x02, (0x0C000000 & (uint32_t) addr) >> 26);   /*Chip select*/
  }
  spiWrite(0x03, data);                                     /*Data*/
  lastAddr = addr;
}
