/**************************************************************************//**
 * @file
 * @brief EBI implementation of Board Control interface
 *        This implementation works for devices w/o LCD display on the
 *        MCU module, specifically the EFM32_G2xx_DK development board
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

/**************************************************************************//**
 * @brief Configure EBI (external bus interface) for Board Control register
 * access
 *****************************************************************************/
void DVK_EBI_configure(void)
{
  GPIO_TypeDef *gpio = GPIO;
  EBI_TypeDef  *ebi  = EBI;
  CMU_TypeDef  *cmu  = CMU;

  /* Run time check if we have EBI on-chip capability on this device */
  switch ((DEVINFO->PART & _DEVINFO_PART_DEVICE_NUMBER_MASK) >>
          _DEVINFO_PART_DEVICE_NUMBER_SHIFT)
  {
  /* Only device types EFM32G 280/290/880 and 890 have EBI capability */
  case 280:
  case 290:
  case 880:
  case 890:
    break;
  default:
    /* This device do not have EBI capability - use SPI to interface DVK */
    /* With high probability your project has been configured for an */
    /* incorrect part number. */
    while (1) ;
  }

  /* Enable clocks */
  cmu->HFCORECLKEN0 |= CMU_HFCORECLKEN0_EBI;
  cmu->HFPERCLKEN0  |= CMU_HFPERCLKEN0_GPIO;

  /* Configure bus connect PC bit 12 active low */
  gpio->P[2].MODEH |=
    GPIO_P_MODEH_MODE12_PUSHPULL;

  gpio->P[2].DOUT &= ~(1UL << 12);

  /* Configure GPIO pins as push pull */
  /* EBI AD9..15 */
  gpio->P[0].MODEL |=
    (GPIO_P_MODEL_MODE0_PUSHPULL |
     GPIO_P_MODEL_MODE1_PUSHPULL |
     GPIO_P_MODEL_MODE2_PUSHPULL |
     GPIO_P_MODEL_MODE3_PUSHPULL |
     GPIO_P_MODEL_MODE4_PUSHPULL |
     GPIO_P_MODEL_MODE5_PUSHPULL |
     GPIO_P_MODEL_MODE6_PUSHPULL);
  /* EBI AD8 */
  gpio->P[0].MODEH |=
    GPIO_P_MODEH_MODE15_PUSHPULL;
  /* EBI CS0-CS3 */
  gpio->P[3].MODEH |=
    (GPIO_P_MODEH_MODE9_PUSHPULL | 
     GPIO_P_MODEH_MODE10_PUSHPULL |
     GPIO_P_MODEH_MODE11_PUSHPULL |
     GPIO_P_MODEH_MODE12_PUSHPULL);
  /* EBI AD0..7 */
  gpio->P[4].MODEH |=
    (GPIO_P_MODEH_MODE8_PUSHPULL |
     GPIO_P_MODEH_MODE9_PUSHPULL |
     GPIO_P_MODEH_MODE10_PUSHPULL |
     GPIO_P_MODEH_MODE11_PUSHPULL |
     GPIO_P_MODEH_MODE12_PUSHPULL |
     GPIO_P_MODEH_MODE13_PUSHPULL |
     GPIO_P_MODEH_MODE14_PUSHPULL |
     GPIO_P_MODEH_MODE15_PUSHPULL);
  /* EBI ARDY/ALEN/Wen/Ren */
  gpio->P[5].MODEL |=
    (GPIO_P_MODEL_MODE2_PUSHPULL |
     GPIO_P_MODEL_MODE3_PUSHPULL |
     GPIO_P_MODEL_MODE4_PUSHPULL |
     GPIO_P_MODEL_MODE5_PUSHPULL);

  /* Configure EBI controller */
  /* 16 bit address, 16 bit data mode */
  /* Enable bank 0 address map 0x80000000, FPGA Flash */
  /* Enable bank 1 address map 0x84000000, FPGA SRAM */
  /* Enable bank 2 address map 0x88000000, FPGA TFT Display (SSD2119) */
  /* Enable bank 3 address map 0x8c000000, FPGA Board Control Registers */
  ebi->CTRL =
    EBI_CTRL_MODE_D16A16ALE |
    EBI_CTRL_BANK0EN |
    EBI_CTRL_BANK1EN |
    EBI_CTRL_BANK2EN |
    EBI_CTRL_BANK3EN;

  /* Setup and hold time */
  ebi->ADDRTIMING = 3 << _EBI_ADDRTIMING_ADDRHOLD_SHIFT | 3 << _EBI_ADDRTIMING_ADDRSET_SHIFT;

  /* Default values for all write timing registers, read timing conservative */
  ebi->RDTIMING = 7 << _EBI_RDTIMING_RDSTRB_SHIFT | 3 << _EBI_RDTIMING_RDHOLD_SHIFT | 3 << _EBI_RDTIMING_RDSETUP_SHIFT;
  ebi->WRTIMING = 7 << _EBI_WRTIMING_WRSTRB_SHIFT | 3 << _EBI_WRTIMING_WRHOLD_SHIFT | 3 << _EBI_WRTIMING_WRSETUP_SHIFT;
  ebi->POLARITY = _EBI_POLARITY_RESETVALUE;

  /* Toggle on all chip selects for all banks */
  ebi->ROUTE =
    EBI_ROUTE_CS0PEN |
    EBI_ROUTE_CS1PEN |
    EBI_ROUTE_CS2PEN |
    EBI_ROUTE_CS3PEN |
    EBI_ROUTE_ALEPEN |
    EBI_ROUTE_EBIPEN;
}


/**************************************************************************//**
 * @brief Initialize EBI
 * access
 *****************************************************************************/
void DVK_EBI_init(void)
{
  uint16_t ebiMagic;
  int      ctr;
  volatile int i;

  /* Configure EBI */
  DVK_EBI_configure();
  /* Verify that EBI access is working, if not kit is in SPI mode and needs to
   * be configured for EBI access */
  ebiMagic = DVK_EBI_readRegister(BC_MAGIC);
  if (ebiMagic != BC_MAGIC_VALUE)
  {
    /* Disable EBI */
    DVK_EBI_disable();
    /* Enable SPI interface */
    DVK_SPI_init();
    /* Set EBI mode - after this SPI access will no longer be available */
    DVK_SPI_writeRegister(BC_CFG, BC_CFG_EBI);
    /* Disable SPI */
    DVK_SPI_disable();
    /* Now setup EBI again */
    DVK_EBI_configure();
    /* Wait until ready */
    ctr = 0;
    do {
      /* Check if FPGA responds */
      ebiMagic = DVK_EBI_readRegister(BC_MAGIC);
      ctr++;
      DVK_EBI_writeRegister(BC_LED, ctr);
    } while (ebiMagic != BC_MAGIC_VALUE);
  }
}

/**************************************************************************//**
 * @brief Disable EBI interface, free all GPIO pins
 *****************************************************************************/
void DVK_EBI_disable(void)
{
  GPIO_TypeDef *gpio = GPIO;
  EBI_TypeDef  *ebi  = EBI;
  CMU_TypeDef  *cmu  = CMU;

  /* Toggle off all chip selects for all banks */
  ebi->ROUTE = _EBI_ROUTE_RESETVALUE;

  /* Disable EBI controller */
  ebi->CTRL = _EBI_CTRL_RESETVALUE;

  /* Disable EBI clock */
  cmu->HFCORECLKEN0 &= ~(CMU_HFCORECLKEN0_EBI);

  /* Disable EBI _BC_BUS_CONNECT */
  gpio->P[2].MODEH &= ~(_GPIO_P_MODEH_MODE12_MASK);

  /* Configure GPIO pins as disabled */
  gpio->P[0].MODEL &= ~(
    _GPIO_P_MODEL_MODE0_MASK |
    _GPIO_P_MODEL_MODE1_MASK |
    _GPIO_P_MODEL_MODE2_MASK |
    _GPIO_P_MODEL_MODE3_MASK |
    _GPIO_P_MODEL_MODE4_MASK |
    _GPIO_P_MODEL_MODE5_MASK |
    _GPIO_P_MODEL_MODE6_MASK);
  gpio->P[0].MODEH &= ~(_GPIO_P_MODEH_MODE15_MASK);
  gpio->P[3].MODEH &= ~(
    _GPIO_P_MODEH_MODE9_MASK|    
    _GPIO_P_MODEH_MODE10_MASK|
    _GPIO_P_MODEH_MODE11_MASK|
    _GPIO_P_MODEH_MODE12_MASK
    );
  gpio->P[4].MODEH &= ~(
    _GPIO_P_MODEH_MODE8_MASK |
    _GPIO_P_MODEH_MODE9_MASK |
    _GPIO_P_MODEH_MODE10_MASK |
    _GPIO_P_MODEH_MODE11_MASK |
    _GPIO_P_MODEH_MODE12_MASK |
    _GPIO_P_MODEH_MODE13_MASK |
    _GPIO_P_MODEH_MODE14_MASK |
    _GPIO_P_MODEH_MODE15_MASK);
  gpio->P[5].MODEL &= ~(
    _GPIO_P_MODEL_MODE2_MASK |
    _GPIO_P_MODEL_MODE3_MASK |
    _GPIO_P_MODEL_MODE4_MASK |
    _GPIO_P_MODEL_MODE5_MASK);
}

/**************************************************************************//**
 * @brief Write data into 16-bit board control register
 * @param addr Address to board control register
 * @param data Data to write into register
 *****************************************************************************/
void DVK_EBI_writeRegister(volatile uint16_t *addr, uint16_t data)
{
  *addr = data;
}

/**************************************************************************//**
 * @brief Write data into 16-bit board control register
 * @param addr Register to read from
 *****************************************************************************/
uint16_t DVK_EBI_readRegister(volatile uint16_t *addr)
{
  return *addr;
}
