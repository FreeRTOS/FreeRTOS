/*This file is prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief USART driver for AVR32 UC3.
 *
 * This file contains basic functions for the AVR32 USART, with support for all
 * modes, settings and clock speeds.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices with a USART module can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 ******************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


#include "usart.h"


//------------------------------------------------------------------------------
/*! \name Private Functions
 */
//! @{


/*! \brief Checks if the USART is in multidrop mode.
 *
 * \param usart Base address of the USART instance.
 *
 * \return \c 1 if the USART is in multidrop mode, otherwise \c 0.
 */
#if __GNUC__
__attribute__((__always_inline__))
#endif
static __inline__ int usart_mode_is_multidrop(volatile avr32_usart_t *usart)
{
  return ((usart->mr >> AVR32_USART_MR_PAR_OFFSET) & AVR32_USART_MR_PAR_MULTI) == AVR32_USART_MR_PAR_MULTI;
}


/*! \brief Calculates a clock divider (\e CD) that gets the USART as close to a
 *         wanted baudrate as possible.
 *
 * \todo manage the FP fractal part to avoid big errors
 *
 * Baudrate calculation:
 * \f$ baudrate = \frac{Selected Clock}{16 \times CD} \f$ with 16x oversampling or
 * \f$ baudrate = \frac{Selected Clock}{8 \times CD} \f$ with 8x oversampling or
 * \f$ baudrate = \frac{Selected Clock}{CD} \f$ with SYNC bit set to allow high speed.
 *
 * \param usart     Base address of the USART instance.
 * \param baudrate  Wanted baudrate.
 * \param pba_hz    USART module input clock frequency (PBA clock, Hz).
 *
 * \retval USART_SUCCESS        Baudrate successfully initialized.
 * \retval USART_INVALID_INPUT  Wanted baudrate is impossible with given clock speed.
 */

static int usart_set_baudrate(volatile avr32_usart_t *usart, unsigned int baudrate, long pba_hz)
{
  // Clock divider.
  int cd;

  // Baudrate calculation.
  if (baudrate < pba_hz / 16)
  {
    // Use 16x oversampling, clear SYNC bit.
    usart->mr &=~ (AVR32_USART_MR_OVER_MASK | AVR32_USART_MR_SYNC_MASK);
    cd = (pba_hz + 8 * baudrate) / (16 * baudrate); 

    if ((cd >65535)) return USART_INVALID_INPUT;
  }
  else if (baudrate < pba_hz / 8)
  {
    // Use 8x oversampling.
    usart->mr |= AVR32_USART_MR_OVER_MASK;
    // clear SYNC bit
    usart->mr &=~ AVR32_USART_MR_SYNC_MASK;
        
    cd = (pba_hz + 4 * baudrate) / (8 * baudrate);

    if ((cd < 1)||(cd >65535)) return USART_INVALID_INPUT;
  }
  else
  {
    // set SYNC to 1 
    usart->mr |= AVR32_USART_MR_SYNC_MASK;
    // use PBA/BaudRate
    cd = (pba_hz / baudrate);    
  }
  usart->brgr = cd << AVR32_USART_BRGR_CD_OFFSET;

  return USART_SUCCESS;
}

//! @}


//------------------------------------------------------------------------------
/*! \name Initialization Functions
 */
//! @{


void usart_reset(volatile avr32_usart_t *usart)
{
  // Disable all USART interrupts.
  // Interrupts needed should be set explicitly on every reset.
  usart->idr = 0xFFFFFFFF;

  // Reset mode and other registers that could cause unpredictable behavior after reset.
  usart->mr = 0;
  usart->rtor = 0;
  usart->ttgr = 0;

  // Shutdown TX and RX (will be re-enabled when setup has successfully completed),
  // reset status bits and turn off DTR and RTS.
  usart->cr = AVR32_USART_CR_RSTRX_MASK   |
              AVR32_USART_CR_RSTTX_MASK   |
              AVR32_USART_CR_RSTSTA_MASK  |
              AVR32_USART_CR_RSTIT_MASK   |
              AVR32_USART_CR_RSTNACK_MASK |
              AVR32_USART_CR_DTRDIS_MASK  |
              AVR32_USART_CR_RTSDIS_MASK;
}


int usart_init_rs232(volatile avr32_usart_t *usart, const usart_options_t *opt, long pba_hz)
{
  // Reset the USART and shutdown TX and RX.
  usart_reset(usart);

  // Check input values.
  if (!opt) // Null pointer.
    return USART_INVALID_INPUT;
  if (opt->charlength < 5 || opt->charlength > 9 ||
      opt->paritytype > 7 ||
      opt->stopbits > 2 + 255 ||
      opt->channelmode > 3)
    return USART_INVALID_INPUT;

  if (usart_set_baudrate(usart, opt->baudrate, pba_hz) == USART_INVALID_INPUT)
    return USART_INVALID_INPUT;

  if (opt->charlength == 9)
  {
    // Character length set to 9 bits. MODE9 dominates CHRL.
    usart->mr |= AVR32_USART_MR_MODE9_MASK;
  }
  else
  {
    // CHRL gives the character length (- 5) when MODE9 = 0.
    usart->mr |= (opt->charlength - 5) << AVR32_USART_MR_CHRL_OFFSET;
  }

  usart->mr |= (opt->channelmode << AVR32_USART_MR_CHMODE_OFFSET) |
               (opt->paritytype << AVR32_USART_MR_PAR_OFFSET);

  if (opt->stopbits > USART_2_STOPBITS)
  {
    // Set two stop bits
    usart->mr |= AVR32_USART_MR_NBSTOP_2 << AVR32_USART_MR_NBSTOP_OFFSET;
    // and a timeguard period gives the rest.
    usart->ttgr = opt->stopbits - USART_2_STOPBITS;
  }
  else
    // Insert 1, 1.5 or 2 stop bits.
    usart->mr |= opt->stopbits << AVR32_USART_MR_NBSTOP_OFFSET;

  // Setup complete; enable communication.
  // Enable input and output.
  usart->cr |= AVR32_USART_CR_TXEN_MASK |
               AVR32_USART_CR_RXEN_MASK;

  return USART_SUCCESS;
}


int usart_init_hw_handshaking(volatile avr32_usart_t *usart, const usart_options_t *opt, long pba_hz)
{
  // First: Setup standard RS232.
  if (usart_init_rs232(usart, opt, pba_hz) == USART_INVALID_INPUT)
    return USART_INVALID_INPUT;

  // Clear previous mode.
  usart->mr &= ~AVR32_USART_MR_MODE_MASK;
  // Hardware handshaking.
  usart->mr |= USART_MODE_HW_HSH << AVR32_USART_MR_MODE_OFFSET;

  return USART_SUCCESS;
}


int usart_init_IrDA(volatile avr32_usart_t *usart, const usart_options_t *opt,
                    long pba_hz, unsigned char irda_filter)
{
  // First: Setup standard RS232.
  if (usart_init_rs232(usart, opt, pba_hz) == USART_INVALID_INPUT)
    return USART_INVALID_INPUT;

  // Set IrDA counter.
  usart->ifr = irda_filter;

  // Activate "low-pass filtering" of input.
  usart->mr |= AVR32_USART_MR_FILTER_MASK;

  return USART_SUCCESS;
}


int usart_init_modem(volatile avr32_usart_t *usart, const usart_options_t *opt, long pba_hz)
{
  // First: Setup standard RS232.
  if (usart_init_rs232(usart, opt, pba_hz) == USART_INVALID_INPUT)
    return USART_INVALID_INPUT;

  // Clear previous mode.
  usart->mr &= ~AVR32_USART_MR_MODE_MASK;
  // Set modem mode.
  usart->mr |= USART_MODE_MODEM << AVR32_USART_MR_MODE_OFFSET;

  return USART_SUCCESS;
}


int usart_init_rs485(volatile avr32_usart_t *usart, const usart_options_t *opt, long pba_hz)
{
  // First: Setup standard RS232.
  if (usart_init_rs232(usart, opt, pba_hz) == USART_INVALID_INPUT)
    return USART_INVALID_INPUT;

  // Clear previous mode.
  usart->mr &= ~AVR32_USART_MR_MODE_MASK;
  // Set RS485 mode.
  usart->mr |= USART_MODE_RS485 << AVR32_USART_MR_MODE_OFFSET;

  return USART_SUCCESS;
}


int usart_init_iso7816(volatile avr32_usart_t *usart, const iso7816_options_t *opt, int t, long pba_hz)
{
  // Reset the USART and shutdown TX and RX.
  usart_reset(usart);

  // Check input values.
  if (!opt) // Null pointer.
    return USART_INVALID_INPUT;

  if (t == 0)
  {
    // Set USART mode to ISO7816, T=0.
    // The T=0 protocol always uses 2 stop bits.
    usart->mr = (USART_MODE_ISO7816_T0 << AVR32_USART_MR_MODE_OFFSET) |
                (AVR32_USART_MR_NBSTOP_2 << AVR32_USART_MR_NBSTOP_OFFSET) |
                (opt->bit_order << AVR32_USART_MR_MSBF_OFFSET); // Allow MSBF in T=0.
  }
  else if (t == 1)
  {
    // Only LSB first in the T=1 protocol.
    // max_iterations field is only used in T=0 mode.
    if (opt->bit_order != 0 ||
        opt->max_iterations != 0)
      return USART_INVALID_INPUT;
    // Set USART mode to ISO7816, T=1.
    // The T=1 protocol always uses 1 stop bit.
    usart->mr = (USART_MODE_ISO7816_T1 << AVR32_USART_MR_MODE_OFFSET) |
                (AVR32_USART_MR_NBSTOP_1 << AVR32_USART_MR_NBSTOP_OFFSET);
  }
  else
    return USART_INVALID_INPUT;

  if (usart_set_baudrate(usart, opt->iso7816_hz, pba_hz) == USART_INVALID_INPUT)
    return USART_INVALID_INPUT;

  // Set FIDI register: bit rate = selected clock/FI_DI_ratio/16.
  usart->fidi = opt->fidi_ratio;
  // Set ISO7816 spesific options in the MODE register.
  usart->mr |= (opt->inhibit_nack << AVR32_USART_MR_INACK_OFFSET) |
               (opt->dis_suc_nack << AVR32_USART_MR_DSNACK_OFFSET) |
               (opt->max_iterations << AVR32_USART_MR_MAX_ITERATION_OFFSET) |
               AVR32_USART_MR_CLKO_MASK;  // Enable clock output.

  // Setup complete; enable input.
  // Leave TX disabled for now.
  usart->cr |= AVR32_USART_CR_RXEN_MASK;

  return USART_SUCCESS;
}
//! @}


//------------------------------------------------------------------------------
/*! \name Transmit/Receive Functions
 */
//! @{


int usart_send_address(volatile avr32_usart_t *usart, int address)
{
  // Check if USART is in multidrop / RS485 mode.
  if (!usart_mode_is_multidrop(usart)) return USART_MODE_FAULT;

  // Prepare to send an address.
  usart->cr |= AVR32_USART_CR_SENDA_MASK;

  // Write the address to TX.
  usart_bw_write_char(usart, address);

  return USART_SUCCESS;
}


int usart_write_char(volatile avr32_usart_t *usart, int c)
{
  if (usart->csr & AVR32_USART_CSR_TXRDY_MASK)
  {
    usart->thr = c;
    return USART_SUCCESS;
  }
  else
    return USART_TX_BUSY;
}


int usart_putchar(volatile avr32_usart_t *usart, int c)
{
  int timeout = USART_DEFAULT_TIMEOUT;

  if (c == '\n')
  {
    do
    {
      if (!timeout--) return USART_FAILURE;
    } while (usart_write_char(usart, '\r') != USART_SUCCESS);

    timeout = USART_DEFAULT_TIMEOUT;
  }

  do
  {
    if (!timeout--) return USART_FAILURE;
  } while (usart_write_char(usart, c) != USART_SUCCESS);

  return USART_SUCCESS;
}


int usart_read_char(volatile avr32_usart_t *usart, int *c)
{
  // Check for errors: frame, parity and overrun. In RS485 mode, a parity error
  // would mean that an address char has been received.
  if (usart->csr & (AVR32_USART_CSR_OVRE_MASK |
                    AVR32_USART_CSR_FRAME_MASK |
                    AVR32_USART_CSR_PARE_MASK))
    return USART_RX_ERROR;

  // No error; if we really did receive a char, read it and return SUCCESS.
  if (usart->csr & AVR32_USART_CSR_RXRDY_MASK)
  {
    *c = (unsigned short)usart->rhr;
    return USART_SUCCESS;
  }
  else
    return USART_RX_EMPTY;
}


int usart_getchar(volatile avr32_usart_t *usart)
{
  int c, ret;

  while ((ret = usart_read_char(usart, &c)) == USART_RX_EMPTY);

  if (ret == USART_RX_ERROR)
    return USART_FAILURE;

  return c;
}


void usart_write_line(volatile avr32_usart_t *usart, const char *string)
{
  while (*string != '\0')
    usart_putchar(usart, *string++);
}


int usart_get_echo_line(volatile avr32_usart_t *usart)
{
  int rx_char;
  int retval = USART_SUCCESS;

  while (1)
  {
    rx_char = usart_getchar(usart);
    if (rx_char == USART_FAILURE)
    {
      usart_write_line(usart, "Error!!!\n");
      break;
    }
    if (rx_char == '\x03')
    {
      retval = USART_FAILURE;
      break;
    }
    usart_putchar(usart, rx_char);
    if (rx_char == '\r')
    {
      usart_putchar(usart, '\n');
      break;
    }
  }

  return retval;
}


//! @}
