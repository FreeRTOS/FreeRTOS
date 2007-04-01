/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief Power Manager driver.
 *
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support email: avr32@atmel.com
 *
 *****************************************************************************/

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


#ifndef _PM_H_
#define _PM_H_

#if __GNUC__
#  include <avr32/io.h>
#elif __ICCAVR32__
#  include <avr32/iouc3a0512.h>
#  include <avr32/uc3a0512.h>
#else
#  error Unknown compiler
#endif

#include "compiler.h"
#include "preprocessor.h"


/*! \brief Sets the MCU in the specified sleep mode.
 *
 * \param mode Sleep mode:
 *   \arg \c AVR32_PM_SMODE_IDLE: Idle;
 *   \arg \c AVR32_PM_SMODE_FROZEN: Frozen;
 *   \arg \c AVR32_PM_SMODE_STANDBY: Standby;
 *   \arg \c AVR32_PM_SMODE_STOP: Stop;
 *   \arg \c AVR32_PM_SMODE_SHUTDOWN: Shutdown (DeepStop);
 *   \arg \c AVR32_PM_SMODE_STATIC: Static.
 */
#define SLEEP(mode)   {__asm__ __volatile__ ("sleep "STRINGZ(mode));}


/*!
 * \brief This function will enable the external clock mode of the oscillator 0.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_enable_osc0_ext_clock(volatile avr32_pm_t *pm);


/*!
 * \brief This function will enable the crystal mode of the oscillator 0.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param fosc0 Oscillator 0 crystal frequency (Hz)
 */
extern void pm_enable_osc0_crystal(volatile avr32_pm_t *pm, unsigned int fosc0);


/*!
 * \brief This function will enable the oscillator 0 to be used with a startup time.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param startup Clock 0 startup time. Time is expressed in term of RCOsc periods (3-bit value)
 */
extern void pm_enable_clk0(volatile avr32_pm_t *pm, unsigned int startup);


/*!
 * \brief This function will disable the oscillator 0.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_disable_clk0(volatile avr32_pm_t *pm);


/*!
 * \brief This function will enable the oscillator 0 to be used with no startup time.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param startup Clock 0 startup time. Time is expressed in term of RCOsc periods (3-bit value) but not checked.
 */
extern void pm_enable_clk0_no_wait(volatile avr32_pm_t *pm, unsigned int startup);


/*!
 * \brief This function will wait until the Osc0 clock is ready.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_wait_for_clk0_ready(volatile avr32_pm_t *pm);


/*!
 * \brief This function will enable the external clock mode of the oscillator 1.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_enable_osc1_ext_clock(volatile avr32_pm_t *pm);


/*!
 * \brief This function will enable the crystal mode of the oscillator 1.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param fosc1 Oscillator 1 crystal frequency (Hz)
 */
extern void pm_enable_osc1_crystal(volatile avr32_pm_t *pm, unsigned int fosc1);


/*!
 * \brief This function will enable the oscillator 1 to be used with a startup time.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param startup Clock 1 startup time. Time is expressed in term of RCOsc periods (3-bit value)
 */
extern void pm_enable_clk1(volatile avr32_pm_t *pm, unsigned int startup);


/*!
 * \brief This function will disable the oscillator 1.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_disable_clk1(volatile avr32_pm_t *pm);


/*!
 * \brief This function will enable the oscillator 1 to be used with no startup time.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param startup Clock 1 startup time. Time is expressed in term of RCOsc periods (3-bit value) but not checked.
 */
extern void pm_enable_clk1_no_wait(volatile avr32_pm_t *pm, unsigned int startup);


/*!
 * \brief This function will wait until the Osc1 clock is ready.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_wait_for_clk1_ready(volatile avr32_pm_t *pm);


/*!
 * \brief This function will enable the external clock mode of the 32-kHz oscillator.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_enable_osc32_ext_clock(volatile avr32_pm_t *pm);


/*!
 * \brief This function will enable the crystal mode of the 32-kHz oscillator.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_enable_osc32_crystal(volatile avr32_pm_t *pm);


/*!
 * \brief This function will enable the oscillator 32 to be used with a startup time.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param startup Clock 32 kHz startup time. Time is expressed in term of RCOsc periods (3-bit value)
 */
extern void pm_enable_clk32(volatile avr32_pm_t *pm, unsigned int startup);


/*!
 * \brief This function will disable the oscillator 32.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_disable_clk32(volatile avr32_pm_t *pm);


/*!
 * \brief This function will enable the oscillator 32 to be used with no startup time.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param startup Clock 32 kHz startup time. Time is expressed in term of RCOsc periods (3-bit value) but not checked.
 */
extern void pm_enable_clk32_no_wait(volatile avr32_pm_t *pm, unsigned int startup);


/*!
 * \brief This function will wait until the osc32 clock is ready.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_wait_for_clk32_ready(volatile avr32_pm_t *pm);


//FIXME update this header -SM
/*!
 * \brief This function will select all the power manager clocks.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param pbadiv Peripheral Bus A clock divisor enable
 * \param pbasel Peripheral Bus A select
 * \param pbbdiv Peripheral Bus B clock divisor enable
 * \param pbbsel Peripheral Bus B select
 * \param hsbdiv High Speed Bus clock divisor enable (CPU clock = HSB clock)
 * \param hsbsel High Speed Bus select (CPU clock = HSB clock )
 */
extern void pm_cksel(volatile avr32_pm_t *pm, unsigned int pbadiv, unsigned int pbasel, unsigned int pbbdiv, unsigned int pbbsel, unsigned int hsbdiv, unsigned int hsbsel);


/*!
 * \brief This function will setup a generic clock.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param gc generic clock number (0 for gc0...)
 * \param osc_or_pll Use OSC (=0) or PLL (=1)
 * \param pll_osc Select Osc0/PLL0 or Osc1/PLL1
 * \param diven Generic clock divisor enable
 * \param div Generic clock divisor
 */
extern void pm_gc_setup(volatile avr32_pm_t *pm, unsigned int gc, unsigned int osc_or_pll, unsigned int pll_osc, unsigned int diven, unsigned int div);


/*!
 * \brief This function will enable a generic clock.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param gc generic clock number (0 for gc0...)
 */
extern void pm_gc_enable(volatile avr32_pm_t *pm, unsigned int gc);


/*!
 * \brief This function will disable a generic clock.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param gc generic clock number (0 for gc0...)
 */
extern void pm_gc_disable(volatile avr32_pm_t *pm, unsigned int gc);


//FIXME update this header -SM
/*!
 * \brief This function will setup a PLL.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param pll PLL number(0 for PLL0, 1 for PLL1)
 * \param mul
 * \param div
 * \param osc
 * \param lockcount
 */
extern void pm_pll_setup(volatile avr32_pm_t *pm, unsigned int pll, unsigned int mul, unsigned int div, unsigned int osc, unsigned int lockcount);


//FIXME update this header -SM
/*!
 * \brief This function will set a PLL option.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param pll PLL number(0 for PLL0, 1 for PLL1)
 * \param pll_freq Set to 1 for VCO frequency range 80-180MHz, set to 0 for VCO frequency range 160-240Mhz.
 * \param pll_div2 Divide the PLL output frequency by 2 (this settings does not change the FVCO value)
 * \param pll_wbwdisable 1 Disable the Wide-Bandith Mode (Wide-Bandwith mode allow a faster startup time and out-of-lock time). 0 to enable the Wide-Bandith Mode.
 */
extern void pm_pll_set_option(volatile avr32_pm_t *pm, unsigned int pll, unsigned int  pll_freq, unsigned int  pll_div2, unsigned int  pll_wbwdisable);


//FIXME update this header -SM
/*!
 * \brief This function will get a PLL option.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param pll PLL number(0 for PLL0, 1 for PLL1)
 * \return       Option
 */
extern unsigned int pm_pll_get_option(volatile avr32_pm_t *pm, unsigned int pll);


/*!
 * \brief This function will enable a PLL.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param pll PLL number(0 for PLL0, 1 for PLL1)
 */
extern void pm_pll_enable(volatile avr32_pm_t *pm, unsigned int pll);


/*!
 * \brief This function will disable a PLL.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param pll PLL number(0 for PLL0, 1 for PLL1)
 */
extern void pm_pll_disable(volatile avr32_pm_t *pm, unsigned int pll);


/*!
 * \brief This function will wait for PLL0 locked
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_wait_for_pll0_locked(volatile avr32_pm_t *pm);


/*!
 * \brief This function will wait for PLL1 locked
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 */
extern void pm_wait_for_pll1_locked(volatile avr32_pm_t *pm);


/*!
 * \brief This function will switch the power manager main clock.
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param clock Clock to be switched on. AVR32_PM_MCSEL_SLOW for RCOsc, AVR32_PM_MCSEL_OSC0 for Osc0, AVR32_PM_MCSEL_PLL0 for PLL0.
 */
extern void pm_switch_to_clock(volatile avr32_pm_t *pm, unsigned long clock);


/*!
 * \brief Switch main clock to clock Osc0 (crystal mode)
 * \param pm Base address of the Power Manager (i.e. &AVR32_PM)
 * \param fosc0 Oscillator 0 crystal frequency (Hz)
 * \param startup Crystal 0 startup time. Time is expressed in term of RCOsc periods (3-bit value)
 */
extern void pm_switch_to_osc0(volatile avr32_pm_t *pm, unsigned int fosc0, unsigned int startup);


#endif  // _PM_H_
