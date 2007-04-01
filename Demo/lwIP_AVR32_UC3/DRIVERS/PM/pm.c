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


#include "pm.h"


void pm_enable_osc0_ext_clock(volatile avr32_pm_t *pm)
{
  union {
    unsigned long                  oscctrl0;
    avr32_pm_oscctrl0_t            OSCCTRL0;
  } oscctrl0 ;
  // Read
  oscctrl0.oscctrl0 = pm->oscctrl0;
  // Modify
  oscctrl0.OSCCTRL0.mode = AVR32_PM_OSCCTRL0_MODE_EXT_CLOCK;
  // Write
  pm->oscctrl0 = oscctrl0.oscctrl0;
}


void pm_enable_osc0_crystal(volatile avr32_pm_t *pm, unsigned int fosc0)
{
  union {
    unsigned long                  oscctrl0;
    avr32_pm_oscctrl0_t            OSCCTRL0;
  } oscctrl0 ;
  // Read
  oscctrl0.oscctrl0 = pm->oscctrl0;
  // Modify
  oscctrl0.OSCCTRL0.mode = (fosc0 < 8000000) ? AVR32_PM_OSCCTRL0_MODE_CRYSTAL_G2 :
                                               AVR32_PM_OSCCTRL0_MODE_CRYSTAL_G3;
  // Write
  pm->oscctrl0 = oscctrl0.oscctrl0;
}


void pm_enable_clk0(volatile avr32_pm_t *pm, unsigned int startup)
{
  union {
    avr32_pm_mcctrl_t    MCCTRL;
    unsigned long        mcctrl;
  } mcctrl;
  union {
    unsigned long                  oscctrl0;
    avr32_pm_oscctrl0_t            OSCCTRL0;
  } oscctrl0 ;

  // Read register
  mcctrl.mcctrl     = pm->mcctrl;
  oscctrl0.oscctrl0 = pm->oscctrl0;
  // Modify
  mcctrl.MCCTRL.osc0en = 1;
  oscctrl0.OSCCTRL0.startup = startup;
  // Write back
  pm->oscctrl0 = oscctrl0.oscctrl0;
  pm->mcctrl   = mcctrl.mcctrl;

  while(!pm->ISR.osc0rdy); //For osc output valid
}


void pm_disable_clk0(volatile avr32_pm_t *pm)
{
  union {
    avr32_pm_mcctrl_t    MCCTRL;
    unsigned long        mcctrl;
  } mcctrl;

  // Read register
  mcctrl.mcctrl      = pm->mcctrl;

  // Modify
  mcctrl.MCCTRL.osc0en = 0;

  // Write back
  pm->mcctrl   = mcctrl.mcctrl;
}


void pm_enable_clk0_no_wait(volatile avr32_pm_t *pm, unsigned int startup)
{
  union {
    avr32_pm_mcctrl_t    MCCTRL;
    unsigned long        mcctrl;
  } mcctrl;
  union {
    unsigned long                  oscctrl0;
    avr32_pm_oscctrl0_t            OSCCTRL0;
  } oscctrl0 ;

  // Read register
  mcctrl.mcctrl      = pm->mcctrl;
  oscctrl0.oscctrl0  = pm->oscctrl0;
  // Modify
  mcctrl.MCCTRL.osc0en = 1;
  oscctrl0.OSCCTRL0.startup=startup;
  // Write back
  pm->mcctrl   = mcctrl.mcctrl;
  pm->oscctrl0 = oscctrl0.oscctrl0;
}


void pm_wait_for_clk0_ready(volatile avr32_pm_t *pm)
{
  while(!pm->ISR.osc0rdy);
}


void pm_enable_osc1_ext_clock(volatile avr32_pm_t *pm)
{
  union {
    unsigned long                  oscctrl1;
    avr32_pm_oscctrl1_t            OSCCTRL1;
  } oscctrl1 ;
  // Read
  oscctrl1.oscctrl1= pm->oscctrl1;
  // Modify
  oscctrl1.OSCCTRL1.mode = AVR32_PM_OSCCTRL1_MODE_EXT_CLOCK;
  // Write
  pm->oscctrl1 = oscctrl1.oscctrl1;
}


void pm_enable_osc1_crystal(volatile avr32_pm_t *pm, unsigned int fosc1)
{
  union {
    unsigned long                  oscctrl1;
    avr32_pm_oscctrl1_t            OSCCTRL1;
  } oscctrl1 ;
  // Read
  oscctrl1.oscctrl1= pm->oscctrl1;
  // Modify
  oscctrl1.OSCCTRL1.mode = (fosc1 < 8000000) ? AVR32_PM_OSCCTRL1_MODE_CRYSTAL_G2 :
                                               AVR32_PM_OSCCTRL1_MODE_CRYSTAL_G3;
  // Write
  pm->oscctrl1 = oscctrl1.oscctrl1;
}


void pm_enable_clk1(volatile avr32_pm_t *pm, unsigned int startup)
{
  union {
    avr32_pm_mcctrl_t    MCCTRL;
    unsigned long        mcctrl;
  } mcctrl;
  union {
    unsigned long                  oscctrl1;
    avr32_pm_oscctrl1_t            OSCCTRL1;
  } oscctrl1 ;

  // Read register
  mcctrl.mcctrl      = pm->mcctrl;
  oscctrl1.oscctrl1  = pm->oscctrl1;

  mcctrl.MCCTRL.osc1en = 1;
  oscctrl1.OSCCTRL1.startup=startup;
  // Write back
  pm->oscctrl1 = oscctrl1.oscctrl1;
  pm->mcctrl   = mcctrl.mcctrl;

  while(!pm->ISR.osc1rdy);
}


void pm_disable_clk1(volatile avr32_pm_t *pm)
{
  union {
    avr32_pm_mcctrl_t    MCCTRL;
    unsigned long        mcctrl;
  } mcctrl;


  // Read register
  mcctrl.mcctrl      = pm->mcctrl;

  // Modify
  mcctrl.MCCTRL.osc1en = 0;

  // Write back
  pm->mcctrl   = mcctrl.mcctrl;
}


void pm_enable_clk1_no_wait(volatile avr32_pm_t *pm, unsigned int startup)
{
  union {
    avr32_pm_mcctrl_t    MCCTRL;
    unsigned long        mcctrl;
  } mcctrl;
  union {
    unsigned long                  oscctrl1;
    avr32_pm_oscctrl1_t            OSCCTRL1;
  } oscctrl1 ;

  // Read register
  mcctrl.mcctrl      = pm->mcctrl;
  oscctrl1.oscctrl1  = pm->oscctrl1;

  mcctrl.MCCTRL.osc1en = 1;
  oscctrl1.OSCCTRL1.startup=startup;
  // Write back
  pm->oscctrl1 = oscctrl1.oscctrl1;
  pm->mcctrl   = mcctrl.mcctrl;
}


void pm_wait_for_clk1_ready(volatile avr32_pm_t *pm)
{
  while(!pm->ISR.osc1rdy);
}


void pm_enable_osc32_ext_clock(volatile avr32_pm_t *pm)
{
  union {
    unsigned long           oscctrl32;
    avr32_pm_oscctrl32_t    OSCCTRL32;
  } u_ctrl;
  u_ctrl.oscctrl32 = pm->oscctrl32;
  u_ctrl.OSCCTRL32.mode = AVR32_PM_OSCCTRL32_MODE_EXT_CLOCK;
  pm->oscctrl32 = u_ctrl.oscctrl32;
}


void pm_enable_osc32_crystal(volatile avr32_pm_t *pm)
{
  union {
    unsigned long           oscctrl32;
    avr32_pm_oscctrl32_t    OSCCTRL32;
  } u_ctrl;
  u_ctrl.oscctrl32 = pm->oscctrl32;
  u_ctrl.OSCCTRL32.mode = AVR32_PM_OSCCTRL32_MODE_CRYSTAL;
  pm->oscctrl32 = u_ctrl.oscctrl32;
}


void pm_enable_clk32(volatile avr32_pm_t *pm, unsigned int startup)
{
  union {
    unsigned long                   oscctrl32;
    avr32_pm_oscctrl32_t            OSCCTRL32;
  } oscctrl32 ;

  // Read register
  oscctrl32.oscctrl32  = pm->oscctrl32;
  // Modify
  oscctrl32.OSCCTRL32.osc32en = 1;
  oscctrl32.OSCCTRL32.startup=startup;
  // Write back
  pm->oscctrl32 = oscctrl32.oscctrl32;

  while(!pm->ISR.osc32rdy);
}


void pm_disable_clk32(volatile avr32_pm_t *pm)
{
  // To get rid of a GCC bug
  // This makes C code longer, but not ASM
    union {
    unsigned long                   oscctrl32;
    avr32_pm_oscctrl32_t            OSCCTRL32;
  } oscctrl32 ;

  // Read register
  oscctrl32.oscctrl32  = pm->oscctrl32;
  // Modify
  oscctrl32.OSCCTRL32.osc32en = 0;
  // Write back
  pm->oscctrl32 = oscctrl32.oscctrl32;
}


void pm_enable_clk32_no_wait(volatile avr32_pm_t *pm, unsigned int startup)
{
  union {
    unsigned long                  oscctrl32;
    avr32_pm_oscctrl32_t           OSCCTRL32;
  } oscctrl32 ;

  // Read register
  oscctrl32.oscctrl32  = pm->oscctrl32;
  // Modify
  oscctrl32.OSCCTRL32.osc32en = 1;
  oscctrl32.OSCCTRL32.startup=startup;
  // Write back
  pm->oscctrl32 = oscctrl32.oscctrl32;
}


void pm_wait_for_clk32_ready(volatile avr32_pm_t *pm)
{
  // To get rid of a GCC bug
  // This makes C code longer, but not ASM

  while(!pm->ISR.osc32rdy);
}


void pm_cksel(volatile avr32_pm_t *pm,
              unsigned int pbadiv,
              unsigned int pbasel,
              unsigned int pbbdiv,
              unsigned int pbbsel,
              unsigned int hsbdiv,
              unsigned int hsbsel)
{
  // Force the compiler to generate only one 32 bits access
  union {
    avr32_pm_cksel_t selval ;
    unsigned long uword32;
  } cksel;

  cksel.uword32 = 0;

  cksel.selval.cpudiv = hsbdiv;
  cksel.selval.cpusel = hsbsel;
  cksel.selval.hsbdiv = hsbdiv;
  cksel.selval.hsbsel = hsbsel;
  cksel.selval.pbbdiv = pbbdiv;
  cksel.selval.pbbsel = pbbsel;
  cksel.selval.pbadiv = pbadiv;
  cksel.selval.pbasel = pbasel;

  pm->cksel = cksel.uword32;

  // Wait for ckrdy bit and then clear it
  while(!(pm->ISR.ckrdy));

  return;
}


void pm_gc_setup(volatile avr32_pm_t *pm,
                  unsigned int gc,
                  unsigned int osc_or_pll, // Use Osc (=0) or PLL (=1)
                  unsigned int pll_osc, // Sel Osc0/PLL0 or Osc1/PLL1
                  unsigned int diven,
                  unsigned int div) {
  union {
    unsigned long                  gcctrl;
    avr32_pm_gcctrl_t              GCCTRL;
  } u_gc;

  u_gc.GCCTRL.oscsel = pll_osc;
  u_gc.GCCTRL.pllsel = osc_or_pll;
  u_gc.GCCTRL.diven  = diven;
  u_gc.GCCTRL.div    = div;
  u_gc.GCCTRL.cen    = 0; // Disable GC first
  pm->gcctrl[gc] = u_gc.gcctrl;
}


void pm_gc_enable(volatile avr32_pm_t *pm,
                  unsigned int gc) {
  union {
    unsigned long                  gcctrl;
    avr32_pm_gcctrl_t              GCCTRL;
  } u_gc;
  u_gc.gcctrl = pm->gcctrl[gc];
  u_gc.GCCTRL.cen = 1;
  pm->gcctrl[gc] = u_gc.gcctrl;
}


void pm_gc_disable(volatile avr32_pm_t *pm,
                   unsigned int gc) {
  union {
    unsigned long                  gcctrl;
    avr32_pm_gcctrl_t              GCCTRL;
  } u_gc;
  u_gc.gcctrl = pm->gcctrl[gc];
  u_gc.GCCTRL.cen = 0;
  pm->gcctrl[gc] = u_gc.gcctrl;
}


void pm_pll_setup(volatile avr32_pm_t *pm,
                  unsigned int pll,
                  unsigned int mul,
                  unsigned int div,
                  unsigned int osc,
                  unsigned int lockcount) {

  union {
    unsigned long                  pll    ;
    avr32_pm_pll_t                 PLL    ;
  } u_pll;

  u_pll.pll=0;

  u_pll.PLL.pllmul   = mul;
  u_pll.PLL.plldiv   = div;
  u_pll.PLL.pllosc   = osc;
  u_pll.PLL.pllcount = lockcount;

  u_pll.PLL.pllopt   = 0;

  u_pll.PLL.plltest  = 0;

  (pm->pll)[pll] = u_pll.pll;
}


void pm_pll_set_option(volatile avr32_pm_t *pm,
                       unsigned int pll,
                       unsigned int pll_freq,
                       unsigned int pll_div2,
                       unsigned int pll_wbwdisable) {
  union {
    unsigned long                  pll    ;
    avr32_pm_pll_t                 PLL    ;
  } u_pll;

  u_pll.pll = (pm->pll)[pll];
  u_pll.PLL.pllopt = pll_freq | (pll_div2<<1) | (pll_wbwdisable<<2);
  (pm->pll)[pll] = u_pll.pll;
}


unsigned int pm_pll_get_option(volatile avr32_pm_t *pm,
                               unsigned int pll) {
  return (pm->PLL)[pll].pllopt;
}


void pm_pll_enable(volatile avr32_pm_t *pm,
                  unsigned int pll) {
  union {
    unsigned long                  pll    ;
    avr32_pm_pll_t                 PLL    ;
  } u_pll;

  u_pll.pll = (pm->pll)[pll];
  u_pll.PLL.pllen = 1;
  (pm->pll)[pll] = u_pll.pll;
}


void pm_pll_disable(volatile avr32_pm_t *pm,
                  unsigned int pll) {
  union {
    unsigned long                  pll    ;
    avr32_pm_pll_t                 PLL    ;
  } u_pll;

  u_pll.pll = (pm->pll)[pll];
  u_pll.PLL.pllen = 0;
  (pm->pll)[pll] = u_pll.pll;
}


void pm_wait_for_pll0_locked(volatile avr32_pm_t *pm)
{
  while(!pm->ISR.lock0);

  // Bypass the lock signal of the PLL
  pm->pll[0] |= AVR32_PM_PLL0_PLLBPL_MASK;
}


void pm_wait_for_pll1_locked(volatile avr32_pm_t *pm)
{
  while(!pm->ISR.lock1);

  // Bypass the lock signal of the PLL
  pm->pll[1] |= AVR32_PM_PLL1_PLLBPL_MASK;
}


void pm_switch_to_clock(volatile avr32_pm_t *pm, unsigned long clock)
{
  union {
    avr32_pm_mcctrl_t    MCCTRL;
    unsigned long        mcctrl;
  } mcctrl;
  // Read
  mcctrl.mcctrl      = pm->mcctrl;
  // Modify
  mcctrl.MCCTRL.mcsel = clock;
  // Write Back
  pm->MCCTRL.mcsel = mcctrl.mcctrl;
}


void pm_switch_to_osc0(volatile avr32_pm_t *pm, unsigned int fosc0, unsigned int startup)
{
  pm_enable_osc0_crystal(pm, fosc0);            // Enable the Osc0 in crystal mode
  pm_enable_clk0(pm, startup);                  // Crystal startup time - This parameter is critical and depends on the characteristics of the crystal
  pm_switch_to_clock(pm, AVR32_PM_MCSEL_OSC0);  // Then switch main clock to Osc0
}


void pm_bod_enable_irq(volatile struct avr32_pm_t *pm) {

  union {
          unsigned long                  ier ;
          avr32_pm_ier_t                 IER ;
  } u_ier;
  u_ier.ier = 0;
  u_ier.IER.boddet = 1;

  pm->ier  = u_ier.ier;
}


void pm_bod_disable_irq(volatile struct avr32_pm_t *pm) {

  union {
          unsigned long                idr ;
          avr32_pm_idr_t               IDR ;
  } u_idr;
  u_idr.idr = 0;
  u_idr.IDR.boddet = 1;

  pm->idr  = u_idr.idr;
}


void pm_bod_clear_irq(volatile struct avr32_pm_t *pm) {

  union {
          unsigned long                icr ;
          avr32_pm_idr_t               ICR ;
  } u_icr;
  u_icr.icr = 0;
  u_icr.ICR.boddet = 1;

  pm->icr  = u_icr.icr;
}


unsigned long pm_bod_get_irq_status(volatile struct avr32_pm_t *pm) {

  return pm->ISR.boddet;
}


unsigned long pm_bod_get_irq_enable_bit(volatile struct avr32_pm_t *pm) {

  return pm->IMR.boddet;
}


unsigned long pm_bod_get_level(volatile avr32_pm_t *pm) {
  union {
    unsigned long                  bod   ;
    avr32_pm_bod_t                 BOD   ;
  } u_bod;

  u_bod.bod = pm->bod;

  return (unsigned long) u_bod.BOD.level;

}


void pm_write_gplp(volatile avr32_pm_t *pm,unsigned long gplp, unsigned long value) {
  (pm->gplp)[gplp] = value;

}


unsigned long pm_read_gplp(volatile avr32_pm_t *pm,unsigned long gplp) {

  return (pm->gplp)[gplp];
}
