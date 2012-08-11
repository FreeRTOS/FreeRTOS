//  ----------------------------------------------------------------------------
//          ATMEL Microcontroller Software Support  -  ROUSSET  -
//  ----------------------------------------------------------------------------
//  Copyright (c) 2006, Atmel Corporation
// 
//  All rights reserved.
// 
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions are met:
// 
//  - Redistributions of source code must retain the above copyright notice,
//  this list of conditions and the disclaimer below.
// 
//  - Redistributions in binary form must reproduce the above copyright notice,
//  this list of conditions and the disclaimer below in the documentation and/or
//  other materials provided with the distribution. 
// 
//  Atmel's name may not be used to endorse or promote products derived from
//  this software without specific prior written permission. 
//  
//  DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
//  IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
//  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
//  DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
//  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
//  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
//  OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
//  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
//  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
//  EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//  ----------------------------------------------------------------------------
// File Name           : AT91SAM9XE512.h
// Object              : AT91SAM9XE512 definitions
// Generated           : AT91 SW Application Group  02/13/2008 (18:25:59)
// 
// CVS Reference       : /AT91SAM9XE512.pl/1.16/Wed Jan 30 14:02:22 2008//
// CVS Reference       : /SYS_SAM9260.pl/1.2/Wed Feb 13 13:29:23 2008//
// CVS Reference       : /HMATRIX1_SAM9260.pl/1.7/Mon Apr 23 10:39:45 2007//
// CVS Reference       : /CCR_SAM9260.pl/1.2/Mon Apr 16 10:47:39 2007//
// CVS Reference       : /PMC_SAM9262.pl/1.4/Mon Mar  7 18:03:13 2005//
// CVS Reference       : /ADC_6051C.pl/1.1/Mon Jan 31 13:12:40 2005//
// CVS Reference       : /HSDRAMC1_6100A.pl/1.2/Mon Aug  9 10:52:25 2004//
// CVS Reference       : /HSMC3_6105A.pl/1.4/Tue Nov 16 09:16:23 2004//
// CVS Reference       : /AIC_6075A.pl/1.1/Mon Jul 12 17:04:01 2004//
// CVS Reference       : /PDC_6074C.pl/1.2/Thu Feb  3 09:02:11 2005//
// CVS Reference       : /DBGU_6059D.pl/1.1/Mon Jan 31 13:54:41 2005//
// CVS Reference       : /PIO_6057A.pl/1.2/Thu Feb  3 10:29:42 2005//
// CVS Reference       : /RSTC_6098A.pl/1.3/Thu Nov  4 13:57:00 2004//
// CVS Reference       : /SHDWC_6122A.pl/1.3/Wed Oct  6 14:16:58 2004//
// CVS Reference       : /RTTC_6081A.pl/1.2/Thu Nov  4 13:57:22 2004//
// CVS Reference       : /PITC_6079A.pl/1.2/Thu Nov  4 13:56:22 2004//
// CVS Reference       : /WDTC_6080A.pl/1.3/Thu Nov  4 13:58:52 2004//
// CVS Reference       : /EFC2_IGS036.pl/1.2/Fri Nov 10 10:47:53 2006//
// CVS Reference       : /TC_6082A.pl/1.7/Wed Mar  9 16:31:51 2005//
// CVS Reference       : /MCI_6101E.pl/1.1/Fri Jun  3 13:20:23 2005//
// CVS Reference       : /TWI_6061B.pl/1.2/Fri Aug  4 08:53:02 2006//
// CVS Reference       : /US_6089C.pl/1.1/Mon Jan 31 13:56:02 2005//
// CVS Reference       : /SSC_6078A.pl/1.1/Tue Jul 13 07:10:41 2004//
// CVS Reference       : /SPI_6088D.pl/1.3/Fri May 20 14:23:02 2005//
// CVS Reference       : /EMACB_6119A.pl/1.6/Wed Jul 13 15:25:00 2005//
// CVS Reference       : /UDP_6ept_puon.pl/1.1/Wed Aug 30 14:20:53 2006//
// CVS Reference       : /UHP_6127A.pl/1.1/Wed Feb 23 16:03:17 2005//
// CVS Reference       : /EBI_SAM9260.pl/1.1/Fri Sep 30 12:12:14 2005//
// CVS Reference       : /HECC_6143A.pl/1.1/Wed Feb  9 17:16:57 2005//
// CVS Reference       : /ISI_xxxxx.pl/1.3/Thu Mar  3 11:11:48 2005//
//  ----------------------------------------------------------------------------

#ifndef AT91SAM9XE512_H
#define AT91SAM9XE512_H

#ifndef __ASSEMBLY__
typedef volatile unsigned int AT91_REG;// Hardware register definition
#define AT91_CAST(a) (a)
#else
#define AT91_CAST(a)
#endif

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR System Peripherals
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_SYS {
	AT91_REG	 Reserved0[2560]; 	// 
	AT91_REG	 ECC_CR; 	//  ECC reset register
	AT91_REG	 ECC_MR; 	//  ECC Page size register
	AT91_REG	 ECC_SR; 	//  ECC Status register
	AT91_REG	 ECC_PR; 	//  ECC Parity register
	AT91_REG	 ECC_NPR; 	//  ECC Parity N register
	AT91_REG	 Reserved1[58]; 	// 
	AT91_REG	 ECC_VR; 	//  ECC Version register
	AT91_REG	 Reserved2[64]; 	// 
	AT91_REG	 SDRAMC_MR; 	// SDRAM Controller Mode Register
	AT91_REG	 SDRAMC_TR; 	// SDRAM Controller Refresh Timer Register
	AT91_REG	 SDRAMC_CR; 	// SDRAM Controller Configuration Register
	AT91_REG	 SDRAMC_HSR; 	// SDRAM Controller High Speed Register
	AT91_REG	 SDRAMC_LPR; 	// SDRAM Controller Low Power Register
	AT91_REG	 SDRAMC_IER; 	// SDRAM Controller Interrupt Enable Register
	AT91_REG	 SDRAMC_IDR; 	// SDRAM Controller Interrupt Disable Register
	AT91_REG	 SDRAMC_IMR; 	// SDRAM Controller Interrupt Mask Register
	AT91_REG	 SDRAMC_ISR; 	// SDRAM Controller Interrupt Mask Register
	AT91_REG	 SDRAMC_MDR; 	// SDRAM Memory Device Register
	AT91_REG	 Reserved3[118]; 	// 
	AT91_REG	 SMC_SETUP0; 	//  Setup Register for CS 0
	AT91_REG	 SMC_PULSE0; 	//  Pulse Register for CS 0
	AT91_REG	 SMC_CYCLE0; 	//  Cycle Register for CS 0
	AT91_REG	 SMC_CTRL0; 	//  Control Register for CS 0
	AT91_REG	 SMC_SETUP1; 	//  Setup Register for CS 1
	AT91_REG	 SMC_PULSE1; 	//  Pulse Register for CS 1
	AT91_REG	 SMC_CYCLE1; 	//  Cycle Register for CS 1
	AT91_REG	 SMC_CTRL1; 	//  Control Register for CS 1
	AT91_REG	 SMC_SETUP2; 	//  Setup Register for CS 2
	AT91_REG	 SMC_PULSE2; 	//  Pulse Register for CS 2
	AT91_REG	 SMC_CYCLE2; 	//  Cycle Register for CS 2
	AT91_REG	 SMC_CTRL2; 	//  Control Register for CS 2
	AT91_REG	 SMC_SETUP3; 	//  Setup Register for CS 3
	AT91_REG	 SMC_PULSE3; 	//  Pulse Register for CS 3
	AT91_REG	 SMC_CYCLE3; 	//  Cycle Register for CS 3
	AT91_REG	 SMC_CTRL3; 	//  Control Register for CS 3
	AT91_REG	 SMC_SETUP4; 	//  Setup Register for CS 4
	AT91_REG	 SMC_PULSE4; 	//  Pulse Register for CS 4
	AT91_REG	 SMC_CYCLE4; 	//  Cycle Register for CS 4
	AT91_REG	 SMC_CTRL4; 	//  Control Register for CS 4
	AT91_REG	 SMC_SETUP5; 	//  Setup Register for CS 5
	AT91_REG	 SMC_PULSE5; 	//  Pulse Register for CS 5
	AT91_REG	 SMC_CYCLE5; 	//  Cycle Register for CS 5
	AT91_REG	 SMC_CTRL5; 	//  Control Register for CS 5
	AT91_REG	 SMC_SETUP6; 	//  Setup Register for CS 6
	AT91_REG	 SMC_PULSE6; 	//  Pulse Register for CS 6
	AT91_REG	 SMC_CYCLE6; 	//  Cycle Register for CS 6
	AT91_REG	 SMC_CTRL6; 	//  Control Register for CS 6
	AT91_REG	 SMC_SETUP7; 	//  Setup Register for CS 7
	AT91_REG	 SMC_PULSE7; 	//  Pulse Register for CS 7
	AT91_REG	 SMC_CYCLE7; 	//  Cycle Register for CS 7
	AT91_REG	 SMC_CTRL7; 	//  Control Register for CS 7
	AT91_REG	 Reserved4[96]; 	// 
	AT91_REG	 MATRIX_MCFG0; 	//  Master Configuration Register 0 (ram96k)     
	AT91_REG	 MATRIX_MCFG1; 	//  Master Configuration Register 1 (rom)    
	AT91_REG	 MATRIX_MCFG2; 	//  Master Configuration Register 2 (hperiphs) 
	AT91_REG	 MATRIX_MCFG3; 	//  Master Configuration Register 3 (ebi)
	AT91_REG	 MATRIX_MCFG4; 	//  Master Configuration Register 4 (bridge)    
	AT91_REG	 MATRIX_MCFG5; 	//  Master Configuration Register 5 (mailbox)    
	AT91_REG	 MATRIX_MCFG6; 	//  Master Configuration Register 6 (ram16k)  
	AT91_REG	 MATRIX_MCFG7; 	//  Master Configuration Register 7 (teak_prog)     
	AT91_REG	 Reserved5[8]; 	// 
	AT91_REG	 MATRIX_SCFG0; 	//  Slave Configuration Register 0 (ram96k)     
	AT91_REG	 MATRIX_SCFG1; 	//  Slave Configuration Register 1 (rom)    
	AT91_REG	 MATRIX_SCFG2; 	//  Slave Configuration Register 2 (hperiphs) 
	AT91_REG	 MATRIX_SCFG3; 	//  Slave Configuration Register 3 (ebi)
	AT91_REG	 MATRIX_SCFG4; 	//  Slave Configuration Register 4 (bridge)    
	AT91_REG	 Reserved6[11]; 	// 
	AT91_REG	 MATRIX_PRAS0; 	//  PRAS0 (ram0) 
	AT91_REG	 MATRIX_PRBS0; 	//  PRBS0 (ram0) 
	AT91_REG	 MATRIX_PRAS1; 	//  PRAS1 (ram1) 
	AT91_REG	 MATRIX_PRBS1; 	//  PRBS1 (ram1) 
	AT91_REG	 MATRIX_PRAS2; 	//  PRAS2 (ram2) 
	AT91_REG	 MATRIX_PRBS2; 	//  PRBS2 (ram2) 
	AT91_REG	 MATRIX_PRAS3; 	//  PRAS3 : usb_dev_hs
	AT91_REG	 MATRIX_PRBS3; 	//  PRBS3 : usb_dev_hs
	AT91_REG	 MATRIX_PRAS4; 	//  PRAS4 : ebi
	AT91_REG	 MATRIX_PRBS4; 	//  PRBS4 : ebi
	AT91_REG	 Reserved7[22]; 	// 
	AT91_REG	 MATRIX_MRCR; 	//  Master Remp Control Register 
	AT91_REG	 Reserved8[6]; 	// 
	AT91_REG	 CCFG_EBICSA; 	//  EBI Chip Select Assignement Register
	AT91_REG	 Reserved9[3]; 	// 
	AT91_REG	 MATRIX_TEAKCFG; 	//  Slave 7 (teak_prog) Special Function Register
	AT91_REG	 Reserved10[51]; 	// 
	AT91_REG	 CCFG_MATRIXVERSION; 	//  Version Register
	AT91_REG	 AIC_SMR[32]; 	// Source Mode Register
	AT91_REG	 AIC_SVR[32]; 	// Source Vector Register
	AT91_REG	 AIC_IVR; 	// IRQ Vector Register
	AT91_REG	 AIC_FVR; 	// FIQ Vector Register
	AT91_REG	 AIC_ISR; 	// Interrupt Status Register
	AT91_REG	 AIC_IPR; 	// Interrupt Pending Register
	AT91_REG	 AIC_IMR; 	// Interrupt Mask Register
	AT91_REG	 AIC_CISR; 	// Core Interrupt Status Register
	AT91_REG	 Reserved11[2]; 	// 
	AT91_REG	 AIC_IECR; 	// Interrupt Enable Command Register
	AT91_REG	 AIC_IDCR; 	// Interrupt Disable Command Register
	AT91_REG	 AIC_ICCR; 	// Interrupt Clear Command Register
	AT91_REG	 AIC_ISCR; 	// Interrupt Set Command Register
	AT91_REG	 AIC_EOICR; 	// End of Interrupt Command Register
	AT91_REG	 AIC_SPU; 	// Spurious Vector Register
	AT91_REG	 AIC_DCR; 	// Debug Control Register (Protect)
	AT91_REG	 Reserved12[1]; 	// 
	AT91_REG	 AIC_FFER; 	// Fast Forcing Enable Register
	AT91_REG	 AIC_FFDR; 	// Fast Forcing Disable Register
	AT91_REG	 AIC_FFSR; 	// Fast Forcing Status Register
	AT91_REG	 Reserved13[45]; 	// 
	AT91_REG	 DBGU_CR; 	// Control Register
	AT91_REG	 DBGU_MR; 	// Mode Register
	AT91_REG	 DBGU_IER; 	// Interrupt Enable Register
	AT91_REG	 DBGU_IDR; 	// Interrupt Disable Register
	AT91_REG	 DBGU_IMR; 	// Interrupt Mask Register
	AT91_REG	 DBGU_CSR; 	// Channel Status Register
	AT91_REG	 DBGU_RHR; 	// Receiver Holding Register
	AT91_REG	 DBGU_THR; 	// Transmitter Holding Register
	AT91_REG	 DBGU_BRGR; 	// Baud Rate Generator Register
	AT91_REG	 Reserved14[7]; 	// 
	AT91_REG	 DBGU_CIDR; 	// Chip ID Register
	AT91_REG	 DBGU_EXID; 	// Chip ID Extension Register
	AT91_REG	 DBGU_FNTR; 	// Force NTRST Register
	AT91_REG	 Reserved15[45]; 	// 
	AT91_REG	 DBGU_RPR; 	// Receive Pointer Register
	AT91_REG	 DBGU_RCR; 	// Receive Counter Register
	AT91_REG	 DBGU_TPR; 	// Transmit Pointer Register
	AT91_REG	 DBGU_TCR; 	// Transmit Counter Register
	AT91_REG	 DBGU_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 DBGU_RNCR; 	// Receive Next Counter Register
	AT91_REG	 DBGU_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 DBGU_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 DBGU_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 DBGU_PTSR; 	// PDC Transfer Status Register
	AT91_REG	 Reserved16[54]; 	// 
	AT91_REG	 PIOA_PER; 	// PIO Enable Register
	AT91_REG	 PIOA_PDR; 	// PIO Disable Register
	AT91_REG	 PIOA_PSR; 	// PIO Status Register
	AT91_REG	 Reserved17[1]; 	// 
	AT91_REG	 PIOA_OER; 	// Output Enable Register
	AT91_REG	 PIOA_ODR; 	// Output Disable Registerr
	AT91_REG	 PIOA_OSR; 	// Output Status Register
	AT91_REG	 Reserved18[1]; 	// 
	AT91_REG	 PIOA_IFER; 	// Input Filter Enable Register
	AT91_REG	 PIOA_IFDR; 	// Input Filter Disable Register
	AT91_REG	 PIOA_IFSR; 	// Input Filter Status Register
	AT91_REG	 Reserved19[1]; 	// 
	AT91_REG	 PIOA_SODR; 	// Set Output Data Register
	AT91_REG	 PIOA_CODR; 	// Clear Output Data Register
	AT91_REG	 PIOA_ODSR; 	// Output Data Status Register
	AT91_REG	 PIOA_PDSR; 	// Pin Data Status Register
	AT91_REG	 PIOA_IER; 	// Interrupt Enable Register
	AT91_REG	 PIOA_IDR; 	// Interrupt Disable Register
	AT91_REG	 PIOA_IMR; 	// Interrupt Mask Register
	AT91_REG	 PIOA_ISR; 	// Interrupt Status Register
	AT91_REG	 PIOA_MDER; 	// Multi-driver Enable Register
	AT91_REG	 PIOA_MDDR; 	// Multi-driver Disable Register
	AT91_REG	 PIOA_MDSR; 	// Multi-driver Status Register
	AT91_REG	 Reserved20[1]; 	// 
	AT91_REG	 PIOA_PPUDR; 	// Pull-up Disable Register
	AT91_REG	 PIOA_PPUER; 	// Pull-up Enable Register
	AT91_REG	 PIOA_PPUSR; 	// Pull-up Status Register
	AT91_REG	 Reserved21[1]; 	// 
	AT91_REG	 PIOA_ASR; 	// Select A Register
	AT91_REG	 PIOA_BSR; 	// Select B Register
	AT91_REG	 PIOA_ABSR; 	// AB Select Status Register
	AT91_REG	 Reserved22[9]; 	// 
	AT91_REG	 PIOA_OWER; 	// Output Write Enable Register
	AT91_REG	 PIOA_OWDR; 	// Output Write Disable Register
	AT91_REG	 PIOA_OWSR; 	// Output Write Status Register
	AT91_REG	 Reserved23[213]; 	// 
	AT91_REG	 PIOB_PER; 	// PIO Enable Register
	AT91_REG	 PIOB_PDR; 	// PIO Disable Register
	AT91_REG	 PIOB_PSR; 	// PIO Status Register
	AT91_REG	 Reserved24[1]; 	// 
	AT91_REG	 PIOB_OER; 	// Output Enable Register
	AT91_REG	 PIOB_ODR; 	// Output Disable Registerr
	AT91_REG	 PIOB_OSR; 	// Output Status Register
	AT91_REG	 Reserved25[1]; 	// 
	AT91_REG	 PIOB_IFER; 	// Input Filter Enable Register
	AT91_REG	 PIOB_IFDR; 	// Input Filter Disable Register
	AT91_REG	 PIOB_IFSR; 	// Input Filter Status Register
	AT91_REG	 Reserved26[1]; 	// 
	AT91_REG	 PIOB_SODR; 	// Set Output Data Register
	AT91_REG	 PIOB_CODR; 	// Clear Output Data Register
	AT91_REG	 PIOB_ODSR; 	// Output Data Status Register
	AT91_REG	 PIOB_PDSR; 	// Pin Data Status Register
	AT91_REG	 PIOB_IER; 	// Interrupt Enable Register
	AT91_REG	 PIOB_IDR; 	// Interrupt Disable Register
	AT91_REG	 PIOB_IMR; 	// Interrupt Mask Register
	AT91_REG	 PIOB_ISR; 	// Interrupt Status Register
	AT91_REG	 PIOB_MDER; 	// Multi-driver Enable Register
	AT91_REG	 PIOB_MDDR; 	// Multi-driver Disable Register
	AT91_REG	 PIOB_MDSR; 	// Multi-driver Status Register
	AT91_REG	 Reserved27[1]; 	// 
	AT91_REG	 PIOB_PPUDR; 	// Pull-up Disable Register
	AT91_REG	 PIOB_PPUER; 	// Pull-up Enable Register
	AT91_REG	 PIOB_PPUSR; 	// Pull-up Status Register
	AT91_REG	 Reserved28[1]; 	// 
	AT91_REG	 PIOB_ASR; 	// Select A Register
	AT91_REG	 PIOB_BSR; 	// Select B Register
	AT91_REG	 PIOB_ABSR; 	// AB Select Status Register
	AT91_REG	 Reserved29[9]; 	// 
	AT91_REG	 PIOB_OWER; 	// Output Write Enable Register
	AT91_REG	 PIOB_OWDR; 	// Output Write Disable Register
	AT91_REG	 PIOB_OWSR; 	// Output Write Status Register
	AT91_REG	 Reserved30[85]; 	// 
	AT91_REG	 PIOC_PER; 	// PIO Enable Register
	AT91_REG	 PIOC_PDR; 	// PIO Disable Register
	AT91_REG	 PIOC_PSR; 	// PIO Status Register
	AT91_REG	 Reserved31[1]; 	// 
	AT91_REG	 PIOC_OER; 	// Output Enable Register
	AT91_REG	 PIOC_ODR; 	// Output Disable Registerr
	AT91_REG	 PIOC_OSR; 	// Output Status Register
	AT91_REG	 Reserved32[1]; 	// 
	AT91_REG	 PIOC_IFER; 	// Input Filter Enable Register
	AT91_REG	 PIOC_IFDR; 	// Input Filter Disable Register
	AT91_REG	 PIOC_IFSR; 	// Input Filter Status Register
	AT91_REG	 Reserved33[1]; 	// 
	AT91_REG	 PIOC_SODR; 	// Set Output Data Register
	AT91_REG	 PIOC_CODR; 	// Clear Output Data Register
	AT91_REG	 PIOC_ODSR; 	// Output Data Status Register
	AT91_REG	 PIOC_PDSR; 	// Pin Data Status Register
	AT91_REG	 PIOC_IER; 	// Interrupt Enable Register
	AT91_REG	 PIOC_IDR; 	// Interrupt Disable Register
	AT91_REG	 PIOC_IMR; 	// Interrupt Mask Register
	AT91_REG	 PIOC_ISR; 	// Interrupt Status Register
	AT91_REG	 PIOC_MDER; 	// Multi-driver Enable Register
	AT91_REG	 PIOC_MDDR; 	// Multi-driver Disable Register
	AT91_REG	 PIOC_MDSR; 	// Multi-driver Status Register
	AT91_REG	 Reserved34[1]; 	// 
	AT91_REG	 PIOC_PPUDR; 	// Pull-up Disable Register
	AT91_REG	 PIOC_PPUER; 	// Pull-up Enable Register
	AT91_REG	 PIOC_PPUSR; 	// Pull-up Status Register
	AT91_REG	 Reserved35[1]; 	// 
	AT91_REG	 PIOC_ASR; 	// Select A Register
	AT91_REG	 PIOC_BSR; 	// Select B Register
	AT91_REG	 PIOC_ABSR; 	// AB Select Status Register
	AT91_REG	 Reserved36[9]; 	// 
	AT91_REG	 PIOC_OWER; 	// Output Write Enable Register
	AT91_REG	 PIOC_OWDR; 	// Output Write Disable Register
	AT91_REG	 PIOC_OWSR; 	// Output Write Status Register
	AT91_REG	 Reserved37[85]; 	// 
	AT91_REG	 PMC_SCER; 	// System Clock Enable Register
	AT91_REG	 PMC_SCDR; 	// System Clock Disable Register
	AT91_REG	 PMC_SCSR; 	// System Clock Status Register
	AT91_REG	 Reserved38[1]; 	// 
	AT91_REG	 PMC_PCER; 	// Peripheral Clock Enable Register
	AT91_REG	 PMC_PCDR; 	// Peripheral Clock Disable Register
	AT91_REG	 PMC_PCSR; 	// Peripheral Clock Status Register
	AT91_REG	 Reserved39[1]; 	// 
	AT91_REG	 PMC_MOR; 	// Main Oscillator Register
	AT91_REG	 PMC_MCFR; 	// Main Clock  Frequency Register
	AT91_REG	 PMC_PLLAR; 	// PLL A Register
	AT91_REG	 PMC_PLLBR; 	// PLL B Register
	AT91_REG	 PMC_MCKR; 	// Master Clock Register
	AT91_REG	 Reserved40[3]; 	// 
	AT91_REG	 PMC_PCKR[8]; 	// Programmable Clock Register
	AT91_REG	 PMC_IER; 	// Interrupt Enable Register
	AT91_REG	 PMC_IDR; 	// Interrupt Disable Register
	AT91_REG	 PMC_SR; 	// Status Register
	AT91_REG	 PMC_IMR; 	// Interrupt Mask Register
	AT91_REG	 Reserved41[36]; 	// 
	AT91_REG	 RSTC_RCR; 	// Reset Control Register
	AT91_REG	 RSTC_RSR; 	// Reset Status Register
	AT91_REG	 RSTC_RMR; 	// Reset Mode Register
	AT91_REG	 Reserved42[1]; 	// 
	AT91_REG	 SHDWC_SHCR; 	// Shut Down Control Register
	AT91_REG	 SHDWC_SHMR; 	// Shut Down Mode Register
	AT91_REG	 SHDWC_SHSR; 	// Shut Down Status Register
	AT91_REG	 Reserved43[1]; 	// 
	AT91_REG	 RTTC_RTMR; 	// Real-time Mode Register
	AT91_REG	 RTTC_RTAR; 	// Real-time Alarm Register
	AT91_REG	 RTTC_RTVR; 	// Real-time Value Register
	AT91_REG	 RTTC_RTSR; 	// Real-time Status Register
	AT91_REG	 PITC_PIMR; 	// Period Interval Mode Register
	AT91_REG	 PITC_PISR; 	// Period Interval Status Register
	AT91_REG	 PITC_PIVR; 	// Period Interval Value Register
	AT91_REG	 PITC_PIIR; 	// Period Interval Image Register
	AT91_REG	 WDTC_WDCR; 	// Watchdog Control Register
	AT91_REG	 WDTC_WDMR; 	// Watchdog Mode Register
	AT91_REG	 WDTC_WDSR; 	// Watchdog Status Register
	AT91_REG	 Reserved44[1]; 	// 
	AT91_REG	 SYS_GPBR[4]; 	// General Purpose Register
} AT91S_SYS, *AT91PS_SYS;
#else
#define SYS_GPBR        (AT91_CAST(AT91_REG *) 	0x00003D50) // (SYS_GPBR) General Purpose Register

#endif
// -------- GPBR : (SYS Offset: 0x3d50) GPBR General Purpose Register -------- 
#define AT91C_GPBR_GPRV       (0x0 <<  0) // (SYS) General Purpose Register Value

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR External Bus Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_EBI {
	AT91_REG	 EBI_DUMMY; 	// Dummy register - Do not use
} AT91S_EBI, *AT91PS_EBI;
#else
#define EBI_DUMMY       (AT91_CAST(AT91_REG *) 	0x00000000) // (EBI_DUMMY) Dummy register - Do not use

#endif

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Error Correction Code controller
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_ECC {
	AT91_REG	 ECC_CR; 	//  ECC reset register
	AT91_REG	 ECC_MR; 	//  ECC Page size register
	AT91_REG	 ECC_SR; 	//  ECC Status register
	AT91_REG	 ECC_PR; 	//  ECC Parity register
	AT91_REG	 ECC_NPR; 	//  ECC Parity N register
	AT91_REG	 Reserved0[58]; 	// 
	AT91_REG	 ECC_VR; 	//  ECC Version register
} AT91S_ECC, *AT91PS_ECC;
#else
#define ECC_CR          (AT91_CAST(AT91_REG *) 	0x00000000) // (ECC_CR)  ECC reset register
#define ECC_MR          (AT91_CAST(AT91_REG *) 	0x00000004) // (ECC_MR)  ECC Page size register
#define ECC_SR          (AT91_CAST(AT91_REG *) 	0x00000008) // (ECC_SR)  ECC Status register
#define ECC_PR          (AT91_CAST(AT91_REG *) 	0x0000000C) // (ECC_PR)  ECC Parity register
#define ECC_NPR         (AT91_CAST(AT91_REG *) 	0x00000010) // (ECC_NPR)  ECC Parity N register
#define ECC_VR          (AT91_CAST(AT91_REG *) 	0x000000FC) // (ECC_VR)  ECC Version register

#endif
// -------- ECC_CR : (ECC Offset: 0x0) ECC reset register -------- 
#define AT91C_ECC_RST         (0x1 <<  0) // (ECC) ECC reset parity
// -------- ECC_MR : (ECC Offset: 0x4) ECC page size register -------- 
#define AT91C_ECC_PAGE_SIZE   (0x3 <<  0) // (ECC) Nand Flash page size
// -------- ECC_SR : (ECC Offset: 0x8) ECC status register -------- 
#define AT91C_ECC_RECERR      (0x1 <<  0) // (ECC) ECC error
#define AT91C_ECC_ECCERR      (0x1 <<  1) // (ECC) ECC single error
#define AT91C_ECC_MULERR      (0x1 <<  2) // (ECC) ECC_MULERR
// -------- ECC_PR : (ECC Offset: 0xc) ECC parity register -------- 
#define AT91C_ECC_BITADDR     (0xF <<  0) // (ECC) Bit address error
#define AT91C_ECC_WORDADDR    (0xFFF <<  4) // (ECC) address of the failing bit
// -------- ECC_NPR : (ECC Offset: 0x10) ECC N parity register -------- 
#define AT91C_ECC_NPARITY     (0xFFFF <<  0) // (ECC) ECC parity N 
// -------- ECC_VR : (ECC Offset: 0xfc) ECC version register -------- 
#define AT91C_ECC_VR          (0xF <<  0) // (ECC) ECC version register

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR SDRAM Controller Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_SDRAMC {
	AT91_REG	 SDRAMC_MR; 	// SDRAM Controller Mode Register
	AT91_REG	 SDRAMC_TR; 	// SDRAM Controller Refresh Timer Register
	AT91_REG	 SDRAMC_CR; 	// SDRAM Controller Configuration Register
	AT91_REG	 SDRAMC_HSR; 	// SDRAM Controller High Speed Register
	AT91_REG	 SDRAMC_LPR; 	// SDRAM Controller Low Power Register
	AT91_REG	 SDRAMC_IER; 	// SDRAM Controller Interrupt Enable Register
	AT91_REG	 SDRAMC_IDR; 	// SDRAM Controller Interrupt Disable Register
	AT91_REG	 SDRAMC_IMR; 	// SDRAM Controller Interrupt Mask Register
	AT91_REG	 SDRAMC_ISR; 	// SDRAM Controller Interrupt Mask Register
	AT91_REG	 SDRAMC_MDR; 	// SDRAM Memory Device Register
} AT91S_SDRAMC, *AT91PS_SDRAMC;
#else
#define SDRAMC_MR       (AT91_CAST(AT91_REG *) 	0x00000000) // (SDRAMC_MR) SDRAM Controller Mode Register
#define SDRAMC_TR       (AT91_CAST(AT91_REG *) 	0x00000004) // (SDRAMC_TR) SDRAM Controller Refresh Timer Register
#define SDRAMC_CR       (AT91_CAST(AT91_REG *) 	0x00000008) // (SDRAMC_CR) SDRAM Controller Configuration Register
#define SDRAMC_HSR      (AT91_CAST(AT91_REG *) 	0x0000000C) // (SDRAMC_HSR) SDRAM Controller High Speed Register
#define SDRAMC_LPR      (AT91_CAST(AT91_REG *) 	0x00000010) // (SDRAMC_LPR) SDRAM Controller Low Power Register
#define SDRAMC_IER      (AT91_CAST(AT91_REG *) 	0x00000014) // (SDRAMC_IER) SDRAM Controller Interrupt Enable Register
#define SDRAMC_IDR      (AT91_CAST(AT91_REG *) 	0x00000018) // (SDRAMC_IDR) SDRAM Controller Interrupt Disable Register
#define SDRAMC_IMR      (AT91_CAST(AT91_REG *) 	0x0000001C) // (SDRAMC_IMR) SDRAM Controller Interrupt Mask Register
#define SDRAMC_ISR      (AT91_CAST(AT91_REG *) 	0x00000020) // (SDRAMC_ISR) SDRAM Controller Interrupt Mask Register
#define SDRAMC_MDR      (AT91_CAST(AT91_REG *) 	0x00000024) // (SDRAMC_MDR) SDRAM Memory Device Register

#endif
// -------- SDRAMC_MR : (SDRAMC Offset: 0x0) SDRAM Controller Mode Register -------- 
#define AT91C_SDRAMC_MODE     (0xF <<  0) // (SDRAMC) Mode
#define 	AT91C_SDRAMC_MODE_NORMAL_CMD           (0x0) // (SDRAMC) Normal Mode
#define 	AT91C_SDRAMC_MODE_NOP_CMD              (0x1) // (SDRAMC) Issue a NOP Command at every access
#define 	AT91C_SDRAMC_MODE_PRCGALL_CMD          (0x2) // (SDRAMC) Issue a All Banks Precharge Command at every access
#define 	AT91C_SDRAMC_MODE_LMR_CMD              (0x3) // (SDRAMC) Issue a Load Mode Register at every access
#define 	AT91C_SDRAMC_MODE_RFSH_CMD             (0x4) // (SDRAMC) Issue a Refresh
#define 	AT91C_SDRAMC_MODE_EXT_LMR_CMD          (0x5) // (SDRAMC) Issue an Extended Load Mode Register
#define 	AT91C_SDRAMC_MODE_DEEP_CMD             (0x6) // (SDRAMC) Enter Deep Power Mode
// -------- SDRAMC_TR : (SDRAMC Offset: 0x4) SDRAMC Refresh Timer Register -------- 
#define AT91C_SDRAMC_COUNT    (0xFFF <<  0) // (SDRAMC) Refresh Counter
// -------- SDRAMC_CR : (SDRAMC Offset: 0x8) SDRAM Configuration Register -------- 
#define AT91C_SDRAMC_NC       (0x3 <<  0) // (SDRAMC) Number of Column Bits
#define 	AT91C_SDRAMC_NC_8                    (0x0) // (SDRAMC) 8 Bits
#define 	AT91C_SDRAMC_NC_9                    (0x1) // (SDRAMC) 9 Bits
#define 	AT91C_SDRAMC_NC_10                   (0x2) // (SDRAMC) 10 Bits
#define 	AT91C_SDRAMC_NC_11                   (0x3) // (SDRAMC) 11 Bits
#define AT91C_SDRAMC_NR       (0x3 <<  2) // (SDRAMC) Number of Row Bits
#define 	AT91C_SDRAMC_NR_11                   (0x0 <<  2) // (SDRAMC) 11 Bits
#define 	AT91C_SDRAMC_NR_12                   (0x1 <<  2) // (SDRAMC) 12 Bits
#define 	AT91C_SDRAMC_NR_13                   (0x2 <<  2) // (SDRAMC) 13 Bits
#define AT91C_SDRAMC_NB       (0x1 <<  4) // (SDRAMC) Number of Banks
#define 	AT91C_SDRAMC_NB_2_BANKS              (0x0 <<  4) // (SDRAMC) 2 banks
#define 	AT91C_SDRAMC_NB_4_BANKS              (0x1 <<  4) // (SDRAMC) 4 banks
#define AT91C_SDRAMC_CAS      (0x3 <<  5) // (SDRAMC) CAS Latency
#define 	AT91C_SDRAMC_CAS_2                    (0x2 <<  5) // (SDRAMC) 2 cycles
#define 	AT91C_SDRAMC_CAS_3                    (0x3 <<  5) // (SDRAMC) 3 cycles
#define AT91C_SDRAMC_DBW      (0x1 <<  7) // (SDRAMC) Data Bus Width
#define 	AT91C_SDRAMC_DBW_32_BITS              (0x0 <<  7) // (SDRAMC) 32 Bits datas bus
#define 	AT91C_SDRAMC_DBW_16_BITS              (0x1 <<  7) // (SDRAMC) 16 Bits datas bus
#define AT91C_SDRAMC_TWR      (0xF <<  8) // (SDRAMC) Number of Write Recovery Time Cycles
#define 	AT91C_SDRAMC_TWR_0                    (0x0 <<  8) // (SDRAMC) Value :  0
#define 	AT91C_SDRAMC_TWR_1                    (0x1 <<  8) // (SDRAMC) Value :  1
#define 	AT91C_SDRAMC_TWR_2                    (0x2 <<  8) // (SDRAMC) Value :  2
#define 	AT91C_SDRAMC_TWR_3                    (0x3 <<  8) // (SDRAMC) Value :  3
#define 	AT91C_SDRAMC_TWR_4                    (0x4 <<  8) // (SDRAMC) Value :  4
#define 	AT91C_SDRAMC_TWR_5                    (0x5 <<  8) // (SDRAMC) Value :  5
#define 	AT91C_SDRAMC_TWR_6                    (0x6 <<  8) // (SDRAMC) Value :  6
#define 	AT91C_SDRAMC_TWR_7                    (0x7 <<  8) // (SDRAMC) Value :  7
#define 	AT91C_SDRAMC_TWR_8                    (0x8 <<  8) // (SDRAMC) Value :  8
#define 	AT91C_SDRAMC_TWR_9                    (0x9 <<  8) // (SDRAMC) Value :  9
#define 	AT91C_SDRAMC_TWR_10                   (0xA <<  8) // (SDRAMC) Value : 10
#define 	AT91C_SDRAMC_TWR_11                   (0xB <<  8) // (SDRAMC) Value : 11
#define 	AT91C_SDRAMC_TWR_12                   (0xC <<  8) // (SDRAMC) Value : 12
#define 	AT91C_SDRAMC_TWR_13                   (0xD <<  8) // (SDRAMC) Value : 13
#define 	AT91C_SDRAMC_TWR_14                   (0xE <<  8) // (SDRAMC) Value : 14
#define 	AT91C_SDRAMC_TWR_15                   (0xF <<  8) // (SDRAMC) Value : 15
#define AT91C_SDRAMC_TRC      (0xF << 12) // (SDRAMC) Number of RAS Cycle Time Cycles
#define 	AT91C_SDRAMC_TRC_0                    (0x0 << 12) // (SDRAMC) Value :  0
#define 	AT91C_SDRAMC_TRC_1                    (0x1 << 12) // (SDRAMC) Value :  1
#define 	AT91C_SDRAMC_TRC_2                    (0x2 << 12) // (SDRAMC) Value :  2
#define 	AT91C_SDRAMC_TRC_3                    (0x3 << 12) // (SDRAMC) Value :  3
#define 	AT91C_SDRAMC_TRC_4                    (0x4 << 12) // (SDRAMC) Value :  4
#define 	AT91C_SDRAMC_TRC_5                    (0x5 << 12) // (SDRAMC) Value :  5
#define 	AT91C_SDRAMC_TRC_6                    (0x6 << 12) // (SDRAMC) Value :  6
#define 	AT91C_SDRAMC_TRC_7                    (0x7 << 12) // (SDRAMC) Value :  7
#define 	AT91C_SDRAMC_TRC_8                    (0x8 << 12) // (SDRAMC) Value :  8
#define 	AT91C_SDRAMC_TRC_9                    (0x9 << 12) // (SDRAMC) Value :  9
#define 	AT91C_SDRAMC_TRC_10                   (0xA << 12) // (SDRAMC) Value : 10
#define 	AT91C_SDRAMC_TRC_11                   (0xB << 12) // (SDRAMC) Value : 11
#define 	AT91C_SDRAMC_TRC_12                   (0xC << 12) // (SDRAMC) Value : 12
#define 	AT91C_SDRAMC_TRC_13                   (0xD << 12) // (SDRAMC) Value : 13
#define 	AT91C_SDRAMC_TRC_14                   (0xE << 12) // (SDRAMC) Value : 14
#define 	AT91C_SDRAMC_TRC_15                   (0xF << 12) // (SDRAMC) Value : 15
#define AT91C_SDRAMC_TRP      (0xF << 16) // (SDRAMC) Number of RAS Precharge Time Cycles
#define 	AT91C_SDRAMC_TRP_0                    (0x0 << 16) // (SDRAMC) Value :  0
#define 	AT91C_SDRAMC_TRP_1                    (0x1 << 16) // (SDRAMC) Value :  1
#define 	AT91C_SDRAMC_TRP_2                    (0x2 << 16) // (SDRAMC) Value :  2
#define 	AT91C_SDRAMC_TRP_3                    (0x3 << 16) // (SDRAMC) Value :  3
#define 	AT91C_SDRAMC_TRP_4                    (0x4 << 16) // (SDRAMC) Value :  4
#define 	AT91C_SDRAMC_TRP_5                    (0x5 << 16) // (SDRAMC) Value :  5
#define 	AT91C_SDRAMC_TRP_6                    (0x6 << 16) // (SDRAMC) Value :  6
#define 	AT91C_SDRAMC_TRP_7                    (0x7 << 16) // (SDRAMC) Value :  7
#define 	AT91C_SDRAMC_TRP_8                    (0x8 << 16) // (SDRAMC) Value :  8
#define 	AT91C_SDRAMC_TRP_9                    (0x9 << 16) // (SDRAMC) Value :  9
#define 	AT91C_SDRAMC_TRP_10                   (0xA << 16) // (SDRAMC) Value : 10
#define 	AT91C_SDRAMC_TRP_11                   (0xB << 16) // (SDRAMC) Value : 11
#define 	AT91C_SDRAMC_TRP_12                   (0xC << 16) // (SDRAMC) Value : 12
#define 	AT91C_SDRAMC_TRP_13                   (0xD << 16) // (SDRAMC) Value : 13
#define 	AT91C_SDRAMC_TRP_14                   (0xE << 16) // (SDRAMC) Value : 14
#define 	AT91C_SDRAMC_TRP_15                   (0xF << 16) // (SDRAMC) Value : 15
#define AT91C_SDRAMC_TRCD     (0xF << 20) // (SDRAMC) Number of RAS to CAS Delay Cycles
#define 	AT91C_SDRAMC_TRCD_0                    (0x0 << 20) // (SDRAMC) Value :  0
#define 	AT91C_SDRAMC_TRCD_1                    (0x1 << 20) // (SDRAMC) Value :  1
#define 	AT91C_SDRAMC_TRCD_2                    (0x2 << 20) // (SDRAMC) Value :  2
#define 	AT91C_SDRAMC_TRCD_3                    (0x3 << 20) // (SDRAMC) Value :  3
#define 	AT91C_SDRAMC_TRCD_4                    (0x4 << 20) // (SDRAMC) Value :  4
#define 	AT91C_SDRAMC_TRCD_5                    (0x5 << 20) // (SDRAMC) Value :  5
#define 	AT91C_SDRAMC_TRCD_6                    (0x6 << 20) // (SDRAMC) Value :  6
#define 	AT91C_SDRAMC_TRCD_7                    (0x7 << 20) // (SDRAMC) Value :  7
#define 	AT91C_SDRAMC_TRCD_8                    (0x8 << 20) // (SDRAMC) Value :  8
#define 	AT91C_SDRAMC_TRCD_9                    (0x9 << 20) // (SDRAMC) Value :  9
#define 	AT91C_SDRAMC_TRCD_10                   (0xA << 20) // (SDRAMC) Value : 10
#define 	AT91C_SDRAMC_TRCD_11                   (0xB << 20) // (SDRAMC) Value : 11
#define 	AT91C_SDRAMC_TRCD_12                   (0xC << 20) // (SDRAMC) Value : 12
#define 	AT91C_SDRAMC_TRCD_13                   (0xD << 20) // (SDRAMC) Value : 13
#define 	AT91C_SDRAMC_TRCD_14                   (0xE << 20) // (SDRAMC) Value : 14
#define 	AT91C_SDRAMC_TRCD_15                   (0xF << 20) // (SDRAMC) Value : 15
#define AT91C_SDRAMC_TRAS     (0xF << 24) // (SDRAMC) Number of RAS Active Time Cycles
#define 	AT91C_SDRAMC_TRAS_0                    (0x0 << 24) // (SDRAMC) Value :  0
#define 	AT91C_SDRAMC_TRAS_1                    (0x1 << 24) // (SDRAMC) Value :  1
#define 	AT91C_SDRAMC_TRAS_2                    (0x2 << 24) // (SDRAMC) Value :  2
#define 	AT91C_SDRAMC_TRAS_3                    (0x3 << 24) // (SDRAMC) Value :  3
#define 	AT91C_SDRAMC_TRAS_4                    (0x4 << 24) // (SDRAMC) Value :  4
#define 	AT91C_SDRAMC_TRAS_5                    (0x5 << 24) // (SDRAMC) Value :  5
#define 	AT91C_SDRAMC_TRAS_6                    (0x6 << 24) // (SDRAMC) Value :  6
#define 	AT91C_SDRAMC_TRAS_7                    (0x7 << 24) // (SDRAMC) Value :  7
#define 	AT91C_SDRAMC_TRAS_8                    (0x8 << 24) // (SDRAMC) Value :  8
#define 	AT91C_SDRAMC_TRAS_9                    (0x9 << 24) // (SDRAMC) Value :  9
#define 	AT91C_SDRAMC_TRAS_10                   (0xA << 24) // (SDRAMC) Value : 10
#define 	AT91C_SDRAMC_TRAS_11                   (0xB << 24) // (SDRAMC) Value : 11
#define 	AT91C_SDRAMC_TRAS_12                   (0xC << 24) // (SDRAMC) Value : 12
#define 	AT91C_SDRAMC_TRAS_13                   (0xD << 24) // (SDRAMC) Value : 13
#define 	AT91C_SDRAMC_TRAS_14                   (0xE << 24) // (SDRAMC) Value : 14
#define 	AT91C_SDRAMC_TRAS_15                   (0xF << 24) // (SDRAMC) Value : 15
#define AT91C_SDRAMC_TXSR     (0xF << 28) // (SDRAMC) Number of Command Recovery Time Cycles
#define 	AT91C_SDRAMC_TXSR_0                    (0x0 << 28) // (SDRAMC) Value :  0
#define 	AT91C_SDRAMC_TXSR_1                    (0x1 << 28) // (SDRAMC) Value :  1
#define 	AT91C_SDRAMC_TXSR_2                    (0x2 << 28) // (SDRAMC) Value :  2
#define 	AT91C_SDRAMC_TXSR_3                    (0x3 << 28) // (SDRAMC) Value :  3
#define 	AT91C_SDRAMC_TXSR_4                    (0x4 << 28) // (SDRAMC) Value :  4
#define 	AT91C_SDRAMC_TXSR_5                    (0x5 << 28) // (SDRAMC) Value :  5
#define 	AT91C_SDRAMC_TXSR_6                    (0x6 << 28) // (SDRAMC) Value :  6
#define 	AT91C_SDRAMC_TXSR_7                    (0x7 << 28) // (SDRAMC) Value :  7
#define 	AT91C_SDRAMC_TXSR_8                    (0x8 << 28) // (SDRAMC) Value :  8
#define 	AT91C_SDRAMC_TXSR_9                    (0x9 << 28) // (SDRAMC) Value :  9
#define 	AT91C_SDRAMC_TXSR_10                   (0xA << 28) // (SDRAMC) Value : 10
#define 	AT91C_SDRAMC_TXSR_11                   (0xB << 28) // (SDRAMC) Value : 11
#define 	AT91C_SDRAMC_TXSR_12                   (0xC << 28) // (SDRAMC) Value : 12
#define 	AT91C_SDRAMC_TXSR_13                   (0xD << 28) // (SDRAMC) Value : 13
#define 	AT91C_SDRAMC_TXSR_14                   (0xE << 28) // (SDRAMC) Value : 14
#define 	AT91C_SDRAMC_TXSR_15                   (0xF << 28) // (SDRAMC) Value : 15
// -------- SDRAMC_HSR : (SDRAMC Offset: 0xc) SDRAM Controller High Speed Register -------- 
#define AT91C_SDRAMC_DA       (0x1 <<  0) // (SDRAMC) Decode Cycle Enable Bit
#define 	AT91C_SDRAMC_DA_DISABLE              (0x0) // (SDRAMC) Disable Decode Cycle
#define 	AT91C_SDRAMC_DA_ENABLE               (0x1) // (SDRAMC) Enable Decode Cycle
// -------- SDRAMC_LPR : (SDRAMC Offset: 0x10) SDRAM Controller Low-power Register -------- 
#define AT91C_SDRAMC_LPCB     (0x3 <<  0) // (SDRAMC) Low-power Configurations
#define 	AT91C_SDRAMC_LPCB_DISABLE              (0x0) // (SDRAMC) Disable Low Power Features
#define 	AT91C_SDRAMC_LPCB_SELF_REFRESH         (0x1) // (SDRAMC) Enable SELF_REFRESH
#define 	AT91C_SDRAMC_LPCB_POWER_DOWN           (0x2) // (SDRAMC) Enable POWER_DOWN
#define 	AT91C_SDRAMC_LPCB_DEEP_POWER_DOWN      (0x3) // (SDRAMC) Enable DEEP_POWER_DOWN
#define AT91C_SDRAMC_PASR     (0x7 <<  4) // (SDRAMC) Partial Array Self Refresh (only for Low Power SDRAM)
#define AT91C_SDRAMC_TCSR     (0x3 <<  8) // (SDRAMC) Temperature Compensated Self Refresh (only for Low Power SDRAM)
#define AT91C_SDRAMC_DS       (0x3 << 10) // (SDRAMC) Drive Strenght (only for Low Power SDRAM)
#define AT91C_SDRAMC_TIMEOUT  (0x3 << 12) // (SDRAMC) Time to define when Low Power Mode is enabled
#define 	AT91C_SDRAMC_TIMEOUT_0_CLK_CYCLES         (0x0 << 12) // (SDRAMC) Activate SDRAM Low Power Mode Immediately
#define 	AT91C_SDRAMC_TIMEOUT_64_CLK_CYCLES        (0x1 << 12) // (SDRAMC) Activate SDRAM Low Power Mode after 64 clock cycles after the end of the last transfer
#define 	AT91C_SDRAMC_TIMEOUT_128_CLK_CYCLES       (0x2 << 12) // (SDRAMC) Activate SDRAM Low Power Mode after 64 clock cycles after the end of the last transfer
// -------- SDRAMC_IER : (SDRAMC Offset: 0x14) SDRAM Controller Interrupt Enable Register -------- 
#define AT91C_SDRAMC_RES      (0x1 <<  0) // (SDRAMC) Refresh Error Status
// -------- SDRAMC_IDR : (SDRAMC Offset: 0x18) SDRAM Controller Interrupt Disable Register -------- 
// -------- SDRAMC_IMR : (SDRAMC Offset: 0x1c) SDRAM Controller Interrupt Mask Register -------- 
// -------- SDRAMC_ISR : (SDRAMC Offset: 0x20) SDRAM Controller Interrupt Status Register -------- 
// -------- SDRAMC_MDR : (SDRAMC Offset: 0x24) SDRAM Controller Memory Device Register -------- 
#define AT91C_SDRAMC_MD       (0x3 <<  0) // (SDRAMC) Memory Device Type
#define 	AT91C_SDRAMC_MD_SDRAM                (0x0) // (SDRAMC) SDRAM Mode
#define 	AT91C_SDRAMC_MD_LOW_POWER_SDRAM      (0x1) // (SDRAMC) SDRAM Low Power Mode

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Static Memory Controller Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_SMC {
	AT91_REG	 SMC_SETUP0; 	//  Setup Register for CS 0
	AT91_REG	 SMC_PULSE0; 	//  Pulse Register for CS 0
	AT91_REG	 SMC_CYCLE0; 	//  Cycle Register for CS 0
	AT91_REG	 SMC_CTRL0; 	//  Control Register for CS 0
	AT91_REG	 SMC_SETUP1; 	//  Setup Register for CS 1
	AT91_REG	 SMC_PULSE1; 	//  Pulse Register for CS 1
	AT91_REG	 SMC_CYCLE1; 	//  Cycle Register for CS 1
	AT91_REG	 SMC_CTRL1; 	//  Control Register for CS 1
	AT91_REG	 SMC_SETUP2; 	//  Setup Register for CS 2
	AT91_REG	 SMC_PULSE2; 	//  Pulse Register for CS 2
	AT91_REG	 SMC_CYCLE2; 	//  Cycle Register for CS 2
	AT91_REG	 SMC_CTRL2; 	//  Control Register for CS 2
	AT91_REG	 SMC_SETUP3; 	//  Setup Register for CS 3
	AT91_REG	 SMC_PULSE3; 	//  Pulse Register for CS 3
	AT91_REG	 SMC_CYCLE3; 	//  Cycle Register for CS 3
	AT91_REG	 SMC_CTRL3; 	//  Control Register for CS 3
	AT91_REG	 SMC_SETUP4; 	//  Setup Register for CS 4
	AT91_REG	 SMC_PULSE4; 	//  Pulse Register for CS 4
	AT91_REG	 SMC_CYCLE4; 	//  Cycle Register for CS 4
	AT91_REG	 SMC_CTRL4; 	//  Control Register for CS 4
	AT91_REG	 SMC_SETUP5; 	//  Setup Register for CS 5
	AT91_REG	 SMC_PULSE5; 	//  Pulse Register for CS 5
	AT91_REG	 SMC_CYCLE5; 	//  Cycle Register for CS 5
	AT91_REG	 SMC_CTRL5; 	//  Control Register for CS 5
	AT91_REG	 SMC_SETUP6; 	//  Setup Register for CS 6
	AT91_REG	 SMC_PULSE6; 	//  Pulse Register for CS 6
	AT91_REG	 SMC_CYCLE6; 	//  Cycle Register for CS 6
	AT91_REG	 SMC_CTRL6; 	//  Control Register for CS 6
	AT91_REG	 SMC_SETUP7; 	//  Setup Register for CS 7
	AT91_REG	 SMC_PULSE7; 	//  Pulse Register for CS 7
	AT91_REG	 SMC_CYCLE7; 	//  Cycle Register for CS 7
	AT91_REG	 SMC_CTRL7; 	//  Control Register for CS 7
} AT91S_SMC, *AT91PS_SMC;
#else
#define SETUP0          (AT91_CAST(AT91_REG *) 	0x00000000) // (SETUP0)  Setup Register for CS 0
#define PULSE0          (AT91_CAST(AT91_REG *) 	0x00000004) // (PULSE0)  Pulse Register for CS 0
#define CYCLE0          (AT91_CAST(AT91_REG *) 	0x00000008) // (CYCLE0)  Cycle Register for CS 0
#define CTRL0           (AT91_CAST(AT91_REG *) 	0x0000000C) // (CTRL0)  Control Register for CS 0
#define SETUP1          (AT91_CAST(AT91_REG *) 	0x00000010) // (SETUP1)  Setup Register for CS 1
#define PULSE1          (AT91_CAST(AT91_REG *) 	0x00000014) // (PULSE1)  Pulse Register for CS 1
#define CYCLE1          (AT91_CAST(AT91_REG *) 	0x00000018) // (CYCLE1)  Cycle Register for CS 1
#define CTRL1           (AT91_CAST(AT91_REG *) 	0x0000001C) // (CTRL1)  Control Register for CS 1
#define SETUP2          (AT91_CAST(AT91_REG *) 	0x00000020) // (SETUP2)  Setup Register for CS 2
#define PULSE2          (AT91_CAST(AT91_REG *) 	0x00000024) // (PULSE2)  Pulse Register for CS 2
#define CYCLE2          (AT91_CAST(AT91_REG *) 	0x00000028) // (CYCLE2)  Cycle Register for CS 2
#define CTRL2           (AT91_CAST(AT91_REG *) 	0x0000002C) // (CTRL2)  Control Register for CS 2
#define SETUP3          (AT91_CAST(AT91_REG *) 	0x00000030) // (SETUP3)  Setup Register for CS 3
#define PULSE3          (AT91_CAST(AT91_REG *) 	0x00000034) // (PULSE3)  Pulse Register for CS 3
#define CYCLE3          (AT91_CAST(AT91_REG *) 	0x00000038) // (CYCLE3)  Cycle Register for CS 3
#define CTRL3           (AT91_CAST(AT91_REG *) 	0x0000003C) // (CTRL3)  Control Register for CS 3
#define SETUP4          (AT91_CAST(AT91_REG *) 	0x00000040) // (SETUP4)  Setup Register for CS 4
#define PULSE4          (AT91_CAST(AT91_REG *) 	0x00000044) // (PULSE4)  Pulse Register for CS 4
#define CYCLE4          (AT91_CAST(AT91_REG *) 	0x00000048) // (CYCLE4)  Cycle Register for CS 4
#define CTRL4           (AT91_CAST(AT91_REG *) 	0x0000004C) // (CTRL4)  Control Register for CS 4
#define SETUP5          (AT91_CAST(AT91_REG *) 	0x00000050) // (SETUP5)  Setup Register for CS 5
#define PULSE5          (AT91_CAST(AT91_REG *) 	0x00000054) // (PULSE5)  Pulse Register for CS 5
#define CYCLE5          (AT91_CAST(AT91_REG *) 	0x00000058) // (CYCLE5)  Cycle Register for CS 5
#define CTRL5           (AT91_CAST(AT91_REG *) 	0x0000005C) // (CTRL5)  Control Register for CS 5
#define SETUP6          (AT91_CAST(AT91_REG *) 	0x00000060) // (SETUP6)  Setup Register for CS 6
#define PULSE6          (AT91_CAST(AT91_REG *) 	0x00000064) // (PULSE6)  Pulse Register for CS 6
#define CYCLE6          (AT91_CAST(AT91_REG *) 	0x00000068) // (CYCLE6)  Cycle Register for CS 6
#define CTRL6           (AT91_CAST(AT91_REG *) 	0x0000006C) // (CTRL6)  Control Register for CS 6
#define SETUP7          (AT91_CAST(AT91_REG *) 	0x00000070) // (SETUP7)  Setup Register for CS 7
#define PULSE7          (AT91_CAST(AT91_REG *) 	0x00000074) // (PULSE7)  Pulse Register for CS 7
#define CYCLE7          (AT91_CAST(AT91_REG *) 	0x00000078) // (CYCLE7)  Cycle Register for CS 7
#define CTRL7           (AT91_CAST(AT91_REG *) 	0x0000007C) // (CTRL7)  Control Register for CS 7

#endif
// -------- SMC_SETUP : (SMC Offset: 0x0) Setup Register for CS x -------- 
#define AT91C_SMC_NWESETUP    (0x3F <<  0) // (SMC) NWE Setup Length
#define AT91C_SMC_NCSSETUPWR  (0x3F <<  8) // (SMC) NCS Setup Length in WRite Access
#define AT91C_SMC_NRDSETUP    (0x3F << 16) // (SMC) NRD Setup Length
#define AT91C_SMC_NCSSETUPRD  (0x3F << 24) // (SMC) NCS Setup Length in ReaD Access
// -------- SMC_PULSE : (SMC Offset: 0x4) Pulse Register for CS x -------- 
#define AT91C_SMC_NWEPULSE    (0x7F <<  0) // (SMC) NWE Pulse Length
#define AT91C_SMC_NCSPULSEWR  (0x7F <<  8) // (SMC) NCS Pulse Length in WRite Access
#define AT91C_SMC_NRDPULSE    (0x7F << 16) // (SMC) NRD Pulse Length
#define AT91C_SMC_NCSPULSERD  (0x7F << 24) // (SMC) NCS Pulse Length in ReaD Access
// -------- SMC_CYC : (SMC Offset: 0x8) Cycle Register for CS x -------- 
#define AT91C_SMC_NWECYCLE    (0x1FF <<  0) // (SMC) Total Write Cycle Length
#define AT91C_SMC_NRDCYCLE    (0x1FF << 16) // (SMC) Total Read Cycle Length
// -------- SMC_CTRL : (SMC Offset: 0xc) Control Register for CS x -------- 
#define AT91C_SMC_READMODE    (0x1 <<  0) // (SMC) Read Mode
#define AT91C_SMC_WRITEMODE   (0x1 <<  1) // (SMC) Write Mode
#define AT91C_SMC_NWAITM      (0x3 <<  4) // (SMC) NWAIT Mode
#define 	AT91C_SMC_NWAITM_NWAIT_DISABLE        (0x0 <<  4) // (SMC) External NWAIT disabled.
#define 	AT91C_SMC_NWAITM_NWAIT_ENABLE_FROZEN  (0x2 <<  4) // (SMC) External NWAIT enabled in frozen mode.
#define 	AT91C_SMC_NWAITM_NWAIT_ENABLE_READY   (0x3 <<  4) // (SMC) External NWAIT enabled in ready mode.
#define AT91C_SMC_BAT         (0x1 <<  8) // (SMC) Byte Access Type
#define 	AT91C_SMC_BAT_BYTE_SELECT          (0x0 <<  8) // (SMC) Write controled by ncs, nbs0, nbs1, nbs2, nbs3. Read controled by ncs, nrd, nbs0, nbs1, nbs2, nbs3.
#define 	AT91C_SMC_BAT_BYTE_WRITE           (0x1 <<  8) // (SMC) Write controled by ncs, nwe0, nwe1, nwe2, nwe3. Read controled by ncs and nrd.
#define AT91C_SMC_DBW         (0x3 << 12) // (SMC) Data Bus Width
#define 	AT91C_SMC_DBW_WIDTH_EIGTH_BITS     (0x0 << 12) // (SMC) 8 bits.
#define 	AT91C_SMC_DBW_WIDTH_SIXTEEN_BITS   (0x1 << 12) // (SMC) 16 bits.
#define 	AT91C_SMC_DBW_WIDTH_THIRTY_TWO_BITS (0x2 << 12) // (SMC) 32 bits.
#define AT91C_SMC_TDF         (0xF << 16) // (SMC) Data Float Time.
#define AT91C_SMC_TDFEN       (0x1 << 20) // (SMC) TDF Enabled.
#define AT91C_SMC_PMEN        (0x1 << 24) // (SMC) Page Mode Enabled.
#define AT91C_SMC_PS          (0x3 << 28) // (SMC) Page Size
#define 	AT91C_SMC_PS_SIZE_FOUR_BYTES      (0x0 << 28) // (SMC) 4 bytes.
#define 	AT91C_SMC_PS_SIZE_EIGHT_BYTES     (0x1 << 28) // (SMC) 8 bytes.
#define 	AT91C_SMC_PS_SIZE_SIXTEEN_BYTES   (0x2 << 28) // (SMC) 16 bytes.
#define 	AT91C_SMC_PS_SIZE_THIRTY_TWO_BYTES (0x3 << 28) // (SMC) 32 bytes.
// -------- SMC_SETUP : (SMC Offset: 0x10) Setup Register for CS x -------- 
// -------- SMC_PULSE : (SMC Offset: 0x14) Pulse Register for CS x -------- 
// -------- SMC_CYC : (SMC Offset: 0x18) Cycle Register for CS x -------- 
// -------- SMC_CTRL : (SMC Offset: 0x1c) Control Register for CS x -------- 
// -------- SMC_SETUP : (SMC Offset: 0x20) Setup Register for CS x -------- 
// -------- SMC_PULSE : (SMC Offset: 0x24) Pulse Register for CS x -------- 
// -------- SMC_CYC : (SMC Offset: 0x28) Cycle Register for CS x -------- 
// -------- SMC_CTRL : (SMC Offset: 0x2c) Control Register for CS x -------- 
// -------- SMC_SETUP : (SMC Offset: 0x30) Setup Register for CS x -------- 
// -------- SMC_PULSE : (SMC Offset: 0x34) Pulse Register for CS x -------- 
// -------- SMC_CYC : (SMC Offset: 0x38) Cycle Register for CS x -------- 
// -------- SMC_CTRL : (SMC Offset: 0x3c) Control Register for CS x -------- 
// -------- SMC_SETUP : (SMC Offset: 0x40) Setup Register for CS x -------- 
// -------- SMC_PULSE : (SMC Offset: 0x44) Pulse Register for CS x -------- 
// -------- SMC_CYC : (SMC Offset: 0x48) Cycle Register for CS x -------- 
// -------- SMC_CTRL : (SMC Offset: 0x4c) Control Register for CS x -------- 
// -------- SMC_SETUP : (SMC Offset: 0x50) Setup Register for CS x -------- 
// -------- SMC_PULSE : (SMC Offset: 0x54) Pulse Register for CS x -------- 
// -------- SMC_CYC : (SMC Offset: 0x58) Cycle Register for CS x -------- 
// -------- SMC_CTRL : (SMC Offset: 0x5c) Control Register for CS x -------- 
// -------- SMC_SETUP : (SMC Offset: 0x60) Setup Register for CS x -------- 
// -------- SMC_PULSE : (SMC Offset: 0x64) Pulse Register for CS x -------- 
// -------- SMC_CYC : (SMC Offset: 0x68) Cycle Register for CS x -------- 
// -------- SMC_CTRL : (SMC Offset: 0x6c) Control Register for CS x -------- 
// -------- SMC_SETUP : (SMC Offset: 0x70) Setup Register for CS x -------- 
// -------- SMC_PULSE : (SMC Offset: 0x74) Pulse Register for CS x -------- 
// -------- SMC_CYC : (SMC Offset: 0x78) Cycle Register for CS x -------- 
// -------- SMC_CTRL : (SMC Offset: 0x7c) Control Register for CS x -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR AHB Matrix Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_MATRIX {
	AT91_REG	 MATRIX_MCFG0; 	//  Master Configuration Register 0 (ram96k)     
	AT91_REG	 MATRIX_MCFG1; 	//  Master Configuration Register 1 (rom)    
	AT91_REG	 MATRIX_MCFG2; 	//  Master Configuration Register 2 (hperiphs) 
	AT91_REG	 MATRIX_MCFG3; 	//  Master Configuration Register 3 (ebi)
	AT91_REG	 MATRIX_MCFG4; 	//  Master Configuration Register 4 (bridge)    
	AT91_REG	 MATRIX_MCFG5; 	//  Master Configuration Register 5 (mailbox)    
	AT91_REG	 MATRIX_MCFG6; 	//  Master Configuration Register 6 (ram16k)  
	AT91_REG	 MATRIX_MCFG7; 	//  Master Configuration Register 7 (teak_prog)     
	AT91_REG	 Reserved0[8]; 	// 
	AT91_REG	 MATRIX_SCFG0; 	//  Slave Configuration Register 0 (ram96k)     
	AT91_REG	 MATRIX_SCFG1; 	//  Slave Configuration Register 1 (rom)    
	AT91_REG	 MATRIX_SCFG2; 	//  Slave Configuration Register 2 (hperiphs) 
	AT91_REG	 MATRIX_SCFG3; 	//  Slave Configuration Register 3 (ebi)
	AT91_REG	 MATRIX_SCFG4; 	//  Slave Configuration Register 4 (bridge)    
	AT91_REG	 Reserved1[11]; 	// 
	AT91_REG	 MATRIX_PRAS0; 	//  PRAS0 (ram0) 
	AT91_REG	 MATRIX_PRBS0; 	//  PRBS0 (ram0) 
	AT91_REG	 MATRIX_PRAS1; 	//  PRAS1 (ram1) 
	AT91_REG	 MATRIX_PRBS1; 	//  PRBS1 (ram1) 
	AT91_REG	 MATRIX_PRAS2; 	//  PRAS2 (ram2) 
	AT91_REG	 MATRIX_PRBS2; 	//  PRBS2 (ram2) 
	AT91_REG	 MATRIX_PRAS3; 	//  PRAS3 : usb_dev_hs
	AT91_REG	 MATRIX_PRBS3; 	//  PRBS3 : usb_dev_hs
	AT91_REG	 MATRIX_PRAS4; 	//  PRAS4 : ebi
	AT91_REG	 MATRIX_PRBS4; 	//  PRBS4 : ebi
	AT91_REG	 Reserved2[22]; 	// 
	AT91_REG	 MATRIX_MRCR; 	//  Master Remp Control Register 
	AT91_REG	 Reserved3[6]; 	// 
	AT91_REG	 MATRIX_EBI; 	//  Slave 3 (ebi) Special Function Register
	AT91_REG	 Reserved4[3]; 	// 
	AT91_REG	 MATRIX_TEAKCFG; 	//  Slave 7 (teak_prog) Special Function Register
	AT91_REG	 Reserved5[51]; 	// 
	AT91_REG	 MATRIX_VERSION; 	//  Version Register
} AT91S_MATRIX, *AT91PS_MATRIX;
#else
#define MATRIX_MCFG0    (AT91_CAST(AT91_REG *) 	0x00000000) // (MATRIX_MCFG0)  Master Configuration Register 0 (ram96k)     
#define MATRIX_MCFG1    (AT91_CAST(AT91_REG *) 	0x00000004) // (MATRIX_MCFG1)  Master Configuration Register 1 (rom)    
#define MATRIX_MCFG2    (AT91_CAST(AT91_REG *) 	0x00000008) // (MATRIX_MCFG2)  Master Configuration Register 2 (hperiphs) 
#define MATRIX_MCFG3    (AT91_CAST(AT91_REG *) 	0x0000000C) // (MATRIX_MCFG3)  Master Configuration Register 3 (ebi)
#define MATRIX_MCFG4    (AT91_CAST(AT91_REG *) 	0x00000010) // (MATRIX_MCFG4)  Master Configuration Register 4 (bridge)    
#define MATRIX_MCFG5    (AT91_CAST(AT91_REG *) 	0x00000014) // (MATRIX_MCFG5)  Master Configuration Register 5 (mailbox)    
#define MATRIX_MCFG6    (AT91_CAST(AT91_REG *) 	0x00000018) // (MATRIX_MCFG6)  Master Configuration Register 6 (ram16k)  
#define MATRIX_MCFG7    (AT91_CAST(AT91_REG *) 	0x0000001C) // (MATRIX_MCFG7)  Master Configuration Register 7 (teak_prog)     
#define MATRIX_SCFG0    (AT91_CAST(AT91_REG *) 	0x00000040) // (MATRIX_SCFG0)  Slave Configuration Register 0 (ram96k)     
#define MATRIX_SCFG1    (AT91_CAST(AT91_REG *) 	0x00000044) // (MATRIX_SCFG1)  Slave Configuration Register 1 (rom)    
#define MATRIX_SCFG2    (AT91_CAST(AT91_REG *) 	0x00000048) // (MATRIX_SCFG2)  Slave Configuration Register 2 (hperiphs) 
#define MATRIX_SCFG3    (AT91_CAST(AT91_REG *) 	0x0000004C) // (MATRIX_SCFG3)  Slave Configuration Register 3 (ebi)
#define MATRIX_SCFG4    (AT91_CAST(AT91_REG *) 	0x00000050) // (MATRIX_SCFG4)  Slave Configuration Register 4 (bridge)    
#define MATRIX_PRAS0    (AT91_CAST(AT91_REG *) 	0x00000080) // (MATRIX_PRAS0)  PRAS0 (ram0) 
#define MATRIX_PRBS0    (AT91_CAST(AT91_REG *) 	0x00000084) // (MATRIX_PRBS0)  PRBS0 (ram0) 
#define MATRIX_PRAS1    (AT91_CAST(AT91_REG *) 	0x00000088) // (MATRIX_PRAS1)  PRAS1 (ram1) 
#define MATRIX_PRBS1    (AT91_CAST(AT91_REG *) 	0x0000008C) // (MATRIX_PRBS1)  PRBS1 (ram1) 
#define MATRIX_PRAS2    (AT91_CAST(AT91_REG *) 	0x00000090) // (MATRIX_PRAS2)  PRAS2 (ram2) 
#define MATRIX_PRBS2    (AT91_CAST(AT91_REG *) 	0x00000094) // (MATRIX_PRBS2)  PRBS2 (ram2) 
#define MATRIX_PRAS3    (AT91_CAST(AT91_REG *) 	0x00000098) // (MATRIX_PRAS3)  PRAS3 : usb_dev_hs
#define MATRIX_PRBS3    (AT91_CAST(AT91_REG *) 	0x0000009C) // (MATRIX_PRBS3)  PRBS3 : usb_dev_hs
#define MATRIX_PRAS4    (AT91_CAST(AT91_REG *) 	0x000000A0) // (MATRIX_PRAS4)  PRAS4 : ebi
#define MATRIX_PRBS4    (AT91_CAST(AT91_REG *) 	0x000000A4) // (MATRIX_PRBS4)  PRBS4 : ebi
#define MATRIX_MRCR     (AT91_CAST(AT91_REG *) 	0x00000100) // (MATRIX_MRCR)  Master Remp Control Register 
#define MATRIX_EBI      (AT91_CAST(AT91_REG *) 	0x0000011C) // (MATRIX_EBI)  Slave 3 (ebi) Special Function Register
#define MATRIX_TEAKCFG  (AT91_CAST(AT91_REG *) 	0x0000012C) // (MATRIX_TEAKCFG)  Slave 7 (teak_prog) Special Function Register
#define MATRIX_VERSION  (AT91_CAST(AT91_REG *) 	0x000001FC) // (MATRIX_VERSION)  Version Register

#endif
// -------- MATRIX_SCFG0 : (MATRIX Offset: 0x40) Slave Configuration Register 0 -------- 
#define AT91C_MATRIX_SLOT_CYCLE (0xFF <<  0) // (MATRIX) Maximum Number of Allowed Cycles for a Burst
#define AT91C_MATRIX_DEFMSTR_TYPE (0x3 << 16) // (MATRIX) Default Master Type
#define 	AT91C_MATRIX_DEFMSTR_TYPE_NO_DEFMSTR           (0x0 << 16) // (MATRIX) No Default Master. At the end of current slave access, if no other master request is pending, the slave is deconnected from all masters. This results in having a one cycle latency for the first transfer of a burst.
#define 	AT91C_MATRIX_DEFMSTR_TYPE_LAST_DEFMSTR         (0x1 << 16) // (MATRIX) Last Default Master. At the end of current slave access, if no other master request is pending, the slave stay connected with the last master having accessed it. This results in not having the one cycle latency when the last master re-trying access on the slave.
#define 	AT91C_MATRIX_DEFMSTR_TYPE_FIXED_DEFMSTR        (0x2 << 16) // (MATRIX) Fixed Default Master. At the end of current slave access, if no other master request is pending, the slave connects with fixed which number is in FIXED_DEFMSTR field. This results in not having the one cycle latency when the fixed master re-trying access on the slave.
#define AT91C_MATRIX_FIXED_DEFMSTR0 (0x7 << 18) // (MATRIX) Fixed Index of Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR0_ARM926I              (0x0 << 18) // (MATRIX) ARM926EJ-S Instruction Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR0_ARM926D              (0x1 << 18) // (MATRIX) ARM926EJ-S Data Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR0_HPDC3                (0x2 << 18) // (MATRIX) HPDC3 Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR0_LCDC                 (0x3 << 18) // (MATRIX) LCDC Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR0_DMA                  (0x4 << 18) // (MATRIX) DMA Master is Default Master
// -------- MATRIX_SCFG1 : (MATRIX Offset: 0x44) Slave Configuration Register 1 -------- 
#define AT91C_MATRIX_FIXED_DEFMSTR1 (0x7 << 18) // (MATRIX) Fixed Index of Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR1_ARM926I              (0x0 << 18) // (MATRIX) ARM926EJ-S Instruction Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR1_ARM926D              (0x1 << 18) // (MATRIX) ARM926EJ-S Data Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR1_HPDC3                (0x2 << 18) // (MATRIX) HPDC3 Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR1_LCDC                 (0x3 << 18) // (MATRIX) LCDC Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR1_DMA                  (0x4 << 18) // (MATRIX) DMA Master is Default Master
// -------- MATRIX_SCFG2 : (MATRIX Offset: 0x48) Slave Configuration Register 2 -------- 
#define AT91C_MATRIX_FIXED_DEFMSTR2 (0x1 << 18) // (MATRIX) Fixed Index of Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR2_ARM926I              (0x0 << 18) // (MATRIX) ARM926EJ-S Instruction Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR2_ARM926D              (0x1 << 18) // (MATRIX) ARM926EJ-S Data Master is Default Master
// -------- MATRIX_SCFG3 : (MATRIX Offset: 0x4c) Slave Configuration Register 3 -------- 
#define AT91C_MATRIX_FIXED_DEFMSTR3 (0x7 << 18) // (MATRIX) Fixed Index of Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR3_ARM926I              (0x0 << 18) // (MATRIX) ARM926EJ-S Instruction Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR3_ARM926D              (0x1 << 18) // (MATRIX) ARM926EJ-S Data Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR3_HPDC3                (0x2 << 18) // (MATRIX) HPDC3 Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR3_LCDC                 (0x3 << 18) // (MATRIX) LCDC Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR3_DMA                  (0x4 << 18) // (MATRIX) DMA Master is Default Master
// -------- MATRIX_SCFG4 : (MATRIX Offset: 0x50) Slave Configuration Register 4 -------- 
#define AT91C_MATRIX_FIXED_DEFMSTR4 (0x3 << 18) // (MATRIX) Fixed Index of Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR4_ARM926I              (0x0 << 18) // (MATRIX) ARM926EJ-S Instruction Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR4_ARM926D              (0x1 << 18) // (MATRIX) ARM926EJ-S Data Master is Default Master
#define 	AT91C_MATRIX_FIXED_DEFMSTR4_HPDC3                (0x2 << 18) // (MATRIX) HPDC3 Master is Default Master
// -------- MATRIX_PRAS0 : (MATRIX Offset: 0x80) PRAS0 Register -------- 
#define AT91C_MATRIX_M0PR     (0x3 <<  0) // (MATRIX) ARM926EJ-S Instruction priority
#define AT91C_MATRIX_M1PR     (0x3 <<  4) // (MATRIX) ARM926EJ-S Data priority
#define AT91C_MATRIX_M2PR     (0x3 <<  8) // (MATRIX) PDC priority
#define AT91C_MATRIX_M3PR     (0x3 << 12) // (MATRIX) LCDC priority
#define AT91C_MATRIX_M4PR     (0x3 << 16) // (MATRIX) 2DGC priority
#define AT91C_MATRIX_M5PR     (0x3 << 20) // (MATRIX) ISI priority
#define AT91C_MATRIX_M6PR     (0x3 << 24) // (MATRIX) DMA priority
#define AT91C_MATRIX_M7PR     (0x3 << 28) // (MATRIX) EMAC priority
// -------- MATRIX_PRBS0 : (MATRIX Offset: 0x84) PRBS0 Register -------- 
#define AT91C_MATRIX_M8PR     (0x3 <<  0) // (MATRIX) USB priority
// -------- MATRIX_PRAS1 : (MATRIX Offset: 0x88) PRAS1 Register -------- 
// -------- MATRIX_PRBS1 : (MATRIX Offset: 0x8c) PRBS1 Register -------- 
// -------- MATRIX_PRAS2 : (MATRIX Offset: 0x90) PRAS2 Register -------- 
// -------- MATRIX_PRBS2 : (MATRIX Offset: 0x94) PRBS2 Register -------- 
// -------- MATRIX_PRAS3 : (MATRIX Offset: 0x98) PRAS3 Register -------- 
// -------- MATRIX_PRBS3 : (MATRIX Offset: 0x9c) PRBS3 Register -------- 
// -------- MATRIX_PRAS4 : (MATRIX Offset: 0xa0) PRAS4 Register -------- 
// -------- MATRIX_PRBS4 : (MATRIX Offset: 0xa4) PRBS4 Register -------- 
// -------- MATRIX_MRCR : (MATRIX Offset: 0x100) MRCR Register -------- 
#define AT91C_MATRIX_RCA926I  (0x1 <<  0) // (MATRIX) Remap Command for ARM926EJ-S Instruction Master
#define AT91C_MATRIX_RCA926D  (0x1 <<  1) // (MATRIX) Remap Command for ARM926EJ-S Data Master
// -------- MATRIX_EBI : (MATRIX Offset: 0x11c) EBI (Slave 3) Special Function Register -------- 
#define AT91C_MATRIX_CS1A     (0x1 <<  1) // (MATRIX) Chip Select 1 Assignment
#define 	AT91C_MATRIX_CS1A_SMC                  (0x0 <<  1) // (MATRIX) Chip Select 1 is assigned to the Static Memory Controller.
#define 	AT91C_MATRIX_CS1A_SDRAMC               (0x1 <<  1) // (MATRIX) Chip Select 1 is assigned to the SDRAM Controller.
#define AT91C_MATRIX_CS3A     (0x1 <<  3) // (MATRIX) Chip Select 3 Assignment
#define 	AT91C_MATRIX_CS3A_SMC                  (0x0 <<  3) // (MATRIX) Chip Select 3 is only assigned to the Static Memory Controller and NCS3 behaves as defined by the SMC.
#define 	AT91C_MATRIX_CS3A_SM                   (0x1 <<  3) // (MATRIX) Chip Select 3 is assigned to the Static Memory Controller and the SmartMedia Logic is activated.
#define AT91C_MATRIX_CS4A     (0x1 <<  4) // (MATRIX) Chip Select 4 Assignment
#define 	AT91C_MATRIX_CS4A_SMC                  (0x0 <<  4) // (MATRIX) Chip Select 4 is only assigned to the Static Memory Controller and NCS4 behaves as defined by the SMC.
#define 	AT91C_MATRIX_CS4A_CF                   (0x1 <<  4) // (MATRIX) Chip Select 4 is assigned to the Static Memory Controller and the CompactFlash Logic (first slot) is activated.
#define AT91C_MATRIX_CS5A     (0x1 <<  5) // (MATRIX) Chip Select 5 Assignment
#define 	AT91C_MATRIX_CS5A_SMC                  (0x0 <<  5) // (MATRIX) Chip Select 5 is only assigned to the Static Memory Controller and NCS5 behaves as defined by the SMC
#define 	AT91C_MATRIX_CS5A_CF                   (0x1 <<  5) // (MATRIX) Chip Select 5 is assigned to the Static Memory Controller and the CompactFlash Logic (second slot) is activated.
#define AT91C_MATRIX_DBPUC    (0x1 <<  8) // (MATRIX) Data Bus Pull-up Configuration
// -------- MATRIX_TEAKCFG : (MATRIX Offset: 0x12c) Slave 7 Special Function Register -------- 
#define AT91C_TEAK_PROGRAM_ACCESS (0x1 <<  0) // (MATRIX) TEAK program memory access from AHB
#define 	AT91C_TEAK_PROGRAM_ACCESS_DISABLED             (0x0) // (MATRIX) TEAK program access disabled
#define 	AT91C_TEAK_PROGRAM_ACCESS_ENABLED              (0x1) // (MATRIX) TEAK program access enabled
#define AT91C_TEAK_BOOT       (0x1 <<  1) // (MATRIX) TEAK program start from boot routine
#define 	AT91C_TEAK_BOOT_DISABLED             (0x0 <<  1) // (MATRIX) TEAK program starts from boot routine disabled
#define 	AT91C_TEAK_BOOT_ENABLED              (0x1 <<  1) // (MATRIX) TEAK program starts from boot routine enabled
#define AT91C_TEAK_NRESET     (0x1 <<  2) // (MATRIX) active low TEAK reset
#define 	AT91C_TEAK_NRESET_ENABLED              (0x0 <<  2) // (MATRIX) active low TEAK reset enabled
#define 	AT91C_TEAK_NRESET_DISABLED             (0x1 <<  2) // (MATRIX) active low TEAK reset disabled
#define AT91C_TEAK_LVECTORP   (0x3FFFF << 14) // (MATRIX) boot routine start address

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Chip Configuration Registers
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_CCFG {
	AT91_REG	 Reserved0[3]; 	// 
	AT91_REG	 CCFG_EBICSA; 	//  EBI Chip Select Assignement Register
	AT91_REG	 Reserved1[55]; 	// 
	AT91_REG	 CCFG_MATRIXVERSION; 	//  Version Register
} AT91S_CCFG, *AT91PS_CCFG;
#else
#define CCFG_EBICSA     (AT91_CAST(AT91_REG *) 	0x0000000C) // (CCFG_EBICSA)  EBI Chip Select Assignement Register
#define CCFG_MATRIXVERSION (AT91_CAST(AT91_REG *) 	0x000000EC) // (CCFG_MATRIXVERSION)  Version Register

#endif
// -------- CCFG_EBICSA : (CCFG Offset: 0xc) EBI Chip Select Assignement Register -------- 
#define AT91C_EBI_CS1A        (0x1 <<  1) // (CCFG) Chip Select 1 Assignment
#define 	AT91C_EBI_CS1A_SMC                  (0x0 <<  1) // (CCFG) Chip Select 1 is assigned to the Static Memory Controller.
#define 	AT91C_EBI_CS1A_SDRAMC               (0x1 <<  1) // (CCFG) Chip Select 1 is assigned to the SDRAM Controller.
#define AT91C_EBI_CS3A        (0x1 <<  3) // (CCFG) Chip Select 3 Assignment
#define 	AT91C_EBI_CS3A_SMC                  (0x0 <<  3) // (CCFG) Chip Select 3 is only assigned to the Static Memory Controller and NCS3 behaves as defined by the SMC.
#define 	AT91C_EBI_CS3A_SM                   (0x1 <<  3) // (CCFG) Chip Select 3 is assigned to the Static Memory Controller and the SmartMedia Logic is activated.
#define AT91C_EBI_CS4A        (0x1 <<  4) // (CCFG) Chip Select 4 Assignment
#define 	AT91C_EBI_CS4A_SMC                  (0x0 <<  4) // (CCFG) Chip Select 4 is only assigned to the Static Memory Controller and NCS4 behaves as defined by the SMC.
#define 	AT91C_EBI_CS4A_CF                   (0x1 <<  4) // (CCFG) Chip Select 4 is assigned to the Static Memory Controller and the CompactFlash Logic (first slot) is activated.
#define AT91C_EBI_CS5A        (0x1 <<  5) // (CCFG) Chip Select 5 Assignment
#define 	AT91C_EBI_CS5A_SMC                  (0x0 <<  5) // (CCFG) Chip Select 5 is only assigned to the Static Memory Controller and NCS5 behaves as defined by the SMC
#define 	AT91C_EBI_CS5A_CF                   (0x1 <<  5) // (CCFG) Chip Select 5 is assigned to the Static Memory Controller and the CompactFlash Logic (second slot) is activated.
#define AT91C_EBI_DBPUC       (0x1 <<  8) // (CCFG) Data Bus Pull-up Configuration
#define AT91C_EBI_SUPPLY      (0x1 << 16) // (CCFG) EBI supply selection

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Peripheral DMA Controller
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_PDC {
	AT91_REG	 PDC_RPR; 	// Receive Pointer Register
	AT91_REG	 PDC_RCR; 	// Receive Counter Register
	AT91_REG	 PDC_TPR; 	// Transmit Pointer Register
	AT91_REG	 PDC_TCR; 	// Transmit Counter Register
	AT91_REG	 PDC_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 PDC_RNCR; 	// Receive Next Counter Register
	AT91_REG	 PDC_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 PDC_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 PDC_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 PDC_PTSR; 	// PDC Transfer Status Register
} AT91S_PDC, *AT91PS_PDC;
#else
#define PDC_RPR         (AT91_CAST(AT91_REG *) 	0x00000000) // (PDC_RPR) Receive Pointer Register
#define PDC_RCR         (AT91_CAST(AT91_REG *) 	0x00000004) // (PDC_RCR) Receive Counter Register
#define PDC_TPR         (AT91_CAST(AT91_REG *) 	0x00000008) // (PDC_TPR) Transmit Pointer Register
#define PDC_TCR         (AT91_CAST(AT91_REG *) 	0x0000000C) // (PDC_TCR) Transmit Counter Register
#define PDC_RNPR        (AT91_CAST(AT91_REG *) 	0x00000010) // (PDC_RNPR) Receive Next Pointer Register
#define PDC_RNCR        (AT91_CAST(AT91_REG *) 	0x00000014) // (PDC_RNCR) Receive Next Counter Register
#define PDC_TNPR        (AT91_CAST(AT91_REG *) 	0x00000018) // (PDC_TNPR) Transmit Next Pointer Register
#define PDC_TNCR        (AT91_CAST(AT91_REG *) 	0x0000001C) // (PDC_TNCR) Transmit Next Counter Register
#define PDC_PTCR        (AT91_CAST(AT91_REG *) 	0x00000020) // (PDC_PTCR) PDC Transfer Control Register
#define PDC_PTSR        (AT91_CAST(AT91_REG *) 	0x00000024) // (PDC_PTSR) PDC Transfer Status Register

#endif
// -------- PDC_PTCR : (PDC Offset: 0x20) PDC Transfer Control Register -------- 
#define AT91C_PDC_RXTEN       (0x1 <<  0) // (PDC) Receiver Transfer Enable
#define AT91C_PDC_RXTDIS      (0x1 <<  1) // (PDC) Receiver Transfer Disable
#define AT91C_PDC_TXTEN       (0x1 <<  8) // (PDC) Transmitter Transfer Enable
#define AT91C_PDC_TXTDIS      (0x1 <<  9) // (PDC) Transmitter Transfer Disable
// -------- PDC_PTSR : (PDC Offset: 0x24) PDC Transfer Status Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Debug Unit
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_DBGU {
	AT91_REG	 DBGU_CR; 	// Control Register
	AT91_REG	 DBGU_MR; 	// Mode Register
	AT91_REG	 DBGU_IER; 	// Interrupt Enable Register
	AT91_REG	 DBGU_IDR; 	// Interrupt Disable Register
	AT91_REG	 DBGU_IMR; 	// Interrupt Mask Register
	AT91_REG	 DBGU_CSR; 	// Channel Status Register
	AT91_REG	 DBGU_RHR; 	// Receiver Holding Register
	AT91_REG	 DBGU_THR; 	// Transmitter Holding Register
	AT91_REG	 DBGU_BRGR; 	// Baud Rate Generator Register
	AT91_REG	 Reserved0[7]; 	// 
	AT91_REG	 DBGU_CIDR; 	// Chip ID Register
	AT91_REG	 DBGU_EXID; 	// Chip ID Extension Register
	AT91_REG	 DBGU_FNTR; 	// Force NTRST Register
	AT91_REG	 Reserved1[45]; 	// 
	AT91_REG	 DBGU_RPR; 	// Receive Pointer Register
	AT91_REG	 DBGU_RCR; 	// Receive Counter Register
	AT91_REG	 DBGU_TPR; 	// Transmit Pointer Register
	AT91_REG	 DBGU_TCR; 	// Transmit Counter Register
	AT91_REG	 DBGU_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 DBGU_RNCR; 	// Receive Next Counter Register
	AT91_REG	 DBGU_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 DBGU_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 DBGU_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 DBGU_PTSR; 	// PDC Transfer Status Register
} AT91S_DBGU, *AT91PS_DBGU;
#else
#define DBGU_CR         (AT91_CAST(AT91_REG *) 	0x00000000) // (DBGU_CR) Control Register
#define DBGU_MR         (AT91_CAST(AT91_REG *) 	0x00000004) // (DBGU_MR) Mode Register
#define DBGU_IER        (AT91_CAST(AT91_REG *) 	0x00000008) // (DBGU_IER) Interrupt Enable Register
#define DBGU_IDR        (AT91_CAST(AT91_REG *) 	0x0000000C) // (DBGU_IDR) Interrupt Disable Register
#define DBGU_IMR        (AT91_CAST(AT91_REG *) 	0x00000010) // (DBGU_IMR) Interrupt Mask Register
#define DBGU_CSR        (AT91_CAST(AT91_REG *) 	0x00000014) // (DBGU_CSR) Channel Status Register
#define DBGU_RHR        (AT91_CAST(AT91_REG *) 	0x00000018) // (DBGU_RHR) Receiver Holding Register
#define DBGU_THR        (AT91_CAST(AT91_REG *) 	0x0000001C) // (DBGU_THR) Transmitter Holding Register
#define DBGU_BRGR       (AT91_CAST(AT91_REG *) 	0x00000020) // (DBGU_BRGR) Baud Rate Generator Register
#define DBGU_CIDR       (AT91_CAST(AT91_REG *) 	0x00000040) // (DBGU_CIDR) Chip ID Register
#define DBGU_EXID       (AT91_CAST(AT91_REG *) 	0x00000044) // (DBGU_EXID) Chip ID Extension Register
#define DBGU_FNTR       (AT91_CAST(AT91_REG *) 	0x00000048) // (DBGU_FNTR) Force NTRST Register

#endif
// -------- DBGU_CR : (DBGU Offset: 0x0) Debug Unit Control Register -------- 
#define AT91C_US_RSTRX        (0x1 <<  2) // (DBGU) Reset Receiver
#define AT91C_US_RSTTX        (0x1 <<  3) // (DBGU) Reset Transmitter
#define AT91C_US_RXEN         (0x1 <<  4) // (DBGU) Receiver Enable
#define AT91C_US_RXDIS        (0x1 <<  5) // (DBGU) Receiver Disable
#define AT91C_US_TXEN         (0x1 <<  6) // (DBGU) Transmitter Enable
#define AT91C_US_TXDIS        (0x1 <<  7) // (DBGU) Transmitter Disable
#define AT91C_US_RSTSTA       (0x1 <<  8) // (DBGU) Reset Status Bits
// -------- DBGU_MR : (DBGU Offset: 0x4) Debug Unit Mode Register -------- 
#define AT91C_US_PAR          (0x7 <<  9) // (DBGU) Parity type
#define 	AT91C_US_PAR_EVEN                 (0x0 <<  9) // (DBGU) Even Parity
#define 	AT91C_US_PAR_ODD                  (0x1 <<  9) // (DBGU) Odd Parity
#define 	AT91C_US_PAR_SPACE                (0x2 <<  9) // (DBGU) Parity forced to 0 (Space)
#define 	AT91C_US_PAR_MARK                 (0x3 <<  9) // (DBGU) Parity forced to 1 (Mark)
#define 	AT91C_US_PAR_NONE                 (0x4 <<  9) // (DBGU) No Parity
#define 	AT91C_US_PAR_MULTI_DROP           (0x6 <<  9) // (DBGU) Multi-drop mode
#define AT91C_US_CHMODE       (0x3 << 14) // (DBGU) Channel Mode
#define 	AT91C_US_CHMODE_NORMAL               (0x0 << 14) // (DBGU) Normal Mode: The USART channel operates as an RX/TX USART.
#define 	AT91C_US_CHMODE_AUTO                 (0x1 << 14) // (DBGU) Automatic Echo: Receiver Data Input is connected to the TXD pin.
#define 	AT91C_US_CHMODE_LOCAL                (0x2 << 14) // (DBGU) Local Loopback: Transmitter Output Signal is connected to Receiver Input Signal.
#define 	AT91C_US_CHMODE_REMOTE               (0x3 << 14) // (DBGU) Remote Loopback: RXD pin is internally connected to TXD pin.
// -------- DBGU_IER : (DBGU Offset: 0x8) Debug Unit Interrupt Enable Register -------- 
#define AT91C_US_RXRDY        (0x1 <<  0) // (DBGU) RXRDY Interrupt
#define AT91C_US_TXRDY        (0x1 <<  1) // (DBGU) TXRDY Interrupt
#define AT91C_US_ENDRX        (0x1 <<  3) // (DBGU) End of Receive Transfer Interrupt
#define AT91C_US_ENDTX        (0x1 <<  4) // (DBGU) End of Transmit Interrupt
#define AT91C_US_OVRE         (0x1 <<  5) // (DBGU) Overrun Interrupt
#define AT91C_US_FRAME        (0x1 <<  6) // (DBGU) Framing Error Interrupt
#define AT91C_US_PARE         (0x1 <<  7) // (DBGU) Parity Error Interrupt
#define AT91C_US_TXEMPTY      (0x1 <<  9) // (DBGU) TXEMPTY Interrupt
#define AT91C_US_TXBUFE       (0x1 << 11) // (DBGU) TXBUFE Interrupt
#define AT91C_US_RXBUFF       (0x1 << 12) // (DBGU) RXBUFF Interrupt
#define AT91C_US_COMM_TX      (0x1 << 30) // (DBGU) COMM_TX Interrupt
#define AT91C_US_COMM_RX      (0x1 << 31) // (DBGU) COMM_RX Interrupt
// -------- DBGU_IDR : (DBGU Offset: 0xc) Debug Unit Interrupt Disable Register -------- 
// -------- DBGU_IMR : (DBGU Offset: 0x10) Debug Unit Interrupt Mask Register -------- 
// -------- DBGU_CSR : (DBGU Offset: 0x14) Debug Unit Channel Status Register -------- 
// -------- DBGU_FNTR : (DBGU Offset: 0x48) Debug Unit FORCE_NTRST Register -------- 
#define AT91C_US_FORCE_NTRST  (0x1 <<  0) // (DBGU) Force NTRST in JTAG

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Advanced Interrupt Controller
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_AIC {
	AT91_REG	 AIC_SMR[32]; 	// Source Mode Register
	AT91_REG	 AIC_SVR[32]; 	// Source Vector Register
	AT91_REG	 AIC_IVR; 	// IRQ Vector Register
	AT91_REG	 AIC_FVR; 	// FIQ Vector Register
	AT91_REG	 AIC_ISR; 	// Interrupt Status Register
	AT91_REG	 AIC_IPR; 	// Interrupt Pending Register
	AT91_REG	 AIC_IMR; 	// Interrupt Mask Register
	AT91_REG	 AIC_CISR; 	// Core Interrupt Status Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 AIC_IECR; 	// Interrupt Enable Command Register
	AT91_REG	 AIC_IDCR; 	// Interrupt Disable Command Register
	AT91_REG	 AIC_ICCR; 	// Interrupt Clear Command Register
	AT91_REG	 AIC_ISCR; 	// Interrupt Set Command Register
	AT91_REG	 AIC_EOICR; 	// End of Interrupt Command Register
	AT91_REG	 AIC_SPU; 	// Spurious Vector Register
	AT91_REG	 AIC_DCR; 	// Debug Control Register (Protect)
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 AIC_FFER; 	// Fast Forcing Enable Register
	AT91_REG	 AIC_FFDR; 	// Fast Forcing Disable Register
	AT91_REG	 AIC_FFSR; 	// Fast Forcing Status Register
} AT91S_AIC, *AT91PS_AIC;
#else
#define AIC_SMR         (AT91_CAST(AT91_REG *) 	0x00000000) // (AIC_SMR) Source Mode Register
#define AIC_SVR         (AT91_CAST(AT91_REG *) 	0x00000080) // (AIC_SVR) Source Vector Register
#define AIC_IVR         (AT91_CAST(AT91_REG *) 	0x00000100) // (AIC_IVR) IRQ Vector Register
#define AIC_FVR         (AT91_CAST(AT91_REG *) 	0x00000104) // (AIC_FVR) FIQ Vector Register
#define AIC_ISR         (AT91_CAST(AT91_REG *) 	0x00000108) // (AIC_ISR) Interrupt Status Register
#define AIC_IPR         (AT91_CAST(AT91_REG *) 	0x0000010C) // (AIC_IPR) Interrupt Pending Register
#define AIC_IMR         (AT91_CAST(AT91_REG *) 	0x00000110) // (AIC_IMR) Interrupt Mask Register
#define AIC_CISR        (AT91_CAST(AT91_REG *) 	0x00000114) // (AIC_CISR) Core Interrupt Status Register
#define AIC_IECR        (AT91_CAST(AT91_REG *) 	0x00000120) // (AIC_IECR) Interrupt Enable Command Register
#define AIC_IDCR        (AT91_CAST(AT91_REG *) 	0x00000124) // (AIC_IDCR) Interrupt Disable Command Register
#define AIC_ICCR        (AT91_CAST(AT91_REG *) 	0x00000128) // (AIC_ICCR) Interrupt Clear Command Register
#define AIC_ISCR        (AT91_CAST(AT91_REG *) 	0x0000012C) // (AIC_ISCR) Interrupt Set Command Register
#define AIC_EOICR       (AT91_CAST(AT91_REG *) 	0x00000130) // (AIC_EOICR) End of Interrupt Command Register
#define AIC_SPU         (AT91_CAST(AT91_REG *) 	0x00000134) // (AIC_SPU) Spurious Vector Register
#define AIC_DCR         (AT91_CAST(AT91_REG *) 	0x00000138) // (AIC_DCR) Debug Control Register (Protect)
#define AIC_FFER        (AT91_CAST(AT91_REG *) 	0x00000140) // (AIC_FFER) Fast Forcing Enable Register
#define AIC_FFDR        (AT91_CAST(AT91_REG *) 	0x00000144) // (AIC_FFDR) Fast Forcing Disable Register
#define AIC_FFSR        (AT91_CAST(AT91_REG *) 	0x00000148) // (AIC_FFSR) Fast Forcing Status Register

#endif
// -------- AIC_SMR : (AIC Offset: 0x0) Control Register -------- 
#define AT91C_AIC_PRIOR       (0x7 <<  0) // (AIC) Priority Level
#define 	AT91C_AIC_PRIOR_LOWEST               (0x0) // (AIC) Lowest priority level
#define 	AT91C_AIC_PRIOR_HIGHEST              (0x7) // (AIC) Highest priority level
#define AT91C_AIC_SRCTYPE     (0x3 <<  5) // (AIC) Interrupt Source Type
#define 	AT91C_AIC_SRCTYPE_INT_LEVEL_SENSITIVE  (0x0 <<  5) // (AIC) Internal Sources Code Label Level Sensitive
#define 	AT91C_AIC_SRCTYPE_INT_EDGE_TRIGGERED   (0x1 <<  5) // (AIC) Internal Sources Code Label Edge triggered
#define 	AT91C_AIC_SRCTYPE_EXT_HIGH_LEVEL       (0x2 <<  5) // (AIC) External Sources Code Label High-level Sensitive
#define 	AT91C_AIC_SRCTYPE_EXT_POSITIVE_EDGE    (0x3 <<  5) // (AIC) External Sources Code Label Positive Edge triggered
// -------- AIC_CISR : (AIC Offset: 0x114) AIC Core Interrupt Status Register -------- 
#define AT91C_AIC_NFIQ        (0x1 <<  0) // (AIC) NFIQ Status
#define AT91C_AIC_NIRQ        (0x1 <<  1) // (AIC) NIRQ Status
// -------- AIC_DCR : (AIC Offset: 0x138) AIC Debug Control Register (Protect) -------- 
#define AT91C_AIC_DCR_PROT    (0x1 <<  0) // (AIC) Protection Mode
#define AT91C_AIC_DCR_GMSK    (0x1 <<  1) // (AIC) General Mask

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Parallel Input Output Controler
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_PIO {
	AT91_REG	 PIO_PER; 	// PIO Enable Register
	AT91_REG	 PIO_PDR; 	// PIO Disable Register
	AT91_REG	 PIO_PSR; 	// PIO Status Register
	AT91_REG	 Reserved0[1]; 	// 
	AT91_REG	 PIO_OER; 	// Output Enable Register
	AT91_REG	 PIO_ODR; 	// Output Disable Registerr
	AT91_REG	 PIO_OSR; 	// Output Status Register
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 PIO_IFER; 	// Input Filter Enable Register
	AT91_REG	 PIO_IFDR; 	// Input Filter Disable Register
	AT91_REG	 PIO_IFSR; 	// Input Filter Status Register
	AT91_REG	 Reserved2[1]; 	// 
	AT91_REG	 PIO_SODR; 	// Set Output Data Register
	AT91_REG	 PIO_CODR; 	// Clear Output Data Register
	AT91_REG	 PIO_ODSR; 	// Output Data Status Register
	AT91_REG	 PIO_PDSR; 	// Pin Data Status Register
	AT91_REG	 PIO_IER; 	// Interrupt Enable Register
	AT91_REG	 PIO_IDR; 	// Interrupt Disable Register
	AT91_REG	 PIO_IMR; 	// Interrupt Mask Register
	AT91_REG	 PIO_ISR; 	// Interrupt Status Register
	AT91_REG	 PIO_MDER; 	// Multi-driver Enable Register
	AT91_REG	 PIO_MDDR; 	// Multi-driver Disable Register
	AT91_REG	 PIO_MDSR; 	// Multi-driver Status Register
	AT91_REG	 Reserved3[1]; 	// 
	AT91_REG	 PIO_PPUDR; 	// Pull-up Disable Register
	AT91_REG	 PIO_PPUER; 	// Pull-up Enable Register
	AT91_REG	 PIO_PPUSR; 	// Pull-up Status Register
	AT91_REG	 Reserved4[1]; 	// 
	AT91_REG	 PIO_ASR; 	// Select A Register
	AT91_REG	 PIO_BSR; 	// Select B Register
	AT91_REG	 PIO_ABSR; 	// AB Select Status Register
	AT91_REG	 Reserved5[9]; 	// 
	AT91_REG	 PIO_OWER; 	// Output Write Enable Register
	AT91_REG	 PIO_OWDR; 	// Output Write Disable Register
	AT91_REG	 PIO_OWSR; 	// Output Write Status Register
} AT91S_PIO, *AT91PS_PIO;
#else
#define PIO_PER         (AT91_CAST(AT91_REG *) 	0x00000000) // (PIO_PER) PIO Enable Register
#define PIO_PDR         (AT91_CAST(AT91_REG *) 	0x00000004) // (PIO_PDR) PIO Disable Register
#define PIO_PSR         (AT91_CAST(AT91_REG *) 	0x00000008) // (PIO_PSR) PIO Status Register
#define PIO_OER         (AT91_CAST(AT91_REG *) 	0x00000010) // (PIO_OER) Output Enable Register
#define PIO_ODR         (AT91_CAST(AT91_REG *) 	0x00000014) // (PIO_ODR) Output Disable Registerr
#define PIO_OSR         (AT91_CAST(AT91_REG *) 	0x00000018) // (PIO_OSR) Output Status Register
#define PIO_IFER        (AT91_CAST(AT91_REG *) 	0x00000020) // (PIO_IFER) Input Filter Enable Register
#define PIO_IFDR        (AT91_CAST(AT91_REG *) 	0x00000024) // (PIO_IFDR) Input Filter Disable Register
#define PIO_IFSR        (AT91_CAST(AT91_REG *) 	0x00000028) // (PIO_IFSR) Input Filter Status Register
#define PIO_SODR        (AT91_CAST(AT91_REG *) 	0x00000030) // (PIO_SODR) Set Output Data Register
#define PIO_CODR        (AT91_CAST(AT91_REG *) 	0x00000034) // (PIO_CODR) Clear Output Data Register
#define PIO_ODSR        (AT91_CAST(AT91_REG *) 	0x00000038) // (PIO_ODSR) Output Data Status Register
#define PIO_PDSR        (AT91_CAST(AT91_REG *) 	0x0000003C) // (PIO_PDSR) Pin Data Status Register
#define PIO_IER         (AT91_CAST(AT91_REG *) 	0x00000040) // (PIO_IER) Interrupt Enable Register
#define PIO_IDR         (AT91_CAST(AT91_REG *) 	0x00000044) // (PIO_IDR) Interrupt Disable Register
#define PIO_IMR         (AT91_CAST(AT91_REG *) 	0x00000048) // (PIO_IMR) Interrupt Mask Register
#define PIO_ISR         (AT91_CAST(AT91_REG *) 	0x0000004C) // (PIO_ISR) Interrupt Status Register
#define PIO_MDER        (AT91_CAST(AT91_REG *) 	0x00000050) // (PIO_MDER) Multi-driver Enable Register
#define PIO_MDDR        (AT91_CAST(AT91_REG *) 	0x00000054) // (PIO_MDDR) Multi-driver Disable Register
#define PIO_MDSR        (AT91_CAST(AT91_REG *) 	0x00000058) // (PIO_MDSR) Multi-driver Status Register
#define PIO_PPUDR       (AT91_CAST(AT91_REG *) 	0x00000060) // (PIO_PPUDR) Pull-up Disable Register
#define PIO_PPUER       (AT91_CAST(AT91_REG *) 	0x00000064) // (PIO_PPUER) Pull-up Enable Register
#define PIO_PPUSR       (AT91_CAST(AT91_REG *) 	0x00000068) // (PIO_PPUSR) Pull-up Status Register
#define PIO_ASR         (AT91_CAST(AT91_REG *) 	0x00000070) // (PIO_ASR) Select A Register
#define PIO_BSR         (AT91_CAST(AT91_REG *) 	0x00000074) // (PIO_BSR) Select B Register
#define PIO_ABSR        (AT91_CAST(AT91_REG *) 	0x00000078) // (PIO_ABSR) AB Select Status Register
#define PIO_OWER        (AT91_CAST(AT91_REG *) 	0x000000A0) // (PIO_OWER) Output Write Enable Register
#define PIO_OWDR        (AT91_CAST(AT91_REG *) 	0x000000A4) // (PIO_OWDR) Output Write Disable Register
#define PIO_OWSR        (AT91_CAST(AT91_REG *) 	0x000000A8) // (PIO_OWSR) Output Write Status Register

#endif

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Embedded Flash Controller 2.0
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_EFC {
	AT91_REG	 EFC_FMR; 	// EFC Flash Mode Register
	AT91_REG	 EFC_FCR; 	// EFC Flash Command Register
	AT91_REG	 EFC_FSR; 	// EFC Flash Status Register
	AT91_REG	 EFC_FRR; 	// EFC Flash Result Register
	AT91_REG	 EFC_FVR; 	// EFC Flash Version Register
} AT91S_EFC, *AT91PS_EFC;
#else
#define EFC_FMR         (AT91_CAST(AT91_REG *) 	0x00000000) // (EFC_FMR) EFC Flash Mode Register
#define EFC_FCR         (AT91_CAST(AT91_REG *) 	0x00000004) // (EFC_FCR) EFC Flash Command Register
#define EFC_FSR         (AT91_CAST(AT91_REG *) 	0x00000008) // (EFC_FSR) EFC Flash Status Register
#define EFC_FRR         (AT91_CAST(AT91_REG *) 	0x0000000C) // (EFC_FRR) EFC Flash Result Register
#define EFC_FVR         (AT91_CAST(AT91_REG *) 	0x00000010) // (EFC_FVR) EFC Flash Version Register

#endif
// -------- EFC_FMR : (EFC Offset: 0x0) EFC Flash Mode Register -------- 
#define AT91C_EFC_FRDY        (0x1 <<  0) // (EFC) Ready Interrupt Enable
#define AT91C_EFC_FWS         (0xF <<  8) // (EFC) Flash Wait State.
#define 	AT91C_EFC_FWS_0WS                  (0x0 <<  8) // (EFC) 0 Wait State
#define 	AT91C_EFC_FWS_1WS                  (0x1 <<  8) // (EFC) 1 Wait State
#define 	AT91C_EFC_FWS_2WS                  (0x2 <<  8) // (EFC) 2 Wait States
#define 	AT91C_EFC_FWS_3WS                  (0x3 <<  8) // (EFC) 3 Wait States
// -------- EFC_FCR : (EFC Offset: 0x4) EFC Flash Command Register -------- 
#define AT91C_EFC_FCMD        (0xFF <<  0) // (EFC) Flash Command
#define 	AT91C_EFC_FCMD_GETD                 (0x0) // (EFC) Get Flash Descriptor
#define 	AT91C_EFC_FCMD_WP                   (0x1) // (EFC) Write Page
#define 	AT91C_EFC_FCMD_WPL                  (0x2) // (EFC) Write Page and Lock
#define 	AT91C_EFC_FCMD_EWP                  (0x3) // (EFC) Erase Page and Write Page
#define 	AT91C_EFC_FCMD_EWPL                 (0x4) // (EFC) Erase Page and Write Page then Lock
#define 	AT91C_EFC_FCMD_EA                   (0x5) // (EFC) Erase All
#define 	AT91C_EFC_FCMD_EPL                  (0x6) // (EFC) Erase Plane
#define 	AT91C_EFC_FCMD_EPA                  (0x7) // (EFC) Erase Pages
#define 	AT91C_EFC_FCMD_SLB                  (0x8) // (EFC) Set Lock Bit
#define 	AT91C_EFC_FCMD_CLB                  (0x9) // (EFC) Clear Lock Bit
#define 	AT91C_EFC_FCMD_GLB                  (0xA) // (EFC) Get Lock Bit
#define 	AT91C_EFC_FCMD_SFB                  (0xB) // (EFC) Set Fuse Bit
#define 	AT91C_EFC_FCMD_CFB                  (0xC) // (EFC) Clear Fuse Bit
#define 	AT91C_EFC_FCMD_GFB                  (0xD) // (EFC) Get Fuse Bit
#define AT91C_EFC_FARG        (0xFFFF <<  8) // (EFC) Flash Command Argument
#define AT91C_EFC_FKEY        (0xFF << 24) // (EFC) Flash Writing Protection Key
// -------- EFC_FSR : (EFC Offset: 0x8) EFC Flash Status Register -------- 
#define AT91C_EFC_FRDY_S      (0x1 <<  0) // (EFC) Flash Ready Status
#define AT91C_EFC_FCMDE       (0x1 <<  1) // (EFC) Flash Command Error Status
#define AT91C_EFC_LOCKE       (0x1 <<  2) // (EFC) Flash Lock Error Status
// -------- EFC_FRR : (EFC Offset: 0xc) EFC Flash Result Register -------- 
#define AT91C_EFC_FVALUE      (0x0 <<  0) // (EFC) Flash Result Value

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Clock Generator Controler
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_CKGR {
	AT91_REG	 CKGR_MOR; 	// Main Oscillator Register
	AT91_REG	 CKGR_MCFR; 	// Main Clock  Frequency Register
	AT91_REG	 CKGR_PLLAR; 	// PLL A Register
	AT91_REG	 CKGR_PLLBR; 	// PLL B Register
} AT91S_CKGR, *AT91PS_CKGR;
#else
#define CKGR_MOR        (AT91_CAST(AT91_REG *) 	0x00000000) // (CKGR_MOR) Main Oscillator Register
#define CKGR_MCFR       (AT91_CAST(AT91_REG *) 	0x00000004) // (CKGR_MCFR) Main Clock  Frequency Register
#define CKGR_PLLAR      (AT91_CAST(AT91_REG *) 	0x00000008) // (CKGR_PLLAR) PLL A Register
#define CKGR_PLLBR      (AT91_CAST(AT91_REG *) 	0x0000000C) // (CKGR_PLLBR) PLL B Register

#endif
// -------- CKGR_MOR : (CKGR Offset: 0x0) Main Oscillator Register -------- 
#define AT91C_CKGR_MOSCEN     (0x1 <<  0) // (CKGR) Main Oscillator Enable
#define AT91C_CKGR_OSCBYPASS  (0x1 <<  1) // (CKGR) Main Oscillator Bypass
#define AT91C_CKGR_OSCOUNT    (0xFF <<  8) // (CKGR) Main Oscillator Start-up Time
// -------- CKGR_MCFR : (CKGR Offset: 0x4) Main Clock Frequency Register -------- 
#define AT91C_CKGR_MAINF      (0xFFFF <<  0) // (CKGR) Main Clock Frequency
#define AT91C_CKGR_MAINRDY    (0x1 << 16) // (CKGR) Main Clock Ready
// -------- CKGR_PLLAR : (CKGR Offset: 0x8) PLL A Register -------- 
#define AT91C_CKGR_DIVA       (0xFF <<  0) // (CKGR) Divider A Selected
#define 	AT91C_CKGR_DIVA_0                    (0x0) // (CKGR) Divider A output is 0
#define 	AT91C_CKGR_DIVA_BYPASS               (0x1) // (CKGR) Divider A is bypassed
#define AT91C_CKGR_PLLACOUNT  (0x3F <<  8) // (CKGR) PLL A Counter
#define AT91C_CKGR_OUTA       (0x3 << 14) // (CKGR) PLL A Output Frequency Range
#define 	AT91C_CKGR_OUTA_0                    (0x0 << 14) // (CKGR) Please refer to the PLLA datasheet
#define 	AT91C_CKGR_OUTA_1                    (0x1 << 14) // (CKGR) Please refer to the PLLA datasheet
#define 	AT91C_CKGR_OUTA_2                    (0x2 << 14) // (CKGR) Please refer to the PLLA datasheet
#define 	AT91C_CKGR_OUTA_3                    (0x3 << 14) // (CKGR) Please refer to the PLLA datasheet
#define AT91C_CKGR_MULA       (0x7FF << 16) // (CKGR) PLL A Multiplier
#define AT91C_CKGR_SRCA       (0x1 << 29) // (CKGR) 
// -------- CKGR_PLLBR : (CKGR Offset: 0xc) PLL B Register -------- 
#define AT91C_CKGR_DIVB       (0xFF <<  0) // (CKGR) Divider B Selected
#define 	AT91C_CKGR_DIVB_0                    (0x0) // (CKGR) Divider B output is 0
#define 	AT91C_CKGR_DIVB_BYPASS               (0x1) // (CKGR) Divider B is bypassed
#define AT91C_CKGR_PLLBCOUNT  (0x3F <<  8) // (CKGR) PLL B Counter
#define AT91C_CKGR_OUTB       (0x3 << 14) // (CKGR) PLL B Output Frequency Range
#define 	AT91C_CKGR_OUTB_0                    (0x0 << 14) // (CKGR) Please refer to the PLLB datasheet
#define 	AT91C_CKGR_OUTB_1                    (0x1 << 14) // (CKGR) Please refer to the PLLB datasheet
#define 	AT91C_CKGR_OUTB_2                    (0x2 << 14) // (CKGR) Please refer to the PLLB datasheet
#define 	AT91C_CKGR_OUTB_3                    (0x3 << 14) // (CKGR) Please refer to the PLLB datasheet
#define AT91C_CKGR_MULB       (0x7FF << 16) // (CKGR) PLL B Multiplier
#define AT91C_CKGR_USBDIV     (0x3 << 28) // (CKGR) Divider for USB Clocks
#define 	AT91C_CKGR_USBDIV_0                    (0x0 << 28) // (CKGR) Divider output is PLL clock output
#define 	AT91C_CKGR_USBDIV_1                    (0x1 << 28) // (CKGR) Divider output is PLL clock output divided by 2
#define 	AT91C_CKGR_USBDIV_2                    (0x2 << 28) // (CKGR) Divider output is PLL clock output divided by 4

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Power Management Controler
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_PMC {
	AT91_REG	 PMC_SCER; 	// System Clock Enable Register
	AT91_REG	 PMC_SCDR; 	// System Clock Disable Register
	AT91_REG	 PMC_SCSR; 	// System Clock Status Register
	AT91_REG	 Reserved0[1]; 	// 
	AT91_REG	 PMC_PCER; 	// Peripheral Clock Enable Register
	AT91_REG	 PMC_PCDR; 	// Peripheral Clock Disable Register
	AT91_REG	 PMC_PCSR; 	// Peripheral Clock Status Register
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 PMC_MOR; 	// Main Oscillator Register
	AT91_REG	 PMC_MCFR; 	// Main Clock  Frequency Register
	AT91_REG	 PMC_PLLAR; 	// PLL A Register
	AT91_REG	 PMC_PLLBR; 	// PLL B Register
	AT91_REG	 PMC_MCKR; 	// Master Clock Register
	AT91_REG	 Reserved2[3]; 	// 
	AT91_REG	 PMC_PCKR[8]; 	// Programmable Clock Register
	AT91_REG	 PMC_IER; 	// Interrupt Enable Register
	AT91_REG	 PMC_IDR; 	// Interrupt Disable Register
	AT91_REG	 PMC_SR; 	// Status Register
	AT91_REG	 PMC_IMR; 	// Interrupt Mask Register
} AT91S_PMC, *AT91PS_PMC;
#else
#define PMC_SCER        (AT91_CAST(AT91_REG *) 	0x00000000) // (PMC_SCER) System Clock Enable Register
#define PMC_SCDR        (AT91_CAST(AT91_REG *) 	0x00000004) // (PMC_SCDR) System Clock Disable Register
#define PMC_SCSR        (AT91_CAST(AT91_REG *) 	0x00000008) // (PMC_SCSR) System Clock Status Register
#define PMC_PCER        (AT91_CAST(AT91_REG *) 	0x00000010) // (PMC_PCER) Peripheral Clock Enable Register
#define PMC_PCDR        (AT91_CAST(AT91_REG *) 	0x00000014) // (PMC_PCDR) Peripheral Clock Disable Register
#define PMC_PCSR        (AT91_CAST(AT91_REG *) 	0x00000018) // (PMC_PCSR) Peripheral Clock Status Register
#define PMC_MCKR        (AT91_CAST(AT91_REG *) 	0x00000030) // (PMC_MCKR) Master Clock Register
#define PMC_PCKR        (AT91_CAST(AT91_REG *) 	0x00000040) // (PMC_PCKR) Programmable Clock Register
#define PMC_IER         (AT91_CAST(AT91_REG *) 	0x00000060) // (PMC_IER) Interrupt Enable Register
#define PMC_IDR         (AT91_CAST(AT91_REG *) 	0x00000064) // (PMC_IDR) Interrupt Disable Register
#define PMC_SR          (AT91_CAST(AT91_REG *) 	0x00000068) // (PMC_SR) Status Register
#define PMC_IMR         (AT91_CAST(AT91_REG *) 	0x0000006C) // (PMC_IMR) Interrupt Mask Register

#endif
// -------- PMC_SCER : (PMC Offset: 0x0) System Clock Enable Register -------- 
#define AT91C_PMC_PCK         (0x1 <<  0) // (PMC) Processor Clock
#define AT91C_PMC_OTG         (0x1 <<  5) // (PMC) USB OTG Clock
#define AT91C_PMC_UHP         (0x1 <<  6) // (PMC) USB Host Port Clock
#define AT91C_PMC_UDP         (0x1 <<  7) // (PMC) USB Device Port Clock
#define AT91C_PMC_PCK0        (0x1 <<  8) // (PMC) Programmable Clock Output
#define AT91C_PMC_PCK1        (0x1 <<  9) // (PMC) Programmable Clock Output
#define AT91C_PMC_PCK2        (0x1 << 10) // (PMC) Programmable Clock Output
#define AT91C_PMC_PCK3        (0x1 << 11) // (PMC) Programmable Clock Output
// -------- PMC_SCDR : (PMC Offset: 0x4) System Clock Disable Register -------- 
// -------- PMC_SCSR : (PMC Offset: 0x8) System Clock Status Register -------- 
// -------- CKGR_MOR : (PMC Offset: 0x20) Main Oscillator Register -------- 
// -------- CKGR_MCFR : (PMC Offset: 0x24) Main Clock Frequency Register -------- 
// -------- CKGR_PLLAR : (PMC Offset: 0x28) PLL A Register -------- 
// -------- CKGR_PLLBR : (PMC Offset: 0x2c) PLL B Register -------- 
// -------- PMC_MCKR : (PMC Offset: 0x30) Master Clock Register -------- 
#define AT91C_PMC_CSS         (0x3 <<  0) // (PMC) Programmable Clock Selection
#define 	AT91C_PMC_CSS_SLOW_CLK             (0x0) // (PMC) Slow Clock is selected
#define 	AT91C_PMC_CSS_MAIN_CLK             (0x1) // (PMC) Main Clock is selected
#define 	AT91C_PMC_CSS_PLLA_CLK             (0x2) // (PMC) Clock from PLL A is selected
#define 	AT91C_PMC_CSS_PLLB_CLK             (0x3) // (PMC) Clock from PLL B is selected
#define AT91C_PMC_PRES        (0x7 <<  2) // (PMC) Programmable Clock Prescaler
#define 	AT91C_PMC_PRES_CLK                  (0x0 <<  2) // (PMC) Selected clock
#define 	AT91C_PMC_PRES_CLK_2                (0x1 <<  2) // (PMC) Selected clock divided by 2
#define 	AT91C_PMC_PRES_CLK_4                (0x2 <<  2) // (PMC) Selected clock divided by 4
#define 	AT91C_PMC_PRES_CLK_8                (0x3 <<  2) // (PMC) Selected clock divided by 8
#define 	AT91C_PMC_PRES_CLK_16               (0x4 <<  2) // (PMC) Selected clock divided by 16
#define 	AT91C_PMC_PRES_CLK_32               (0x5 <<  2) // (PMC) Selected clock divided by 32
#define 	AT91C_PMC_PRES_CLK_64               (0x6 <<  2) // (PMC) Selected clock divided by 64
#define AT91C_PMC_MDIV        (0x3 <<  8) // (PMC) Master Clock Division
#define 	AT91C_PMC_MDIV_1                    (0x0 <<  8) // (PMC) The master clock and the processor clock are the same
#define 	AT91C_PMC_MDIV_2                    (0x1 <<  8) // (PMC) The processor clock is twice as fast as the master clock
#define 	AT91C_PMC_MDIV_3                    (0x2 <<  8) // (PMC) The processor clock is four times faster than the master clock
// -------- PMC_PCKR : (PMC Offset: 0x40) Programmable Clock Register -------- 
// -------- PMC_IER : (PMC Offset: 0x60) PMC Interrupt Enable Register -------- 
#define AT91C_PMC_MOSCS       (0x1 <<  0) // (PMC) MOSC Status/Enable/Disable/Mask
#define AT91C_PMC_LOCKA       (0x1 <<  1) // (PMC) PLL A Status/Enable/Disable/Mask
#define AT91C_PMC_LOCKB       (0x1 <<  2) // (PMC) PLL B Status/Enable/Disable/Mask
#define AT91C_PMC_MCKRDY      (0x1 <<  3) // (PMC) Master Clock Status/Enable/Disable/Mask
#define AT91C_PMC_PCK0RDY     (0x1 <<  8) // (PMC) PCK0_RDY Status/Enable/Disable/Mask
#define AT91C_PMC_PCK1RDY     (0x1 <<  9) // (PMC) PCK1_RDY Status/Enable/Disable/Mask
#define AT91C_PMC_PCK2RDY     (0x1 << 10) // (PMC) PCK2_RDY Status/Enable/Disable/Mask
#define AT91C_PMC_PCK3RDY     (0x1 << 11) // (PMC) PCK3_RDY Status/Enable/Disable/Mask
// -------- PMC_IDR : (PMC Offset: 0x64) PMC Interrupt Disable Register -------- 
// -------- PMC_SR : (PMC Offset: 0x68) PMC Status Register -------- 
// -------- PMC_IMR : (PMC Offset: 0x6c) PMC Interrupt Mask Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Reset Controller Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_RSTC {
	AT91_REG	 RSTC_RCR; 	// Reset Control Register
	AT91_REG	 RSTC_RSR; 	// Reset Status Register
	AT91_REG	 RSTC_RMR; 	// Reset Mode Register
} AT91S_RSTC, *AT91PS_RSTC;
#else
#define RSTC_RCR        (AT91_CAST(AT91_REG *) 	0x00000000) // (RSTC_RCR) Reset Control Register
#define RSTC_RSR        (AT91_CAST(AT91_REG *) 	0x00000004) // (RSTC_RSR) Reset Status Register
#define RSTC_RMR        (AT91_CAST(AT91_REG *) 	0x00000008) // (RSTC_RMR) Reset Mode Register

#endif
// -------- RSTC_RCR : (RSTC Offset: 0x0) Reset Control Register -------- 
#define AT91C_RSTC_PROCRST    (0x1 <<  0) // (RSTC) Processor Reset
#define AT91C_RSTC_ICERST     (0x1 <<  1) // (RSTC) ICE Interface Reset
#define AT91C_RSTC_PERRST     (0x1 <<  2) // (RSTC) Peripheral Reset
#define AT91C_RSTC_EXTRST     (0x1 <<  3) // (RSTC) External Reset
#define AT91C_RSTC_KEY        (0xFF << 24) // (RSTC) Password
// -------- RSTC_RSR : (RSTC Offset: 0x4) Reset Status Register -------- 
#define AT91C_RSTC_URSTS      (0x1 <<  0) // (RSTC) User Reset Status
#define AT91C_RSTC_RSTTYP     (0x7 <<  8) // (RSTC) Reset Type
#define 	AT91C_RSTC_RSTTYP_GENERAL              (0x0 <<  8) // (RSTC) General reset. Both VDDCORE and VDDBU rising.
#define 	AT91C_RSTC_RSTTYP_WAKEUP               (0x1 <<  8) // (RSTC) WakeUp Reset. VDDCORE rising.
#define 	AT91C_RSTC_RSTTYP_WATCHDOG             (0x2 <<  8) // (RSTC) Watchdog Reset. Watchdog overflow occured.
#define 	AT91C_RSTC_RSTTYP_SOFTWARE             (0x3 <<  8) // (RSTC) Software Reset. Processor reset required by the software.
#define 	AT91C_RSTC_RSTTYP_USER                 (0x4 <<  8) // (RSTC) User Reset. NRST pin detected low.
#define AT91C_RSTC_NRSTL      (0x1 << 16) // (RSTC) NRST pin level
#define AT91C_RSTC_SRCMP      (0x1 << 17) // (RSTC) Software Reset Command in Progress.
// -------- RSTC_RMR : (RSTC Offset: 0x8) Reset Mode Register -------- 
#define AT91C_RSTC_URSTEN     (0x1 <<  0) // (RSTC) User Reset Enable
#define AT91C_RSTC_URSTIEN    (0x1 <<  4) // (RSTC) User Reset Interrupt Enable
#define AT91C_RSTC_ERSTL      (0xF <<  8) // (RSTC) User Reset Enable

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Shut Down Controller Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_SHDWC {
	AT91_REG	 SHDWC_SHCR; 	// Shut Down Control Register
	AT91_REG	 SHDWC_SHMR; 	// Shut Down Mode Register
	AT91_REG	 SHDWC_SHSR; 	// Shut Down Status Register
} AT91S_SHDWC, *AT91PS_SHDWC;
#else
#define SHDWC_SHCR      (AT91_CAST(AT91_REG *) 	0x00000000) // (SHDWC_SHCR) Shut Down Control Register
#define SHDWC_SHMR      (AT91_CAST(AT91_REG *) 	0x00000004) // (SHDWC_SHMR) Shut Down Mode Register
#define SHDWC_SHSR      (AT91_CAST(AT91_REG *) 	0x00000008) // (SHDWC_SHSR) Shut Down Status Register

#endif
// -------- SHDWC_SHCR : (SHDWC Offset: 0x0) Shut Down Control Register -------- 
#define AT91C_SHDWC_SHDW      (0x1 <<  0) // (SHDWC) Processor Reset
#define AT91C_SHDWC_KEY       (0xFF << 24) // (SHDWC) Shut down KEY Password
// -------- SHDWC_SHMR : (SHDWC Offset: 0x4) Shut Down Mode Register -------- 
#define AT91C_SHDWC_WKMODE0   (0x3 <<  0) // (SHDWC) Wake Up 0 Mode Selection
#define 	AT91C_SHDWC_WKMODE0_NONE                 (0x0) // (SHDWC) None. No detection is performed on the wake up input.
#define 	AT91C_SHDWC_WKMODE0_HIGH                 (0x1) // (SHDWC) High Level.
#define 	AT91C_SHDWC_WKMODE0_LOW                  (0x2) // (SHDWC) Low Level.
#define 	AT91C_SHDWC_WKMODE0_ANYLEVEL             (0x3) // (SHDWC) Any level change.
#define AT91C_SHDWC_CPTWK0    (0xF <<  4) // (SHDWC) Counter On Wake Up 0
#define AT91C_SHDWC_WKMODE1   (0x3 <<  8) // (SHDWC) Wake Up 1 Mode Selection
#define 	AT91C_SHDWC_WKMODE1_NONE                 (0x0 <<  8) // (SHDWC) None. No detection is performed on the wake up input.
#define 	AT91C_SHDWC_WKMODE1_HIGH                 (0x1 <<  8) // (SHDWC) High Level.
#define 	AT91C_SHDWC_WKMODE1_LOW                  (0x2 <<  8) // (SHDWC) Low Level.
#define 	AT91C_SHDWC_WKMODE1_ANYLEVEL             (0x3 <<  8) // (SHDWC) Any level change.
#define AT91C_SHDWC_CPTWK1    (0xF << 12) // (SHDWC) Counter On Wake Up 1
#define AT91C_SHDWC_RTTWKEN   (0x1 << 16) // (SHDWC) Real Time Timer Wake Up Enable
#define AT91C_SHDWC_RTCWKEN   (0x1 << 17) // (SHDWC) Real Time Clock Wake Up Enable
// -------- SHDWC_SHSR : (SHDWC Offset: 0x8) Shut Down Status Register -------- 
#define AT91C_SHDWC_WAKEUP0   (0x1 <<  0) // (SHDWC) Wake Up 0 Status
#define AT91C_SHDWC_WAKEUP1   (0x1 <<  1) // (SHDWC) Wake Up 1 Status
#define AT91C_SHDWC_FWKUP     (0x1 <<  2) // (SHDWC) Force Wake Up Status
#define AT91C_SHDWC_RTTWK     (0x1 << 16) // (SHDWC) Real Time Timer wake Up
#define AT91C_SHDWC_RTCWK     (0x1 << 17) // (SHDWC) Real Time Clock wake Up

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Real Time Timer Controller Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_RTTC {
	AT91_REG	 RTTC_RTMR; 	// Real-time Mode Register
	AT91_REG	 RTTC_RTAR; 	// Real-time Alarm Register
	AT91_REG	 RTTC_RTVR; 	// Real-time Value Register
	AT91_REG	 RTTC_RTSR; 	// Real-time Status Register
} AT91S_RTTC, *AT91PS_RTTC;
#else
#define RTTC_RTMR       (AT91_CAST(AT91_REG *) 	0x00000000) // (RTTC_RTMR) Real-time Mode Register
#define RTTC_RTAR       (AT91_CAST(AT91_REG *) 	0x00000004) // (RTTC_RTAR) Real-time Alarm Register
#define RTTC_RTVR       (AT91_CAST(AT91_REG *) 	0x00000008) // (RTTC_RTVR) Real-time Value Register
#define RTTC_RTSR       (AT91_CAST(AT91_REG *) 	0x0000000C) // (RTTC_RTSR) Real-time Status Register

#endif
// -------- RTTC_RTMR : (RTTC Offset: 0x0) Real-time Mode Register -------- 
#define AT91C_RTTC_RTPRES     (0xFFFF <<  0) // (RTTC) Real-time Timer Prescaler Value
#define AT91C_RTTC_ALMIEN     (0x1 << 16) // (RTTC) Alarm Interrupt Enable
#define AT91C_RTTC_RTTINCIEN  (0x1 << 17) // (RTTC) Real Time Timer Increment Interrupt Enable
#define AT91C_RTTC_RTTRST     (0x1 << 18) // (RTTC) Real Time Timer Restart
// -------- RTTC_RTAR : (RTTC Offset: 0x4) Real-time Alarm Register -------- 
#define AT91C_RTTC_ALMV       (0x0 <<  0) // (RTTC) Alarm Value
// -------- RTTC_RTVR : (RTTC Offset: 0x8) Current Real-time Value Register -------- 
#define AT91C_RTTC_CRTV       (0x0 <<  0) // (RTTC) Current Real-time Value
// -------- RTTC_RTSR : (RTTC Offset: 0xc) Real-time Status Register -------- 
#define AT91C_RTTC_ALMS       (0x1 <<  0) // (RTTC) Real-time Alarm Status
#define AT91C_RTTC_RTTINC     (0x1 <<  1) // (RTTC) Real-time Timer Increment

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Periodic Interval Timer Controller Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_PITC {
	AT91_REG	 PITC_PIMR; 	// Period Interval Mode Register
	AT91_REG	 PITC_PISR; 	// Period Interval Status Register
	AT91_REG	 PITC_PIVR; 	// Period Interval Value Register
	AT91_REG	 PITC_PIIR; 	// Period Interval Image Register
} AT91S_PITC, *AT91PS_PITC;
#else
#define PITC_PIMR       (AT91_CAST(AT91_REG *) 	0x00000000) // (PITC_PIMR) Period Interval Mode Register
#define PITC_PISR       (AT91_CAST(AT91_REG *) 	0x00000004) // (PITC_PISR) Period Interval Status Register
#define PITC_PIVR       (AT91_CAST(AT91_REG *) 	0x00000008) // (PITC_PIVR) Period Interval Value Register
#define PITC_PIIR       (AT91_CAST(AT91_REG *) 	0x0000000C) // (PITC_PIIR) Period Interval Image Register

#endif
// -------- PITC_PIMR : (PITC Offset: 0x0) Periodic Interval Mode Register -------- 
#define AT91C_PITC_PIV        (0xFFFFF <<  0) // (PITC) Periodic Interval Value
#define AT91C_PITC_PITEN      (0x1 << 24) // (PITC) Periodic Interval Timer Enabled
#define AT91C_PITC_PITIEN     (0x1 << 25) // (PITC) Periodic Interval Timer Interrupt Enable
// -------- PITC_PISR : (PITC Offset: 0x4) Periodic Interval Status Register -------- 
#define AT91C_PITC_PITS       (0x1 <<  0) // (PITC) Periodic Interval Timer Status
// -------- PITC_PIVR : (PITC Offset: 0x8) Periodic Interval Value Register -------- 
#define AT91C_PITC_CPIV       (0xFFFFF <<  0) // (PITC) Current Periodic Interval Value
#define AT91C_PITC_PICNT      (0xFFF << 20) // (PITC) Periodic Interval Counter
// -------- PITC_PIIR : (PITC Offset: 0xc) Periodic Interval Image Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Watchdog Timer Controller Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_WDTC {
	AT91_REG	 WDTC_WDCR; 	// Watchdog Control Register
	AT91_REG	 WDTC_WDMR; 	// Watchdog Mode Register
	AT91_REG	 WDTC_WDSR; 	// Watchdog Status Register
} AT91S_WDTC, *AT91PS_WDTC;
#else
#define WDTC_WDCR       (AT91_CAST(AT91_REG *) 	0x00000000) // (WDTC_WDCR) Watchdog Control Register
#define WDTC_WDMR       (AT91_CAST(AT91_REG *) 	0x00000004) // (WDTC_WDMR) Watchdog Mode Register
#define WDTC_WDSR       (AT91_CAST(AT91_REG *) 	0x00000008) // (WDTC_WDSR) Watchdog Status Register

#endif
// -------- WDTC_WDCR : (WDTC Offset: 0x0) Periodic Interval Image Register -------- 
#define AT91C_WDTC_WDRSTT     (0x1 <<  0) // (WDTC) Watchdog Restart
#define AT91C_WDTC_KEY        (0xFF << 24) // (WDTC) Watchdog KEY Password
// -------- WDTC_WDMR : (WDTC Offset: 0x4) Watchdog Mode Register -------- 
#define AT91C_WDTC_WDV        (0xFFF <<  0) // (WDTC) Watchdog Timer Restart
#define AT91C_WDTC_WDFIEN     (0x1 << 12) // (WDTC) Watchdog Fault Interrupt Enable
#define AT91C_WDTC_WDRSTEN    (0x1 << 13) // (WDTC) Watchdog Reset Enable
#define AT91C_WDTC_WDRPROC    (0x1 << 14) // (WDTC) Watchdog Timer Restart
#define AT91C_WDTC_WDDIS      (0x1 << 15) // (WDTC) Watchdog Disable
#define AT91C_WDTC_WDD        (0xFFF << 16) // (WDTC) Watchdog Delta Value
#define AT91C_WDTC_WDDBGHLT   (0x1 << 28) // (WDTC) Watchdog Debug Halt
#define AT91C_WDTC_WDIDLEHLT  (0x1 << 29) // (WDTC) Watchdog Idle Halt
// -------- WDTC_WDSR : (WDTC Offset: 0x8) Watchdog Status Register -------- 
#define AT91C_WDTC_WDUNF      (0x1 <<  0) // (WDTC) Watchdog Underflow
#define AT91C_WDTC_WDERR      (0x1 <<  1) // (WDTC) Watchdog Error

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Timer Counter Channel Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_TC {
	AT91_REG	 TC_CCR; 	// Channel Control Register
	AT91_REG	 TC_CMR; 	// Channel Mode Register (Capture Mode / Waveform Mode)
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 TC_CV; 	// Counter Value
	AT91_REG	 TC_RA; 	// Register A
	AT91_REG	 TC_RB; 	// Register B
	AT91_REG	 TC_RC; 	// Register C
	AT91_REG	 TC_SR; 	// Status Register
	AT91_REG	 TC_IER; 	// Interrupt Enable Register
	AT91_REG	 TC_IDR; 	// Interrupt Disable Register
	AT91_REG	 TC_IMR; 	// Interrupt Mask Register
} AT91S_TC, *AT91PS_TC;
#else
#define TC_CCR          (AT91_CAST(AT91_REG *) 	0x00000000) // (TC_CCR) Channel Control Register
#define TC_CMR          (AT91_CAST(AT91_REG *) 	0x00000004) // (TC_CMR) Channel Mode Register (Capture Mode / Waveform Mode)
#define TC_CV           (AT91_CAST(AT91_REG *) 	0x00000010) // (TC_CV) Counter Value
#define TC_RA           (AT91_CAST(AT91_REG *) 	0x00000014) // (TC_RA) Register A
#define TC_RB           (AT91_CAST(AT91_REG *) 	0x00000018) // (TC_RB) Register B
#define TC_RC           (AT91_CAST(AT91_REG *) 	0x0000001C) // (TC_RC) Register C
#define TC_SR           (AT91_CAST(AT91_REG *) 	0x00000020) // (TC_SR) Status Register
#define TC_IER          (AT91_CAST(AT91_REG *) 	0x00000024) // (TC_IER) Interrupt Enable Register
#define TC_IDR          (AT91_CAST(AT91_REG *) 	0x00000028) // (TC_IDR) Interrupt Disable Register
#define TC_IMR          (AT91_CAST(AT91_REG *) 	0x0000002C) // (TC_IMR) Interrupt Mask Register

#endif
// -------- TC_CCR : (TC Offset: 0x0) TC Channel Control Register -------- 
#define AT91C_TC_CLKEN        (0x1 <<  0) // (TC) Counter Clock Enable Command
#define AT91C_TC_CLKDIS       (0x1 <<  1) // (TC) Counter Clock Disable Command
#define AT91C_TC_SWTRG        (0x1 <<  2) // (TC) Software Trigger Command
// -------- TC_CMR : (TC Offset: 0x4) TC Channel Mode Register: Capture Mode / Waveform Mode -------- 
#define AT91C_TC_CLKS         (0x7 <<  0) // (TC) Clock Selection
#define 	AT91C_TC_CLKS_TIMER_DIV1_CLOCK     (0x0) // (TC) Clock selected: TIMER_DIV1_CLOCK
#define 	AT91C_TC_CLKS_TIMER_DIV2_CLOCK     (0x1) // (TC) Clock selected: TIMER_DIV2_CLOCK
#define 	AT91C_TC_CLKS_TIMER_DIV3_CLOCK     (0x2) // (TC) Clock selected: TIMER_DIV3_CLOCK
#define 	AT91C_TC_CLKS_TIMER_DIV4_CLOCK     (0x3) // (TC) Clock selected: TIMER_DIV4_CLOCK
#define 	AT91C_TC_CLKS_TIMER_DIV5_CLOCK     (0x4) // (TC) Clock selected: TIMER_DIV5_CLOCK
#define 	AT91C_TC_CLKS_XC0                  (0x5) // (TC) Clock selected: XC0
#define 	AT91C_TC_CLKS_XC1                  (0x6) // (TC) Clock selected: XC1
#define 	AT91C_TC_CLKS_XC2                  (0x7) // (TC) Clock selected: XC2
#define AT91C_TC_CLKI         (0x1 <<  3) // (TC) Clock Invert
#define AT91C_TC_BURST        (0x3 <<  4) // (TC) Burst Signal Selection
#define 	AT91C_TC_BURST_NONE                 (0x0 <<  4) // (TC) The clock is not gated by an external signal
#define 	AT91C_TC_BURST_XC0                  (0x1 <<  4) // (TC) XC0 is ANDed with the selected clock
#define 	AT91C_TC_BURST_XC1                  (0x2 <<  4) // (TC) XC1 is ANDed with the selected clock
#define 	AT91C_TC_BURST_XC2                  (0x3 <<  4) // (TC) XC2 is ANDed with the selected clock
#define AT91C_TC_CPCSTOP      (0x1 <<  6) // (TC) Counter Clock Stopped with RC Compare
#define AT91C_TC_LDBSTOP      (0x1 <<  6) // (TC) Counter Clock Stopped with RB Loading
#define AT91C_TC_CPCDIS       (0x1 <<  7) // (TC) Counter Clock Disable with RC Compare
#define AT91C_TC_LDBDIS       (0x1 <<  7) // (TC) Counter Clock Disabled with RB Loading
#define AT91C_TC_ETRGEDG      (0x3 <<  8) // (TC) External Trigger Edge Selection
#define 	AT91C_TC_ETRGEDG_NONE                 (0x0 <<  8) // (TC) Edge: None
#define 	AT91C_TC_ETRGEDG_RISING               (0x1 <<  8) // (TC) Edge: rising edge
#define 	AT91C_TC_ETRGEDG_FALLING              (0x2 <<  8) // (TC) Edge: falling edge
#define 	AT91C_TC_ETRGEDG_BOTH                 (0x3 <<  8) // (TC) Edge: each edge
#define AT91C_TC_EEVTEDG      (0x3 <<  8) // (TC) External Event Edge Selection
#define 	AT91C_TC_EEVTEDG_NONE                 (0x0 <<  8) // (TC) Edge: None
#define 	AT91C_TC_EEVTEDG_RISING               (0x1 <<  8) // (TC) Edge: rising edge
#define 	AT91C_TC_EEVTEDG_FALLING              (0x2 <<  8) // (TC) Edge: falling edge
#define 	AT91C_TC_EEVTEDG_BOTH                 (0x3 <<  8) // (TC) Edge: each edge
#define AT91C_TC_EEVT         (0x3 << 10) // (TC) External Event  Selection
#define 	AT91C_TC_EEVT_TIOB                 (0x0 << 10) // (TC) Signal selected as external event: TIOB TIOB direction: input
#define 	AT91C_TC_EEVT_XC0                  (0x1 << 10) // (TC) Signal selected as external event: XC0 TIOB direction: output
#define 	AT91C_TC_EEVT_XC1                  (0x2 << 10) // (TC) Signal selected as external event: XC1 TIOB direction: output
#define 	AT91C_TC_EEVT_XC2                  (0x3 << 10) // (TC) Signal selected as external event: XC2 TIOB direction: output
#define AT91C_TC_ABETRG       (0x1 << 10) // (TC) TIOA or TIOB External Trigger Selection
#define AT91C_TC_ENETRG       (0x1 << 12) // (TC) External Event Trigger enable
#define AT91C_TC_WAVESEL      (0x3 << 13) // (TC) Waveform  Selection
#define 	AT91C_TC_WAVESEL_UP                   (0x0 << 13) // (TC) UP mode without atomatic trigger on RC Compare
#define 	AT91C_TC_WAVESEL_UPDOWN               (0x1 << 13) // (TC) UPDOWN mode without automatic trigger on RC Compare
#define 	AT91C_TC_WAVESEL_UP_AUTO              (0x2 << 13) // (TC) UP mode with automatic trigger on RC Compare
#define 	AT91C_TC_WAVESEL_UPDOWN_AUTO          (0x3 << 13) // (TC) UPDOWN mode with automatic trigger on RC Compare
#define AT91C_TC_CPCTRG       (0x1 << 14) // (TC) RC Compare Trigger Enable
#define AT91C_TC_WAVE         (0x1 << 15) // (TC) 
#define AT91C_TC_ACPA         (0x3 << 16) // (TC) RA Compare Effect on TIOA
#define 	AT91C_TC_ACPA_NONE                 (0x0 << 16) // (TC) Effect: none
#define 	AT91C_TC_ACPA_SET                  (0x1 << 16) // (TC) Effect: set
#define 	AT91C_TC_ACPA_CLEAR                (0x2 << 16) // (TC) Effect: clear
#define 	AT91C_TC_ACPA_TOGGLE               (0x3 << 16) // (TC) Effect: toggle
#define AT91C_TC_LDRA         (0x3 << 16) // (TC) RA Loading Selection
#define 	AT91C_TC_LDRA_NONE                 (0x0 << 16) // (TC) Edge: None
#define 	AT91C_TC_LDRA_RISING               (0x1 << 16) // (TC) Edge: rising edge of TIOA
#define 	AT91C_TC_LDRA_FALLING              (0x2 << 16) // (TC) Edge: falling edge of TIOA
#define 	AT91C_TC_LDRA_BOTH                 (0x3 << 16) // (TC) Edge: each edge of TIOA
#define AT91C_TC_ACPC         (0x3 << 18) // (TC) RC Compare Effect on TIOA
#define 	AT91C_TC_ACPC_NONE                 (0x0 << 18) // (TC) Effect: none
#define 	AT91C_TC_ACPC_SET                  (0x1 << 18) // (TC) Effect: set
#define 	AT91C_TC_ACPC_CLEAR                (0x2 << 18) // (TC) Effect: clear
#define 	AT91C_TC_ACPC_TOGGLE               (0x3 << 18) // (TC) Effect: toggle
#define AT91C_TC_LDRB         (0x3 << 18) // (TC) RB Loading Selection
#define 	AT91C_TC_LDRB_NONE                 (0x0 << 18) // (TC) Edge: None
#define 	AT91C_TC_LDRB_RISING               (0x1 << 18) // (TC) Edge: rising edge of TIOA
#define 	AT91C_TC_LDRB_FALLING              (0x2 << 18) // (TC) Edge: falling edge of TIOA
#define 	AT91C_TC_LDRB_BOTH                 (0x3 << 18) // (TC) Edge: each edge of TIOA
#define AT91C_TC_AEEVT        (0x3 << 20) // (TC) External Event Effect on TIOA
#define 	AT91C_TC_AEEVT_NONE                 (0x0 << 20) // (TC) Effect: none
#define 	AT91C_TC_AEEVT_SET                  (0x1 << 20) // (TC) Effect: set
#define 	AT91C_TC_AEEVT_CLEAR                (0x2 << 20) // (TC) Effect: clear
#define 	AT91C_TC_AEEVT_TOGGLE               (0x3 << 20) // (TC) Effect: toggle
#define AT91C_TC_ASWTRG       (0x3 << 22) // (TC) Software Trigger Effect on TIOA
#define 	AT91C_TC_ASWTRG_NONE                 (0x0 << 22) // (TC) Effect: none
#define 	AT91C_TC_ASWTRG_SET                  (0x1 << 22) // (TC) Effect: set
#define 	AT91C_TC_ASWTRG_CLEAR                (0x2 << 22) // (TC) Effect: clear
#define 	AT91C_TC_ASWTRG_TOGGLE               (0x3 << 22) // (TC) Effect: toggle
#define AT91C_TC_BCPB         (0x3 << 24) // (TC) RB Compare Effect on TIOB
#define 	AT91C_TC_BCPB_NONE                 (0x0 << 24) // (TC) Effect: none
#define 	AT91C_TC_BCPB_SET                  (0x1 << 24) // (TC) Effect: set
#define 	AT91C_TC_BCPB_CLEAR                (0x2 << 24) // (TC) Effect: clear
#define 	AT91C_TC_BCPB_TOGGLE               (0x3 << 24) // (TC) Effect: toggle
#define AT91C_TC_BCPC         (0x3 << 26) // (TC) RC Compare Effect on TIOB
#define 	AT91C_TC_BCPC_NONE                 (0x0 << 26) // (TC) Effect: none
#define 	AT91C_TC_BCPC_SET                  (0x1 << 26) // (TC) Effect: set
#define 	AT91C_TC_BCPC_CLEAR                (0x2 << 26) // (TC) Effect: clear
#define 	AT91C_TC_BCPC_TOGGLE               (0x3 << 26) // (TC) Effect: toggle
#define AT91C_TC_BEEVT        (0x3 << 28) // (TC) External Event Effect on TIOB
#define 	AT91C_TC_BEEVT_NONE                 (0x0 << 28) // (TC) Effect: none
#define 	AT91C_TC_BEEVT_SET                  (0x1 << 28) // (TC) Effect: set
#define 	AT91C_TC_BEEVT_CLEAR                (0x2 << 28) // (TC) Effect: clear
#define 	AT91C_TC_BEEVT_TOGGLE               (0x3 << 28) // (TC) Effect: toggle
#define AT91C_TC_BSWTRG       (0x3 << 30) // (TC) Software Trigger Effect on TIOB
#define 	AT91C_TC_BSWTRG_NONE                 (0x0 << 30) // (TC) Effect: none
#define 	AT91C_TC_BSWTRG_SET                  (0x1 << 30) // (TC) Effect: set
#define 	AT91C_TC_BSWTRG_CLEAR                (0x2 << 30) // (TC) Effect: clear
#define 	AT91C_TC_BSWTRG_TOGGLE               (0x3 << 30) // (TC) Effect: toggle
// -------- TC_SR : (TC Offset: 0x20) TC Channel Status Register -------- 
#define AT91C_TC_COVFS        (0x1 <<  0) // (TC) Counter Overflow
#define AT91C_TC_LOVRS        (0x1 <<  1) // (TC) Load Overrun
#define AT91C_TC_CPAS         (0x1 <<  2) // (TC) RA Compare
#define AT91C_TC_CPBS         (0x1 <<  3) // (TC) RB Compare
#define AT91C_TC_CPCS         (0x1 <<  4) // (TC) RC Compare
#define AT91C_TC_LDRAS        (0x1 <<  5) // (TC) RA Loading
#define AT91C_TC_LDRBS        (0x1 <<  6) // (TC) RB Loading
#define AT91C_TC_ETRGS        (0x1 <<  7) // (TC) External Trigger
#define AT91C_TC_CLKSTA       (0x1 << 16) // (TC) Clock Enabling
#define AT91C_TC_MTIOA        (0x1 << 17) // (TC) TIOA Mirror
#define AT91C_TC_MTIOB        (0x1 << 18) // (TC) TIOA Mirror
// -------- TC_IER : (TC Offset: 0x24) TC Channel Interrupt Enable Register -------- 
// -------- TC_IDR : (TC Offset: 0x28) TC Channel Interrupt Disable Register -------- 
// -------- TC_IMR : (TC Offset: 0x2c) TC Channel Interrupt Mask Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Timer Counter Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_TCB {
	AT91S_TC	 TCB_TC0; 	// TC Channel 0
	AT91_REG	 Reserved0[4]; 	// 
	AT91S_TC	 TCB_TC1; 	// TC Channel 1
	AT91_REG	 Reserved1[4]; 	// 
	AT91S_TC	 TCB_TC2; 	// TC Channel 2
	AT91_REG	 Reserved2[4]; 	// 
	AT91_REG	 TCB_BCR; 	// TC Block Control Register
	AT91_REG	 TCB_BMR; 	// TC Block Mode Register
} AT91S_TCB, *AT91PS_TCB;
#else
#define TCB_BCR         (AT91_CAST(AT91_REG *) 	0x000000C0) // (TCB_BCR) TC Block Control Register
#define TCB_BMR         (AT91_CAST(AT91_REG *) 	0x000000C4) // (TCB_BMR) TC Block Mode Register

#endif
// -------- TCB_BCR : (TCB Offset: 0xc0) TC Block Control Register -------- 
#define AT91C_TCB_SYNC        (0x1 <<  0) // (TCB) Synchro Command
// -------- TCB_BMR : (TCB Offset: 0xc4) TC Block Mode Register -------- 
#define AT91C_TCB_TC0XC0S     (0x3 <<  0) // (TCB) External Clock Signal 0 Selection
#define 	AT91C_TCB_TC0XC0S_TCLK0                (0x0) // (TCB) TCLK0 connected to XC0
#define 	AT91C_TCB_TC0XC0S_NONE                 (0x1) // (TCB) None signal connected to XC0
#define 	AT91C_TCB_TC0XC0S_TIOA1                (0x2) // (TCB) TIOA1 connected to XC0
#define 	AT91C_TCB_TC0XC0S_TIOA2                (0x3) // (TCB) TIOA2 connected to XC0
#define AT91C_TCB_TC1XC1S     (0x3 <<  2) // (TCB) External Clock Signal 1 Selection
#define 	AT91C_TCB_TC1XC1S_TCLK1                (0x0 <<  2) // (TCB) TCLK1 connected to XC1
#define 	AT91C_TCB_TC1XC1S_NONE                 (0x1 <<  2) // (TCB) None signal connected to XC1
#define 	AT91C_TCB_TC1XC1S_TIOA0                (0x2 <<  2) // (TCB) TIOA0 connected to XC1
#define 	AT91C_TCB_TC1XC1S_TIOA2                (0x3 <<  2) // (TCB) TIOA2 connected to XC1
#define AT91C_TCB_TC2XC2S     (0x3 <<  4) // (TCB) External Clock Signal 2 Selection
#define 	AT91C_TCB_TC2XC2S_TCLK2                (0x0 <<  4) // (TCB) TCLK2 connected to XC2
#define 	AT91C_TCB_TC2XC2S_NONE                 (0x1 <<  4) // (TCB) None signal connected to XC2
#define 	AT91C_TCB_TC2XC2S_TIOA0                (0x2 <<  4) // (TCB) TIOA0 connected to XC2
#define 	AT91C_TCB_TC2XC2S_TIOA1                (0x3 <<  4) // (TCB) TIOA2 connected to XC2

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Multimedia Card Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_MCI {
	AT91_REG	 MCI_CR; 	// MCI Control Register
	AT91_REG	 MCI_MR; 	// MCI Mode Register
	AT91_REG	 MCI_DTOR; 	// MCI Data Timeout Register
	AT91_REG	 MCI_SDCR; 	// MCI SD Card Register
	AT91_REG	 MCI_ARGR; 	// MCI Argument Register
	AT91_REG	 MCI_CMDR; 	// MCI Command Register
	AT91_REG	 MCI_BLKR; 	// MCI Block Register
	AT91_REG	 Reserved0[1]; 	// 
	AT91_REG	 MCI_RSPR[4]; 	// MCI Response Register
	AT91_REG	 MCI_RDR; 	// MCI Receive Data Register
	AT91_REG	 MCI_TDR; 	// MCI Transmit Data Register
	AT91_REG	 Reserved1[2]; 	// 
	AT91_REG	 MCI_SR; 	// MCI Status Register
	AT91_REG	 MCI_IER; 	// MCI Interrupt Enable Register
	AT91_REG	 MCI_IDR; 	// MCI Interrupt Disable Register
	AT91_REG	 MCI_IMR; 	// MCI Interrupt Mask Register
	AT91_REG	 Reserved2[43]; 	// 
	AT91_REG	 MCI_VR; 	// MCI Version Register
	AT91_REG	 MCI_RPR; 	// Receive Pointer Register
	AT91_REG	 MCI_RCR; 	// Receive Counter Register
	AT91_REG	 MCI_TPR; 	// Transmit Pointer Register
	AT91_REG	 MCI_TCR; 	// Transmit Counter Register
	AT91_REG	 MCI_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 MCI_RNCR; 	// Receive Next Counter Register
	AT91_REG	 MCI_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 MCI_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 MCI_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 MCI_PTSR; 	// PDC Transfer Status Register
} AT91S_MCI, *AT91PS_MCI;
#else
#define MCI_CR          (AT91_CAST(AT91_REG *) 	0x00000000) // (MCI_CR) MCI Control Register
#define MCI_MR          (AT91_CAST(AT91_REG *) 	0x00000004) // (MCI_MR) MCI Mode Register
#define MCI_DTOR        (AT91_CAST(AT91_REG *) 	0x00000008) // (MCI_DTOR) MCI Data Timeout Register
#define MCI_SDCR        (AT91_CAST(AT91_REG *) 	0x0000000C) // (MCI_SDCR) MCI SD Card Register
#define MCI_ARGR        (AT91_CAST(AT91_REG *) 	0x00000010) // (MCI_ARGR) MCI Argument Register
#define MCI_CMDR        (AT91_CAST(AT91_REG *) 	0x00000014) // (MCI_CMDR) MCI Command Register
#define MCI_BLKR        (AT91_CAST(AT91_REG *) 	0x00000018) // (MCI_BLKR) MCI Block Register
#define MCI_RSPR        (AT91_CAST(AT91_REG *) 	0x00000020) // (MCI_RSPR) MCI Response Register
#define MCI_RDR         (AT91_CAST(AT91_REG *) 	0x00000030) // (MCI_RDR) MCI Receive Data Register
#define MCI_TDR         (AT91_CAST(AT91_REG *) 	0x00000034) // (MCI_TDR) MCI Transmit Data Register
#define MCI_SR          (AT91_CAST(AT91_REG *) 	0x00000040) // (MCI_SR) MCI Status Register
#define MCI_IER         (AT91_CAST(AT91_REG *) 	0x00000044) // (MCI_IER) MCI Interrupt Enable Register
#define MCI_IDR         (AT91_CAST(AT91_REG *) 	0x00000048) // (MCI_IDR) MCI Interrupt Disable Register
#define MCI_IMR         (AT91_CAST(AT91_REG *) 	0x0000004C) // (MCI_IMR) MCI Interrupt Mask Register
#define MCI_VR          (AT91_CAST(AT91_REG *) 	0x000000FC) // (MCI_VR) MCI Version Register

#endif
// -------- MCI_CR : (MCI Offset: 0x0) MCI Control Register -------- 
#define AT91C_MCI_MCIEN       (0x1 <<  0) // (MCI) Multimedia Interface Enable
#define AT91C_MCI_MCIDIS      (0x1 <<  1) // (MCI) Multimedia Interface Disable
#define AT91C_MCI_PWSEN       (0x1 <<  2) // (MCI) Power Save Mode Enable
#define AT91C_MCI_PWSDIS      (0x1 <<  3) // (MCI) Power Save Mode Disable
#define AT91C_MCI_SWRST       (0x1 <<  7) // (MCI) MCI Software reset
// -------- MCI_MR : (MCI Offset: 0x4) MCI Mode Register -------- 
#define AT91C_MCI_CLKDIV      (0xFF <<  0) // (MCI) Clock Divider
#define AT91C_MCI_PWSDIV      (0x7 <<  8) // (MCI) Power Saving Divider
#define AT91C_MCI_RDPROOF     (0x1 << 11) // (MCI) Read Proof Enable
#define AT91C_MCI_WRPROOF     (0x1 << 12) // (MCI) Write Proof Enable
#define AT91C_MCI_PDCFBYTE    (0x1 << 13) // (MCI) PDC Force Byte Transfer
#define AT91C_MCI_PDCPADV     (0x1 << 14) // (MCI) PDC Padding Value
#define AT91C_MCI_PDCMODE     (0x1 << 15) // (MCI) PDC Oriented Mode
#define AT91C_MCI_BLKLEN      (0xFFFF << 16) // (MCI) Data Block Length
// -------- MCI_DTOR : (MCI Offset: 0x8) MCI Data Timeout Register -------- 
#define AT91C_MCI_DTOCYC      (0xF <<  0) // (MCI) Data Timeout Cycle Number
#define AT91C_MCI_DTOMUL      (0x7 <<  4) // (MCI) Data Timeout Multiplier
#define 	AT91C_MCI_DTOMUL_1                    (0x0 <<  4) // (MCI) DTOCYC x 1
#define 	AT91C_MCI_DTOMUL_16                   (0x1 <<  4) // (MCI) DTOCYC x 16
#define 	AT91C_MCI_DTOMUL_128                  (0x2 <<  4) // (MCI) DTOCYC x 128
#define 	AT91C_MCI_DTOMUL_256                  (0x3 <<  4) // (MCI) DTOCYC x 256
#define 	AT91C_MCI_DTOMUL_1024                 (0x4 <<  4) // (MCI) DTOCYC x 1024
#define 	AT91C_MCI_DTOMUL_4096                 (0x5 <<  4) // (MCI) DTOCYC x 4096
#define 	AT91C_MCI_DTOMUL_65536                (0x6 <<  4) // (MCI) DTOCYC x 65536
#define 	AT91C_MCI_DTOMUL_1048576              (0x7 <<  4) // (MCI) DTOCYC x 1048576
// -------- MCI_SDCR : (MCI Offset: 0xc) MCI SD Card Register -------- 
#define AT91C_MCI_SCDSEL      (0x3 <<  0) // (MCI) SD Card Selector
#define AT91C_MCI_SCDBUS      (0x1 <<  7) // (MCI) SDCard/SDIO Bus Width
// -------- MCI_CMDR : (MCI Offset: 0x14) MCI Command Register -------- 
#define AT91C_MCI_CMDNB       (0x3F <<  0) // (MCI) Command Number
#define AT91C_MCI_RSPTYP      (0x3 <<  6) // (MCI) Response Type
#define 	AT91C_MCI_RSPTYP_NO                   (0x0 <<  6) // (MCI) No response
#define 	AT91C_MCI_RSPTYP_48                   (0x1 <<  6) // (MCI) 48-bit response
#define 	AT91C_MCI_RSPTYP_136                  (0x2 <<  6) // (MCI) 136-bit response
#define AT91C_MCI_SPCMD       (0x7 <<  8) // (MCI) Special CMD
#define 	AT91C_MCI_SPCMD_NONE                 (0x0 <<  8) // (MCI) Not a special CMD
#define 	AT91C_MCI_SPCMD_INIT                 (0x1 <<  8) // (MCI) Initialization CMD
#define 	AT91C_MCI_SPCMD_SYNC                 (0x2 <<  8) // (MCI) Synchronized CMD
#define 	AT91C_MCI_SPCMD_IT_CMD               (0x4 <<  8) // (MCI) Interrupt command
#define 	AT91C_MCI_SPCMD_IT_REP               (0x5 <<  8) // (MCI) Interrupt response
#define AT91C_MCI_OPDCMD      (0x1 << 11) // (MCI) Open Drain Command
#define AT91C_MCI_MAXLAT      (0x1 << 12) // (MCI) Maximum Latency for Command to respond
#define AT91C_MCI_TRCMD       (0x3 << 16) // (MCI) Transfer CMD
#define 	AT91C_MCI_TRCMD_NO                   (0x0 << 16) // (MCI) No transfer
#define 	AT91C_MCI_TRCMD_START                (0x1 << 16) // (MCI) Start transfer
#define 	AT91C_MCI_TRCMD_STOP                 (0x2 << 16) // (MCI) Stop transfer
#define AT91C_MCI_TRDIR       (0x1 << 18) // (MCI) Transfer Direction
#define AT91C_MCI_TRTYP       (0x7 << 19) // (MCI) Transfer Type
#define 	AT91C_MCI_TRTYP_BLOCK                (0x0 << 19) // (MCI) MMC/SDCard Single Block Transfer type
#define 	AT91C_MCI_TRTYP_MULTIPLE             (0x1 << 19) // (MCI) MMC/SDCard Multiple Block transfer type
#define 	AT91C_MCI_TRTYP_STREAM               (0x2 << 19) // (MCI) MMC Stream transfer type
#define 	AT91C_MCI_TRTYP_SDIO_BYTE            (0x4 << 19) // (MCI) SDIO Byte transfer type
#define 	AT91C_MCI_TRTYP_SDIO_BLOCK           (0x5 << 19) // (MCI) SDIO Block transfer type
#define AT91C_MCI_IOSPCMD     (0x3 << 24) // (MCI) SDIO Special Command
#define 	AT91C_MCI_IOSPCMD_NONE                 (0x0 << 24) // (MCI) NOT a special command
#define 	AT91C_MCI_IOSPCMD_SUSPEND              (0x1 << 24) // (MCI) SDIO Suspend Command
#define 	AT91C_MCI_IOSPCMD_RESUME               (0x2 << 24) // (MCI) SDIO Resume Command
// -------- MCI_BLKR : (MCI Offset: 0x18) MCI Block Register -------- 
#define AT91C_MCI_BCNT        (0xFFFF <<  0) // (MCI) MMC/SDIO Block Count / SDIO Byte Count
// -------- MCI_SR : (MCI Offset: 0x40) MCI Status Register -------- 
#define AT91C_MCI_CMDRDY      (0x1 <<  0) // (MCI) Command Ready flag
#define AT91C_MCI_RXRDY       (0x1 <<  1) // (MCI) RX Ready flag
#define AT91C_MCI_TXRDY       (0x1 <<  2) // (MCI) TX Ready flag
#define AT91C_MCI_BLKE        (0x1 <<  3) // (MCI) Data Block Transfer Ended flag
#define AT91C_MCI_DTIP        (0x1 <<  4) // (MCI) Data Transfer in Progress flag
#define AT91C_MCI_NOTBUSY     (0x1 <<  5) // (MCI) Data Line Not Busy flag
#define AT91C_MCI_ENDRX       (0x1 <<  6) // (MCI) End of RX Buffer flag
#define AT91C_MCI_ENDTX       (0x1 <<  7) // (MCI) End of TX Buffer flag
#define AT91C_MCI_SDIOIRQA    (0x1 <<  8) // (MCI) SDIO Interrupt for Slot A
#define AT91C_MCI_SDIOIRQB    (0x1 <<  9) // (MCI) SDIO Interrupt for Slot B
#define AT91C_MCI_SDIOIRQC    (0x1 << 10) // (MCI) SDIO Interrupt for Slot C
#define AT91C_MCI_SDIOIRQD    (0x1 << 11) // (MCI) SDIO Interrupt for Slot D
#define AT91C_MCI_RXBUFF      (0x1 << 14) // (MCI) RX Buffer Full flag
#define AT91C_MCI_TXBUFE      (0x1 << 15) // (MCI) TX Buffer Empty flag
#define AT91C_MCI_RINDE       (0x1 << 16) // (MCI) Response Index Error flag
#define AT91C_MCI_RDIRE       (0x1 << 17) // (MCI) Response Direction Error flag
#define AT91C_MCI_RCRCE       (0x1 << 18) // (MCI) Response CRC Error flag
#define AT91C_MCI_RENDE       (0x1 << 19) // (MCI) Response End Bit Error flag
#define AT91C_MCI_RTOE        (0x1 << 20) // (MCI) Response Time-out Error flag
#define AT91C_MCI_DCRCE       (0x1 << 21) // (MCI) data CRC Error flag
#define AT91C_MCI_DTOE        (0x1 << 22) // (MCI) Data timeout Error flag
#define AT91C_MCI_OVRE        (0x1 << 30) // (MCI) Overrun flag
#define AT91C_MCI_UNRE        (0x1 << 31) // (MCI) Underrun flag
// -------- MCI_IER : (MCI Offset: 0x44) MCI Interrupt Enable Register -------- 
// -------- MCI_IDR : (MCI Offset: 0x48) MCI Interrupt Disable Register -------- 
// -------- MCI_IMR : (MCI Offset: 0x4c) MCI Interrupt Mask Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Two-wire Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_TWI {
	AT91_REG	 TWI_CR; 	// Control Register
	AT91_REG	 TWI_MMR; 	// Master Mode Register
	AT91_REG	 TWI_SMR; 	// Slave Mode Register
	AT91_REG	 TWI_IADR; 	// Internal Address Register
	AT91_REG	 TWI_CWGR; 	// Clock Waveform Generator Register
	AT91_REG	 Reserved0[3]; 	// 
	AT91_REG	 TWI_SR; 	// Status Register
	AT91_REG	 TWI_IER; 	// Interrupt Enable Register
	AT91_REG	 TWI_IDR; 	// Interrupt Disable Register
	AT91_REG	 TWI_IMR; 	// Interrupt Mask Register
	AT91_REG	 TWI_RHR; 	// Receive Holding Register
	AT91_REG	 TWI_THR; 	// Transmit Holding Register
	AT91_REG	 Reserved1[50]; 	// 
	AT91_REG	 TWI_RPR; 	// Receive Pointer Register
	AT91_REG	 TWI_RCR; 	// Receive Counter Register
	AT91_REG	 TWI_TPR; 	// Transmit Pointer Register
	AT91_REG	 TWI_TCR; 	// Transmit Counter Register
	AT91_REG	 TWI_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 TWI_RNCR; 	// Receive Next Counter Register
	AT91_REG	 TWI_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 TWI_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 TWI_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 TWI_PTSR; 	// PDC Transfer Status Register
} AT91S_TWI, *AT91PS_TWI;
#else
#define TWI_CR          (AT91_CAST(AT91_REG *) 	0x00000000) // (TWI_CR) Control Register
#define TWI_MMR         (AT91_CAST(AT91_REG *) 	0x00000004) // (TWI_MMR) Master Mode Register
#define TWI_SMR         (AT91_CAST(AT91_REG *) 	0x00000008) // (TWI_SMR) Slave Mode Register
#define TWI_IADR        (AT91_CAST(AT91_REG *) 	0x0000000C) // (TWI_IADR) Internal Address Register
#define TWI_CWGR        (AT91_CAST(AT91_REG *) 	0x00000010) // (TWI_CWGR) Clock Waveform Generator Register
#define TWI_SR          (AT91_CAST(AT91_REG *) 	0x00000020) // (TWI_SR) Status Register
#define TWI_IER         (AT91_CAST(AT91_REG *) 	0x00000024) // (TWI_IER) Interrupt Enable Register
#define TWI_IDR         (AT91_CAST(AT91_REG *) 	0x00000028) // (TWI_IDR) Interrupt Disable Register
#define TWI_IMR         (AT91_CAST(AT91_REG *) 	0x0000002C) // (TWI_IMR) Interrupt Mask Register
#define TWI_RHR         (AT91_CAST(AT91_REG *) 	0x00000030) // (TWI_RHR) Receive Holding Register
#define TWI_THR         (AT91_CAST(AT91_REG *) 	0x00000034) // (TWI_THR) Transmit Holding Register

#endif
// -------- TWI_CR : (TWI Offset: 0x0) TWI Control Register -------- 
#define AT91C_TWI_START       (0x1 <<  0) // (TWI) Send a START Condition
#define AT91C_TWI_STOP        (0x1 <<  1) // (TWI) Send a STOP Condition
#define AT91C_TWI_MSEN        (0x1 <<  2) // (TWI) TWI Master Transfer Enabled
#define AT91C_TWI_MSDIS       (0x1 <<  3) // (TWI) TWI Master Transfer Disabled
#define AT91C_TWI_SVEN        (0x1 <<  4) // (TWI) TWI Slave mode Enabled
#define AT91C_TWI_SVDIS       (0x1 <<  5) // (TWI) TWI Slave mode Disabled
#define AT91C_TWI_SWRST       (0x1 <<  7) // (TWI) Software Reset
// -------- TWI_MMR : (TWI Offset: 0x4) TWI Master Mode Register -------- 
#define AT91C_TWI_IADRSZ      (0x3 <<  8) // (TWI) Internal Device Address Size
#define 	AT91C_TWI_IADRSZ_NO                   (0x0 <<  8) // (TWI) No internal device address
#define 	AT91C_TWI_IADRSZ_1_BYTE               (0x1 <<  8) // (TWI) One-byte internal device address
#define 	AT91C_TWI_IADRSZ_2_BYTE               (0x2 <<  8) // (TWI) Two-byte internal device address
#define 	AT91C_TWI_IADRSZ_3_BYTE               (0x3 <<  8) // (TWI) Three-byte internal device address
#define AT91C_TWI_MREAD       (0x1 << 12) // (TWI) Master Read Direction
#define AT91C_TWI_DADR        (0x7F << 16) // (TWI) Device Address
// -------- TWI_SMR : (TWI Offset: 0x8) TWI Slave Mode Register -------- 
#define AT91C_TWI_SADR        (0x7F << 16) // (TWI) Slave Address
// -------- TWI_CWGR : (TWI Offset: 0x10) TWI Clock Waveform Generator Register -------- 
#define AT91C_TWI_CLDIV       (0xFF <<  0) // (TWI) Clock Low Divider
#define AT91C_TWI_CHDIV       (0xFF <<  8) // (TWI) Clock High Divider
#define AT91C_TWI_CKDIV       (0x7 << 16) // (TWI) Clock Divider
// -------- TWI_SR : (TWI Offset: 0x20) TWI Status Register -------- 
#define AT91C_TWI_TXCOMP_SLAVE (0x1 <<  0) // (TWI) Transmission Completed
#define AT91C_TWI_TXCOMP_MASTER (0x1 <<  0) // (TWI) Transmission Completed
#define AT91C_TWI_RXRDY       (0x1 <<  1) // (TWI) Receive holding register ReaDY
#define AT91C_TWI_TXRDY_MASTER (0x1 <<  2) // (TWI) Transmit holding register ReaDY
#define AT91C_TWI_TXRDY_SLAVE (0x1 <<  2) // (TWI) Transmit holding register ReaDY
#define AT91C_TWI_SVREAD      (0x1 <<  3) // (TWI) Slave READ (used only in Slave mode)
#define AT91C_TWI_SVACC       (0x1 <<  4) // (TWI) Slave ACCess (used only in Slave mode)
#define AT91C_TWI_GACC        (0x1 <<  5) // (TWI) General Call ACcess (used only in Slave mode)
#define AT91C_TWI_OVRE        (0x1 <<  6) // (TWI) Overrun Error (used only in Master and Multi-master mode)
#define AT91C_TWI_NACK_SLAVE  (0x1 <<  8) // (TWI) Not Acknowledged
#define AT91C_TWI_NACK_MASTER (0x1 <<  8) // (TWI) Not Acknowledged
#define AT91C_TWI_ARBLST_MULTI_MASTER (0x1 <<  9) // (TWI) Arbitration Lost (used only in Multimaster mode)
#define AT91C_TWI_SCLWS       (0x1 << 10) // (TWI) Clock Wait State (used only in Slave mode)
#define AT91C_TWI_EOSACC      (0x1 << 11) // (TWI) End Of Slave ACCess (used only in Slave mode)
#define AT91C_TWI_ENDRX       (0x1 << 12) // (TWI) End of Receiver Transfer
#define AT91C_TWI_ENDTX       (0x1 << 13) // (TWI) End of Receiver Transfer
#define AT91C_TWI_RXBUFF      (0x1 << 14) // (TWI) RXBUFF Interrupt
#define AT91C_TWI_TXBUFE      (0x1 << 15) // (TWI) TXBUFE Interrupt
// -------- TWI_IER : (TWI Offset: 0x24) TWI Interrupt Enable Register -------- 
// -------- TWI_IDR : (TWI Offset: 0x28) TWI Interrupt Disable Register -------- 
// -------- TWI_IMR : (TWI Offset: 0x2c) TWI Interrupt Mask Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Usart
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_USART {
	AT91_REG	 US_CR; 	// Control Register
	AT91_REG	 US_MR; 	// Mode Register
	AT91_REG	 US_IER; 	// Interrupt Enable Register
	AT91_REG	 US_IDR; 	// Interrupt Disable Register
	AT91_REG	 US_IMR; 	// Interrupt Mask Register
	AT91_REG	 US_CSR; 	// Channel Status Register
	AT91_REG	 US_RHR; 	// Receiver Holding Register
	AT91_REG	 US_THR; 	// Transmitter Holding Register
	AT91_REG	 US_BRGR; 	// Baud Rate Generator Register
	AT91_REG	 US_RTOR; 	// Receiver Time-out Register
	AT91_REG	 US_TTGR; 	// Transmitter Time-guard Register
	AT91_REG	 Reserved0[5]; 	// 
	AT91_REG	 US_FIDI; 	// FI_DI_Ratio Register
	AT91_REG	 US_NER; 	// Nb Errors Register
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 US_IF; 	// IRDA_FILTER Register
	AT91_REG	 Reserved2[44]; 	// 
	AT91_REG	 US_RPR; 	// Receive Pointer Register
	AT91_REG	 US_RCR; 	// Receive Counter Register
	AT91_REG	 US_TPR; 	// Transmit Pointer Register
	AT91_REG	 US_TCR; 	// Transmit Counter Register
	AT91_REG	 US_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 US_RNCR; 	// Receive Next Counter Register
	AT91_REG	 US_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 US_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 US_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 US_PTSR; 	// PDC Transfer Status Register
} AT91S_USART, *AT91PS_USART;
#else
#define US_CR           (AT91_CAST(AT91_REG *) 	0x00000000) // (US_CR) Control Register
#define US_MR           (AT91_CAST(AT91_REG *) 	0x00000004) // (US_MR) Mode Register
#define US_IER          (AT91_CAST(AT91_REG *) 	0x00000008) // (US_IER) Interrupt Enable Register
#define US_IDR          (AT91_CAST(AT91_REG *) 	0x0000000C) // (US_IDR) Interrupt Disable Register
#define US_IMR          (AT91_CAST(AT91_REG *) 	0x00000010) // (US_IMR) Interrupt Mask Register
#define US_CSR          (AT91_CAST(AT91_REG *) 	0x00000014) // (US_CSR) Channel Status Register
#define US_RHR          (AT91_CAST(AT91_REG *) 	0x00000018) // (US_RHR) Receiver Holding Register
#define US_THR          (AT91_CAST(AT91_REG *) 	0x0000001C) // (US_THR) Transmitter Holding Register
#define US_BRGR         (AT91_CAST(AT91_REG *) 	0x00000020) // (US_BRGR) Baud Rate Generator Register
#define US_RTOR         (AT91_CAST(AT91_REG *) 	0x00000024) // (US_RTOR) Receiver Time-out Register
#define US_TTGR         (AT91_CAST(AT91_REG *) 	0x00000028) // (US_TTGR) Transmitter Time-guard Register
#define US_FIDI         (AT91_CAST(AT91_REG *) 	0x00000040) // (US_FIDI) FI_DI_Ratio Register
#define US_NER          (AT91_CAST(AT91_REG *) 	0x00000044) // (US_NER) Nb Errors Register
#define US_IF           (AT91_CAST(AT91_REG *) 	0x0000004C) // (US_IF) IRDA_FILTER Register

#endif
// -------- US_CR : (USART Offset: 0x0) Debug Unit Control Register -------- 
#define AT91C_US_STTBRK       (0x1 <<  9) // (USART) Start Break
#define AT91C_US_STPBRK       (0x1 << 10) // (USART) Stop Break
#define AT91C_US_STTTO        (0x1 << 11) // (USART) Start Time-out
#define AT91C_US_SENDA        (0x1 << 12) // (USART) Send Address
#define AT91C_US_RSTIT        (0x1 << 13) // (USART) Reset Iterations
#define AT91C_US_RSTNACK      (0x1 << 14) // (USART) Reset Non Acknowledge
#define AT91C_US_RETTO        (0x1 << 15) // (USART) Rearm Time-out
#define AT91C_US_DTREN        (0x1 << 16) // (USART) Data Terminal ready Enable
#define AT91C_US_DTRDIS       (0x1 << 17) // (USART) Data Terminal ready Disable
#define AT91C_US_RTSEN        (0x1 << 18) // (USART) Request to Send enable
#define AT91C_US_RTSDIS       (0x1 << 19) // (USART) Request to Send Disable
// -------- US_MR : (USART Offset: 0x4) Debug Unit Mode Register -------- 
#define AT91C_US_USMODE       (0xF <<  0) // (USART) Usart mode
#define 	AT91C_US_USMODE_NORMAL               (0x0) // (USART) Normal
#define 	AT91C_US_USMODE_RS485                (0x1) // (USART) RS485
#define 	AT91C_US_USMODE_HWHSH                (0x2) // (USART) Hardware Handshaking
#define 	AT91C_US_USMODE_MODEM                (0x3) // (USART) Modem
#define 	AT91C_US_USMODE_ISO7816_0            (0x4) // (USART) ISO7816 protocol: T = 0
#define 	AT91C_US_USMODE_ISO7816_1            (0x6) // (USART) ISO7816 protocol: T = 1
#define 	AT91C_US_USMODE_IRDA                 (0x8) // (USART) IrDA
#define 	AT91C_US_USMODE_SWHSH                (0xC) // (USART) Software Handshaking
#define AT91C_US_CLKS         (0x3 <<  4) // (USART) Clock Selection (Baud Rate generator Input Clock
#define 	AT91C_US_CLKS_CLOCK                (0x0 <<  4) // (USART) Clock
#define 	AT91C_US_CLKS_FDIV1                (0x1 <<  4) // (USART) fdiv1
#define 	AT91C_US_CLKS_SLOW                 (0x2 <<  4) // (USART) slow_clock (ARM)
#define 	AT91C_US_CLKS_EXT                  (0x3 <<  4) // (USART) External (SCK)
#define AT91C_US_CHRL         (0x3 <<  6) // (USART) Clock Selection (Baud Rate generator Input Clock
#define 	AT91C_US_CHRL_5_BITS               (0x0 <<  6) // (USART) Character Length: 5 bits
#define 	AT91C_US_CHRL_6_BITS               (0x1 <<  6) // (USART) Character Length: 6 bits
#define 	AT91C_US_CHRL_7_BITS               (0x2 <<  6) // (USART) Character Length: 7 bits
#define 	AT91C_US_CHRL_8_BITS               (0x3 <<  6) // (USART) Character Length: 8 bits
#define AT91C_US_SYNC         (0x1 <<  8) // (USART) Synchronous Mode Select
#define AT91C_US_NBSTOP       (0x3 << 12) // (USART) Number of Stop bits
#define 	AT91C_US_NBSTOP_1_BIT                (0x0 << 12) // (USART) 1 stop bit
#define 	AT91C_US_NBSTOP_15_BIT               (0x1 << 12) // (USART) Asynchronous (SYNC=0) 2 stop bits Synchronous (SYNC=1) 2 stop bits
#define 	AT91C_US_NBSTOP_2_BIT                (0x2 << 12) // (USART) 2 stop bits
#define AT91C_US_MSBF         (0x1 << 16) // (USART) Bit Order
#define AT91C_US_MODE9        (0x1 << 17) // (USART) 9-bit Character length
#define AT91C_US_CKLO         (0x1 << 18) // (USART) Clock Output Select
#define AT91C_US_OVER         (0x1 << 19) // (USART) Over Sampling Mode
#define AT91C_US_INACK        (0x1 << 20) // (USART) Inhibit Non Acknowledge
#define AT91C_US_DSNACK       (0x1 << 21) // (USART) Disable Successive NACK
#define AT91C_US_MAX_ITER     (0x1 << 24) // (USART) Number of Repetitions
#define AT91C_US_FILTER       (0x1 << 28) // (USART) Receive Line Filter
// -------- US_IER : (USART Offset: 0x8) Debug Unit Interrupt Enable Register -------- 
#define AT91C_US_RXBRK        (0x1 <<  2) // (USART) Break Received/End of Break
#define AT91C_US_TIMEOUT      (0x1 <<  8) // (USART) Receiver Time-out
#define AT91C_US_ITERATION    (0x1 << 10) // (USART) Max number of Repetitions Reached
#define AT91C_US_NACK         (0x1 << 13) // (USART) Non Acknowledge
#define AT91C_US_RIIC         (0x1 << 16) // (USART) Ring INdicator Input Change Flag
#define AT91C_US_DSRIC        (0x1 << 17) // (USART) Data Set Ready Input Change Flag
#define AT91C_US_DCDIC        (0x1 << 18) // (USART) Data Carrier Flag
#define AT91C_US_CTSIC        (0x1 << 19) // (USART) Clear To Send Input Change Flag
// -------- US_IDR : (USART Offset: 0xc) Debug Unit Interrupt Disable Register -------- 
// -------- US_IMR : (USART Offset: 0x10) Debug Unit Interrupt Mask Register -------- 
// -------- US_CSR : (USART Offset: 0x14) Debug Unit Channel Status Register -------- 
#define AT91C_US_RI           (0x1 << 20) // (USART) Image of RI Input
#define AT91C_US_DSR          (0x1 << 21) // (USART) Image of DSR Input
#define AT91C_US_DCD          (0x1 << 22) // (USART) Image of DCD Input
#define AT91C_US_CTS          (0x1 << 23) // (USART) Image of CTS Input

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Synchronous Serial Controller Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_SSC {
	AT91_REG	 SSC_CR; 	// Control Register
	AT91_REG	 SSC_CMR; 	// Clock Mode Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 SSC_RCMR; 	// Receive Clock ModeRegister
	AT91_REG	 SSC_RFMR; 	// Receive Frame Mode Register
	AT91_REG	 SSC_TCMR; 	// Transmit Clock Mode Register
	AT91_REG	 SSC_TFMR; 	// Transmit Frame Mode Register
	AT91_REG	 SSC_RHR; 	// Receive Holding Register
	AT91_REG	 SSC_THR; 	// Transmit Holding Register
	AT91_REG	 Reserved1[2]; 	// 
	AT91_REG	 SSC_RSHR; 	// Receive Sync Holding Register
	AT91_REG	 SSC_TSHR; 	// Transmit Sync Holding Register
	AT91_REG	 Reserved2[2]; 	// 
	AT91_REG	 SSC_SR; 	// Status Register
	AT91_REG	 SSC_IER; 	// Interrupt Enable Register
	AT91_REG	 SSC_IDR; 	// Interrupt Disable Register
	AT91_REG	 SSC_IMR; 	// Interrupt Mask Register
	AT91_REG	 Reserved3[44]; 	// 
	AT91_REG	 SSC_RPR; 	// Receive Pointer Register
	AT91_REG	 SSC_RCR; 	// Receive Counter Register
	AT91_REG	 SSC_TPR; 	// Transmit Pointer Register
	AT91_REG	 SSC_TCR; 	// Transmit Counter Register
	AT91_REG	 SSC_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 SSC_RNCR; 	// Receive Next Counter Register
	AT91_REG	 SSC_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 SSC_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 SSC_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 SSC_PTSR; 	// PDC Transfer Status Register
} AT91S_SSC, *AT91PS_SSC;
#else
#define SSC_CR          (AT91_CAST(AT91_REG *) 	0x00000000) // (SSC_CR) Control Register
#define SSC_CMR         (AT91_CAST(AT91_REG *) 	0x00000004) // (SSC_CMR) Clock Mode Register
#define SSC_RCMR        (AT91_CAST(AT91_REG *) 	0x00000010) // (SSC_RCMR) Receive Clock ModeRegister
#define SSC_RFMR        (AT91_CAST(AT91_REG *) 	0x00000014) // (SSC_RFMR) Receive Frame Mode Register
#define SSC_TCMR        (AT91_CAST(AT91_REG *) 	0x00000018) // (SSC_TCMR) Transmit Clock Mode Register
#define SSC_TFMR        (AT91_CAST(AT91_REG *) 	0x0000001C) // (SSC_TFMR) Transmit Frame Mode Register
#define SSC_RHR         (AT91_CAST(AT91_REG *) 	0x00000020) // (SSC_RHR) Receive Holding Register
#define SSC_THR         (AT91_CAST(AT91_REG *) 	0x00000024) // (SSC_THR) Transmit Holding Register
#define SSC_RSHR        (AT91_CAST(AT91_REG *) 	0x00000030) // (SSC_RSHR) Receive Sync Holding Register
#define SSC_TSHR        (AT91_CAST(AT91_REG *) 	0x00000034) // (SSC_TSHR) Transmit Sync Holding Register
#define SSC_SR          (AT91_CAST(AT91_REG *) 	0x00000040) // (SSC_SR) Status Register
#define SSC_IER         (AT91_CAST(AT91_REG *) 	0x00000044) // (SSC_IER) Interrupt Enable Register
#define SSC_IDR         (AT91_CAST(AT91_REG *) 	0x00000048) // (SSC_IDR) Interrupt Disable Register
#define SSC_IMR         (AT91_CAST(AT91_REG *) 	0x0000004C) // (SSC_IMR) Interrupt Mask Register

#endif
// -------- SSC_CR : (SSC Offset: 0x0) SSC Control Register -------- 
#define AT91C_SSC_RXEN        (0x1 <<  0) // (SSC) Receive Enable
#define AT91C_SSC_RXDIS       (0x1 <<  1) // (SSC) Receive Disable
#define AT91C_SSC_TXEN        (0x1 <<  8) // (SSC) Transmit Enable
#define AT91C_SSC_TXDIS       (0x1 <<  9) // (SSC) Transmit Disable
#define AT91C_SSC_SWRST       (0x1 << 15) // (SSC) Software Reset
// -------- SSC_RCMR : (SSC Offset: 0x10) SSC Receive Clock Mode Register -------- 
#define AT91C_SSC_CKS         (0x3 <<  0) // (SSC) Receive/Transmit Clock Selection
#define 	AT91C_SSC_CKS_DIV                  (0x0) // (SSC) Divided Clock
#define 	AT91C_SSC_CKS_TK                   (0x1) // (SSC) TK Clock signal
#define 	AT91C_SSC_CKS_RK                   (0x2) // (SSC) RK pin
#define AT91C_SSC_CKO         (0x7 <<  2) // (SSC) Receive/Transmit Clock Output Mode Selection
#define 	AT91C_SSC_CKO_NONE                 (0x0 <<  2) // (SSC) Receive/Transmit Clock Output Mode: None RK pin: Input-only
#define 	AT91C_SSC_CKO_CONTINOUS            (0x1 <<  2) // (SSC) Continuous Receive/Transmit Clock RK pin: Output
#define 	AT91C_SSC_CKO_DATA_TX              (0x2 <<  2) // (SSC) Receive/Transmit Clock only during data transfers RK pin: Output
#define AT91C_SSC_CKI         (0x1 <<  5) // (SSC) Receive/Transmit Clock Inversion
#define AT91C_SSC_START       (0xF <<  8) // (SSC) Receive/Transmit Start Selection
#define 	AT91C_SSC_START_CONTINOUS            (0x0 <<  8) // (SSC) Continuous, as soon as the receiver is enabled, and immediately after the end of transfer of the previous data.
#define 	AT91C_SSC_START_TX                   (0x1 <<  8) // (SSC) Transmit/Receive start
#define 	AT91C_SSC_START_LOW_RF               (0x2 <<  8) // (SSC) Detection of a low level on RF input
#define 	AT91C_SSC_START_HIGH_RF              (0x3 <<  8) // (SSC) Detection of a high level on RF input
#define 	AT91C_SSC_START_FALL_RF              (0x4 <<  8) // (SSC) Detection of a falling edge on RF input
#define 	AT91C_SSC_START_RISE_RF              (0x5 <<  8) // (SSC) Detection of a rising edge on RF input
#define 	AT91C_SSC_START_LEVEL_RF             (0x6 <<  8) // (SSC) Detection of any level change on RF input
#define 	AT91C_SSC_START_EDGE_RF              (0x7 <<  8) // (SSC) Detection of any edge on RF input
#define 	AT91C_SSC_START_0                    (0x8 <<  8) // (SSC) Compare 0
#define AT91C_SSC_STTDLY      (0xFF << 16) // (SSC) Receive/Transmit Start Delay
#define AT91C_SSC_PERIOD      (0xFF << 24) // (SSC) Receive/Transmit Period Divider Selection
// -------- SSC_RFMR : (SSC Offset: 0x14) SSC Receive Frame Mode Register -------- 
#define AT91C_SSC_DATLEN      (0x1F <<  0) // (SSC) Data Length
#define AT91C_SSC_LOOP        (0x1 <<  5) // (SSC) Loop Mode
#define AT91C_SSC_MSBF        (0x1 <<  7) // (SSC) Most Significant Bit First
#define AT91C_SSC_DATNB       (0xF <<  8) // (SSC) Data Number per Frame
#define AT91C_SSC_FSLEN       (0xF << 16) // (SSC) Receive/Transmit Frame Sync length
#define AT91C_SSC_FSOS        (0x7 << 20) // (SSC) Receive/Transmit Frame Sync Output Selection
#define 	AT91C_SSC_FSOS_NONE                 (0x0 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: None RK pin Input-only
#define 	AT91C_SSC_FSOS_NEGATIVE             (0x1 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: Negative Pulse
#define 	AT91C_SSC_FSOS_POSITIVE             (0x2 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: Positive Pulse
#define 	AT91C_SSC_FSOS_LOW                  (0x3 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: Driver Low during data transfer
#define 	AT91C_SSC_FSOS_HIGH                 (0x4 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: Driver High during data transfer
#define 	AT91C_SSC_FSOS_TOGGLE               (0x5 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: Toggling at each start of data transfer
#define AT91C_SSC_FSEDGE      (0x1 << 24) // (SSC) Frame Sync Edge Detection
// -------- SSC_TCMR : (SSC Offset: 0x18) SSC Transmit Clock Mode Register -------- 
// -------- SSC_TFMR : (SSC Offset: 0x1c) SSC Transmit Frame Mode Register -------- 
#define AT91C_SSC_DATDEF      (0x1 <<  5) // (SSC) Data Default Value
#define AT91C_SSC_FSDEN       (0x1 << 23) // (SSC) Frame Sync Data Enable
// -------- SSC_SR : (SSC Offset: 0x40) SSC Status Register -------- 
#define AT91C_SSC_TXRDY       (0x1 <<  0) // (SSC) Transmit Ready
#define AT91C_SSC_TXEMPTY     (0x1 <<  1) // (SSC) Transmit Empty
#define AT91C_SSC_ENDTX       (0x1 <<  2) // (SSC) End Of Transmission
#define AT91C_SSC_TXBUFE      (0x1 <<  3) // (SSC) Transmit Buffer Empty
#define AT91C_SSC_RXRDY       (0x1 <<  4) // (SSC) Receive Ready
#define AT91C_SSC_OVRUN       (0x1 <<  5) // (SSC) Receive Overrun
#define AT91C_SSC_ENDRX       (0x1 <<  6) // (SSC) End of Reception
#define AT91C_SSC_RXBUFF      (0x1 <<  7) // (SSC) Receive Buffer Full
#define AT91C_SSC_TXSYN       (0x1 << 10) // (SSC) Transmit Sync
#define AT91C_SSC_RXSYN       (0x1 << 11) // (SSC) Receive Sync
#define AT91C_SSC_TXENA       (0x1 << 16) // (SSC) Transmit Enable
#define AT91C_SSC_RXENA       (0x1 << 17) // (SSC) Receive Enable
// -------- SSC_IER : (SSC Offset: 0x44) SSC Interrupt Enable Register -------- 
// -------- SSC_IDR : (SSC Offset: 0x48) SSC Interrupt Disable Register -------- 
// -------- SSC_IMR : (SSC Offset: 0x4c) SSC Interrupt Mask Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Serial Parallel Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_SPI {
	AT91_REG	 SPI_CR; 	// Control Register
	AT91_REG	 SPI_MR; 	// Mode Register
	AT91_REG	 SPI_RDR; 	// Receive Data Register
	AT91_REG	 SPI_TDR; 	// Transmit Data Register
	AT91_REG	 SPI_SR; 	// Status Register
	AT91_REG	 SPI_IER; 	// Interrupt Enable Register
	AT91_REG	 SPI_IDR; 	// Interrupt Disable Register
	AT91_REG	 SPI_IMR; 	// Interrupt Mask Register
	AT91_REG	 Reserved0[4]; 	// 
	AT91_REG	 SPI_CSR[4]; 	// Chip Select Register
	AT91_REG	 Reserved1[48]; 	// 
	AT91_REG	 SPI_RPR; 	// Receive Pointer Register
	AT91_REG	 SPI_RCR; 	// Receive Counter Register
	AT91_REG	 SPI_TPR; 	// Transmit Pointer Register
	AT91_REG	 SPI_TCR; 	// Transmit Counter Register
	AT91_REG	 SPI_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 SPI_RNCR; 	// Receive Next Counter Register
	AT91_REG	 SPI_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 SPI_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 SPI_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 SPI_PTSR; 	// PDC Transfer Status Register
} AT91S_SPI, *AT91PS_SPI;
#else
#define SPI_CR          (AT91_CAST(AT91_REG *) 	0x00000000) // (SPI_CR) Control Register
#define SPI_MR          (AT91_CAST(AT91_REG *) 	0x00000004) // (SPI_MR) Mode Register
#define SPI_RDR         (AT91_CAST(AT91_REG *) 	0x00000008) // (SPI_RDR) Receive Data Register
#define SPI_TDR         (AT91_CAST(AT91_REG *) 	0x0000000C) // (SPI_TDR) Transmit Data Register
#define SPI_SR          (AT91_CAST(AT91_REG *) 	0x00000010) // (SPI_SR) Status Register
#define SPI_IER         (AT91_CAST(AT91_REG *) 	0x00000014) // (SPI_IER) Interrupt Enable Register
#define SPI_IDR         (AT91_CAST(AT91_REG *) 	0x00000018) // (SPI_IDR) Interrupt Disable Register
#define SPI_IMR         (AT91_CAST(AT91_REG *) 	0x0000001C) // (SPI_IMR) Interrupt Mask Register
#define SPI_CSR         (AT91_CAST(AT91_REG *) 	0x00000030) // (SPI_CSR) Chip Select Register

#endif
// -------- SPI_CR : (SPI Offset: 0x0) SPI Control Register -------- 
#define AT91C_SPI_SPIEN       (0x1 <<  0) // (SPI) SPI Enable
#define AT91C_SPI_SPIDIS      (0x1 <<  1) // (SPI) SPI Disable
#define AT91C_SPI_SWRST       (0x1 <<  7) // (SPI) SPI Software reset
#define AT91C_SPI_LASTXFER    (0x1 << 24) // (SPI) SPI Last Transfer
// -------- SPI_MR : (SPI Offset: 0x4) SPI Mode Register -------- 
#define AT91C_SPI_MSTR        (0x1 <<  0) // (SPI) Master/Slave Mode
#define AT91C_SPI_PS          (0x1 <<  1) // (SPI) Peripheral Select
#define 	AT91C_SPI_PS_FIXED                (0x0 <<  1) // (SPI) Fixed Peripheral Select
#define 	AT91C_SPI_PS_VARIABLE             (0x1 <<  1) // (SPI) Variable Peripheral Select
#define AT91C_SPI_PCSDEC      (0x1 <<  2) // (SPI) Chip Select Decode
#define AT91C_SPI_FDIV        (0x1 <<  3) // (SPI) Clock Selection
#define AT91C_SPI_MODFDIS     (0x1 <<  4) // (SPI) Mode Fault Detection
#define AT91C_SPI_LLB         (0x1 <<  7) // (SPI) Clock Selection
#define AT91C_SPI_PCS         (0xF << 16) // (SPI) Peripheral Chip Select
#define AT91C_SPI_DLYBCS      (0xFF << 24) // (SPI) Delay Between Chip Selects
// -------- SPI_RDR : (SPI Offset: 0x8) Receive Data Register -------- 
#define AT91C_SPI_RD          (0xFFFF <<  0) // (SPI) Receive Data
#define AT91C_SPI_RPCS        (0xF << 16) // (SPI) Peripheral Chip Select Status
// -------- SPI_TDR : (SPI Offset: 0xc) Transmit Data Register -------- 
#define AT91C_SPI_TD          (0xFFFF <<  0) // (SPI) Transmit Data
#define AT91C_SPI_TPCS        (0xF << 16) // (SPI) Peripheral Chip Select Status
// -------- SPI_SR : (SPI Offset: 0x10) Status Register -------- 
#define AT91C_SPI_RDRF        (0x1 <<  0) // (SPI) Receive Data Register Full
#define AT91C_SPI_TDRE        (0x1 <<  1) // (SPI) Transmit Data Register Empty
#define AT91C_SPI_MODF        (0x1 <<  2) // (SPI) Mode Fault Error
#define AT91C_SPI_OVRES       (0x1 <<  3) // (SPI) Overrun Error Status
#define AT91C_SPI_ENDRX       (0x1 <<  4) // (SPI) End of Receiver Transfer
#define AT91C_SPI_ENDTX       (0x1 <<  5) // (SPI) End of Receiver Transfer
#define AT91C_SPI_RXBUFF      (0x1 <<  6) // (SPI) RXBUFF Interrupt
#define AT91C_SPI_TXBUFE      (0x1 <<  7) // (SPI) TXBUFE Interrupt
#define AT91C_SPI_NSSR        (0x1 <<  8) // (SPI) NSSR Interrupt
#define AT91C_SPI_TXEMPTY     (0x1 <<  9) // (SPI) TXEMPTY Interrupt
#define AT91C_SPI_SPIENS      (0x1 << 16) // (SPI) Enable Status
// -------- SPI_IER : (SPI Offset: 0x14) Interrupt Enable Register -------- 
// -------- SPI_IDR : (SPI Offset: 0x18) Interrupt Disable Register -------- 
// -------- SPI_IMR : (SPI Offset: 0x1c) Interrupt Mask Register -------- 
// -------- SPI_CSR : (SPI Offset: 0x30) Chip Select Register -------- 
#define AT91C_SPI_CPOL        (0x1 <<  0) // (SPI) Clock Polarity
#define AT91C_SPI_NCPHA       (0x1 <<  1) // (SPI) Clock Phase
#define AT91C_SPI_CSAAT       (0x1 <<  3) // (SPI) Chip Select Active After Transfer
#define AT91C_SPI_BITS        (0xF <<  4) // (SPI) Bits Per Transfer
#define 	AT91C_SPI_BITS_8                    (0x0 <<  4) // (SPI) 8 Bits Per transfer
#define 	AT91C_SPI_BITS_9                    (0x1 <<  4) // (SPI) 9 Bits Per transfer
#define 	AT91C_SPI_BITS_10                   (0x2 <<  4) // (SPI) 10 Bits Per transfer
#define 	AT91C_SPI_BITS_11                   (0x3 <<  4) // (SPI) 11 Bits Per transfer
#define 	AT91C_SPI_BITS_12                   (0x4 <<  4) // (SPI) 12 Bits Per transfer
#define 	AT91C_SPI_BITS_13                   (0x5 <<  4) // (SPI) 13 Bits Per transfer
#define 	AT91C_SPI_BITS_14                   (0x6 <<  4) // (SPI) 14 Bits Per transfer
#define 	AT91C_SPI_BITS_15                   (0x7 <<  4) // (SPI) 15 Bits Per transfer
#define 	AT91C_SPI_BITS_16                   (0x8 <<  4) // (SPI) 16 Bits Per transfer
#define AT91C_SPI_SCBR        (0xFF <<  8) // (SPI) Serial Clock Baud Rate
#define AT91C_SPI_DLYBS       (0xFF << 16) // (SPI) Delay Before SPCK
#define AT91C_SPI_DLYBCT      (0xFF << 24) // (SPI) Delay Between Consecutive Transfers

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Analog to Digital Convertor
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_ADC {
	AT91_REG	 ADC_CR; 	// ADC Control Register
	AT91_REG	 ADC_MR; 	// ADC Mode Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 ADC_CHER; 	// ADC Channel Enable Register
	AT91_REG	 ADC_CHDR; 	// ADC Channel Disable Register
	AT91_REG	 ADC_CHSR; 	// ADC Channel Status Register
	AT91_REG	 ADC_SR; 	// ADC Status Register
	AT91_REG	 ADC_LCDR; 	// ADC Last Converted Data Register
	AT91_REG	 ADC_IER; 	// ADC Interrupt Enable Register
	AT91_REG	 ADC_IDR; 	// ADC Interrupt Disable Register
	AT91_REG	 ADC_IMR; 	// ADC Interrupt Mask Register
	AT91_REG	 ADC_CDR0; 	// ADC Channel Data Register 0
	AT91_REG	 ADC_CDR1; 	// ADC Channel Data Register 1
	AT91_REG	 ADC_CDR2; 	// ADC Channel Data Register 2
	AT91_REG	 ADC_CDR3; 	// ADC Channel Data Register 3
	AT91_REG	 ADC_CDR4; 	// ADC Channel Data Register 4
	AT91_REG	 ADC_CDR5; 	// ADC Channel Data Register 5
	AT91_REG	 ADC_CDR6; 	// ADC Channel Data Register 6
	AT91_REG	 ADC_CDR7; 	// ADC Channel Data Register 7
	AT91_REG	 Reserved1[44]; 	// 
	AT91_REG	 ADC_RPR; 	// Receive Pointer Register
	AT91_REG	 ADC_RCR; 	// Receive Counter Register
	AT91_REG	 ADC_TPR; 	// Transmit Pointer Register
	AT91_REG	 ADC_TCR; 	// Transmit Counter Register
	AT91_REG	 ADC_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 ADC_RNCR; 	// Receive Next Counter Register
	AT91_REG	 ADC_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 ADC_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 ADC_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 ADC_PTSR; 	// PDC Transfer Status Register
} AT91S_ADC, *AT91PS_ADC;
#else
#define ADC_CR          (AT91_CAST(AT91_REG *) 	0x00000000) // (ADC_CR) ADC Control Register
#define ADC_MR          (AT91_CAST(AT91_REG *) 	0x00000004) // (ADC_MR) ADC Mode Register
#define ADC_CHER        (AT91_CAST(AT91_REG *) 	0x00000010) // (ADC_CHER) ADC Channel Enable Register
#define ADC_CHDR        (AT91_CAST(AT91_REG *) 	0x00000014) // (ADC_CHDR) ADC Channel Disable Register
#define ADC_CHSR        (AT91_CAST(AT91_REG *) 	0x00000018) // (ADC_CHSR) ADC Channel Status Register
#define ADC_SR          (AT91_CAST(AT91_REG *) 	0x0000001C) // (ADC_SR) ADC Status Register
#define ADC_LCDR        (AT91_CAST(AT91_REG *) 	0x00000020) // (ADC_LCDR) ADC Last Converted Data Register
#define ADC_IER         (AT91_CAST(AT91_REG *) 	0x00000024) // (ADC_IER) ADC Interrupt Enable Register
#define ADC_IDR         (AT91_CAST(AT91_REG *) 	0x00000028) // (ADC_IDR) ADC Interrupt Disable Register
#define ADC_IMR         (AT91_CAST(AT91_REG *) 	0x0000002C) // (ADC_IMR) ADC Interrupt Mask Register
#define ADC_CDR0        (AT91_CAST(AT91_REG *) 	0x00000030) // (ADC_CDR0) ADC Channel Data Register 0
#define ADC_CDR1        (AT91_CAST(AT91_REG *) 	0x00000034) // (ADC_CDR1) ADC Channel Data Register 1
#define ADC_CDR2        (AT91_CAST(AT91_REG *) 	0x00000038) // (ADC_CDR2) ADC Channel Data Register 2
#define ADC_CDR3        (AT91_CAST(AT91_REG *) 	0x0000003C) // (ADC_CDR3) ADC Channel Data Register 3
#define ADC_CDR4        (AT91_CAST(AT91_REG *) 	0x00000040) // (ADC_CDR4) ADC Channel Data Register 4
#define ADC_CDR5        (AT91_CAST(AT91_REG *) 	0x00000044) // (ADC_CDR5) ADC Channel Data Register 5
#define ADC_CDR6        (AT91_CAST(AT91_REG *) 	0x00000048) // (ADC_CDR6) ADC Channel Data Register 6
#define ADC_CDR7        (AT91_CAST(AT91_REG *) 	0x0000004C) // (ADC_CDR7) ADC Channel Data Register 7

#endif
// -------- ADC_CR : (ADC Offset: 0x0) ADC Control Register -------- 
#define AT91C_ADC_SWRST       (0x1 <<  0) // (ADC) Software Reset
#define AT91C_ADC_START       (0x1 <<  1) // (ADC) Start Conversion
// -------- ADC_MR : (ADC Offset: 0x4) ADC Mode Register -------- 
#define AT91C_ADC_TRGEN       (0x1 <<  0) // (ADC) Trigger Enable
#define 	AT91C_ADC_TRGEN_DIS                  (0x0) // (ADC) Hradware triggers are disabled. Starting a conversion is only possible by software
#define 	AT91C_ADC_TRGEN_EN                   (0x1) // (ADC) Hardware trigger selected by TRGSEL field is enabled.
#define AT91C_ADC_TRGSEL      (0x7 <<  1) // (ADC) Trigger Selection
#define 	AT91C_ADC_TRGSEL_TIOA0                (0x0 <<  1) // (ADC) Selected TRGSEL = TIAO0
#define 	AT91C_ADC_TRGSEL_TIOA1                (0x1 <<  1) // (ADC) Selected TRGSEL = TIAO1
#define 	AT91C_ADC_TRGSEL_TIOA2                (0x2 <<  1) // (ADC) Selected TRGSEL = TIAO2
#define 	AT91C_ADC_TRGSEL_TIOA3                (0x3 <<  1) // (ADC) Selected TRGSEL = TIAO3
#define 	AT91C_ADC_TRGSEL_TIOA4                (0x4 <<  1) // (ADC) Selected TRGSEL = TIAO4
#define 	AT91C_ADC_TRGSEL_TIOA5                (0x5 <<  1) // (ADC) Selected TRGSEL = TIAO5
#define 	AT91C_ADC_TRGSEL_EXT                  (0x6 <<  1) // (ADC) Selected TRGSEL = External Trigger
#define AT91C_ADC_LOWRES      (0x1 <<  4) // (ADC) Resolution.
#define 	AT91C_ADC_LOWRES_10_BIT               (0x0 <<  4) // (ADC) 10-bit resolution
#define 	AT91C_ADC_LOWRES_8_BIT                (0x1 <<  4) // (ADC) 8-bit resolution
#define AT91C_ADC_SLEEP       (0x1 <<  5) // (ADC) Sleep Mode
#define 	AT91C_ADC_SLEEP_NORMAL_MODE          (0x0 <<  5) // (ADC) Normal Mode
#define 	AT91C_ADC_SLEEP_MODE                 (0x1 <<  5) // (ADC) Sleep Mode
#define AT91C_ADC_PRESCAL     (0x3F <<  8) // (ADC) Prescaler rate selection
#define AT91C_ADC_STARTUP     (0x1F << 16) // (ADC) Startup Time
#define AT91C_ADC_SHTIM       (0xF << 24) // (ADC) Sample & Hold Time
// -------- 	ADC_CHER : (ADC Offset: 0x10) ADC Channel Enable Register -------- 
#define AT91C_ADC_CH0         (0x1 <<  0) // (ADC) Channel 0
#define AT91C_ADC_CH1         (0x1 <<  1) // (ADC) Channel 1
#define AT91C_ADC_CH2         (0x1 <<  2) // (ADC) Channel 2
#define AT91C_ADC_CH3         (0x1 <<  3) // (ADC) Channel 3
#define AT91C_ADC_CH4         (0x1 <<  4) // (ADC) Channel 4
#define AT91C_ADC_CH5         (0x1 <<  5) // (ADC) Channel 5
#define AT91C_ADC_CH6         (0x1 <<  6) // (ADC) Channel 6
#define AT91C_ADC_CH7         (0x1 <<  7) // (ADC) Channel 7
// -------- 	ADC_CHDR : (ADC Offset: 0x14) ADC Channel Disable Register -------- 
// -------- 	ADC_CHSR : (ADC Offset: 0x18) ADC Channel Status Register -------- 
// -------- ADC_SR : (ADC Offset: 0x1c) ADC Status Register -------- 
#define AT91C_ADC_EOC0        (0x1 <<  0) // (ADC) End of Conversion
#define AT91C_ADC_EOC1        (0x1 <<  1) // (ADC) End of Conversion
#define AT91C_ADC_EOC2        (0x1 <<  2) // (ADC) End of Conversion
#define AT91C_ADC_EOC3        (0x1 <<  3) // (ADC) End of Conversion
#define AT91C_ADC_EOC4        (0x1 <<  4) // (ADC) End of Conversion
#define AT91C_ADC_EOC5        (0x1 <<  5) // (ADC) End of Conversion
#define AT91C_ADC_EOC6        (0x1 <<  6) // (ADC) End of Conversion
#define AT91C_ADC_EOC7        (0x1 <<  7) // (ADC) End of Conversion
#define AT91C_ADC_OVRE0       (0x1 <<  8) // (ADC) Overrun Error
#define AT91C_ADC_OVRE1       (0x1 <<  9) // (ADC) Overrun Error
#define AT91C_ADC_OVRE2       (0x1 << 10) // (ADC) Overrun Error
#define AT91C_ADC_OVRE3       (0x1 << 11) // (ADC) Overrun Error
#define AT91C_ADC_OVRE4       (0x1 << 12) // (ADC) Overrun Error
#define AT91C_ADC_OVRE5       (0x1 << 13) // (ADC) Overrun Error
#define AT91C_ADC_OVRE6       (0x1 << 14) // (ADC) Overrun Error
#define AT91C_ADC_OVRE7       (0x1 << 15) // (ADC) Overrun Error
#define AT91C_ADC_DRDY        (0x1 << 16) // (ADC) Data Ready
#define AT91C_ADC_GOVRE       (0x1 << 17) // (ADC) General Overrun
#define AT91C_ADC_ENDRX       (0x1 << 18) // (ADC) End of Receiver Transfer
#define AT91C_ADC_RXBUFF      (0x1 << 19) // (ADC) RXBUFF Interrupt
// -------- ADC_LCDR : (ADC Offset: 0x20) ADC Last Converted Data Register -------- 
#define AT91C_ADC_LDATA       (0x3FF <<  0) // (ADC) Last Data Converted
// -------- ADC_IER : (ADC Offset: 0x24) ADC Interrupt Enable Register -------- 
// -------- ADC_IDR : (ADC Offset: 0x28) ADC Interrupt Disable Register -------- 
// -------- ADC_IMR : (ADC Offset: 0x2c) ADC Interrupt Mask Register -------- 
// -------- ADC_CDR0 : (ADC Offset: 0x30) ADC Channel Data Register 0 -------- 
#define AT91C_ADC_DATA        (0x3FF <<  0) // (ADC) Converted Data
// -------- ADC_CDR1 : (ADC Offset: 0x34) ADC Channel Data Register 1 -------- 
// -------- ADC_CDR2 : (ADC Offset: 0x38) ADC Channel Data Register 2 -------- 
// -------- ADC_CDR3 : (ADC Offset: 0x3c) ADC Channel Data Register 3 -------- 
// -------- ADC_CDR4 : (ADC Offset: 0x40) ADC Channel Data Register 4 -------- 
// -------- ADC_CDR5 : (ADC Offset: 0x44) ADC Channel Data Register 5 -------- 
// -------- ADC_CDR6 : (ADC Offset: 0x48) ADC Channel Data Register 6 -------- 
// -------- ADC_CDR7 : (ADC Offset: 0x4c) ADC Channel Data Register 7 -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Ethernet MAC 10/100
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_EMAC {
	AT91_REG	 EMAC_NCR; 	// Network Control Register
	AT91_REG	 EMAC_NCFGR; 	// Network Configuration Register
	AT91_REG	 EMAC_NSR; 	// Network Status Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 EMAC_TSR; 	// Transmit Status Register
	AT91_REG	 EMAC_RBQP; 	// Receive Buffer Queue Pointer
	AT91_REG	 EMAC_TBQP; 	// Transmit Buffer Queue Pointer
	AT91_REG	 EMAC_RSR; 	// Receive Status Register
	AT91_REG	 EMAC_ISR; 	// Interrupt Status Register
	AT91_REG	 EMAC_IER; 	// Interrupt Enable Register
	AT91_REG	 EMAC_IDR; 	// Interrupt Disable Register
	AT91_REG	 EMAC_IMR; 	// Interrupt Mask Register
	AT91_REG	 EMAC_MAN; 	// PHY Maintenance Register
	AT91_REG	 EMAC_PTR; 	// Pause Time Register
	AT91_REG	 EMAC_PFR; 	// Pause Frames received Register
	AT91_REG	 EMAC_FTO; 	// Frames Transmitted OK Register
	AT91_REG	 EMAC_SCF; 	// Single Collision Frame Register
	AT91_REG	 EMAC_MCF; 	// Multiple Collision Frame Register
	AT91_REG	 EMAC_FRO; 	// Frames Received OK Register
	AT91_REG	 EMAC_FCSE; 	// Frame Check Sequence Error Register
	AT91_REG	 EMAC_ALE; 	// Alignment Error Register
	AT91_REG	 EMAC_DTF; 	// Deferred Transmission Frame Register
	AT91_REG	 EMAC_LCOL; 	// Late Collision Register
	AT91_REG	 EMAC_ECOL; 	// Excessive Collision Register
	AT91_REG	 EMAC_TUND; 	// Transmit Underrun Error Register
	AT91_REG	 EMAC_CSE; 	// Carrier Sense Error Register
	AT91_REG	 EMAC_RRE; 	// Receive Ressource Error Register
	AT91_REG	 EMAC_ROV; 	// Receive Overrun Errors Register
	AT91_REG	 EMAC_RSE; 	// Receive Symbol Errors Register
	AT91_REG	 EMAC_ELE; 	// Excessive Length Errors Register
	AT91_REG	 EMAC_RJA; 	// Receive Jabbers Register
	AT91_REG	 EMAC_USF; 	// Undersize Frames Register
	AT91_REG	 EMAC_STE; 	// SQE Test Error Register
	AT91_REG	 EMAC_RLE; 	// Receive Length Field Mismatch Register
	AT91_REG	 EMAC_TPF; 	// Transmitted Pause Frames Register
	AT91_REG	 EMAC_HRB; 	// Hash Address Bottom[31:0]
	AT91_REG	 EMAC_HRT; 	// Hash Address Top[63:32]
	AT91_REG	 EMAC_SA1L; 	// Specific Address 1 Bottom, First 4 bytes
	AT91_REG	 EMAC_SA1H; 	// Specific Address 1 Top, Last 2 bytes
	AT91_REG	 EMAC_SA2L; 	// Specific Address 2 Bottom, First 4 bytes
	AT91_REG	 EMAC_SA2H; 	// Specific Address 2 Top, Last 2 bytes
	AT91_REG	 EMAC_SA3L; 	// Specific Address 3 Bottom, First 4 bytes
	AT91_REG	 EMAC_SA3H; 	// Specific Address 3 Top, Last 2 bytes
	AT91_REG	 EMAC_SA4L; 	// Specific Address 4 Bottom, First 4 bytes
	AT91_REG	 EMAC_SA4H; 	// Specific Address 4 Top, Last 2 bytes
	AT91_REG	 EMAC_TID; 	// Type ID Checking Register
	AT91_REG	 EMAC_TPQ; 	// Transmit Pause Quantum Register
	AT91_REG	 EMAC_USRIO; 	// USER Input/Output Register
	AT91_REG	 EMAC_WOL; 	// Wake On LAN Register
	AT91_REG	 Reserved1[13]; 	// 
	AT91_REG	 EMAC_REV; 	// Revision Register
} AT91S_EMAC, *AT91PS_EMAC;
#else
#define EMAC_NCR        (AT91_CAST(AT91_REG *) 	0x00000000) // (EMAC_NCR) Network Control Register
#define EMAC_NCFGR      (AT91_CAST(AT91_REG *) 	0x00000004) // (EMAC_NCFGR) Network Configuration Register
#define EMAC_NSR        (AT91_CAST(AT91_REG *) 	0x00000008) // (EMAC_NSR) Network Status Register
#define EMAC_TSR        (AT91_CAST(AT91_REG *) 	0x00000014) // (EMAC_TSR) Transmit Status Register
#define EMAC_RBQP       (AT91_CAST(AT91_REG *) 	0x00000018) // (EMAC_RBQP) Receive Buffer Queue Pointer
#define EMAC_TBQP       (AT91_CAST(AT91_REG *) 	0x0000001C) // (EMAC_TBQP) Transmit Buffer Queue Pointer
#define EMAC_RSR        (AT91_CAST(AT91_REG *) 	0x00000020) // (EMAC_RSR) Receive Status Register
#define EMAC_ISR        (AT91_CAST(AT91_REG *) 	0x00000024) // (EMAC_ISR) Interrupt Status Register
#define EMAC_IER        (AT91_CAST(AT91_REG *) 	0x00000028) // (EMAC_IER) Interrupt Enable Register
#define EMAC_IDR        (AT91_CAST(AT91_REG *) 	0x0000002C) // (EMAC_IDR) Interrupt Disable Register
#define EMAC_IMR        (AT91_CAST(AT91_REG *) 	0x00000030) // (EMAC_IMR) Interrupt Mask Register
#define EMAC_MAN        (AT91_CAST(AT91_REG *) 	0x00000034) // (EMAC_MAN) PHY Maintenance Register
#define EMAC_PTR        (AT91_CAST(AT91_REG *) 	0x00000038) // (EMAC_PTR) Pause Time Register
#define EMAC_PFR        (AT91_CAST(AT91_REG *) 	0x0000003C) // (EMAC_PFR) Pause Frames received Register
#define EMAC_FTO        (AT91_CAST(AT91_REG *) 	0x00000040) // (EMAC_FTO) Frames Transmitted OK Register
#define EMAC_SCF        (AT91_CAST(AT91_REG *) 	0x00000044) // (EMAC_SCF) Single Collision Frame Register
#define EMAC_MCF        (AT91_CAST(AT91_REG *) 	0x00000048) // (EMAC_MCF) Multiple Collision Frame Register
#define EMAC_FRO        (AT91_CAST(AT91_REG *) 	0x0000004C) // (EMAC_FRO) Frames Received OK Register
#define EMAC_FCSE       (AT91_CAST(AT91_REG *) 	0x00000050) // (EMAC_FCSE) Frame Check Sequence Error Register
#define EMAC_ALE        (AT91_CAST(AT91_REG *) 	0x00000054) // (EMAC_ALE) Alignment Error Register
#define EMAC_DTF        (AT91_CAST(AT91_REG *) 	0x00000058) // (EMAC_DTF) Deferred Transmission Frame Register
#define EMAC_LCOL       (AT91_CAST(AT91_REG *) 	0x0000005C) // (EMAC_LCOL) Late Collision Register
#define EMAC_ECOL       (AT91_CAST(AT91_REG *) 	0x00000060) // (EMAC_ECOL) Excessive Collision Register
#define EMAC_TUND       (AT91_CAST(AT91_REG *) 	0x00000064) // (EMAC_TUND) Transmit Underrun Error Register
#define EMAC_CSE        (AT91_CAST(AT91_REG *) 	0x00000068) // (EMAC_CSE) Carrier Sense Error Register
#define EMAC_RRE        (AT91_CAST(AT91_REG *) 	0x0000006C) // (EMAC_RRE) Receive Ressource Error Register
#define EMAC_ROV        (AT91_CAST(AT91_REG *) 	0x00000070) // (EMAC_ROV) Receive Overrun Errors Register
#define EMAC_RSE        (AT91_CAST(AT91_REG *) 	0x00000074) // (EMAC_RSE) Receive Symbol Errors Register
#define EMAC_ELE        (AT91_CAST(AT91_REG *) 	0x00000078) // (EMAC_ELE) Excessive Length Errors Register
#define EMAC_RJA        (AT91_CAST(AT91_REG *) 	0x0000007C) // (EMAC_RJA) Receive Jabbers Register
#define EMAC_USF        (AT91_CAST(AT91_REG *) 	0x00000080) // (EMAC_USF) Undersize Frames Register
#define EMAC_STE        (AT91_CAST(AT91_REG *) 	0x00000084) // (EMAC_STE) SQE Test Error Register
#define EMAC_RLE        (AT91_CAST(AT91_REG *) 	0x00000088) // (EMAC_RLE) Receive Length Field Mismatch Register
#define EMAC_TPF        (AT91_CAST(AT91_REG *) 	0x0000008C) // (EMAC_TPF) Transmitted Pause Frames Register
#define EMAC_HRB        (AT91_CAST(AT91_REG *) 	0x00000090) // (EMAC_HRB) Hash Address Bottom[31:0]
#define EMAC_HRT        (AT91_CAST(AT91_REG *) 	0x00000094) // (EMAC_HRT) Hash Address Top[63:32]
#define EMAC_SA1L       (AT91_CAST(AT91_REG *) 	0x00000098) // (EMAC_SA1L) Specific Address 1 Bottom, First 4 bytes
#define EMAC_SA1H       (AT91_CAST(AT91_REG *) 	0x0000009C) // (EMAC_SA1H) Specific Address 1 Top, Last 2 bytes
#define EMAC_SA2L       (AT91_CAST(AT91_REG *) 	0x000000A0) // (EMAC_SA2L) Specific Address 2 Bottom, First 4 bytes
#define EMAC_SA2H       (AT91_CAST(AT91_REG *) 	0x000000A4) // (EMAC_SA2H) Specific Address 2 Top, Last 2 bytes
#define EMAC_SA3L       (AT91_CAST(AT91_REG *) 	0x000000A8) // (EMAC_SA3L) Specific Address 3 Bottom, First 4 bytes
#define EMAC_SA3H       (AT91_CAST(AT91_REG *) 	0x000000AC) // (EMAC_SA3H) Specific Address 3 Top, Last 2 bytes
#define EMAC_SA4L       (AT91_CAST(AT91_REG *) 	0x000000B0) // (EMAC_SA4L) Specific Address 4 Bottom, First 4 bytes
#define EMAC_SA4H       (AT91_CAST(AT91_REG *) 	0x000000B4) // (EMAC_SA4H) Specific Address 4 Top, Last 2 bytes
#define EMAC_TID        (AT91_CAST(AT91_REG *) 	0x000000B8) // (EMAC_TID) Type ID Checking Register
#define EMAC_TPQ        (AT91_CAST(AT91_REG *) 	0x000000BC) // (EMAC_TPQ) Transmit Pause Quantum Register
#define EMAC_USRIO      (AT91_CAST(AT91_REG *) 	0x000000C0) // (EMAC_USRIO) USER Input/Output Register
#define EMAC_WOL        (AT91_CAST(AT91_REG *) 	0x000000C4) // (EMAC_WOL) Wake On LAN Register
#define EMAC_REV        (AT91_CAST(AT91_REG *) 	0x000000FC) // (EMAC_REV) Revision Register

#endif
// -------- EMAC_NCR : (EMAC Offset: 0x0)  -------- 
#define AT91C_EMAC_LB         (0x1 <<  0) // (EMAC) Loopback. Optional. When set, loopback signal is at high level.
#define AT91C_EMAC_LLB        (0x1 <<  1) // (EMAC) Loopback local. 
#define AT91C_EMAC_RE         (0x1 <<  2) // (EMAC) Receive enable. 
#define AT91C_EMAC_TE         (0x1 <<  3) // (EMAC) Transmit enable. 
#define AT91C_EMAC_MPE        (0x1 <<  4) // (EMAC) Management port enable. 
#define AT91C_EMAC_CLRSTAT    (0x1 <<  5) // (EMAC) Clear statistics registers. 
#define AT91C_EMAC_INCSTAT    (0x1 <<  6) // (EMAC) Increment statistics registers. 
#define AT91C_EMAC_WESTAT     (0x1 <<  7) // (EMAC) Write enable for statistics registers. 
#define AT91C_EMAC_BP         (0x1 <<  8) // (EMAC) Back pressure. 
#define AT91C_EMAC_TSTART     (0x1 <<  9) // (EMAC) Start Transmission. 
#define AT91C_EMAC_THALT      (0x1 << 10) // (EMAC) Transmission Halt. 
#define AT91C_EMAC_TPFR       (0x1 << 11) // (EMAC) Transmit pause frame 
#define AT91C_EMAC_TZQ        (0x1 << 12) // (EMAC) Transmit zero quantum pause frame
// -------- EMAC_NCFGR : (EMAC Offset: 0x4) Network Configuration Register -------- 
#define AT91C_EMAC_SPD        (0x1 <<  0) // (EMAC) Speed. 
#define AT91C_EMAC_FD         (0x1 <<  1) // (EMAC) Full duplex. 
#define AT91C_EMAC_JFRAME     (0x1 <<  3) // (EMAC) Jumbo Frames. 
#define AT91C_EMAC_CAF        (0x1 <<  4) // (EMAC) Copy all frames. 
#define AT91C_EMAC_NBC        (0x1 <<  5) // (EMAC) No broadcast. 
#define AT91C_EMAC_MTI        (0x1 <<  6) // (EMAC) Multicast hash event enable
#define AT91C_EMAC_UNI        (0x1 <<  7) // (EMAC) Unicast hash enable. 
#define AT91C_EMAC_BIG        (0x1 <<  8) // (EMAC) Receive 1522 bytes. 
#define AT91C_EMAC_EAE        (0x1 <<  9) // (EMAC) External address match enable. 
#define AT91C_EMAC_CLK        (0x3 << 10) // (EMAC) 
#define 	AT91C_EMAC_CLK_HCLK_8               (0x0 << 10) // (EMAC) HCLK divided by 8
#define 	AT91C_EMAC_CLK_HCLK_16              (0x1 << 10) // (EMAC) HCLK divided by 16
#define 	AT91C_EMAC_CLK_HCLK_32              (0x2 << 10) // (EMAC) HCLK divided by 32
#define 	AT91C_EMAC_CLK_HCLK_64              (0x3 << 10) // (EMAC) HCLK divided by 64
#define AT91C_EMAC_RTY        (0x1 << 12) // (EMAC) 
#define AT91C_EMAC_PAE        (0x1 << 13) // (EMAC) 
#define AT91C_EMAC_RBOF       (0x3 << 14) // (EMAC) 
#define 	AT91C_EMAC_RBOF_OFFSET_0             (0x0 << 14) // (EMAC) no offset from start of receive buffer
#define 	AT91C_EMAC_RBOF_OFFSET_1             (0x1 << 14) // (EMAC) one byte offset from start of receive buffer
#define 	AT91C_EMAC_RBOF_OFFSET_2             (0x2 << 14) // (EMAC) two bytes offset from start of receive buffer
#define 	AT91C_EMAC_RBOF_OFFSET_3             (0x3 << 14) // (EMAC) three bytes offset from start of receive buffer
#define AT91C_EMAC_RLCE       (0x1 << 16) // (EMAC) Receive Length field Checking Enable
#define AT91C_EMAC_DRFCS      (0x1 << 17) // (EMAC) Discard Receive FCS
#define AT91C_EMAC_EFRHD      (0x1 << 18) // (EMAC) 
#define AT91C_EMAC_IRXFCS     (0x1 << 19) // (EMAC) Ignore RX FCS
// -------- EMAC_NSR : (EMAC Offset: 0x8) Network Status Register -------- 
#define AT91C_EMAC_LINKR      (0x1 <<  0) // (EMAC) 
#define AT91C_EMAC_MDIO       (0x1 <<  1) // (EMAC) 
#define AT91C_EMAC_IDLE       (0x1 <<  2) // (EMAC) 
// -------- EMAC_TSR : (EMAC Offset: 0x14) Transmit Status Register -------- 
#define AT91C_EMAC_UBR        (0x1 <<  0) // (EMAC) 
#define AT91C_EMAC_COL        (0x1 <<  1) // (EMAC) 
#define AT91C_EMAC_RLES       (0x1 <<  2) // (EMAC) 
#define AT91C_EMAC_TGO        (0x1 <<  3) // (EMAC) Transmit Go
#define AT91C_EMAC_BEX        (0x1 <<  4) // (EMAC) Buffers exhausted mid frame
#define AT91C_EMAC_COMP       (0x1 <<  5) // (EMAC) 
#define AT91C_EMAC_UND        (0x1 <<  6) // (EMAC) 
// -------- EMAC_RSR : (EMAC Offset: 0x20) Receive Status Register -------- 
#define AT91C_EMAC_BNA        (0x1 <<  0) // (EMAC) 
#define AT91C_EMAC_REC        (0x1 <<  1) // (EMAC) 
#define AT91C_EMAC_OVR        (0x1 <<  2) // (EMAC) 
// -------- EMAC_ISR : (EMAC Offset: 0x24) Interrupt Status Register -------- 
#define AT91C_EMAC_MFD        (0x1 <<  0) // (EMAC) 
#define AT91C_EMAC_RCOMP      (0x1 <<  1) // (EMAC) 
#define AT91C_EMAC_RXUBR      (0x1 <<  2) // (EMAC) 
#define AT91C_EMAC_TXUBR      (0x1 <<  3) // (EMAC) 
#define AT91C_EMAC_TUNDR      (0x1 <<  4) // (EMAC) 
#define AT91C_EMAC_RLEX       (0x1 <<  5) // (EMAC) 
#define AT91C_EMAC_TXERR      (0x1 <<  6) // (EMAC) 
#define AT91C_EMAC_TCOMP      (0x1 <<  7) // (EMAC) 
#define AT91C_EMAC_LINK       (0x1 <<  9) // (EMAC) 
#define AT91C_EMAC_ROVR       (0x1 << 10) // (EMAC) 
#define AT91C_EMAC_HRESP      (0x1 << 11) // (EMAC) 
#define AT91C_EMAC_PFRE       (0x1 << 12) // (EMAC) 
#define AT91C_EMAC_PTZ        (0x1 << 13) // (EMAC) 
// -------- EMAC_IER : (EMAC Offset: 0x28) Interrupt Enable Register -------- 
// -------- EMAC_IDR : (EMAC Offset: 0x2c) Interrupt Disable Register -------- 
// -------- EMAC_IMR : (EMAC Offset: 0x30) Interrupt Mask Register -------- 
// -------- EMAC_MAN : (EMAC Offset: 0x34) PHY Maintenance Register -------- 
#define AT91C_EMAC_DATA       (0xFFFF <<  0) // (EMAC) 
#define AT91C_EMAC_CODE       (0x3 << 16) // (EMAC) 
#define AT91C_EMAC_REGA       (0x1F << 18) // (EMAC) 
#define AT91C_EMAC_PHYA       (0x1F << 23) // (EMAC) 
#define AT91C_EMAC_RW         (0x3 << 28) // (EMAC) 
#define AT91C_EMAC_SOF        (0x3 << 30) // (EMAC) 
// -------- EMAC_USRIO : (EMAC Offset: 0xc0) USER Input Output Register -------- 
#define AT91C_EMAC_RMII       (0x1 <<  0) // (EMAC) Reduce MII
#define AT91C_EMAC_CLKEN      (0x1 <<  1) // (EMAC) Clock Enable
// -------- EMAC_WOL : (EMAC Offset: 0xc4) Wake On LAN Register -------- 
#define AT91C_EMAC_IP         (0xFFFF <<  0) // (EMAC) ARP request IP address
#define AT91C_EMAC_MAG        (0x1 << 16) // (EMAC) Magic packet event enable
#define AT91C_EMAC_ARP        (0x1 << 17) // (EMAC) ARP request event enable
#define AT91C_EMAC_SA1        (0x1 << 18) // (EMAC) Specific address register 1 event enable
// -------- EMAC_REV : (EMAC Offset: 0xfc) Revision Register -------- 
#define AT91C_EMAC_REVREF     (0xFFFF <<  0) // (EMAC) 
#define AT91C_EMAC_PARTREF    (0xFFFF << 16) // (EMAC) 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR USB Device Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_UDP {
	AT91_REG	 UDP_NUM; 	// Frame Number Register
	AT91_REG	 UDP_GLBSTATE; 	// Global State Register
	AT91_REG	 UDP_FADDR; 	// Function Address Register
	AT91_REG	 Reserved0[1]; 	// 
	AT91_REG	 UDP_IER; 	// Interrupt Enable Register
	AT91_REG	 UDP_IDR; 	// Interrupt Disable Register
	AT91_REG	 UDP_IMR; 	// Interrupt Mask Register
	AT91_REG	 UDP_ISR; 	// Interrupt Status Register
	AT91_REG	 UDP_ICR; 	// Interrupt Clear Register
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 UDP_RSTEP; 	// Reset Endpoint Register
	AT91_REG	 Reserved2[1]; 	// 
	AT91_REG	 UDP_CSR[6]; 	// Endpoint Control and Status Register
	AT91_REG	 Reserved3[2]; 	// 
	AT91_REG	 UDP_FDR[6]; 	// Endpoint FIFO Data Register
	AT91_REG	 Reserved4[3]; 	// 
	AT91_REG	 UDP_TXVC; 	// Transceiver Control Register
} AT91S_UDP, *AT91PS_UDP;
#else
#define UDP_FRM_NUM     (AT91_CAST(AT91_REG *) 	0x00000000) // (UDP_FRM_NUM) Frame Number Register
#define UDP_GLBSTATE    (AT91_CAST(AT91_REG *) 	0x00000004) // (UDP_GLBSTATE) Global State Register
#define UDP_FADDR       (AT91_CAST(AT91_REG *) 	0x00000008) // (UDP_FADDR) Function Address Register
#define UDP_IER         (AT91_CAST(AT91_REG *) 	0x00000010) // (UDP_IER) Interrupt Enable Register
#define UDP_IDR         (AT91_CAST(AT91_REG *) 	0x00000014) // (UDP_IDR) Interrupt Disable Register
#define UDP_IMR         (AT91_CAST(AT91_REG *) 	0x00000018) // (UDP_IMR) Interrupt Mask Register
#define UDP_ISR         (AT91_CAST(AT91_REG *) 	0x0000001C) // (UDP_ISR) Interrupt Status Register
#define UDP_ICR         (AT91_CAST(AT91_REG *) 	0x00000020) // (UDP_ICR) Interrupt Clear Register
#define UDP_RSTEP       (AT91_CAST(AT91_REG *) 	0x00000028) // (UDP_RSTEP) Reset Endpoint Register
#define UDP_CSR         (AT91_CAST(AT91_REG *) 	0x00000030) // (UDP_CSR) Endpoint Control and Status Register
#define UDP_FDR         (AT91_CAST(AT91_REG *) 	0x00000050) // (UDP_FDR) Endpoint FIFO Data Register
#define UDP_TXVC        (AT91_CAST(AT91_REG *) 	0x00000074) // (UDP_TXVC) Transceiver Control Register

#endif
// -------- UDP_FRM_NUM : (UDP Offset: 0x0) USB Frame Number Register -------- 
#define AT91C_UDP_FRM_NUM     (0x7FF <<  0) // (UDP) Frame Number as Defined in the Packet Field Formats
#define AT91C_UDP_FRM_ERR     (0x1 << 16) // (UDP) Frame Error
#define AT91C_UDP_FRM_OK      (0x1 << 17) // (UDP) Frame OK
// -------- UDP_GLB_STATE : (UDP Offset: 0x4) USB Global State Register -------- 
#define AT91C_UDP_FADDEN      (0x1 <<  0) // (UDP) Function Address Enable
#define AT91C_UDP_CONFG       (0x1 <<  1) // (UDP) Configured
#define AT91C_UDP_ESR         (0x1 <<  2) // (UDP) Enable Send Resume
#define AT91C_UDP_RSMINPR     (0x1 <<  3) // (UDP) A Resume Has Been Sent to the Host
#define AT91C_UDP_RMWUPE      (0x1 <<  4) // (UDP) Remote Wake Up Enable
// -------- UDP_FADDR : (UDP Offset: 0x8) USB Function Address Register -------- 
#define AT91C_UDP_FADD        (0xFF <<  0) // (UDP) Function Address Value
#define AT91C_UDP_FEN         (0x1 <<  8) // (UDP) Function Enable
// -------- UDP_IER : (UDP Offset: 0x10) USB Interrupt Enable Register -------- 
#define AT91C_UDP_EPINT0      (0x1 <<  0) // (UDP) Endpoint 0 Interrupt
#define AT91C_UDP_EPINT1      (0x1 <<  1) // (UDP) Endpoint 0 Interrupt
#define AT91C_UDP_EPINT2      (0x1 <<  2) // (UDP) Endpoint 2 Interrupt
#define AT91C_UDP_EPINT3      (0x1 <<  3) // (UDP) Endpoint 3 Interrupt
#define AT91C_UDP_EPINT4      (0x1 <<  4) // (UDP) Endpoint 4 Interrupt
#define AT91C_UDP_EPINT5      (0x1 <<  5) // (UDP) Endpoint 5 Interrupt
#define AT91C_UDP_RXSUSP      (0x1 <<  8) // (UDP) USB Suspend Interrupt
#define AT91C_UDP_RXRSM       (0x1 <<  9) // (UDP) USB Resume Interrupt
#define AT91C_UDP_EXTRSM      (0x1 << 10) // (UDP) USB External Resume Interrupt
#define AT91C_UDP_SOFINT      (0x1 << 11) // (UDP) USB Start Of frame Interrupt
#define AT91C_UDP_WAKEUP      (0x1 << 13) // (UDP) USB Resume Interrupt
// -------- UDP_IDR : (UDP Offset: 0x14) USB Interrupt Disable Register -------- 
// -------- UDP_IMR : (UDP Offset: 0x18) USB Interrupt Mask Register -------- 
// -------- UDP_ISR : (UDP Offset: 0x1c) USB Interrupt Status Register -------- 
#define AT91C_UDP_ENDBUSRES   (0x1 << 12) // (UDP) USB End Of Bus Reset Interrupt
// -------- UDP_ICR : (UDP Offset: 0x20) USB Interrupt Clear Register -------- 
// -------- UDP_RST_EP : (UDP Offset: 0x28) USB Reset Endpoint Register -------- 
#define AT91C_UDP_EP0         (0x1 <<  0) // (UDP) Reset Endpoint 0
#define AT91C_UDP_EP1         (0x1 <<  1) // (UDP) Reset Endpoint 1
#define AT91C_UDP_EP2         (0x1 <<  2) // (UDP) Reset Endpoint 2
#define AT91C_UDP_EP3         (0x1 <<  3) // (UDP) Reset Endpoint 3
#define AT91C_UDP_EP4         (0x1 <<  4) // (UDP) Reset Endpoint 4
#define AT91C_UDP_EP5         (0x1 <<  5) // (UDP) Reset Endpoint 5
// -------- UDP_CSR : (UDP Offset: 0x30) USB Endpoint Control and Status Register -------- 
#define AT91C_UDP_TXCOMP      (0x1 <<  0) // (UDP) Generates an IN packet with data previously written in the DPR
#define AT91C_UDP_RX_DATA_BK0 (0x1 <<  1) // (UDP) Receive Data Bank 0
#define AT91C_UDP_RXSETUP     (0x1 <<  2) // (UDP) Sends STALL to the Host (Control endpoints)
#define AT91C_UDP_ISOERROR    (0x1 <<  3) // (UDP) Isochronous error (Isochronous endpoints)
#define AT91C_UDP_STALLSENT   (0x1 <<  3) // (UDP) Stall sent (Control, bulk, interrupt endpoints)
#define AT91C_UDP_TXPKTRDY    (0x1 <<  4) // (UDP) Transmit Packet Ready
#define AT91C_UDP_FORCESTALL  (0x1 <<  5) // (UDP) Force Stall (used by Control, Bulk and Isochronous endpoints).
#define AT91C_UDP_RX_DATA_BK1 (0x1 <<  6) // (UDP) Receive Data Bank 1 (only used by endpoints with ping-pong attributes).
#define AT91C_UDP_DIR         (0x1 <<  7) // (UDP) Transfer Direction
#define AT91C_UDP_EPTYPE      (0x7 <<  8) // (UDP) Endpoint type
#define 	AT91C_UDP_EPTYPE_CTRL                 (0x0 <<  8) // (UDP) Control
#define 	AT91C_UDP_EPTYPE_ISO_OUT              (0x1 <<  8) // (UDP) Isochronous OUT
#define 	AT91C_UDP_EPTYPE_BULK_OUT             (0x2 <<  8) // (UDP) Bulk OUT
#define 	AT91C_UDP_EPTYPE_INT_OUT              (0x3 <<  8) // (UDP) Interrupt OUT
#define 	AT91C_UDP_EPTYPE_ISO_IN               (0x5 <<  8) // (UDP) Isochronous IN
#define 	AT91C_UDP_EPTYPE_BULK_IN              (0x6 <<  8) // (UDP) Bulk IN
#define 	AT91C_UDP_EPTYPE_INT_IN               (0x7 <<  8) // (UDP) Interrupt IN
#define AT91C_UDP_DTGLE       (0x1 << 11) // (UDP) Data Toggle
#define AT91C_UDP_EPEDS       (0x1 << 15) // (UDP) Endpoint Enable Disable
#define AT91C_UDP_RXBYTECNT   (0x7FF << 16) // (UDP) Number Of Bytes Available in the FIFO
// -------- UDP_TXVC : (UDP Offset: 0x74) Transceiver Control Register -------- 
#define AT91C_UDP_TXVDIS      (0x1 <<  8) // (UDP) 
#define AT91C_UDP_PUON        (0x1 <<  9) // (UDP) Pull-up ON

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR USB Host Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_UHP {
	AT91_REG	 UHP_HcRevision; 	// Revision
	AT91_REG	 UHP_HcControl; 	// Operating modes for the Host Controller
	AT91_REG	 UHP_HcCommandStatus; 	// Command & status Register
	AT91_REG	 UHP_HcInterruptStatus; 	// Interrupt Status Register
	AT91_REG	 UHP_HcInterruptEnable; 	// Interrupt Enable Register
	AT91_REG	 UHP_HcInterruptDisable; 	// Interrupt Disable Register
	AT91_REG	 UHP_HcHCCA; 	// Pointer to the Host Controller Communication Area
	AT91_REG	 UHP_HcPeriodCurrentED; 	// Current Isochronous or Interrupt Endpoint Descriptor
	AT91_REG	 UHP_HcControlHeadED; 	// First Endpoint Descriptor of the Control list
	AT91_REG	 UHP_HcControlCurrentED; 	// Endpoint Control and Status Register
	AT91_REG	 UHP_HcBulkHeadED; 	// First endpoint register of the Bulk list
	AT91_REG	 UHP_HcBulkCurrentED; 	// Current endpoint of the Bulk list
	AT91_REG	 UHP_HcBulkDoneHead; 	// Last completed transfer descriptor
	AT91_REG	 UHP_HcFmInterval; 	// Bit time between 2 consecutive SOFs
	AT91_REG	 UHP_HcFmRemaining; 	// Bit time remaining in the current Frame
	AT91_REG	 UHP_HcFmNumber; 	// Frame number
	AT91_REG	 UHP_HcPeriodicStart; 	// Periodic Start
	AT91_REG	 UHP_HcLSThreshold; 	// LS Threshold
	AT91_REG	 UHP_HcRhDescriptorA; 	// Root Hub characteristics A
	AT91_REG	 UHP_HcRhDescriptorB; 	// Root Hub characteristics B
	AT91_REG	 UHP_HcRhStatus; 	// Root Hub Status register
	AT91_REG	 UHP_HcRhPortStatus[2]; 	// Root Hub Port Status Register
} AT91S_UHP, *AT91PS_UHP;
#else
#define HcRevision      (AT91_CAST(AT91_REG *) 	0x00000000) // (HcRevision) Revision
#define HcControl       (AT91_CAST(AT91_REG *) 	0x00000004) // (HcControl) Operating modes for the Host Controller
#define HcCommandStatus (AT91_CAST(AT91_REG *) 	0x00000008) // (HcCommandStatus) Command & status Register
#define HcInterruptStatus (AT91_CAST(AT91_REG *) 	0x0000000C) // (HcInterruptStatus) Interrupt Status Register
#define HcInterruptEnable (AT91_CAST(AT91_REG *) 	0x00000010) // (HcInterruptEnable) Interrupt Enable Register
#define HcInterruptDisable (AT91_CAST(AT91_REG *) 	0x00000014) // (HcInterruptDisable) Interrupt Disable Register
#define HcHCCA          (AT91_CAST(AT91_REG *) 	0x00000018) // (HcHCCA) Pointer to the Host Controller Communication Area
#define HcPeriodCurrentED (AT91_CAST(AT91_REG *) 	0x0000001C) // (HcPeriodCurrentED) Current Isochronous or Interrupt Endpoint Descriptor
#define HcControlHeadED (AT91_CAST(AT91_REG *) 	0x00000020) // (HcControlHeadED) First Endpoint Descriptor of the Control list
#define HcControlCurrentED (AT91_CAST(AT91_REG *) 	0x00000024) // (HcControlCurrentED) Endpoint Control and Status Register
#define HcBulkHeadED    (AT91_CAST(AT91_REG *) 	0x00000028) // (HcBulkHeadED) First endpoint register of the Bulk list
#define HcBulkCurrentED (AT91_CAST(AT91_REG *) 	0x0000002C) // (HcBulkCurrentED) Current endpoint of the Bulk list
#define HcBulkDoneHead  (AT91_CAST(AT91_REG *) 	0x00000030) // (HcBulkDoneHead) Last completed transfer descriptor
#define HcFmInterval    (AT91_CAST(AT91_REG *) 	0x00000034) // (HcFmInterval) Bit time between 2 consecutive SOFs
#define HcFmRemaining   (AT91_CAST(AT91_REG *) 	0x00000038) // (HcFmRemaining) Bit time remaining in the current Frame
#define HcFmNumber      (AT91_CAST(AT91_REG *) 	0x0000003C) // (HcFmNumber) Frame number
#define HcPeriodicStart (AT91_CAST(AT91_REG *) 	0x00000040) // (HcPeriodicStart) Periodic Start
#define HcLSThreshold   (AT91_CAST(AT91_REG *) 	0x00000044) // (HcLSThreshold) LS Threshold
#define HcRhDescriptorA (AT91_CAST(AT91_REG *) 	0x00000048) // (HcRhDescriptorA) Root Hub characteristics A
#define HcRhDescriptorB (AT91_CAST(AT91_REG *) 	0x0000004C) // (HcRhDescriptorB) Root Hub characteristics B
#define HcRhStatus      (AT91_CAST(AT91_REG *) 	0x00000050) // (HcRhStatus) Root Hub Status register
#define HcRhPortStatus  (AT91_CAST(AT91_REG *) 	0x00000054) // (HcRhPortStatus) Root Hub Port Status Register

#endif

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Image Sensor Interface
// *****************************************************************************
#ifndef __ASSEMBLY__
typedef struct _AT91S_ISI {
	AT91_REG	 ISI_CR1; 	// Control Register 1
	AT91_REG	 ISI_CR2; 	// Control Register 2
	AT91_REG	 ISI_SR; 	// Status Register
	AT91_REG	 ISI_IER; 	// Interrupt Enable Register
	AT91_REG	 ISI_IDR; 	// Interrupt Disable Register
	AT91_REG	 ISI_IMR; 	// Interrupt Mask Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 ISI_PSIZE; 	// Preview Size Register
	AT91_REG	 ISI_PDECF; 	// Preview Decimation Factor Register
	AT91_REG	 ISI_PFBD; 	// Preview Frame Buffer Address Register
	AT91_REG	 ISI_CDBA; 	// Codec Dma Address Register
	AT91_REG	 ISI_Y2RSET0; 	// Color Space Conversion Register
	AT91_REG	 ISI_Y2RSET1; 	// Color Space Conversion Register
	AT91_REG	 ISI_R2YSET0; 	// Color Space Conversion Register
	AT91_REG	 ISI_R2YSET1; 	// Color Space Conversion Register
	AT91_REG	 ISI_R2YSET2; 	// Color Space Conversion Register
} AT91S_ISI, *AT91PS_ISI;
#else
#define ISI_CR1         (AT91_CAST(AT91_REG *) 	0x00000000) // (ISI_CR1) Control Register 1
#define ISI_CR2         (AT91_CAST(AT91_REG *) 	0x00000004) // (ISI_CR2) Control Register 2
#define ISI_SR          (AT91_CAST(AT91_REG *) 	0x00000008) // (ISI_SR) Status Register
#define ISI_IER         (AT91_CAST(AT91_REG *) 	0x0000000C) // (ISI_IER) Interrupt Enable Register
#define ISI_IDR         (AT91_CAST(AT91_REG *) 	0x00000010) // (ISI_IDR) Interrupt Disable Register
#define ISI_IMR         (AT91_CAST(AT91_REG *) 	0x00000014) // (ISI_IMR) Interrupt Mask Register
#define ISI_PSIZE       (AT91_CAST(AT91_REG *) 	0x00000020) // (ISI_PSIZE) Preview Size Register
#define ISI_PDECF       (AT91_CAST(AT91_REG *) 	0x00000024) // (ISI_PDECF) Preview Decimation Factor Register
#define ISI_PFBD        (AT91_CAST(AT91_REG *) 	0x00000028) // (ISI_PFBD) Preview Frame Buffer Address Register
#define ISI_CDBA        (AT91_CAST(AT91_REG *) 	0x0000002C) // (ISI_CDBA) Codec Dma Address Register
#define ISI_Y2RSET0     (AT91_CAST(AT91_REG *) 	0x00000030) // (ISI_Y2RSET0) Color Space Conversion Register
#define ISI_Y2RSET1     (AT91_CAST(AT91_REG *) 	0x00000034) // (ISI_Y2RSET1) Color Space Conversion Register
#define ISI_R2YSET0     (AT91_CAST(AT91_REG *) 	0x00000038) // (ISI_R2YSET0) Color Space Conversion Register
#define ISI_R2YSET1     (AT91_CAST(AT91_REG *) 	0x0000003C) // (ISI_R2YSET1) Color Space Conversion Register
#define ISI_R2YSET2     (AT91_CAST(AT91_REG *) 	0x00000040) // (ISI_R2YSET2) Color Space Conversion Register

#endif
// -------- ISI_CR1 : (ISI Offset: 0x0) ISI Control Register 1 -------- 
#define AT91C_ISI_RST         (0x1 <<  0) // (ISI) Image sensor interface reset
#define AT91C_ISI_DISABLE     (0x1 <<  1) // (ISI) image sensor disable.
#define AT91C_ISI_HSYNC_POL   (0x1 <<  2) // (ISI) Horizontal synchronisation polarity
#define AT91C_ISI_PIXCLK_POL  (0x1 <<  4) // (ISI) Pixel Clock Polarity
#define AT91C_ISI_EMB_SYNC    (0x1 <<  6) // (ISI) Embedded synchronisation
#define AT91C_ISI_CRC_SYNC    (0x1 <<  7) // (ISI) CRC correction
#define AT91C_ISI_FULL        (0x1 << 12) // (ISI) Full mode is allowed
#define AT91C_ISI_THMASK      (0x3 << 13) // (ISI) DMA Burst Mask
#define 	AT91C_ISI_THMASK_4_8_16_BURST         (0x0 << 13) // (ISI) 4,8 and 16 AHB burst are allowed
#define 	AT91C_ISI_THMASK_8_16_BURST           (0x1 << 13) // (ISI) 8 and 16 AHB burst are allowed
#define 	AT91C_ISI_THMASK_16_BURST             (0x2 << 13) // (ISI) Only 16 AHB burst are allowed
#define AT91C_ISI_CODEC_ON    (0x1 << 15) // (ISI) Enable the codec path
#define AT91C_ISI_SLD         (0xFF << 16) // (ISI) Start of Line Delay
#define AT91C_ISI_SFD         (0xFF << 24) // (ISI) Start of frame Delay
// -------- ISI_CR2 : (ISI Offset: 0x4) ISI Control Register 2 -------- 
#define AT91C_ISI_IM_VSIZE    (0x7FF <<  0) // (ISI) Vertical size of the Image sensor [0..2047]
#define AT91C_ISI_GS_MODE     (0x1 << 11) // (ISI) Grayscale Memory Mode
#define AT91C_ISI_RGB_MODE    (0x3 << 12) // (ISI) RGB mode
#define 	AT91C_ISI_RGB_MODE_RGB_888              (0x0 << 12) // (ISI) RGB 8:8:8 24 bits
#define 	AT91C_ISI_RGB_MODE_RGB_565              (0x1 << 12) // (ISI) RGB 5:6:5 16 bits
#define 	AT91C_ISI_RGB_MODE_RGB_555              (0x2 << 12) // (ISI) RGB 5:5:5 16 bits
#define AT91C_ISI_GRAYSCALE   (0x1 << 13) // (ISI) Grayscale Mode
#define AT91C_ISI_RGB_SWAP    (0x1 << 14) // (ISI) RGB Swap
#define AT91C_ISI_COL_SPACE   (0x1 << 15) // (ISI) Color space for the image data
#define AT91C_ISI_IM_HSIZE    (0x7FF << 16) // (ISI) Horizontal size of the Image sensor [0..2047]
#define 	AT91C_ISI_RGB_MODE_YCC_DEF              (0x0 << 28) // (ISI) Cb(i) Y(i) Cr(i) Y(i+1)
#define 	AT91C_ISI_RGB_MODE_YCC_MOD1             (0x1 << 28) // (ISI) Cr(i) Y(i) Cb(i) Y(i+1)
#define 	AT91C_ISI_RGB_MODE_YCC_MOD2             (0x2 << 28) // (ISI) Y(i) Cb(i) Y(i+1) Cr(i)
#define 	AT91C_ISI_RGB_MODE_YCC_MOD3             (0x3 << 28) // (ISI) Y(i) Cr(i) Y(i+1) Cb(i)
#define AT91C_ISI_RGB_CFG     (0x3 << 30) // (ISI) RGB configuration
#define 	AT91C_ISI_RGB_CFG_RGB_DEF              (0x0 << 30) // (ISI) R/G(MSB)  G(LSB)/B  R/G(MSB)  G(LSB)/B
#define 	AT91C_ISI_RGB_CFG_RGB_MOD1             (0x1 << 30) // (ISI) B/G(MSB)  G(LSB)/R  B/G(MSB)  G(LSB)/R
#define 	AT91C_ISI_RGB_CFG_RGB_MOD2             (0x2 << 30) // (ISI) G(LSB)/R  B/G(MSB)  G(LSB)/R  B/G(MSB)
#define 	AT91C_ISI_RGB_CFG_RGB_MOD3             (0x3 << 30) // (ISI) G(LSB)/B  R/G(MSB)  G(LSB)/B  R/G(MSB)
// -------- ISI_SR : (ISI Offset: 0x8) ISI Status Register -------- 
#define AT91C_ISI_SOF         (0x1 <<  0) // (ISI) Start of Frame
#define AT91C_ISI_DIS         (0x1 <<  1) // (ISI) Image Sensor Interface disable
#define AT91C_ISI_SOFTRST     (0x1 <<  2) // (ISI) Software Reset
#define AT91C_ISI_CRC_ERR     (0x1 <<  4) // (ISI) CRC synchronisation error
#define AT91C_ISI_FO_C_OVF    (0x1 <<  5) // (ISI) Fifo Codec Overflow 
#define AT91C_ISI_FO_P_OVF    (0x1 <<  6) // (ISI) Fifo Preview Overflow 
#define AT91C_ISI_FO_P_EMP    (0x1 <<  7) // (ISI) Fifo Preview Empty
#define AT91C_ISI_FO_C_EMP    (0x1 <<  8) // (ISI) Fifo Codec Empty
#define AT91C_ISI_FR_OVR      (0x1 <<  9) // (ISI) Frame rate overun
// -------- ISI_IER : (ISI Offset: 0xc) ISI Interrupt Enable Register -------- 
// -------- ISI_IDR : (ISI Offset: 0x10) ISI Interrupt Disable Register -------- 
// -------- ISI_IMR : (ISI Offset: 0x14) ISI Interrupt Mask Register -------- 
// -------- ISI_PSIZE : (ISI Offset: 0x20) ISI Preview Register -------- 
#define AT91C_ISI_PREV_VSIZE  (0x3FF <<  0) // (ISI) Vertical size for the preview path
#define AT91C_ISI_PREV_HSIZE  (0x3FF << 16) // (ISI) Horizontal size for the preview path
// -------- ISI_Y2R_SET0 : (ISI Offset: 0x30) Color Space Conversion YCrCb to RGB Register -------- 
#define AT91C_ISI_Y2R_C0      (0xFF <<  0) // (ISI) Color Space Conversion Matrix Coefficient C0
#define AT91C_ISI_Y2R_C1      (0xFF <<  8) // (ISI) Color Space Conversion Matrix Coefficient C1
#define AT91C_ISI_Y2R_C2      (0xFF << 16) // (ISI) Color Space Conversion Matrix Coefficient C2
#define AT91C_ISI_Y2R_C3      (0xFF << 24) // (ISI) Color Space Conversion Matrix Coefficient C3
// -------- ISI_Y2R_SET1 : (ISI Offset: 0x34) ISI Color Space Conversion YCrCb to RGB set 1 Register -------- 
#define AT91C_ISI_Y2R_C4      (0x1FF <<  0) // (ISI) Color Space Conversion Matrix Coefficient C4
#define AT91C_ISI_Y2R_YOFF    (0xFF << 12) // (ISI) Color Space Conversion Luninance default offset
#define AT91C_ISI_Y2R_CROFF   (0xFF << 13) // (ISI) Color Space Conversion Red Chrominance default offset
#define AT91C_ISI_Y2R_CBFF    (0xFF << 14) // (ISI) Color Space Conversion Luninance default offset
// -------- ISI_R2Y_SET0 : (ISI Offset: 0x38) Color Space Conversion RGB to YCrCb set 0 register -------- 
#define AT91C_ISI_R2Y_C0      (0x7F <<  0) // (ISI) Color Space Conversion RGB to YCrCb Matrix coefficient C0
#define AT91C_ISI_R2Y_C1      (0x7F <<  1) // (ISI) Color Space Conversion RGB to YCrCb Matrix coefficient C1
#define AT91C_ISI_R2Y_C2      (0x7F <<  3) // (ISI) Color Space Conversion RGB to YCrCb Matrix coefficient C2
#define AT91C_ISI_R2Y_ROFF    (0x1 <<  4) // (ISI) Color Space Conversion Red component offset
// -------- ISI_R2Y_SET1 : (ISI Offset: 0x3c) Color Space Conversion RGB to YCrCb set 1 register -------- 
#define AT91C_ISI_R2Y_C3      (0x7F <<  0) // (ISI) Color Space Conversion RGB to YCrCb Matrix coefficient C3
#define AT91C_ISI_R2Y_C4      (0x7F <<  1) // (ISI) Color Space Conversion RGB to YCrCb Matrix coefficient C4
#define AT91C_ISI_R2Y_C5      (0x7F <<  3) // (ISI) Color Space Conversion RGB to YCrCb Matrix coefficient C5
#define AT91C_ISI_R2Y_GOFF    (0x1 <<  4) // (ISI) Color Space Conversion Green component offset
// -------- ISI_R2Y_SET2 : (ISI Offset: 0x40) Color Space Conversion RGB to YCrCb set 2 register -------- 
#define AT91C_ISI_R2Y_C6      (0x7F <<  0) // (ISI) Color Space Conversion RGB to YCrCb Matrix coefficient C6
#define AT91C_ISI_R2Y_C7      (0x7F <<  1) // (ISI) Color Space Conversion RGB to YCrCb Matrix coefficient C7
#define AT91C_ISI_R2Y_C8      (0x7F <<  3) // (ISI) Color Space Conversion RGB to YCrCb Matrix coefficient C8
#define AT91C_ISI_R2Y_BOFF    (0x1 <<  4) // (ISI) Color Space Conversion Blue component offset

// *****************************************************************************
//               REGISTER ADDRESS DEFINITION FOR AT91SAM9XE512
// *****************************************************************************
// ========== Register definition for SYS peripheral ========== 
#define AT91C_SYS_GPBR  (AT91_CAST(AT91_REG *) 	0xFFFFFFFF) // (SYS) General Purpose Register
// ========== Register definition for EBI peripheral ========== 
#define AT91C_EBI_DUMMY (AT91_CAST(AT91_REG *) 	0xFFFFEA00) // (EBI) Dummy register - Do not use
// ========== Register definition for HECC peripheral ========== 
#define AT91C_HECC_VR   (AT91_CAST(AT91_REG *) 	0xFFFFE8FC) // (HECC)  ECC Version register
#define AT91C_HECC_NPR  (AT91_CAST(AT91_REG *) 	0xFFFFE810) // (HECC)  ECC Parity N register
#define AT91C_HECC_SR   (AT91_CAST(AT91_REG *) 	0xFFFFE808) // (HECC)  ECC Status register
#define AT91C_HECC_PR   (AT91_CAST(AT91_REG *) 	0xFFFFE80C) // (HECC)  ECC Parity register
#define AT91C_HECC_MR   (AT91_CAST(AT91_REG *) 	0xFFFFE804) // (HECC)  ECC Page size register
#define AT91C_HECC_CR   (AT91_CAST(AT91_REG *) 	0xFFFFE800) // (HECC)  ECC reset register
// ========== Register definition for SDRAMC peripheral ========== 
#define AT91C_SDRAMC_MR (AT91_CAST(AT91_REG *) 	0xFFFFEA00) // (SDRAMC) SDRAM Controller Mode Register
#define AT91C_SDRAMC_IMR (AT91_CAST(AT91_REG *) 	0xFFFFEA1C) // (SDRAMC) SDRAM Controller Interrupt Mask Register
#define AT91C_SDRAMC_LPR (AT91_CAST(AT91_REG *) 	0xFFFFEA10) // (SDRAMC) SDRAM Controller Low Power Register
#define AT91C_SDRAMC_ISR (AT91_CAST(AT91_REG *) 	0xFFFFEA20) // (SDRAMC) SDRAM Controller Interrupt Mask Register
#define AT91C_SDRAMC_IDR (AT91_CAST(AT91_REG *) 	0xFFFFEA18) // (SDRAMC) SDRAM Controller Interrupt Disable Register
#define AT91C_SDRAMC_CR (AT91_CAST(AT91_REG *) 	0xFFFFEA08) // (SDRAMC) SDRAM Controller Configuration Register
#define AT91C_SDRAMC_TR (AT91_CAST(AT91_REG *) 	0xFFFFEA04) // (SDRAMC) SDRAM Controller Refresh Timer Register
#define AT91C_SDRAMC_MDR (AT91_CAST(AT91_REG *) 	0xFFFFEA24) // (SDRAMC) SDRAM Memory Device Register
#define AT91C_SDRAMC_HSR (AT91_CAST(AT91_REG *) 	0xFFFFEA0C) // (SDRAMC) SDRAM Controller High Speed Register
#define AT91C_SDRAMC_IER (AT91_CAST(AT91_REG *) 	0xFFFFEA14) // (SDRAMC) SDRAM Controller Interrupt Enable Register
// ========== Register definition for SMC peripheral ========== 
#define AT91C_SMC_CTRL1 (AT91_CAST(AT91_REG *) 	0xFFFFEC1C) // (SMC)  Control Register for CS 1
#define AT91C_SMC_PULSE7 (AT91_CAST(AT91_REG *) 	0xFFFFEC74) // (SMC)  Pulse Register for CS 7
#define AT91C_SMC_PULSE6 (AT91_CAST(AT91_REG *) 	0xFFFFEC64) // (SMC)  Pulse Register for CS 6
#define AT91C_SMC_SETUP4 (AT91_CAST(AT91_REG *) 	0xFFFFEC40) // (SMC)  Setup Register for CS 4
#define AT91C_SMC_PULSE3 (AT91_CAST(AT91_REG *) 	0xFFFFEC34) // (SMC)  Pulse Register for CS 3
#define AT91C_SMC_CYCLE5 (AT91_CAST(AT91_REG *) 	0xFFFFEC58) // (SMC)  Cycle Register for CS 5
#define AT91C_SMC_CYCLE2 (AT91_CAST(AT91_REG *) 	0xFFFFEC28) // (SMC)  Cycle Register for CS 2
#define AT91C_SMC_CTRL2 (AT91_CAST(AT91_REG *) 	0xFFFFEC2C) // (SMC)  Control Register for CS 2
#define AT91C_SMC_CTRL0 (AT91_CAST(AT91_REG *) 	0xFFFFEC0C) // (SMC)  Control Register for CS 0
#define AT91C_SMC_PULSE5 (AT91_CAST(AT91_REG *) 	0xFFFFEC54) // (SMC)  Pulse Register for CS 5
#define AT91C_SMC_PULSE1 (AT91_CAST(AT91_REG *) 	0xFFFFEC14) // (SMC)  Pulse Register for CS 1
#define AT91C_SMC_PULSE0 (AT91_CAST(AT91_REG *) 	0xFFFFEC04) // (SMC)  Pulse Register for CS 0
#define AT91C_SMC_CYCLE7 (AT91_CAST(AT91_REG *) 	0xFFFFEC78) // (SMC)  Cycle Register for CS 7
#define AT91C_SMC_CTRL4 (AT91_CAST(AT91_REG *) 	0xFFFFEC4C) // (SMC)  Control Register for CS 4
#define AT91C_SMC_CTRL3 (AT91_CAST(AT91_REG *) 	0xFFFFEC3C) // (SMC)  Control Register for CS 3
#define AT91C_SMC_SETUP7 (AT91_CAST(AT91_REG *) 	0xFFFFEC70) // (SMC)  Setup Register for CS 7
#define AT91C_SMC_CTRL7 (AT91_CAST(AT91_REG *) 	0xFFFFEC7C) // (SMC)  Control Register for CS 7
#define AT91C_SMC_SETUP1 (AT91_CAST(AT91_REG *) 	0xFFFFEC10) // (SMC)  Setup Register for CS 1
#define AT91C_SMC_CYCLE0 (AT91_CAST(AT91_REG *) 	0xFFFFEC08) // (SMC)  Cycle Register for CS 0
#define AT91C_SMC_CTRL5 (AT91_CAST(AT91_REG *) 	0xFFFFEC5C) // (SMC)  Control Register for CS 5
#define AT91C_SMC_CYCLE1 (AT91_CAST(AT91_REG *) 	0xFFFFEC18) // (SMC)  Cycle Register for CS 1
#define AT91C_SMC_CTRL6 (AT91_CAST(AT91_REG *) 	0xFFFFEC6C) // (SMC)  Control Register for CS 6
#define AT91C_SMC_SETUP0 (AT91_CAST(AT91_REG *) 	0xFFFFEC00) // (SMC)  Setup Register for CS 0
#define AT91C_SMC_PULSE4 (AT91_CAST(AT91_REG *) 	0xFFFFEC44) // (SMC)  Pulse Register for CS 4
#define AT91C_SMC_SETUP5 (AT91_CAST(AT91_REG *) 	0xFFFFEC50) // (SMC)  Setup Register for CS 5
#define AT91C_SMC_SETUP2 (AT91_CAST(AT91_REG *) 	0xFFFFEC20) // (SMC)  Setup Register for CS 2
#define AT91C_SMC_CYCLE3 (AT91_CAST(AT91_REG *) 	0xFFFFEC38) // (SMC)  Cycle Register for CS 3
#define AT91C_SMC_CYCLE6 (AT91_CAST(AT91_REG *) 	0xFFFFEC68) // (SMC)  Cycle Register for CS 6
#define AT91C_SMC_SETUP6 (AT91_CAST(AT91_REG *) 	0xFFFFEC60) // (SMC)  Setup Register for CS 6
#define AT91C_SMC_CYCLE4 (AT91_CAST(AT91_REG *) 	0xFFFFEC48) // (SMC)  Cycle Register for CS 4
#define AT91C_SMC_PULSE2 (AT91_CAST(AT91_REG *) 	0xFFFFEC24) // (SMC)  Pulse Register for CS 2
#define AT91C_SMC_SETUP3 (AT91_CAST(AT91_REG *) 	0xFFFFEC30) // (SMC)  Setup Register for CS 3
// ========== Register definition for MATRIX peripheral ========== 
#define AT91C_MATRIX_MCFG0 (AT91_CAST(AT91_REG *) 	0xFFFFEE00) // (MATRIX)  Master Configuration Register 0 (ram96k)     
#define AT91C_MATRIX_MCFG7 (AT91_CAST(AT91_REG *) 	0xFFFFEE1C) // (MATRIX)  Master Configuration Register 7 (teak_prog)     
#define AT91C_MATRIX_SCFG1 (AT91_CAST(AT91_REG *) 	0xFFFFEE44) // (MATRIX)  Slave Configuration Register 1 (rom)    
#define AT91C_MATRIX_MCFG4 (AT91_CAST(AT91_REG *) 	0xFFFFEE10) // (MATRIX)  Master Configuration Register 4 (bridge)    
#define AT91C_MATRIX_VERSION (AT91_CAST(AT91_REG *) 	0xFFFFEFFC) // (MATRIX)  Version Register
#define AT91C_MATRIX_MCFG2 (AT91_CAST(AT91_REG *) 	0xFFFFEE08) // (MATRIX)  Master Configuration Register 2 (hperiphs) 
#define AT91C_MATRIX_PRBS4 (AT91_CAST(AT91_REG *) 	0xFFFFEEA4) // (MATRIX)  PRBS4 : ebi
#define AT91C_MATRIX_PRBS0 (AT91_CAST(AT91_REG *) 	0xFFFFEE84) // (MATRIX)  PRBS0 (ram0) 
#define AT91C_MATRIX_SCFG3 (AT91_CAST(AT91_REG *) 	0xFFFFEE4C) // (MATRIX)  Slave Configuration Register 3 (ebi)
#define AT91C_MATRIX_MCFG6 (AT91_CAST(AT91_REG *) 	0xFFFFEE18) // (MATRIX)  Master Configuration Register 6 (ram16k)  
#define AT91C_MATRIX_EBI (AT91_CAST(AT91_REG *) 	0xFFFFEF1C) // (MATRIX)  Slave 3 (ebi) Special Function Register
#define AT91C_MATRIX_SCFG0 (AT91_CAST(AT91_REG *) 	0xFFFFEE40) // (MATRIX)  Slave Configuration Register 0 (ram96k)     
#define AT91C_MATRIX_PRBS3 (AT91_CAST(AT91_REG *) 	0xFFFFEE9C) // (MATRIX)  PRBS3 : usb_dev_hs
#define AT91C_MATRIX_PRAS3 (AT91_CAST(AT91_REG *) 	0xFFFFEE98) // (MATRIX)  PRAS3 : usb_dev_hs
#define AT91C_MATRIX_PRAS0 (AT91_CAST(AT91_REG *) 	0xFFFFEE80) // (MATRIX)  PRAS0 (ram0) 
#define AT91C_MATRIX_MCFG3 (AT91_CAST(AT91_REG *) 	0xFFFFEE0C) // (MATRIX)  Master Configuration Register 3 (ebi)
#define AT91C_MATRIX_PRAS1 (AT91_CAST(AT91_REG *) 	0xFFFFEE88) // (MATRIX)  PRAS1 (ram1) 
#define AT91C_MATRIX_PRAS2 (AT91_CAST(AT91_REG *) 	0xFFFFEE90) // (MATRIX)  PRAS2 (ram2) 
#define AT91C_MATRIX_SCFG2 (AT91_CAST(AT91_REG *) 	0xFFFFEE48) // (MATRIX)  Slave Configuration Register 2 (hperiphs) 
#define AT91C_MATRIX_MCFG5 (AT91_CAST(AT91_REG *) 	0xFFFFEE14) // (MATRIX)  Master Configuration Register 5 (mailbox)    
#define AT91C_MATRIX_MCFG1 (AT91_CAST(AT91_REG *) 	0xFFFFEE04) // (MATRIX)  Master Configuration Register 1 (rom)    
#define AT91C_MATRIX_PRAS4 (AT91_CAST(AT91_REG *) 	0xFFFFEEA0) // (MATRIX)  PRAS4 : ebi
#define AT91C_MATRIX_MRCR (AT91_CAST(AT91_REG *) 	0xFFFFEF00) // (MATRIX)  Master Remp Control Register 
#define AT91C_MATRIX_PRBS2 (AT91_CAST(AT91_REG *) 	0xFFFFEE94) // (MATRIX)  PRBS2 (ram2) 
#define AT91C_MATRIX_SCFG4 (AT91_CAST(AT91_REG *) 	0xFFFFEE50) // (MATRIX)  Slave Configuration Register 4 (bridge)    
#define AT91C_MATRIX_TEAKCFG (AT91_CAST(AT91_REG *) 	0xFFFFEF2C) // (MATRIX)  Slave 7 (teak_prog) Special Function Register
#define AT91C_MATRIX_PRBS1 (AT91_CAST(AT91_REG *) 	0xFFFFEE8C) // (MATRIX)  PRBS1 (ram1) 
// ========== Register definition for CCFG peripheral ========== 
#define AT91C_CCFG_MATRIXVERSION (AT91_CAST(AT91_REG *) 	0xFFFFEFFC) // (CCFG)  Version Register
#define AT91C_CCFG_EBICSA (AT91_CAST(AT91_REG *) 	0xFFFFEF1C) // (CCFG)  EBI Chip Select Assignement Register
// ========== Register definition for PDC_DBGU peripheral ========== 
#define AT91C_DBGU_TCR  (AT91_CAST(AT91_REG *) 	0xFFFFF30C) // (PDC_DBGU) Transmit Counter Register
#define AT91C_DBGU_RNPR (AT91_CAST(AT91_REG *) 	0xFFFFF310) // (PDC_DBGU) Receive Next Pointer Register
#define AT91C_DBGU_TNPR (AT91_CAST(AT91_REG *) 	0xFFFFF318) // (PDC_DBGU) Transmit Next Pointer Register
#define AT91C_DBGU_TPR  (AT91_CAST(AT91_REG *) 	0xFFFFF308) // (PDC_DBGU) Transmit Pointer Register
#define AT91C_DBGU_RPR  (AT91_CAST(AT91_REG *) 	0xFFFFF300) // (PDC_DBGU) Receive Pointer Register
#define AT91C_DBGU_RCR  (AT91_CAST(AT91_REG *) 	0xFFFFF304) // (PDC_DBGU) Receive Counter Register
#define AT91C_DBGU_RNCR (AT91_CAST(AT91_REG *) 	0xFFFFF314) // (PDC_DBGU) Receive Next Counter Register
#define AT91C_DBGU_PTCR (AT91_CAST(AT91_REG *) 	0xFFFFF320) // (PDC_DBGU) PDC Transfer Control Register
#define AT91C_DBGU_PTSR (AT91_CAST(AT91_REG *) 	0xFFFFF324) // (PDC_DBGU) PDC Transfer Status Register
#define AT91C_DBGU_TNCR (AT91_CAST(AT91_REG *) 	0xFFFFF31C) // (PDC_DBGU) Transmit Next Counter Register
// ========== Register definition for DBGU peripheral ========== 
#define AT91C_DBGU_EXID (AT91_CAST(AT91_REG *) 	0xFFFFF244) // (DBGU) Chip ID Extension Register
#define AT91C_DBGU_BRGR (AT91_CAST(AT91_REG *) 	0xFFFFF220) // (DBGU) Baud Rate Generator Register
#define AT91C_DBGU_IDR  (AT91_CAST(AT91_REG *) 	0xFFFFF20C) // (DBGU) Interrupt Disable Register
#define AT91C_DBGU_CSR  (AT91_CAST(AT91_REG *) 	0xFFFFF214) // (DBGU) Channel Status Register
#define AT91C_DBGU_CIDR (AT91_CAST(AT91_REG *) 	0xFFFFF240) // (DBGU) Chip ID Register
#define AT91C_DBGU_MR   (AT91_CAST(AT91_REG *) 	0xFFFFF204) // (DBGU) Mode Register
#define AT91C_DBGU_IMR  (AT91_CAST(AT91_REG *) 	0xFFFFF210) // (DBGU) Interrupt Mask Register
#define AT91C_DBGU_CR   (AT91_CAST(AT91_REG *) 	0xFFFFF200) // (DBGU) Control Register
#define AT91C_DBGU_FNTR (AT91_CAST(AT91_REG *) 	0xFFFFF248) // (DBGU) Force NTRST Register
#define AT91C_DBGU_THR  (AT91_CAST(AT91_REG *) 	0xFFFFF21C) // (DBGU) Transmitter Holding Register
#define AT91C_DBGU_RHR  (AT91_CAST(AT91_REG *) 	0xFFFFF218) // (DBGU) Receiver Holding Register
#define AT91C_DBGU_IER  (AT91_CAST(AT91_REG *) 	0xFFFFF208) // (DBGU) Interrupt Enable Register
// ========== Register definition for AIC peripheral ========== 
#define AT91C_AIC_IVR   (AT91_CAST(AT91_REG *) 	0xFFFFF100) // (AIC) IRQ Vector Register
#define AT91C_AIC_SMR   (AT91_CAST(AT91_REG *) 	0xFFFFF000) // (AIC) Source Mode Register
#define AT91C_AIC_FVR   (AT91_CAST(AT91_REG *) 	0xFFFFF104) // (AIC) FIQ Vector Register
#define AT91C_AIC_DCR   (AT91_CAST(AT91_REG *) 	0xFFFFF138) // (AIC) Debug Control Register (Protect)
#define AT91C_AIC_EOICR (AT91_CAST(AT91_REG *) 	0xFFFFF130) // (AIC) End of Interrupt Command Register
#define AT91C_AIC_SVR   (AT91_CAST(AT91_REG *) 	0xFFFFF080) // (AIC) Source Vector Register
#define AT91C_AIC_FFSR  (AT91_CAST(AT91_REG *) 	0xFFFFF148) // (AIC) Fast Forcing Status Register
#define AT91C_AIC_ICCR  (AT91_CAST(AT91_REG *) 	0xFFFFF128) // (AIC) Interrupt Clear Command Register
#define AT91C_AIC_ISR   (AT91_CAST(AT91_REG *) 	0xFFFFF108) // (AIC) Interrupt Status Register
#define AT91C_AIC_IMR   (AT91_CAST(AT91_REG *) 	0xFFFFF110) // (AIC) Interrupt Mask Register
#define AT91C_AIC_IPR   (AT91_CAST(AT91_REG *) 	0xFFFFF10C) // (AIC) Interrupt Pending Register
#define AT91C_AIC_FFER  (AT91_CAST(AT91_REG *) 	0xFFFFF140) // (AIC) Fast Forcing Enable Register
#define AT91C_AIC_IECR  (AT91_CAST(AT91_REG *) 	0xFFFFF120) // (AIC) Interrupt Enable Command Register
#define AT91C_AIC_ISCR  (AT91_CAST(AT91_REG *) 	0xFFFFF12C) // (AIC) Interrupt Set Command Register
#define AT91C_AIC_FFDR  (AT91_CAST(AT91_REG *) 	0xFFFFF144) // (AIC) Fast Forcing Disable Register
#define AT91C_AIC_CISR  (AT91_CAST(AT91_REG *) 	0xFFFFF114) // (AIC) Core Interrupt Status Register
#define AT91C_AIC_IDCR  (AT91_CAST(AT91_REG *) 	0xFFFFF124) // (AIC) Interrupt Disable Command Register
#define AT91C_AIC_SPU   (AT91_CAST(AT91_REG *) 	0xFFFFF134) // (AIC) Spurious Vector Register
// ========== Register definition for PIOA peripheral ========== 
#define AT91C_PIOA_ODR  (AT91_CAST(AT91_REG *) 	0xFFFFF414) // (PIOA) Output Disable Registerr
#define AT91C_PIOA_SODR (AT91_CAST(AT91_REG *) 	0xFFFFF430) // (PIOA) Set Output Data Register
#define AT91C_PIOA_ISR  (AT91_CAST(AT91_REG *) 	0xFFFFF44C) // (PIOA) Interrupt Status Register
#define AT91C_PIOA_ABSR (AT91_CAST(AT91_REG *) 	0xFFFFF478) // (PIOA) AB Select Status Register
#define AT91C_PIOA_IER  (AT91_CAST(AT91_REG *) 	0xFFFFF440) // (PIOA) Interrupt Enable Register
#define AT91C_PIOA_PPUDR (AT91_CAST(AT91_REG *) 	0xFFFFF460) // (PIOA) Pull-up Disable Register
#define AT91C_PIOA_IMR  (AT91_CAST(AT91_REG *) 	0xFFFFF448) // (PIOA) Interrupt Mask Register
#define AT91C_PIOA_PER  (AT91_CAST(AT91_REG *) 	0xFFFFF400) // (PIOA) PIO Enable Register
#define AT91C_PIOA_IFDR (AT91_CAST(AT91_REG *) 	0xFFFFF424) // (PIOA) Input Filter Disable Register
#define AT91C_PIOA_OWDR (AT91_CAST(AT91_REG *) 	0xFFFFF4A4) // (PIOA) Output Write Disable Register
#define AT91C_PIOA_MDSR (AT91_CAST(AT91_REG *) 	0xFFFFF458) // (PIOA) Multi-driver Status Register
#define AT91C_PIOA_IDR  (AT91_CAST(AT91_REG *) 	0xFFFFF444) // (PIOA) Interrupt Disable Register
#define AT91C_PIOA_ODSR (AT91_CAST(AT91_REG *) 	0xFFFFF438) // (PIOA) Output Data Status Register
#define AT91C_PIOA_PPUSR (AT91_CAST(AT91_REG *) 	0xFFFFF468) // (PIOA) Pull-up Status Register
#define AT91C_PIOA_OWSR (AT91_CAST(AT91_REG *) 	0xFFFFF4A8) // (PIOA) Output Write Status Register
#define AT91C_PIOA_BSR  (AT91_CAST(AT91_REG *) 	0xFFFFF474) // (PIOA) Select B Register
#define AT91C_PIOA_OWER (AT91_CAST(AT91_REG *) 	0xFFFFF4A0) // (PIOA) Output Write Enable Register
#define AT91C_PIOA_IFER (AT91_CAST(AT91_REG *) 	0xFFFFF420) // (PIOA) Input Filter Enable Register
#define AT91C_PIOA_PDSR (AT91_CAST(AT91_REG *) 	0xFFFFF43C) // (PIOA) Pin Data Status Register
#define AT91C_PIOA_PPUER (AT91_CAST(AT91_REG *) 	0xFFFFF464) // (PIOA) Pull-up Enable Register
#define AT91C_PIOA_OSR  (AT91_CAST(AT91_REG *) 	0xFFFFF418) // (PIOA) Output Status Register
#define AT91C_PIOA_ASR  (AT91_CAST(AT91_REG *) 	0xFFFFF470) // (PIOA) Select A Register
#define AT91C_PIOA_MDDR (AT91_CAST(AT91_REG *) 	0xFFFFF454) // (PIOA) Multi-driver Disable Register
#define AT91C_PIOA_CODR (AT91_CAST(AT91_REG *) 	0xFFFFF434) // (PIOA) Clear Output Data Register
#define AT91C_PIOA_MDER (AT91_CAST(AT91_REG *) 	0xFFFFF450) // (PIOA) Multi-driver Enable Register
#define AT91C_PIOA_PDR  (AT91_CAST(AT91_REG *) 	0xFFFFF404) // (PIOA) PIO Disable Register
#define AT91C_PIOA_IFSR (AT91_CAST(AT91_REG *) 	0xFFFFF428) // (PIOA) Input Filter Status Register
#define AT91C_PIOA_OER  (AT91_CAST(AT91_REG *) 	0xFFFFF410) // (PIOA) Output Enable Register
#define AT91C_PIOA_PSR  (AT91_CAST(AT91_REG *) 	0xFFFFF408) // (PIOA) PIO Status Register
// ========== Register definition for PIOB peripheral ========== 
#define AT91C_PIOB_OWDR (AT91_CAST(AT91_REG *) 	0xFFFFF6A4) // (PIOB) Output Write Disable Register
#define AT91C_PIOB_MDER (AT91_CAST(AT91_REG *) 	0xFFFFF650) // (PIOB) Multi-driver Enable Register
#define AT91C_PIOB_PPUSR (AT91_CAST(AT91_REG *) 	0xFFFFF668) // (PIOB) Pull-up Status Register
#define AT91C_PIOB_IMR  (AT91_CAST(AT91_REG *) 	0xFFFFF648) // (PIOB) Interrupt Mask Register
#define AT91C_PIOB_ASR  (AT91_CAST(AT91_REG *) 	0xFFFFF670) // (PIOB) Select A Register
#define AT91C_PIOB_PPUDR (AT91_CAST(AT91_REG *) 	0xFFFFF660) // (PIOB) Pull-up Disable Register
#define AT91C_PIOB_PSR  (AT91_CAST(AT91_REG *) 	0xFFFFF608) // (PIOB) PIO Status Register
#define AT91C_PIOB_IER  (AT91_CAST(AT91_REG *) 	0xFFFFF640) // (PIOB) Interrupt Enable Register
#define AT91C_PIOB_CODR (AT91_CAST(AT91_REG *) 	0xFFFFF634) // (PIOB) Clear Output Data Register
#define AT91C_PIOB_OWER (AT91_CAST(AT91_REG *) 	0xFFFFF6A0) // (PIOB) Output Write Enable Register
#define AT91C_PIOB_ABSR (AT91_CAST(AT91_REG *) 	0xFFFFF678) // (PIOB) AB Select Status Register
#define AT91C_PIOB_IFDR (AT91_CAST(AT91_REG *) 	0xFFFFF624) // (PIOB) Input Filter Disable Register
#define AT91C_PIOB_PDSR (AT91_CAST(AT91_REG *) 	0xFFFFF63C) // (PIOB) Pin Data Status Register
#define AT91C_PIOB_IDR  (AT91_CAST(AT91_REG *) 	0xFFFFF644) // (PIOB) Interrupt Disable Register
#define AT91C_PIOB_OWSR (AT91_CAST(AT91_REG *) 	0xFFFFF6A8) // (PIOB) Output Write Status Register
#define AT91C_PIOB_PDR  (AT91_CAST(AT91_REG *) 	0xFFFFF604) // (PIOB) PIO Disable Register
#define AT91C_PIOB_ODR  (AT91_CAST(AT91_REG *) 	0xFFFFF614) // (PIOB) Output Disable Registerr
#define AT91C_PIOB_IFSR (AT91_CAST(AT91_REG *) 	0xFFFFF628) // (PIOB) Input Filter Status Register
#define AT91C_PIOB_PPUER (AT91_CAST(AT91_REG *) 	0xFFFFF664) // (PIOB) Pull-up Enable Register
#define AT91C_PIOB_SODR (AT91_CAST(AT91_REG *) 	0xFFFFF630) // (PIOB) Set Output Data Register
#define AT91C_PIOB_ISR  (AT91_CAST(AT91_REG *) 	0xFFFFF64C) // (PIOB) Interrupt Status Register
#define AT91C_PIOB_ODSR (AT91_CAST(AT91_REG *) 	0xFFFFF638) // (PIOB) Output Data Status Register
#define AT91C_PIOB_OSR  (AT91_CAST(AT91_REG *) 	0xFFFFF618) // (PIOB) Output Status Register
#define AT91C_PIOB_MDSR (AT91_CAST(AT91_REG *) 	0xFFFFF658) // (PIOB) Multi-driver Status Register
#define AT91C_PIOB_IFER (AT91_CAST(AT91_REG *) 	0xFFFFF620) // (PIOB) Input Filter Enable Register
#define AT91C_PIOB_BSR  (AT91_CAST(AT91_REG *) 	0xFFFFF674) // (PIOB) Select B Register
#define AT91C_PIOB_MDDR (AT91_CAST(AT91_REG *) 	0xFFFFF654) // (PIOB) Multi-driver Disable Register
#define AT91C_PIOB_OER  (AT91_CAST(AT91_REG *) 	0xFFFFF610) // (PIOB) Output Enable Register
#define AT91C_PIOB_PER  (AT91_CAST(AT91_REG *) 	0xFFFFF600) // (PIOB) PIO Enable Register
// ========== Register definition for PIOC peripheral ========== 
#define AT91C_PIOC_OWDR (AT91_CAST(AT91_REG *) 	0xFFFFF8A4) // (PIOC) Output Write Disable Register
#define AT91C_PIOC_SODR (AT91_CAST(AT91_REG *) 	0xFFFFF830) // (PIOC) Set Output Data Register
#define AT91C_PIOC_PPUER (AT91_CAST(AT91_REG *) 	0xFFFFF864) // (PIOC) Pull-up Enable Register
#define AT91C_PIOC_CODR (AT91_CAST(AT91_REG *) 	0xFFFFF834) // (PIOC) Clear Output Data Register
#define AT91C_PIOC_PSR  (AT91_CAST(AT91_REG *) 	0xFFFFF808) // (PIOC) PIO Status Register
#define AT91C_PIOC_PDR  (AT91_CAST(AT91_REG *) 	0xFFFFF804) // (PIOC) PIO Disable Register
#define AT91C_PIOC_ODR  (AT91_CAST(AT91_REG *) 	0xFFFFF814) // (PIOC) Output Disable Registerr
#define AT91C_PIOC_PPUSR (AT91_CAST(AT91_REG *) 	0xFFFFF868) // (PIOC) Pull-up Status Register
#define AT91C_PIOC_ABSR (AT91_CAST(AT91_REG *) 	0xFFFFF878) // (PIOC) AB Select Status Register
#define AT91C_PIOC_IFSR (AT91_CAST(AT91_REG *) 	0xFFFFF828) // (PIOC) Input Filter Status Register
#define AT91C_PIOC_OER  (AT91_CAST(AT91_REG *) 	0xFFFFF810) // (PIOC) Output Enable Register
#define AT91C_PIOC_IMR  (AT91_CAST(AT91_REG *) 	0xFFFFF848) // (PIOC) Interrupt Mask Register
#define AT91C_PIOC_ASR  (AT91_CAST(AT91_REG *) 	0xFFFFF870) // (PIOC) Select A Register
#define AT91C_PIOC_MDDR (AT91_CAST(AT91_REG *) 	0xFFFFF854) // (PIOC) Multi-driver Disable Register
#define AT91C_PIOC_OWSR (AT91_CAST(AT91_REG *) 	0xFFFFF8A8) // (PIOC) Output Write Status Register
#define AT91C_PIOC_PER  (AT91_CAST(AT91_REG *) 	0xFFFFF800) // (PIOC) PIO Enable Register
#define AT91C_PIOC_IDR  (AT91_CAST(AT91_REG *) 	0xFFFFF844) // (PIOC) Interrupt Disable Register
#define AT91C_PIOC_MDER (AT91_CAST(AT91_REG *) 	0xFFFFF850) // (PIOC) Multi-driver Enable Register
#define AT91C_PIOC_PDSR (AT91_CAST(AT91_REG *) 	0xFFFFF83C) // (PIOC) Pin Data Status Register
#define AT91C_PIOC_MDSR (AT91_CAST(AT91_REG *) 	0xFFFFF858) // (PIOC) Multi-driver Status Register
#define AT91C_PIOC_OWER (AT91_CAST(AT91_REG *) 	0xFFFFF8A0) // (PIOC) Output Write Enable Register
#define AT91C_PIOC_BSR  (AT91_CAST(AT91_REG *) 	0xFFFFF874) // (PIOC) Select B Register
#define AT91C_PIOC_PPUDR (AT91_CAST(AT91_REG *) 	0xFFFFF860) // (PIOC) Pull-up Disable Register
#define AT91C_PIOC_IFDR (AT91_CAST(AT91_REG *) 	0xFFFFF824) // (PIOC) Input Filter Disable Register
#define AT91C_PIOC_IER  (AT91_CAST(AT91_REG *) 	0xFFFFF840) // (PIOC) Interrupt Enable Register
#define AT91C_PIOC_OSR  (AT91_CAST(AT91_REG *) 	0xFFFFF818) // (PIOC) Output Status Register
#define AT91C_PIOC_ODSR (AT91_CAST(AT91_REG *) 	0xFFFFF838) // (PIOC) Output Data Status Register
#define AT91C_PIOC_ISR  (AT91_CAST(AT91_REG *) 	0xFFFFF84C) // (PIOC) Interrupt Status Register
#define AT91C_PIOC_IFER (AT91_CAST(AT91_REG *) 	0xFFFFF820) // (PIOC) Input Filter Enable Register
// ========== Register definition for EFC peripheral ========== 
#define AT91C_EFC_FVR   (AT91_CAST(AT91_REG *) 	0xFFFFFA10) // (EFC) EFC Flash Version Register
#define AT91C_EFC_FCR   (AT91_CAST(AT91_REG *) 	0xFFFFFA04) // (EFC) EFC Flash Command Register
#define AT91C_EFC_FMR   (AT91_CAST(AT91_REG *) 	0xFFFFFA00) // (EFC) EFC Flash Mode Register
#define AT91C_EFC_FRR   (AT91_CAST(AT91_REG *) 	0xFFFFFA0C) // (EFC) EFC Flash Result Register
#define AT91C_EFC_FSR   (AT91_CAST(AT91_REG *) 	0xFFFFFA08) // (EFC) EFC Flash Status Register
// ========== Register definition for CKGR peripheral ========== 
#define AT91C_CKGR_MOR  (AT91_CAST(AT91_REG *) 	0xFFFFFC20) // (CKGR) Main Oscillator Register
#define AT91C_CKGR_PLLBR (AT91_CAST(AT91_REG *) 	0xFFFFFC2C) // (CKGR) PLL B Register
#define AT91C_CKGR_MCFR (AT91_CAST(AT91_REG *) 	0xFFFFFC24) // (CKGR) Main Clock  Frequency Register
#define AT91C_CKGR_PLLAR (AT91_CAST(AT91_REG *) 	0xFFFFFC28) // (CKGR) PLL A Register
// ========== Register definition for PMC peripheral ========== 
#define AT91C_PMC_PCER  (AT91_CAST(AT91_REG *) 	0xFFFFFC10) // (PMC) Peripheral Clock Enable Register
#define AT91C_PMC_PCKR  (AT91_CAST(AT91_REG *) 	0xFFFFFC40) // (PMC) Programmable Clock Register
#define AT91C_PMC_MCKR  (AT91_CAST(AT91_REG *) 	0xFFFFFC30) // (PMC) Master Clock Register
#define AT91C_PMC_PLLAR (AT91_CAST(AT91_REG *) 	0xFFFFFC28) // (PMC) PLL A Register
#define AT91C_PMC_PCDR  (AT91_CAST(AT91_REG *) 	0xFFFFFC14) // (PMC) Peripheral Clock Disable Register
#define AT91C_PMC_SCSR  (AT91_CAST(AT91_REG *) 	0xFFFFFC08) // (PMC) System Clock Status Register
#define AT91C_PMC_MCFR  (AT91_CAST(AT91_REG *) 	0xFFFFFC24) // (PMC) Main Clock  Frequency Register
#define AT91C_PMC_IMR   (AT91_CAST(AT91_REG *) 	0xFFFFFC6C) // (PMC) Interrupt Mask Register
#define AT91C_PMC_IER   (AT91_CAST(AT91_REG *) 	0xFFFFFC60) // (PMC) Interrupt Enable Register
#define AT91C_PMC_MOR   (AT91_CAST(AT91_REG *) 	0xFFFFFC20) // (PMC) Main Oscillator Register
#define AT91C_PMC_IDR   (AT91_CAST(AT91_REG *) 	0xFFFFFC64) // (PMC) Interrupt Disable Register
#define AT91C_PMC_PLLBR (AT91_CAST(AT91_REG *) 	0xFFFFFC2C) // (PMC) PLL B Register
#define AT91C_PMC_SCDR  (AT91_CAST(AT91_REG *) 	0xFFFFFC04) // (PMC) System Clock Disable Register
#define AT91C_PMC_PCSR  (AT91_CAST(AT91_REG *) 	0xFFFFFC18) // (PMC) Peripheral Clock Status Register
#define AT91C_PMC_SCER  (AT91_CAST(AT91_REG *) 	0xFFFFFC00) // (PMC) System Clock Enable Register
#define AT91C_PMC_SR    (AT91_CAST(AT91_REG *) 	0xFFFFFC68) // (PMC) Status Register
// ========== Register definition for RSTC peripheral ========== 
#define AT91C_RSTC_RCR  (AT91_CAST(AT91_REG *) 	0xFFFFFD00) // (RSTC) Reset Control Register
#define AT91C_RSTC_RMR  (AT91_CAST(AT91_REG *) 	0xFFFFFD08) // (RSTC) Reset Mode Register
#define AT91C_RSTC_RSR  (AT91_CAST(AT91_REG *) 	0xFFFFFD04) // (RSTC) Reset Status Register
// ========== Register definition for SHDWC peripheral ========== 
#define AT91C_SHDWC_SHSR (AT91_CAST(AT91_REG *) 	0xFFFFFD18) // (SHDWC) Shut Down Status Register
#define AT91C_SHDWC_SHMR (AT91_CAST(AT91_REG *) 	0xFFFFFD14) // (SHDWC) Shut Down Mode Register
#define AT91C_SHDWC_SHCR (AT91_CAST(AT91_REG *) 	0xFFFFFD10) // (SHDWC) Shut Down Control Register
// ========== Register definition for RTTC peripheral ========== 
#define AT91C_RTTC_RTSR (AT91_CAST(AT91_REG *) 	0xFFFFFD2C) // (RTTC) Real-time Status Register
#define AT91C_RTTC_RTMR (AT91_CAST(AT91_REG *) 	0xFFFFFD20) // (RTTC) Real-time Mode Register
#define AT91C_RTTC_RTVR (AT91_CAST(AT91_REG *) 	0xFFFFFD28) // (RTTC) Real-time Value Register
#define AT91C_RTTC_RTAR (AT91_CAST(AT91_REG *) 	0xFFFFFD24) // (RTTC) Real-time Alarm Register
// ========== Register definition for PITC peripheral ========== 
#define AT91C_PITC_PIVR (AT91_CAST(AT91_REG *) 	0xFFFFFD38) // (PITC) Period Interval Value Register
#define AT91C_PITC_PISR (AT91_CAST(AT91_REG *) 	0xFFFFFD34) // (PITC) Period Interval Status Register
#define AT91C_PITC_PIIR (AT91_CAST(AT91_REG *) 	0xFFFFFD3C) // (PITC) Period Interval Image Register
#define AT91C_PITC_PIMR (AT91_CAST(AT91_REG *) 	0xFFFFFD30) // (PITC) Period Interval Mode Register
// ========== Register definition for WDTC peripheral ========== 
#define AT91C_WDTC_WDCR (AT91_CAST(AT91_REG *) 	0xFFFFFD40) // (WDTC) Watchdog Control Register
#define AT91C_WDTC_WDSR (AT91_CAST(AT91_REG *) 	0xFFFFFD48) // (WDTC) Watchdog Status Register
#define AT91C_WDTC_WDMR (AT91_CAST(AT91_REG *) 	0xFFFFFD44) // (WDTC) Watchdog Mode Register
// ========== Register definition for TC0 peripheral ========== 
#define AT91C_TC0_SR    (AT91_CAST(AT91_REG *) 	0xFFFA0020) // (TC0) Status Register
#define AT91C_TC0_RC    (AT91_CAST(AT91_REG *) 	0xFFFA001C) // (TC0) Register C
#define AT91C_TC0_RB    (AT91_CAST(AT91_REG *) 	0xFFFA0018) // (TC0) Register B
#define AT91C_TC0_CCR   (AT91_CAST(AT91_REG *) 	0xFFFA0000) // (TC0) Channel Control Register
#define AT91C_TC0_CMR   (AT91_CAST(AT91_REG *) 	0xFFFA0004) // (TC0) Channel Mode Register (Capture Mode / Waveform Mode)
#define AT91C_TC0_IER   (AT91_CAST(AT91_REG *) 	0xFFFA0024) // (TC0) Interrupt Enable Register
#define AT91C_TC0_RA    (AT91_CAST(AT91_REG *) 	0xFFFA0014) // (TC0) Register A
#define AT91C_TC0_IDR   (AT91_CAST(AT91_REG *) 	0xFFFA0028) // (TC0) Interrupt Disable Register
#define AT91C_TC0_CV    (AT91_CAST(AT91_REG *) 	0xFFFA0010) // (TC0) Counter Value
#define AT91C_TC0_IMR   (AT91_CAST(AT91_REG *) 	0xFFFA002C) // (TC0) Interrupt Mask Register
// ========== Register definition for TC1 peripheral ========== 
#define AT91C_TC1_RB    (AT91_CAST(AT91_REG *) 	0xFFFA0058) // (TC1) Register B
#define AT91C_TC1_CCR   (AT91_CAST(AT91_REG *) 	0xFFFA0040) // (TC1) Channel Control Register
#define AT91C_TC1_IER   (AT91_CAST(AT91_REG *) 	0xFFFA0064) // (TC1) Interrupt Enable Register
#define AT91C_TC1_IDR   (AT91_CAST(AT91_REG *) 	0xFFFA0068) // (TC1) Interrupt Disable Register
#define AT91C_TC1_SR    (AT91_CAST(AT91_REG *) 	0xFFFA0060) // (TC1) Status Register
#define AT91C_TC1_CMR   (AT91_CAST(AT91_REG *) 	0xFFFA0044) // (TC1) Channel Mode Register (Capture Mode / Waveform Mode)
#define AT91C_TC1_RA    (AT91_CAST(AT91_REG *) 	0xFFFA0054) // (TC1) Register A
#define AT91C_TC1_RC    (AT91_CAST(AT91_REG *) 	0xFFFA005C) // (TC1) Register C
#define AT91C_TC1_IMR   (AT91_CAST(AT91_REG *) 	0xFFFA006C) // (TC1) Interrupt Mask Register
#define AT91C_TC1_CV    (AT91_CAST(AT91_REG *) 	0xFFFA0050) // (TC1) Counter Value
// ========== Register definition for TC2 peripheral ========== 
#define AT91C_TC2_CMR   (AT91_CAST(AT91_REG *) 	0xFFFA0084) // (TC2) Channel Mode Register (Capture Mode / Waveform Mode)
#define AT91C_TC2_CCR   (AT91_CAST(AT91_REG *) 	0xFFFA0080) // (TC2) Channel Control Register
#define AT91C_TC2_CV    (AT91_CAST(AT91_REG *) 	0xFFFA0090) // (TC2) Counter Value
#define AT91C_TC2_RA    (AT91_CAST(AT91_REG *) 	0xFFFA0094) // (TC2) Register A
#define AT91C_TC2_RB    (AT91_CAST(AT91_REG *) 	0xFFFA0098) // (TC2) Register B
#define AT91C_TC2_IDR   (AT91_CAST(AT91_REG *) 	0xFFFA00A8) // (TC2) Interrupt Disable Register
#define AT91C_TC2_IMR   (AT91_CAST(AT91_REG *) 	0xFFFA00AC) // (TC2) Interrupt Mask Register
#define AT91C_TC2_RC    (AT91_CAST(AT91_REG *) 	0xFFFA009C) // (TC2) Register C
#define AT91C_TC2_IER   (AT91_CAST(AT91_REG *) 	0xFFFA00A4) // (TC2) Interrupt Enable Register
#define AT91C_TC2_SR    (AT91_CAST(AT91_REG *) 	0xFFFA00A0) // (TC2) Status Register
// ========== Register definition for TC3 peripheral ========== 
#define AT91C_TC3_IER   (AT91_CAST(AT91_REG *) 	0xFFFDC024) // (TC3) Interrupt Enable Register
#define AT91C_TC3_RB    (AT91_CAST(AT91_REG *) 	0xFFFDC018) // (TC3) Register B
#define AT91C_TC3_CMR   (AT91_CAST(AT91_REG *) 	0xFFFDC004) // (TC3) Channel Mode Register (Capture Mode / Waveform Mode)
#define AT91C_TC3_RC    (AT91_CAST(AT91_REG *) 	0xFFFDC01C) // (TC3) Register C
#define AT91C_TC3_CCR   (AT91_CAST(AT91_REG *) 	0xFFFDC000) // (TC3) Channel Control Register
#define AT91C_TC3_SR    (AT91_CAST(AT91_REG *) 	0xFFFDC020) // (TC3) Status Register
#define AT91C_TC3_CV    (AT91_CAST(AT91_REG *) 	0xFFFDC010) // (TC3) Counter Value
#define AT91C_TC3_RA    (AT91_CAST(AT91_REG *) 	0xFFFDC014) // (TC3) Register A
#define AT91C_TC3_IDR   (AT91_CAST(AT91_REG *) 	0xFFFDC028) // (TC3) Interrupt Disable Register
#define AT91C_TC3_IMR   (AT91_CAST(AT91_REG *) 	0xFFFDC02C) // (TC3) Interrupt Mask Register
// ========== Register definition for TC4 peripheral ========== 
#define AT91C_TC4_CMR   (AT91_CAST(AT91_REG *) 	0xFFFDC044) // (TC4) Channel Mode Register (Capture Mode / Waveform Mode)
#define AT91C_TC4_RC    (AT91_CAST(AT91_REG *) 	0xFFFDC05C) // (TC4) Register C
#define AT91C_TC4_SR    (AT91_CAST(AT91_REG *) 	0xFFFDC060) // (TC4) Status Register
#define AT91C_TC4_RB    (AT91_CAST(AT91_REG *) 	0xFFFDC058) // (TC4) Register B
#define AT91C_TC4_IER   (AT91_CAST(AT91_REG *) 	0xFFFDC064) // (TC4) Interrupt Enable Register
#define AT91C_TC4_CV    (AT91_CAST(AT91_REG *) 	0xFFFDC050) // (TC4) Counter Value
#define AT91C_TC4_RA    (AT91_CAST(AT91_REG *) 	0xFFFDC054) // (TC4) Register A
#define AT91C_TC4_IDR   (AT91_CAST(AT91_REG *) 	0xFFFDC068) // (TC4) Interrupt Disable Register
#define AT91C_TC4_IMR   (AT91_CAST(AT91_REG *) 	0xFFFDC06C) // (TC4) Interrupt Mask Register
#define AT91C_TC4_CCR   (AT91_CAST(AT91_REG *) 	0xFFFDC040) // (TC4) Channel Control Register
// ========== Register definition for TC5 peripheral ========== 
#define AT91C_TC5_RB    (AT91_CAST(AT91_REG *) 	0xFFFDC098) // (TC5) Register B
#define AT91C_TC5_RA    (AT91_CAST(AT91_REG *) 	0xFFFDC094) // (TC5) Register A
#define AT91C_TC5_CV    (AT91_CAST(AT91_REG *) 	0xFFFDC090) // (TC5) Counter Value
#define AT91C_TC5_CCR   (AT91_CAST(AT91_REG *) 	0xFFFDC080) // (TC5) Channel Control Register
#define AT91C_TC5_SR    (AT91_CAST(AT91_REG *) 	0xFFFDC0A0) // (TC5) Status Register
#define AT91C_TC5_IER   (AT91_CAST(AT91_REG *) 	0xFFFDC0A4) // (TC5) Interrupt Enable Register
#define AT91C_TC5_IDR   (AT91_CAST(AT91_REG *) 	0xFFFDC0A8) // (TC5) Interrupt Disable Register
#define AT91C_TC5_RC    (AT91_CAST(AT91_REG *) 	0xFFFDC09C) // (TC5) Register C
#define AT91C_TC5_IMR   (AT91_CAST(AT91_REG *) 	0xFFFDC0AC) // (TC5) Interrupt Mask Register
#define AT91C_TC5_CMR   (AT91_CAST(AT91_REG *) 	0xFFFDC084) // (TC5) Channel Mode Register (Capture Mode / Waveform Mode)
// ========== Register definition for TCB0 peripheral ========== 
#define AT91C_TCB0_BMR  (AT91_CAST(AT91_REG *) 	0xFFFA00C4) // (TCB0) TC Block Mode Register
#define AT91C_TCB0_BCR  (AT91_CAST(AT91_REG *) 	0xFFFA00C0) // (TCB0) TC Block Control Register
// ========== Register definition for TCB1 peripheral ========== 
#define AT91C_TCB1_BCR  (AT91_CAST(AT91_REG *) 	0xFFFDC0C0) // (TCB1) TC Block Control Register
#define AT91C_TCB1_BMR  (AT91_CAST(AT91_REG *) 	0xFFFDC0C4) // (TCB1) TC Block Mode Register
// ========== Register definition for PDC_MCI peripheral ========== 
#define AT91C_MCI_RNCR  (AT91_CAST(AT91_REG *) 	0xFFFA8114) // (PDC_MCI) Receive Next Counter Register
#define AT91C_MCI_TCR   (AT91_CAST(AT91_REG *) 	0xFFFA810C) // (PDC_MCI) Transmit Counter Register
#define AT91C_MCI_RCR   (AT91_CAST(AT91_REG *) 	0xFFFA8104) // (PDC_MCI) Receive Counter Register
#define AT91C_MCI_TNPR  (AT91_CAST(AT91_REG *) 	0xFFFA8118) // (PDC_MCI) Transmit Next Pointer Register
#define AT91C_MCI_RNPR  (AT91_CAST(AT91_REG *) 	0xFFFA8110) // (PDC_MCI) Receive Next Pointer Register
#define AT91C_MCI_RPR   (AT91_CAST(AT91_REG *) 	0xFFFA8100) // (PDC_MCI) Receive Pointer Register
#define AT91C_MCI_TNCR  (AT91_CAST(AT91_REG *) 	0xFFFA811C) // (PDC_MCI) Transmit Next Counter Register
#define AT91C_MCI_TPR   (AT91_CAST(AT91_REG *) 	0xFFFA8108) // (PDC_MCI) Transmit Pointer Register
#define AT91C_MCI_PTSR  (AT91_CAST(AT91_REG *) 	0xFFFA8124) // (PDC_MCI) PDC Transfer Status Register
#define AT91C_MCI_PTCR  (AT91_CAST(AT91_REG *) 	0xFFFA8120) // (PDC_MCI) PDC Transfer Control Register
// ========== Register definition for MCI peripheral ========== 
#define AT91C_MCI_RDR   (AT91_CAST(AT91_REG *) 	0xFFFA8030) // (MCI) MCI Receive Data Register
#define AT91C_MCI_CMDR  (AT91_CAST(AT91_REG *) 	0xFFFA8014) // (MCI) MCI Command Register
#define AT91C_MCI_VR    (AT91_CAST(AT91_REG *) 	0xFFFA80FC) // (MCI) MCI Version Register
#define AT91C_MCI_IDR   (AT91_CAST(AT91_REG *) 	0xFFFA8048) // (MCI) MCI Interrupt Disable Register
#define AT91C_MCI_DTOR  (AT91_CAST(AT91_REG *) 	0xFFFA8008) // (MCI) MCI Data Timeout Register
#define AT91C_MCI_TDR   (AT91_CAST(AT91_REG *) 	0xFFFA8034) // (MCI) MCI Transmit Data Register
#define AT91C_MCI_IER   (AT91_CAST(AT91_REG *) 	0xFFFA8044) // (MCI) MCI Interrupt Enable Register
#define AT91C_MCI_BLKR  (AT91_CAST(AT91_REG *) 	0xFFFA8018) // (MCI) MCI Block Register
#define AT91C_MCI_MR    (AT91_CAST(AT91_REG *) 	0xFFFA8004) // (MCI) MCI Mode Register
#define AT91C_MCI_IMR   (AT91_CAST(AT91_REG *) 	0xFFFA804C) // (MCI) MCI Interrupt Mask Register
#define AT91C_MCI_CR    (AT91_CAST(AT91_REG *) 	0xFFFA8000) // (MCI) MCI Control Register
#define AT91C_MCI_ARGR  (AT91_CAST(AT91_REG *) 	0xFFFA8010) // (MCI) MCI Argument Register
#define AT91C_MCI_SDCR  (AT91_CAST(AT91_REG *) 	0xFFFA800C) // (MCI) MCI SD Card Register
#define AT91C_MCI_SR    (AT91_CAST(AT91_REG *) 	0xFFFA8040) // (MCI) MCI Status Register
#define AT91C_MCI_RSPR  (AT91_CAST(AT91_REG *) 	0xFFFA8020) // (MCI) MCI Response Register
// ========== Register definition for PDC_TWI0 peripheral ========== 
#define AT91C_TWI0_PTSR (AT91_CAST(AT91_REG *) 	0xFFFAC124) // (PDC_TWI0) PDC Transfer Status Register
#define AT91C_TWI0_RPR  (AT91_CAST(AT91_REG *) 	0xFFFAC100) // (PDC_TWI0) Receive Pointer Register
#define AT91C_TWI0_RNCR (AT91_CAST(AT91_REG *) 	0xFFFAC114) // (PDC_TWI0) Receive Next Counter Register
#define AT91C_TWI0_RCR  (AT91_CAST(AT91_REG *) 	0xFFFAC104) // (PDC_TWI0) Receive Counter Register
#define AT91C_TWI0_PTCR (AT91_CAST(AT91_REG *) 	0xFFFAC120) // (PDC_TWI0) PDC Transfer Control Register
#define AT91C_TWI0_TPR  (AT91_CAST(AT91_REG *) 	0xFFFAC108) // (PDC_TWI0) Transmit Pointer Register
#define AT91C_TWI0_RNPR (AT91_CAST(AT91_REG *) 	0xFFFAC110) // (PDC_TWI0) Receive Next Pointer Register
#define AT91C_TWI0_TNPR (AT91_CAST(AT91_REG *) 	0xFFFAC118) // (PDC_TWI0) Transmit Next Pointer Register
#define AT91C_TWI0_TCR  (AT91_CAST(AT91_REG *) 	0xFFFAC10C) // (PDC_TWI0) Transmit Counter Register
#define AT91C_TWI0_TNCR (AT91_CAST(AT91_REG *) 	0xFFFAC11C) // (PDC_TWI0) Transmit Next Counter Register
// ========== Register definition for TWI0 peripheral ========== 
#define AT91C_TWI0_THR  (AT91_CAST(AT91_REG *) 	0xFFFAC034) // (TWI0) Transmit Holding Register
#define AT91C_TWI0_IDR  (AT91_CAST(AT91_REG *) 	0xFFFAC028) // (TWI0) Interrupt Disable Register
#define AT91C_TWI0_SMR  (AT91_CAST(AT91_REG *) 	0xFFFAC008) // (TWI0) Slave Mode Register
#define AT91C_TWI0_CWGR (AT91_CAST(AT91_REG *) 	0xFFFAC010) // (TWI0) Clock Waveform Generator Register
#define AT91C_TWI0_IADR (AT91_CAST(AT91_REG *) 	0xFFFAC00C) // (TWI0) Internal Address Register
#define AT91C_TWI0_RHR  (AT91_CAST(AT91_REG *) 	0xFFFAC030) // (TWI0) Receive Holding Register
#define AT91C_TWI0_IER  (AT91_CAST(AT91_REG *) 	0xFFFAC024) // (TWI0) Interrupt Enable Register
#define AT91C_TWI0_MMR  (AT91_CAST(AT91_REG *) 	0xFFFAC004) // (TWI0) Master Mode Register
#define AT91C_TWI0_SR   (AT91_CAST(AT91_REG *) 	0xFFFAC020) // (TWI0) Status Register
#define AT91C_TWI0_IMR  (AT91_CAST(AT91_REG *) 	0xFFFAC02C) // (TWI0) Interrupt Mask Register
#define AT91C_TWI0_CR   (AT91_CAST(AT91_REG *) 	0xFFFAC000) // (TWI0) Control Register
// ========== Register definition for PDC_TWI1 peripheral ========== 
#define AT91C_TWI1_PTSR (AT91_CAST(AT91_REG *) 	0xFFFD8124) // (PDC_TWI1) PDC Transfer Status Register
#define AT91C_TWI1_PTCR (AT91_CAST(AT91_REG *) 	0xFFFD8120) // (PDC_TWI1) PDC Transfer Control Register
#define AT91C_TWI1_TNPR (AT91_CAST(AT91_REG *) 	0xFFFD8118) // (PDC_TWI1) Transmit Next Pointer Register
#define AT91C_TWI1_TNCR (AT91_CAST(AT91_REG *) 	0xFFFD811C) // (PDC_TWI1) Transmit Next Counter Register
#define AT91C_TWI1_RNPR (AT91_CAST(AT91_REG *) 	0xFFFD8110) // (PDC_TWI1) Receive Next Pointer Register
#define AT91C_TWI1_RNCR (AT91_CAST(AT91_REG *) 	0xFFFD8114) // (PDC_TWI1) Receive Next Counter Register
#define AT91C_TWI1_RPR  (AT91_CAST(AT91_REG *) 	0xFFFD8100) // (PDC_TWI1) Receive Pointer Register
#define AT91C_TWI1_TCR  (AT91_CAST(AT91_REG *) 	0xFFFD810C) // (PDC_TWI1) Transmit Counter Register
#define AT91C_TWI1_TPR  (AT91_CAST(AT91_REG *) 	0xFFFD8108) // (PDC_TWI1) Transmit Pointer Register
#define AT91C_TWI1_RCR  (AT91_CAST(AT91_REG *) 	0xFFFD8104) // (PDC_TWI1) Receive Counter Register
// ========== Register definition for TWI1 peripheral ========== 
#define AT91C_TWI1_RHR  (AT91_CAST(AT91_REG *) 	0xFFFD8030) // (TWI1) Receive Holding Register
#define AT91C_TWI1_IER  (AT91_CAST(AT91_REG *) 	0xFFFD8024) // (TWI1) Interrupt Enable Register
#define AT91C_TWI1_CWGR (AT91_CAST(AT91_REG *) 	0xFFFD8010) // (TWI1) Clock Waveform Generator Register
#define AT91C_TWI1_MMR  (AT91_CAST(AT91_REG *) 	0xFFFD8004) // (TWI1) Master Mode Register
#define AT91C_TWI1_IADR (AT91_CAST(AT91_REG *) 	0xFFFD800C) // (TWI1) Internal Address Register
#define AT91C_TWI1_THR  (AT91_CAST(AT91_REG *) 	0xFFFD8034) // (TWI1) Transmit Holding Register
#define AT91C_TWI1_IMR  (AT91_CAST(AT91_REG *) 	0xFFFD802C) // (TWI1) Interrupt Mask Register
#define AT91C_TWI1_SR   (AT91_CAST(AT91_REG *) 	0xFFFD8020) // (TWI1) Status Register
#define AT91C_TWI1_IDR  (AT91_CAST(AT91_REG *) 	0xFFFD8028) // (TWI1) Interrupt Disable Register
#define AT91C_TWI1_CR   (AT91_CAST(AT91_REG *) 	0xFFFD8000) // (TWI1) Control Register
#define AT91C_TWI1_SMR  (AT91_CAST(AT91_REG *) 	0xFFFD8008) // (TWI1) Slave Mode Register
// ========== Register definition for PDC_US0 peripheral ========== 
#define AT91C_US0_TCR   (AT91_CAST(AT91_REG *) 	0xFFFB010C) // (PDC_US0) Transmit Counter Register
#define AT91C_US0_PTCR  (AT91_CAST(AT91_REG *) 	0xFFFB0120) // (PDC_US0) PDC Transfer Control Register
#define AT91C_US0_RNCR  (AT91_CAST(AT91_REG *) 	0xFFFB0114) // (PDC_US0) Receive Next Counter Register
#define AT91C_US0_PTSR  (AT91_CAST(AT91_REG *) 	0xFFFB0124) // (PDC_US0) PDC Transfer Status Register
#define AT91C_US0_TNCR  (AT91_CAST(AT91_REG *) 	0xFFFB011C) // (PDC_US0) Transmit Next Counter Register
#define AT91C_US0_RNPR  (AT91_CAST(AT91_REG *) 	0xFFFB0110) // (PDC_US0) Receive Next Pointer Register
#define AT91C_US0_RCR   (AT91_CAST(AT91_REG *) 	0xFFFB0104) // (PDC_US0) Receive Counter Register
#define AT91C_US0_TPR   (AT91_CAST(AT91_REG *) 	0xFFFB0108) // (PDC_US0) Transmit Pointer Register
#define AT91C_US0_TNPR  (AT91_CAST(AT91_REG *) 	0xFFFB0118) // (PDC_US0) Transmit Next Pointer Register
#define AT91C_US0_RPR   (AT91_CAST(AT91_REG *) 	0xFFFB0100) // (PDC_US0) Receive Pointer Register
// ========== Register definition for US0 peripheral ========== 
#define AT91C_US0_RHR   (AT91_CAST(AT91_REG *) 	0xFFFB0018) // (US0) Receiver Holding Register
#define AT91C_US0_NER   (AT91_CAST(AT91_REG *) 	0xFFFB0044) // (US0) Nb Errors Register
#define AT91C_US0_IER   (AT91_CAST(AT91_REG *) 	0xFFFB0008) // (US0) Interrupt Enable Register
#define AT91C_US0_CR    (AT91_CAST(AT91_REG *) 	0xFFFB0000) // (US0) Control Register
#define AT91C_US0_THR   (AT91_CAST(AT91_REG *) 	0xFFFB001C) // (US0) Transmitter Holding Register
#define AT91C_US0_CSR   (AT91_CAST(AT91_REG *) 	0xFFFB0014) // (US0) Channel Status Register
#define AT91C_US0_BRGR  (AT91_CAST(AT91_REG *) 	0xFFFB0020) // (US0) Baud Rate Generator Register
#define AT91C_US0_RTOR  (AT91_CAST(AT91_REG *) 	0xFFFB0024) // (US0) Receiver Time-out Register
#define AT91C_US0_TTGR  (AT91_CAST(AT91_REG *) 	0xFFFB0028) // (US0) Transmitter Time-guard Register
#define AT91C_US0_IDR   (AT91_CAST(AT91_REG *) 	0xFFFB000C) // (US0) Interrupt Disable Register
#define AT91C_US0_MR    (AT91_CAST(AT91_REG *) 	0xFFFB0004) // (US0) Mode Register
#define AT91C_US0_IF    (AT91_CAST(AT91_REG *) 	0xFFFB004C) // (US0) IRDA_FILTER Register
#define AT91C_US0_FIDI  (AT91_CAST(AT91_REG *) 	0xFFFB0040) // (US0) FI_DI_Ratio Register
#define AT91C_US0_IMR   (AT91_CAST(AT91_REG *) 	0xFFFB0010) // (US0) Interrupt Mask Register
// ========== Register definition for PDC_US1 peripheral ========== 
#define AT91C_US1_PTCR  (AT91_CAST(AT91_REG *) 	0xFFFB4120) // (PDC_US1) PDC Transfer Control Register
#define AT91C_US1_RCR   (AT91_CAST(AT91_REG *) 	0xFFFB4104) // (PDC_US1) Receive Counter Register
#define AT91C_US1_RPR   (AT91_CAST(AT91_REG *) 	0xFFFB4100) // (PDC_US1) Receive Pointer Register
#define AT91C_US1_PTSR  (AT91_CAST(AT91_REG *) 	0xFFFB4124) // (PDC_US1) PDC Transfer Status Register
#define AT91C_US1_TPR   (AT91_CAST(AT91_REG *) 	0xFFFB4108) // (PDC_US1) Transmit Pointer Register
#define AT91C_US1_TCR   (AT91_CAST(AT91_REG *) 	0xFFFB410C) // (PDC_US1) Transmit Counter Register
#define AT91C_US1_RNPR  (AT91_CAST(AT91_REG *) 	0xFFFB4110) // (PDC_US1) Receive Next Pointer Register
#define AT91C_US1_TNCR  (AT91_CAST(AT91_REG *) 	0xFFFB411C) // (PDC_US1) Transmit Next Counter Register
#define AT91C_US1_RNCR  (AT91_CAST(AT91_REG *) 	0xFFFB4114) // (PDC_US1) Receive Next Counter Register
#define AT91C_US1_TNPR  (AT91_CAST(AT91_REG *) 	0xFFFB4118) // (PDC_US1) Transmit Next Pointer Register
// ========== Register definition for US1 peripheral ========== 
#define AT91C_US1_THR   (AT91_CAST(AT91_REG *) 	0xFFFB401C) // (US1) Transmitter Holding Register
#define AT91C_US1_TTGR  (AT91_CAST(AT91_REG *) 	0xFFFB4028) // (US1) Transmitter Time-guard Register
#define AT91C_US1_BRGR  (AT91_CAST(AT91_REG *) 	0xFFFB4020) // (US1) Baud Rate Generator Register
#define AT91C_US1_IDR   (AT91_CAST(AT91_REG *) 	0xFFFB400C) // (US1) Interrupt Disable Register
#define AT91C_US1_MR    (AT91_CAST(AT91_REG *) 	0xFFFB4004) // (US1) Mode Register
#define AT91C_US1_RTOR  (AT91_CAST(AT91_REG *) 	0xFFFB4024) // (US1) Receiver Time-out Register
#define AT91C_US1_CR    (AT91_CAST(AT91_REG *) 	0xFFFB4000) // (US1) Control Register
#define AT91C_US1_IMR   (AT91_CAST(AT91_REG *) 	0xFFFB4010) // (US1) Interrupt Mask Register
#define AT91C_US1_FIDI  (AT91_CAST(AT91_REG *) 	0xFFFB4040) // (US1) FI_DI_Ratio Register
#define AT91C_US1_RHR   (AT91_CAST(AT91_REG *) 	0xFFFB4018) // (US1) Receiver Holding Register
#define AT91C_US1_IER   (AT91_CAST(AT91_REG *) 	0xFFFB4008) // (US1) Interrupt Enable Register
#define AT91C_US1_CSR   (AT91_CAST(AT91_REG *) 	0xFFFB4014) // (US1) Channel Status Register
#define AT91C_US1_IF    (AT91_CAST(AT91_REG *) 	0xFFFB404C) // (US1) IRDA_FILTER Register
#define AT91C_US1_NER   (AT91_CAST(AT91_REG *) 	0xFFFB4044) // (US1) Nb Errors Register
// ========== Register definition for PDC_US2 peripheral ========== 
#define AT91C_US2_TNCR  (AT91_CAST(AT91_REG *) 	0xFFFB811C) // (PDC_US2) Transmit Next Counter Register
#define AT91C_US2_RNCR  (AT91_CAST(AT91_REG *) 	0xFFFB8114) // (PDC_US2) Receive Next Counter Register
#define AT91C_US2_TNPR  (AT91_CAST(AT91_REG *) 	0xFFFB8118) // (PDC_US2) Transmit Next Pointer Register
#define AT91C_US2_PTCR  (AT91_CAST(AT91_REG *) 	0xFFFB8120) // (PDC_US2) PDC Transfer Control Register
#define AT91C_US2_TCR   (AT91_CAST(AT91_REG *) 	0xFFFB810C) // (PDC_US2) Transmit Counter Register
#define AT91C_US2_RPR   (AT91_CAST(AT91_REG *) 	0xFFFB8100) // (PDC_US2) Receive Pointer Register
#define AT91C_US2_TPR   (AT91_CAST(AT91_REG *) 	0xFFFB8108) // (PDC_US2) Transmit Pointer Register
#define AT91C_US2_RCR   (AT91_CAST(AT91_REG *) 	0xFFFB8104) // (PDC_US2) Receive Counter Register
#define AT91C_US2_PTSR  (AT91_CAST(AT91_REG *) 	0xFFFB8124) // (PDC_US2) PDC Transfer Status Register
#define AT91C_US2_RNPR  (AT91_CAST(AT91_REG *) 	0xFFFB8110) // (PDC_US2) Receive Next Pointer Register
// ========== Register definition for US2 peripheral ========== 
#define AT91C_US2_RTOR  (AT91_CAST(AT91_REG *) 	0xFFFB8024) // (US2) Receiver Time-out Register
#define AT91C_US2_CSR   (AT91_CAST(AT91_REG *) 	0xFFFB8014) // (US2) Channel Status Register
#define AT91C_US2_CR    (AT91_CAST(AT91_REG *) 	0xFFFB8000) // (US2) Control Register
#define AT91C_US2_BRGR  (AT91_CAST(AT91_REG *) 	0xFFFB8020) // (US2) Baud Rate Generator Register
#define AT91C_US2_NER   (AT91_CAST(AT91_REG *) 	0xFFFB8044) // (US2) Nb Errors Register
#define AT91C_US2_FIDI  (AT91_CAST(AT91_REG *) 	0xFFFB8040) // (US2) FI_DI_Ratio Register
#define AT91C_US2_TTGR  (AT91_CAST(AT91_REG *) 	0xFFFB8028) // (US2) Transmitter Time-guard Register
#define AT91C_US2_RHR   (AT91_CAST(AT91_REG *) 	0xFFFB8018) // (US2) Receiver Holding Register
#define AT91C_US2_IDR   (AT91_CAST(AT91_REG *) 	0xFFFB800C) // (US2) Interrupt Disable Register
#define AT91C_US2_THR   (AT91_CAST(AT91_REG *) 	0xFFFB801C) // (US2) Transmitter Holding Register
#define AT91C_US2_MR    (AT91_CAST(AT91_REG *) 	0xFFFB8004) // (US2) Mode Register
#define AT91C_US2_IMR   (AT91_CAST(AT91_REG *) 	0xFFFB8010) // (US2) Interrupt Mask Register
#define AT91C_US2_IF    (AT91_CAST(AT91_REG *) 	0xFFFB804C) // (US2) IRDA_FILTER Register
#define AT91C_US2_IER   (AT91_CAST(AT91_REG *) 	0xFFFB8008) // (US2) Interrupt Enable Register
// ========== Register definition for PDC_US3 peripheral ========== 
#define AT91C_US3_RNPR  (AT91_CAST(AT91_REG *) 	0xFFFD0110) // (PDC_US3) Receive Next Pointer Register
#define AT91C_US3_RNCR  (AT91_CAST(AT91_REG *) 	0xFFFD0114) // (PDC_US3) Receive Next Counter Register
#define AT91C_US3_PTSR  (AT91_CAST(AT91_REG *) 	0xFFFD0124) // (PDC_US3) PDC Transfer Status Register
#define AT91C_US3_PTCR  (AT91_CAST(AT91_REG *) 	0xFFFD0120) // (PDC_US3) PDC Transfer Control Register
#define AT91C_US3_TCR   (AT91_CAST(AT91_REG *) 	0xFFFD010C) // (PDC_US3) Transmit Counter Register
#define AT91C_US3_TNPR  (AT91_CAST(AT91_REG *) 	0xFFFD0118) // (PDC_US3) Transmit Next Pointer Register
#define AT91C_US3_RCR   (AT91_CAST(AT91_REG *) 	0xFFFD0104) // (PDC_US3) Receive Counter Register
#define AT91C_US3_TPR   (AT91_CAST(AT91_REG *) 	0xFFFD0108) // (PDC_US3) Transmit Pointer Register
#define AT91C_US3_TNCR  (AT91_CAST(AT91_REG *) 	0xFFFD011C) // (PDC_US3) Transmit Next Counter Register
#define AT91C_US3_RPR   (AT91_CAST(AT91_REG *) 	0xFFFD0100) // (PDC_US3) Receive Pointer Register
// ========== Register definition for US3 peripheral ========== 
#define AT91C_US3_NER   (AT91_CAST(AT91_REG *) 	0xFFFD0044) // (US3) Nb Errors Register
#define AT91C_US3_RTOR  (AT91_CAST(AT91_REG *) 	0xFFFD0024) // (US3) Receiver Time-out Register
#define AT91C_US3_IDR   (AT91_CAST(AT91_REG *) 	0xFFFD000C) // (US3) Interrupt Disable Register
#define AT91C_US3_MR    (AT91_CAST(AT91_REG *) 	0xFFFD0004) // (US3) Mode Register
#define AT91C_US3_FIDI  (AT91_CAST(AT91_REG *) 	0xFFFD0040) // (US3) FI_DI_Ratio Register
#define AT91C_US3_BRGR  (AT91_CAST(AT91_REG *) 	0xFFFD0020) // (US3) Baud Rate Generator Register
#define AT91C_US3_THR   (AT91_CAST(AT91_REG *) 	0xFFFD001C) // (US3) Transmitter Holding Register
#define AT91C_US3_CR    (AT91_CAST(AT91_REG *) 	0xFFFD0000) // (US3) Control Register
#define AT91C_US3_IF    (AT91_CAST(AT91_REG *) 	0xFFFD004C) // (US3) IRDA_FILTER Register
#define AT91C_US3_IER   (AT91_CAST(AT91_REG *) 	0xFFFD0008) // (US3) Interrupt Enable Register
#define AT91C_US3_TTGR  (AT91_CAST(AT91_REG *) 	0xFFFD0028) // (US3) Transmitter Time-guard Register
#define AT91C_US3_RHR   (AT91_CAST(AT91_REG *) 	0xFFFD0018) // (US3) Receiver Holding Register
#define AT91C_US3_IMR   (AT91_CAST(AT91_REG *) 	0xFFFD0010) // (US3) Interrupt Mask Register
#define AT91C_US3_CSR   (AT91_CAST(AT91_REG *) 	0xFFFD0014) // (US3) Channel Status Register
// ========== Register definition for PDC_US4 peripheral ========== 
#define AT91C_US4_TNCR  (AT91_CAST(AT91_REG *) 	0xFFFD411C) // (PDC_US4) Transmit Next Counter Register
#define AT91C_US4_RPR   (AT91_CAST(AT91_REG *) 	0xFFFD4100) // (PDC_US4) Receive Pointer Register
#define AT91C_US4_RNCR  (AT91_CAST(AT91_REG *) 	0xFFFD4114) // (PDC_US4) Receive Next Counter Register
#define AT91C_US4_TPR   (AT91_CAST(AT91_REG *) 	0xFFFD4108) // (PDC_US4) Transmit Pointer Register
#define AT91C_US4_PTCR  (AT91_CAST(AT91_REG *) 	0xFFFD4120) // (PDC_US4) PDC Transfer Control Register
#define AT91C_US4_TCR   (AT91_CAST(AT91_REG *) 	0xFFFD410C) // (PDC_US4) Transmit Counter Register
#define AT91C_US4_RCR   (AT91_CAST(AT91_REG *) 	0xFFFD4104) // (PDC_US4) Receive Counter Register
#define AT91C_US4_RNPR  (AT91_CAST(AT91_REG *) 	0xFFFD4110) // (PDC_US4) Receive Next Pointer Register
#define AT91C_US4_TNPR  (AT91_CAST(AT91_REG *) 	0xFFFD4118) // (PDC_US4) Transmit Next Pointer Register
#define AT91C_US4_PTSR  (AT91_CAST(AT91_REG *) 	0xFFFD4124) // (PDC_US4) PDC Transfer Status Register
// ========== Register definition for US4 peripheral ========== 
#define AT91C_US4_BRGR  (AT91_CAST(AT91_REG *) 	0xFFFD4020) // (US4) Baud Rate Generator Register
#define AT91C_US4_THR   (AT91_CAST(AT91_REG *) 	0xFFFD401C) // (US4) Transmitter Holding Register
#define AT91C_US4_RTOR  (AT91_CAST(AT91_REG *) 	0xFFFD4024) // (US4) Receiver Time-out Register
#define AT91C_US4_IMR   (AT91_CAST(AT91_REG *) 	0xFFFD4010) // (US4) Interrupt Mask Register
#define AT91C_US4_NER   (AT91_CAST(AT91_REG *) 	0xFFFD4044) // (US4) Nb Errors Register
#define AT91C_US4_TTGR  (AT91_CAST(AT91_REG *) 	0xFFFD4028) // (US4) Transmitter Time-guard Register
#define AT91C_US4_FIDI  (AT91_CAST(AT91_REG *) 	0xFFFD4040) // (US4) FI_DI_Ratio Register
#define AT91C_US4_MR    (AT91_CAST(AT91_REG *) 	0xFFFD4004) // (US4) Mode Register
#define AT91C_US4_IER   (AT91_CAST(AT91_REG *) 	0xFFFD4008) // (US4) Interrupt Enable Register
#define AT91C_US4_RHR   (AT91_CAST(AT91_REG *) 	0xFFFD4018) // (US4) Receiver Holding Register
#define AT91C_US4_CR    (AT91_CAST(AT91_REG *) 	0xFFFD4000) // (US4) Control Register
#define AT91C_US4_IF    (AT91_CAST(AT91_REG *) 	0xFFFD404C) // (US4) IRDA_FILTER Register
#define AT91C_US4_IDR   (AT91_CAST(AT91_REG *) 	0xFFFD400C) // (US4) Interrupt Disable Register
#define AT91C_US4_CSR   (AT91_CAST(AT91_REG *) 	0xFFFD4014) // (US4) Channel Status Register
// ========== Register definition for PDC_SSC0 peripheral ========== 
#define AT91C_SSC0_TNPR (AT91_CAST(AT91_REG *) 	0xFFFBC118) // (PDC_SSC0) Transmit Next Pointer Register
#define AT91C_SSC0_TCR  (AT91_CAST(AT91_REG *) 	0xFFFBC10C) // (PDC_SSC0) Transmit Counter Register
#define AT91C_SSC0_RNCR (AT91_CAST(AT91_REG *) 	0xFFFBC114) // (PDC_SSC0) Receive Next Counter Register
#define AT91C_SSC0_RPR  (AT91_CAST(AT91_REG *) 	0xFFFBC100) // (PDC_SSC0) Receive Pointer Register
#define AT91C_SSC0_TPR  (AT91_CAST(AT91_REG *) 	0xFFFBC108) // (PDC_SSC0) Transmit Pointer Register
#define AT91C_SSC0_RCR  (AT91_CAST(AT91_REG *) 	0xFFFBC104) // (PDC_SSC0) Receive Counter Register
#define AT91C_SSC0_RNPR (AT91_CAST(AT91_REG *) 	0xFFFBC110) // (PDC_SSC0) Receive Next Pointer Register
#define AT91C_SSC0_PTCR (AT91_CAST(AT91_REG *) 	0xFFFBC120) // (PDC_SSC0) PDC Transfer Control Register
#define AT91C_SSC0_TNCR (AT91_CAST(AT91_REG *) 	0xFFFBC11C) // (PDC_SSC0) Transmit Next Counter Register
#define AT91C_SSC0_PTSR (AT91_CAST(AT91_REG *) 	0xFFFBC124) // (PDC_SSC0) PDC Transfer Status Register
// ========== Register definition for SSC0 peripheral ========== 
#define AT91C_SSC0_IMR  (AT91_CAST(AT91_REG *) 	0xFFFBC04C) // (SSC0) Interrupt Mask Register
#define AT91C_SSC0_RFMR (AT91_CAST(AT91_REG *) 	0xFFFBC014) // (SSC0) Receive Frame Mode Register
#define AT91C_SSC0_CR   (AT91_CAST(AT91_REG *) 	0xFFFBC000) // (SSC0) Control Register
#define AT91C_SSC0_TFMR (AT91_CAST(AT91_REG *) 	0xFFFBC01C) // (SSC0) Transmit Frame Mode Register
#define AT91C_SSC0_CMR  (AT91_CAST(AT91_REG *) 	0xFFFBC004) // (SSC0) Clock Mode Register
#define AT91C_SSC0_IER  (AT91_CAST(AT91_REG *) 	0xFFFBC044) // (SSC0) Interrupt Enable Register
#define AT91C_SSC0_RHR  (AT91_CAST(AT91_REG *) 	0xFFFBC020) // (SSC0) Receive Holding Register
#define AT91C_SSC0_RCMR (AT91_CAST(AT91_REG *) 	0xFFFBC010) // (SSC0) Receive Clock ModeRegister
#define AT91C_SSC0_SR   (AT91_CAST(AT91_REG *) 	0xFFFBC040) // (SSC0) Status Register
#define AT91C_SSC0_RSHR (AT91_CAST(AT91_REG *) 	0xFFFBC030) // (SSC0) Receive Sync Holding Register
#define AT91C_SSC0_THR  (AT91_CAST(AT91_REG *) 	0xFFFBC024) // (SSC0) Transmit Holding Register
#define AT91C_SSC0_TCMR (AT91_CAST(AT91_REG *) 	0xFFFBC018) // (SSC0) Transmit Clock Mode Register
#define AT91C_SSC0_IDR  (AT91_CAST(AT91_REG *) 	0xFFFBC048) // (SSC0) Interrupt Disable Register
#define AT91C_SSC0_TSHR (AT91_CAST(AT91_REG *) 	0xFFFBC034) // (SSC0) Transmit Sync Holding Register
// ========== Register definition for PDC_SPI0 peripheral ========== 
#define AT91C_SPI0_PTCR (AT91_CAST(AT91_REG *) 	0xFFFC8120) // (PDC_SPI0) PDC Transfer Control Register
#define AT91C_SPI0_TCR  (AT91_CAST(AT91_REG *) 	0xFFFC810C) // (PDC_SPI0) Transmit Counter Register
#define AT91C_SPI0_RPR  (AT91_CAST(AT91_REG *) 	0xFFFC8100) // (PDC_SPI0) Receive Pointer Register
#define AT91C_SPI0_TPR  (AT91_CAST(AT91_REG *) 	0xFFFC8108) // (PDC_SPI0) Transmit Pointer Register
#define AT91C_SPI0_PTSR (AT91_CAST(AT91_REG *) 	0xFFFC8124) // (PDC_SPI0) PDC Transfer Status Register
#define AT91C_SPI0_RNCR (AT91_CAST(AT91_REG *) 	0xFFFC8114) // (PDC_SPI0) Receive Next Counter Register
#define AT91C_SPI0_TNPR (AT91_CAST(AT91_REG *) 	0xFFFC8118) // (PDC_SPI0) Transmit Next Pointer Register
#define AT91C_SPI0_RCR  (AT91_CAST(AT91_REG *) 	0xFFFC8104) // (PDC_SPI0) Receive Counter Register
#define AT91C_SPI0_RNPR (AT91_CAST(AT91_REG *) 	0xFFFC8110) // (PDC_SPI0) Receive Next Pointer Register
#define AT91C_SPI0_TNCR (AT91_CAST(AT91_REG *) 	0xFFFC811C) // (PDC_SPI0) Transmit Next Counter Register
// ========== Register definition for SPI0 peripheral ========== 
#define AT91C_SPI0_IDR  (AT91_CAST(AT91_REG *) 	0xFFFC8018) // (SPI0) Interrupt Disable Register
#define AT91C_SPI0_TDR  (AT91_CAST(AT91_REG *) 	0xFFFC800C) // (SPI0) Transmit Data Register
#define AT91C_SPI0_SR   (AT91_CAST(AT91_REG *) 	0xFFFC8010) // (SPI0) Status Register
#define AT91C_SPI0_CR   (AT91_CAST(AT91_REG *) 	0xFFFC8000) // (SPI0) Control Register
#define AT91C_SPI0_CSR  (AT91_CAST(AT91_REG *) 	0xFFFC8030) // (SPI0) Chip Select Register
#define AT91C_SPI0_RDR  (AT91_CAST(AT91_REG *) 	0xFFFC8008) // (SPI0) Receive Data Register
#define AT91C_SPI0_MR   (AT91_CAST(AT91_REG *) 	0xFFFC8004) // (SPI0) Mode Register
#define AT91C_SPI0_IER  (AT91_CAST(AT91_REG *) 	0xFFFC8014) // (SPI0) Interrupt Enable Register
#define AT91C_SPI0_IMR  (AT91_CAST(AT91_REG *) 	0xFFFC801C) // (SPI0) Interrupt Mask Register
// ========== Register definition for PDC_SPI1 peripheral ========== 
#define AT91C_SPI1_PTCR (AT91_CAST(AT91_REG *) 	0xFFFCC120) // (PDC_SPI1) PDC Transfer Control Register
#define AT91C_SPI1_RNPR (AT91_CAST(AT91_REG *) 	0xFFFCC110) // (PDC_SPI1) Receive Next Pointer Register
#define AT91C_SPI1_RCR  (AT91_CAST(AT91_REG *) 	0xFFFCC104) // (PDC_SPI1) Receive Counter Register
#define AT91C_SPI1_TPR  (AT91_CAST(AT91_REG *) 	0xFFFCC108) // (PDC_SPI1) Transmit Pointer Register
#define AT91C_SPI1_PTSR (AT91_CAST(AT91_REG *) 	0xFFFCC124) // (PDC_SPI1) PDC Transfer Status Register
#define AT91C_SPI1_TNCR (AT91_CAST(AT91_REG *) 	0xFFFCC11C) // (PDC_SPI1) Transmit Next Counter Register
#define AT91C_SPI1_RPR  (AT91_CAST(AT91_REG *) 	0xFFFCC100) // (PDC_SPI1) Receive Pointer Register
#define AT91C_SPI1_TCR  (AT91_CAST(AT91_REG *) 	0xFFFCC10C) // (PDC_SPI1) Transmit Counter Register
#define AT91C_SPI1_RNCR (AT91_CAST(AT91_REG *) 	0xFFFCC114) // (PDC_SPI1) Receive Next Counter Register
#define AT91C_SPI1_TNPR (AT91_CAST(AT91_REG *) 	0xFFFCC118) // (PDC_SPI1) Transmit Next Pointer Register
// ========== Register definition for SPI1 peripheral ========== 
#define AT91C_SPI1_IER  (AT91_CAST(AT91_REG *) 	0xFFFCC014) // (SPI1) Interrupt Enable Register
#define AT91C_SPI1_RDR  (AT91_CAST(AT91_REG *) 	0xFFFCC008) // (SPI1) Receive Data Register
#define AT91C_SPI1_SR   (AT91_CAST(AT91_REG *) 	0xFFFCC010) // (SPI1) Status Register
#define AT91C_SPI1_IMR  (AT91_CAST(AT91_REG *) 	0xFFFCC01C) // (SPI1) Interrupt Mask Register
#define AT91C_SPI1_TDR  (AT91_CAST(AT91_REG *) 	0xFFFCC00C) // (SPI1) Transmit Data Register
#define AT91C_SPI1_IDR  (AT91_CAST(AT91_REG *) 	0xFFFCC018) // (SPI1) Interrupt Disable Register
#define AT91C_SPI1_CSR  (AT91_CAST(AT91_REG *) 	0xFFFCC030) // (SPI1) Chip Select Register
#define AT91C_SPI1_CR   (AT91_CAST(AT91_REG *) 	0xFFFCC000) // (SPI1) Control Register
#define AT91C_SPI1_MR   (AT91_CAST(AT91_REG *) 	0xFFFCC004) // (SPI1) Mode Register
// ========== Register definition for PDC_ADC peripheral ========== 
#define AT91C_ADC_PTCR  (AT91_CAST(AT91_REG *) 	0xFFFE0120) // (PDC_ADC) PDC Transfer Control Register
#define AT91C_ADC_TPR   (AT91_CAST(AT91_REG *) 	0xFFFE0108) // (PDC_ADC) Transmit Pointer Register
#define AT91C_ADC_TCR   (AT91_CAST(AT91_REG *) 	0xFFFE010C) // (PDC_ADC) Transmit Counter Register
#define AT91C_ADC_RCR   (AT91_CAST(AT91_REG *) 	0xFFFE0104) // (PDC_ADC) Receive Counter Register
#define AT91C_ADC_PTSR  (AT91_CAST(AT91_REG *) 	0xFFFE0124) // (PDC_ADC) PDC Transfer Status Register
#define AT91C_ADC_RNPR  (AT91_CAST(AT91_REG *) 	0xFFFE0110) // (PDC_ADC) Receive Next Pointer Register
#define AT91C_ADC_RPR   (AT91_CAST(AT91_REG *) 	0xFFFE0100) // (PDC_ADC) Receive Pointer Register
#define AT91C_ADC_TNCR  (AT91_CAST(AT91_REG *) 	0xFFFE011C) // (PDC_ADC) Transmit Next Counter Register
#define AT91C_ADC_RNCR  (AT91_CAST(AT91_REG *) 	0xFFFE0114) // (PDC_ADC) Receive Next Counter Register
#define AT91C_ADC_TNPR  (AT91_CAST(AT91_REG *) 	0xFFFE0118) // (PDC_ADC) Transmit Next Pointer Register
// ========== Register definition for ADC peripheral ========== 
#define AT91C_ADC_CHDR  (AT91_CAST(AT91_REG *) 	0xFFFE0014) // (ADC) ADC Channel Disable Register
#define AT91C_ADC_CDR3  (AT91_CAST(AT91_REG *) 	0xFFFE003C) // (ADC) ADC Channel Data Register 3
#define AT91C_ADC_CR    (AT91_CAST(AT91_REG *) 	0xFFFE0000) // (ADC) ADC Control Register
#define AT91C_ADC_IMR   (AT91_CAST(AT91_REG *) 	0xFFFE002C) // (ADC) ADC Interrupt Mask Register
#define AT91C_ADC_CDR2  (AT91_CAST(AT91_REG *) 	0xFFFE0038) // (ADC) ADC Channel Data Register 2
#define AT91C_ADC_SR    (AT91_CAST(AT91_REG *) 	0xFFFE001C) // (ADC) ADC Status Register
#define AT91C_ADC_IER   (AT91_CAST(AT91_REG *) 	0xFFFE0024) // (ADC) ADC Interrupt Enable Register
#define AT91C_ADC_CDR7  (AT91_CAST(AT91_REG *) 	0xFFFE004C) // (ADC) ADC Channel Data Register 7
#define AT91C_ADC_CDR0  (AT91_CAST(AT91_REG *) 	0xFFFE0030) // (ADC) ADC Channel Data Register 0
#define AT91C_ADC_CDR5  (AT91_CAST(AT91_REG *) 	0xFFFE0044) // (ADC) ADC Channel Data Register 5
#define AT91C_ADC_CDR4  (AT91_CAST(AT91_REG *) 	0xFFFE0040) // (ADC) ADC Channel Data Register 4
#define AT91C_ADC_CHER  (AT91_CAST(AT91_REG *) 	0xFFFE0010) // (ADC) ADC Channel Enable Register
#define AT91C_ADC_CHSR  (AT91_CAST(AT91_REG *) 	0xFFFE0018) // (ADC) ADC Channel Status Register
#define AT91C_ADC_MR    (AT91_CAST(AT91_REG *) 	0xFFFE0004) // (ADC) ADC Mode Register
#define AT91C_ADC_CDR6  (AT91_CAST(AT91_REG *) 	0xFFFE0048) // (ADC) ADC Channel Data Register 6
#define AT91C_ADC_LCDR  (AT91_CAST(AT91_REG *) 	0xFFFE0020) // (ADC) ADC Last Converted Data Register
#define AT91C_ADC_CDR1  (AT91_CAST(AT91_REG *) 	0xFFFE0034) // (ADC) ADC Channel Data Register 1
#define AT91C_ADC_IDR   (AT91_CAST(AT91_REG *) 	0xFFFE0028) // (ADC) ADC Interrupt Disable Register
// ========== Register definition for EMACB peripheral ========== 
#define AT91C_EMACB_USRIO (AT91_CAST(AT91_REG *) 	0xFFFC40C0) // (EMACB) USER Input/Output Register
#define AT91C_EMACB_RSE (AT91_CAST(AT91_REG *) 	0xFFFC4074) // (EMACB) Receive Symbol Errors Register
#define AT91C_EMACB_SCF (AT91_CAST(AT91_REG *) 	0xFFFC4044) // (EMACB) Single Collision Frame Register
#define AT91C_EMACB_STE (AT91_CAST(AT91_REG *) 	0xFFFC4084) // (EMACB) SQE Test Error Register
#define AT91C_EMACB_SA1H (AT91_CAST(AT91_REG *) 	0xFFFC409C) // (EMACB) Specific Address 1 Top, Last 2 bytes
#define AT91C_EMACB_ROV (AT91_CAST(AT91_REG *) 	0xFFFC4070) // (EMACB) Receive Overrun Errors Register
#define AT91C_EMACB_TBQP (AT91_CAST(AT91_REG *) 	0xFFFC401C) // (EMACB) Transmit Buffer Queue Pointer
#define AT91C_EMACB_IMR (AT91_CAST(AT91_REG *) 	0xFFFC4030) // (EMACB) Interrupt Mask Register
#define AT91C_EMACB_IER (AT91_CAST(AT91_REG *) 	0xFFFC4028) // (EMACB) Interrupt Enable Register
#define AT91C_EMACB_REV (AT91_CAST(AT91_REG *) 	0xFFFC40FC) // (EMACB) Revision Register
#define AT91C_EMACB_SA3L (AT91_CAST(AT91_REG *) 	0xFFFC40A8) // (EMACB) Specific Address 3 Bottom, First 4 bytes
#define AT91C_EMACB_ELE (AT91_CAST(AT91_REG *) 	0xFFFC4078) // (EMACB) Excessive Length Errors Register
#define AT91C_EMACB_HRT (AT91_CAST(AT91_REG *) 	0xFFFC4094) // (EMACB) Hash Address Top[63:32]
#define AT91C_EMACB_SA2L (AT91_CAST(AT91_REG *) 	0xFFFC40A0) // (EMACB) Specific Address 2 Bottom, First 4 bytes
#define AT91C_EMACB_RRE (AT91_CAST(AT91_REG *) 	0xFFFC406C) // (EMACB) Receive Ressource Error Register
#define AT91C_EMACB_FRO (AT91_CAST(AT91_REG *) 	0xFFFC404C) // (EMACB) Frames Received OK Register
#define AT91C_EMACB_TPQ (AT91_CAST(AT91_REG *) 	0xFFFC40BC) // (EMACB) Transmit Pause Quantum Register
#define AT91C_EMACB_ISR (AT91_CAST(AT91_REG *) 	0xFFFC4024) // (EMACB) Interrupt Status Register
#define AT91C_EMACB_TSR (AT91_CAST(AT91_REG *) 	0xFFFC4014) // (EMACB) Transmit Status Register
#define AT91C_EMACB_RLE (AT91_CAST(AT91_REG *) 	0xFFFC4088) // (EMACB) Receive Length Field Mismatch Register
#define AT91C_EMACB_USF (AT91_CAST(AT91_REG *) 	0xFFFC4080) // (EMACB) Undersize Frames Register
#define AT91C_EMACB_WOL (AT91_CAST(AT91_REG *) 	0xFFFC40C4) // (EMACB) Wake On LAN Register
#define AT91C_EMACB_TPF (AT91_CAST(AT91_REG *) 	0xFFFC408C) // (EMACB) Transmitted Pause Frames Register
#define AT91C_EMACB_PTR (AT91_CAST(AT91_REG *) 	0xFFFC4038) // (EMACB) Pause Time Register
#define AT91C_EMACB_TUND (AT91_CAST(AT91_REG *) 	0xFFFC4064) // (EMACB) Transmit Underrun Error Register
#define AT91C_EMACB_MAN (AT91_CAST(AT91_REG *) 	0xFFFC4034) // (EMACB) PHY Maintenance Register
#define AT91C_EMACB_RJA (AT91_CAST(AT91_REG *) 	0xFFFC407C) // (EMACB) Receive Jabbers Register
#define AT91C_EMACB_SA4L (AT91_CAST(AT91_REG *) 	0xFFFC40B0) // (EMACB) Specific Address 4 Bottom, First 4 bytes
#define AT91C_EMACB_CSE (AT91_CAST(AT91_REG *) 	0xFFFC4068) // (EMACB) Carrier Sense Error Register
#define AT91C_EMACB_HRB (AT91_CAST(AT91_REG *) 	0xFFFC4090) // (EMACB) Hash Address Bottom[31:0]
#define AT91C_EMACB_ALE (AT91_CAST(AT91_REG *) 	0xFFFC4054) // (EMACB) Alignment Error Register
#define AT91C_EMACB_SA1L (AT91_CAST(AT91_REG *) 	0xFFFC4098) // (EMACB) Specific Address 1 Bottom, First 4 bytes
#define AT91C_EMACB_NCR (AT91_CAST(AT91_REG *) 	0xFFFC4000) // (EMACB) Network Control Register
#define AT91C_EMACB_FTO (AT91_CAST(AT91_REG *) 	0xFFFC4040) // (EMACB) Frames Transmitted OK Register
#define AT91C_EMACB_ECOL (AT91_CAST(AT91_REG *) 	0xFFFC4060) // (EMACB) Excessive Collision Register
#define AT91C_EMACB_DTF (AT91_CAST(AT91_REG *) 	0xFFFC4058) // (EMACB) Deferred Transmission Frame Register
#define AT91C_EMACB_SA4H (AT91_CAST(AT91_REG *) 	0xFFFC40B4) // (EMACB) Specific Address 4 Top, Last 2 bytes
#define AT91C_EMACB_FCSE (AT91_CAST(AT91_REG *) 	0xFFFC4050) // (EMACB) Frame Check Sequence Error Register
#define AT91C_EMACB_TID (AT91_CAST(AT91_REG *) 	0xFFFC40B8) // (EMACB) Type ID Checking Register
#define AT91C_EMACB_PFR (AT91_CAST(AT91_REG *) 	0xFFFC403C) // (EMACB) Pause Frames received Register
#define AT91C_EMACB_IDR (AT91_CAST(AT91_REG *) 	0xFFFC402C) // (EMACB) Interrupt Disable Register
#define AT91C_EMACB_SA3H (AT91_CAST(AT91_REG *) 	0xFFFC40AC) // (EMACB) Specific Address 3 Top, Last 2 bytes
#define AT91C_EMACB_NSR (AT91_CAST(AT91_REG *) 	0xFFFC4008) // (EMACB) Network Status Register
#define AT91C_EMACB_MCF (AT91_CAST(AT91_REG *) 	0xFFFC4048) // (EMACB) Multiple Collision Frame Register
#define AT91C_EMACB_RBQP (AT91_CAST(AT91_REG *) 	0xFFFC4018) // (EMACB) Receive Buffer Queue Pointer
#define AT91C_EMACB_RSR (AT91_CAST(AT91_REG *) 	0xFFFC4020) // (EMACB) Receive Status Register
#define AT91C_EMACB_SA2H (AT91_CAST(AT91_REG *) 	0xFFFC40A4) // (EMACB) Specific Address 2 Top, Last 2 bytes
#define AT91C_EMACB_NCFGR (AT91_CAST(AT91_REG *) 	0xFFFC4004) // (EMACB) Network Configuration Register
#define AT91C_EMACB_LCOL (AT91_CAST(AT91_REG *) 	0xFFFC405C) // (EMACB) Late Collision Register
// ========== Register definition for UDP peripheral ========== 
#define AT91C_UDP_GLBSTATE (AT91_CAST(AT91_REG *) 	0xFFFA4004) // (UDP) Global State Register
#define AT91C_UDP_FDR   (AT91_CAST(AT91_REG *) 	0xFFFA4050) // (UDP) Endpoint FIFO Data Register
#define AT91C_UDP_RSTEP (AT91_CAST(AT91_REG *) 	0xFFFA4028) // (UDP) Reset Endpoint Register
#define AT91C_UDP_FADDR (AT91_CAST(AT91_REG *) 	0xFFFA4008) // (UDP) Function Address Register
#define AT91C_UDP_NUM   (AT91_CAST(AT91_REG *) 	0xFFFA4000) // (UDP) Frame Number Register
#define AT91C_UDP_IDR   (AT91_CAST(AT91_REG *) 	0xFFFA4014) // (UDP) Interrupt Disable Register
#define AT91C_UDP_IMR   (AT91_CAST(AT91_REG *) 	0xFFFA4018) // (UDP) Interrupt Mask Register
#define AT91C_UDP_CSR   (AT91_CAST(AT91_REG *) 	0xFFFA4030) // (UDP) Endpoint Control and Status Register
#define AT91C_UDP_IER   (AT91_CAST(AT91_REG *) 	0xFFFA4010) // (UDP) Interrupt Enable Register
#define AT91C_UDP_ICR   (AT91_CAST(AT91_REG *) 	0xFFFA4020) // (UDP) Interrupt Clear Register
#define AT91C_UDP_TXVC  (AT91_CAST(AT91_REG *) 	0xFFFA4074) // (UDP) Transceiver Control Register
#define AT91C_UDP_ISR   (AT91_CAST(AT91_REG *) 	0xFFFA401C) // (UDP) Interrupt Status Register
// ========== Register definition for UHP peripheral ========== 
#define AT91C_UHP_HcInterruptStatus (AT91_CAST(AT91_REG *) 	0x0050000C) // (UHP) Interrupt Status Register
#define AT91C_UHP_HcCommandStatus (AT91_CAST(AT91_REG *) 	0x00500008) // (UHP) Command & status Register
#define AT91C_UHP_HcRhStatus (AT91_CAST(AT91_REG *) 	0x00500050) // (UHP) Root Hub Status register
#define AT91C_UHP_HcInterruptDisable (AT91_CAST(AT91_REG *) 	0x00500014) // (UHP) Interrupt Disable Register
#define AT91C_UHP_HcPeriodicStart (AT91_CAST(AT91_REG *) 	0x00500040) // (UHP) Periodic Start
#define AT91C_UHP_HcControlCurrentED (AT91_CAST(AT91_REG *) 	0x00500024) // (UHP) Endpoint Control and Status Register
#define AT91C_UHP_HcPeriodCurrentED (AT91_CAST(AT91_REG *) 	0x0050001C) // (UHP) Current Isochronous or Interrupt Endpoint Descriptor
#define AT91C_UHP_HcBulkHeadED (AT91_CAST(AT91_REG *) 	0x00500028) // (UHP) First endpoint register of the Bulk list
#define AT91C_UHP_HcRevision (AT91_CAST(AT91_REG *) 	0x00500000) // (UHP) Revision
#define AT91C_UHP_HcBulkCurrentED (AT91_CAST(AT91_REG *) 	0x0050002C) // (UHP) Current endpoint of the Bulk list
#define AT91C_UHP_HcRhDescriptorB (AT91_CAST(AT91_REG *) 	0x0050004C) // (UHP) Root Hub characteristics B
#define AT91C_UHP_HcControlHeadED (AT91_CAST(AT91_REG *) 	0x00500020) // (UHP) First Endpoint Descriptor of the Control list
#define AT91C_UHP_HcFmRemaining (AT91_CAST(AT91_REG *) 	0x00500038) // (UHP) Bit time remaining in the current Frame
#define AT91C_UHP_HcHCCA (AT91_CAST(AT91_REG *) 	0x00500018) // (UHP) Pointer to the Host Controller Communication Area
#define AT91C_UHP_HcLSThreshold (AT91_CAST(AT91_REG *) 	0x00500044) // (UHP) LS Threshold
#define AT91C_UHP_HcRhPortStatus (AT91_CAST(AT91_REG *) 	0x00500054) // (UHP) Root Hub Port Status Register
#define AT91C_UHP_HcInterruptEnable (AT91_CAST(AT91_REG *) 	0x00500010) // (UHP) Interrupt Enable Register
#define AT91C_UHP_HcFmNumber (AT91_CAST(AT91_REG *) 	0x0050003C) // (UHP) Frame number
#define AT91C_UHP_HcFmInterval (AT91_CAST(AT91_REG *) 	0x00500034) // (UHP) Bit time between 2 consecutive SOFs
#define AT91C_UHP_HcControl (AT91_CAST(AT91_REG *) 	0x00500004) // (UHP) Operating modes for the Host Controller
#define AT91C_UHP_HcBulkDoneHead (AT91_CAST(AT91_REG *) 	0x00500030) // (UHP) Last completed transfer descriptor
#define AT91C_UHP_HcRhDescriptorA (AT91_CAST(AT91_REG *) 	0x00500048) // (UHP) Root Hub characteristics A
// ========== Register definition for HECC peripheral ========== 
// ========== Register definition for HISI peripheral ========== 
#define AT91C_HISI_PSIZE (AT91_CAST(AT91_REG *) 	0xFFFC0020) // (HISI) Preview Size Register
#define AT91C_HISI_CR1  (AT91_CAST(AT91_REG *) 	0xFFFC0000) // (HISI) Control Register 1
#define AT91C_HISI_R2YSET1 (AT91_CAST(AT91_REG *) 	0xFFFC003C) // (HISI) Color Space Conversion Register
#define AT91C_HISI_CDBA (AT91_CAST(AT91_REG *) 	0xFFFC002C) // (HISI) Codec Dma Address Register
#define AT91C_HISI_IDR  (AT91_CAST(AT91_REG *) 	0xFFFC0010) // (HISI) Interrupt Disable Register
#define AT91C_HISI_R2YSET2 (AT91_CAST(AT91_REG *) 	0xFFFC0040) // (HISI) Color Space Conversion Register
#define AT91C_HISI_Y2RSET1 (AT91_CAST(AT91_REG *) 	0xFFFC0034) // (HISI) Color Space Conversion Register
#define AT91C_HISI_PFBD (AT91_CAST(AT91_REG *) 	0xFFFC0028) // (HISI) Preview Frame Buffer Address Register
#define AT91C_HISI_CR2  (AT91_CAST(AT91_REG *) 	0xFFFC0004) // (HISI) Control Register 2
#define AT91C_HISI_Y2RSET0 (AT91_CAST(AT91_REG *) 	0xFFFC0030) // (HISI) Color Space Conversion Register
#define AT91C_HISI_PDECF (AT91_CAST(AT91_REG *) 	0xFFFC0024) // (HISI) Preview Decimation Factor Register
#define AT91C_HISI_IMR  (AT91_CAST(AT91_REG *) 	0xFFFC0014) // (HISI) Interrupt Mask Register
#define AT91C_HISI_IER  (AT91_CAST(AT91_REG *) 	0xFFFC000C) // (HISI) Interrupt Enable Register
#define AT91C_HISI_R2YSET0 (AT91_CAST(AT91_REG *) 	0xFFFC0038) // (HISI) Color Space Conversion Register
#define AT91C_HISI_SR   (AT91_CAST(AT91_REG *) 	0xFFFC0008) // (HISI) Status Register

// *****************************************************************************
//               PIO DEFINITIONS FOR AT91SAM9XE512
// *****************************************************************************
#define AT91C_PIO_PA0        (1 <<  0) // Pin Controlled by PA0
#define AT91C_PA0_SPI0_MISO (AT91C_PIO_PA0) //  SPI 0 Master In Slave
#define AT91C_PA0_MCDB0    (AT91C_PIO_PA0) //  Multimedia Card B Data 0
#define AT91C_PIO_PA1        (1 <<  1) // Pin Controlled by PA1
#define AT91C_PA1_SPI0_MOSI (AT91C_PIO_PA1) //  SPI 0 Master Out Slave
#define AT91C_PA1_MCCDB    (AT91C_PIO_PA1) //  Multimedia Card B Command
#define AT91C_PIO_PA10       (1 << 10) // Pin Controlled by PA10
#define AT91C_PA10_MCDA2    (AT91C_PIO_PA10) //  Multimedia Card A Data 2
#define AT91C_PA10_ETX2_0   (AT91C_PIO_PA10) //  Ethernet MAC Transmit Data 2
#define AT91C_PIO_PA11       (1 << 11) // Pin Controlled by PA11
#define AT91C_PA11_MCDA3    (AT91C_PIO_PA11) //  Multimedia Card A Data 3
#define AT91C_PA11_ETX3_0   (AT91C_PIO_PA11) //  Ethernet MAC Transmit Data 3
#define AT91C_PIO_PA12       (1 << 12) // Pin Controlled by PA12
#define AT91C_PA12_ETX0     (AT91C_PIO_PA12) //  Ethernet MAC Transmit Data 0
#define AT91C_PIO_PA13       (1 << 13) // Pin Controlled by PA13
#define AT91C_PA13_ETX1     (AT91C_PIO_PA13) //  Ethernet MAC Transmit Data 1
#define AT91C_PIO_PA14       (1 << 14) // Pin Controlled by PA14
#define AT91C_PA14_ERX0     (AT91C_PIO_PA14) //  Ethernet MAC Receive Data 0
#define AT91C_PIO_PA15       (1 << 15) // Pin Controlled by PA15
#define AT91C_PA15_ERX1     (AT91C_PIO_PA15) //  Ethernet MAC Receive Data 1
#define AT91C_PIO_PA16       (1 << 16) // Pin Controlled by PA16
#define AT91C_PA16_ETXEN    (AT91C_PIO_PA16) //  Ethernet MAC Transmit Enable
#define AT91C_PIO_PA17       (1 << 17) // Pin Controlled by PA17
#define AT91C_PA17_ERXDV    (AT91C_PIO_PA17) //  Ethernet MAC Receive Data Valid
#define AT91C_PIO_PA18       (1 << 18) // Pin Controlled by PA18
#define AT91C_PA18_ERXER    (AT91C_PIO_PA18) //  Ethernet MAC Receive Error
#define AT91C_PIO_PA19       (1 << 19) // Pin Controlled by PA19
#define AT91C_PA19_ETXCK    (AT91C_PIO_PA19) //  Ethernet MAC Transmit Clock/Reference Clock
#define AT91C_PIO_PA2        (1 <<  2) // Pin Controlled by PA2
#define AT91C_PA2_SPI0_SPCK (AT91C_PIO_PA2) //  SPI 0 Serial Clock
#define AT91C_PIO_PA20       (1 << 20) // Pin Controlled by PA20
#define AT91C_PA20_EMDC     (AT91C_PIO_PA20) //  Ethernet MAC Management Data Clock
#define AT91C_PIO_PA21       (1 << 21) // Pin Controlled by PA21
#define AT91C_PA21_EMDIO    (AT91C_PIO_PA21) //  Ethernet MAC Management Data Input/Output
#define AT91C_PIO_PA22       (1 << 22) // Pin Controlled by PA22
#define AT91C_PA22_ADTRG    (AT91C_PIO_PA22) //  ADC Trigger
#define AT91C_PA22_ETXER    (AT91C_PIO_PA22) //  Ethernet MAC Transmikt Coding Error
#define AT91C_PIO_PA23       (1 << 23) // Pin Controlled by PA23
#define AT91C_PA23_TWD0     (AT91C_PIO_PA23) //  TWI Two-wire Serial Data 0
#define AT91C_PA23_ETX2_1   (AT91C_PIO_PA23) //  Ethernet MAC Transmit Data 2
#define AT91C_PIO_PA24       (1 << 24) // Pin Controlled by PA24
#define AT91C_PA24_TWCK0    (AT91C_PIO_PA24) //  TWI Two-wire Serial Clock 0
#define AT91C_PA24_ETX3_1   (AT91C_PIO_PA24) //  Ethernet MAC Transmit Data 3
#define AT91C_PIO_PA25       (1 << 25) // Pin Controlled by PA25
#define AT91C_PA25_TCLK0    (AT91C_PIO_PA25) //  Timer Counter 0 external clock input
#define AT91C_PA25_ERX2     (AT91C_PIO_PA25) //  Ethernet MAC Receive Data 2
#define AT91C_PIO_PA26       (1 << 26) // Pin Controlled by PA26
#define AT91C_PA26_TIOA0    (AT91C_PIO_PA26) //  Timer Counter 0 Multipurpose Timer I/O Pin A
#define AT91C_PA26_ERX3     (AT91C_PIO_PA26) //  Ethernet MAC Receive Data 3
#define AT91C_PIO_PA27       (1 << 27) // Pin Controlled by PA27
#define AT91C_PA27_TIOA1    (AT91C_PIO_PA27) //  Timer Counter 1 Multipurpose Timer I/O Pin A
#define AT91C_PA27_ERXCK    (AT91C_PIO_PA27) //  Ethernet MAC Receive Clock
#define AT91C_PIO_PA28       (1 << 28) // Pin Controlled by PA28
#define AT91C_PA28_TIOA2    (AT91C_PIO_PA28) //  Timer Counter 2 Multipurpose Timer I/O Pin A
#define AT91C_PA28_ECRS     (AT91C_PIO_PA28) //  Ethernet MAC Carrier Sense/Carrier Sense and Data Valid
#define AT91C_PIO_PA29       (1 << 29) // Pin Controlled by PA29
#define AT91C_PA29_SCK1     (AT91C_PIO_PA29) //  USART 1 Serial Clock
#define AT91C_PA29_ECOL     (AT91C_PIO_PA29) //  Ethernet MAC Collision Detected
#define AT91C_PIO_PA3        (1 <<  3) // Pin Controlled by PA3
#define AT91C_PA3_SPI0_NPCS0 (AT91C_PIO_PA3) //  SPI 0 Peripheral Chip Select 0
#define AT91C_PA3_MCDB3    (AT91C_PIO_PA3) //  Multimedia Card B Data 3
#define AT91C_PIO_PA30       (1 << 30) // Pin Controlled by PA30
#define AT91C_PA30_SCK2     (AT91C_PIO_PA30) //  USART 2 Serial Clock
#define AT91C_PA30_RXD4     (AT91C_PIO_PA30) //  USART 4 Receive Data
#define AT91C_PIO_PA31       (1 << 31) // Pin Controlled by PA31
#define AT91C_PA31_SCK0     (AT91C_PIO_PA31) //  USART 0 Serial Clock
#define AT91C_PA31_TXD4     (AT91C_PIO_PA31) //  USART 4 Transmit Data
#define AT91C_PIO_PA4        (1 <<  4) // Pin Controlled by PA4
#define AT91C_PA4_RTS2     (AT91C_PIO_PA4) //  USART 2 Ready To Send
#define AT91C_PA4_MCDB2    (AT91C_PIO_PA4) //  Multimedia Card B Data 2
#define AT91C_PIO_PA5        (1 <<  5) // Pin Controlled by PA5
#define AT91C_PA5_CTS2     (AT91C_PIO_PA5) //  USART 2 Clear To Send
#define AT91C_PA5_MCDB1    (AT91C_PIO_PA5) //  Multimedia Card B Data 1
#define AT91C_PIO_PA6        (1 <<  6) // Pin Controlled by PA6
#define AT91C_PA6_MCDA0    (AT91C_PIO_PA6) //  Multimedia Card A Data 0
#define AT91C_PIO_PA7        (1 <<  7) // Pin Controlled by PA7
#define AT91C_PA7_MCCDA    (AT91C_PIO_PA7) //  Multimedia Card A Command
#define AT91C_PIO_PA8        (1 <<  8) // Pin Controlled by PA8
#define AT91C_PA8_MCCK     (AT91C_PIO_PA8) //  Multimedia Card Clock
#define AT91C_PIO_PA9        (1 <<  9) // Pin Controlled by PA9
#define AT91C_PA9_MCDA1    (AT91C_PIO_PA9) //  Multimedia Card A Data 1
#define AT91C_PIO_PB0        (1 <<  0) // Pin Controlled by PB0
#define AT91C_PB0_SPI1_MISO (AT91C_PIO_PB0) //  SPI 1 Master In Slave
#define AT91C_PB0_TIOA3    (AT91C_PIO_PB0) //  Timer Counter 3 Multipurpose Timer I/O Pin A
#define AT91C_PIO_PB1        (1 <<  1) // Pin Controlled by PB1
#define AT91C_PB1_SPI1_MOSI (AT91C_PIO_PB1) //  SPI 1 Master Out Slave
#define AT91C_PB1_TIOB3    (AT91C_PIO_PB1) //  Timer Counter 3 Multipurpose Timer I/O Pin B
#define AT91C_PIO_PB10       (1 << 10) // Pin Controlled by PB10
#define AT91C_PB10_TXD3     (AT91C_PIO_PB10) //  USART 3 Transmit Data
#define AT91C_PB10_ISI_D8   (AT91C_PIO_PB10) //  Image Sensor Data 8
#define AT91C_PIO_PB11       (1 << 11) // Pin Controlled by PB11
#define AT91C_PB11_RXD3     (AT91C_PIO_PB11) //  USART 3 Receive Data
#define AT91C_PB11_ISI_D9   (AT91C_PIO_PB11) //  Image Sensor Data 9
#define AT91C_PIO_PB12       (1 << 12) // Pin Controlled by PB12
#define AT91C_PB12_TWD1     (AT91C_PIO_PB12) //  TWI Two-wire Serial Data 1
#define AT91C_PB12_ISI_D10  (AT91C_PIO_PB12) //  Image Sensor Data 10
#define AT91C_PIO_PB13       (1 << 13) // Pin Controlled by PB13
#define AT91C_PB13_TWCK1    (AT91C_PIO_PB13) //  TWI Two-wire Serial Clock 1
#define AT91C_PB13_ISI_D11  (AT91C_PIO_PB13) //  Image Sensor Data 11
#define AT91C_PIO_PB14       (1 << 14) // Pin Controlled by PB14
#define AT91C_PB14_DRXD     (AT91C_PIO_PB14) //  DBGU Debug Receive Data
#define AT91C_PIO_PB15       (1 << 15) // Pin Controlled by PB15
#define AT91C_PB15_DTXD     (AT91C_PIO_PB15) //  DBGU Debug Transmit Data
#define AT91C_PIO_PB16       (1 << 16) // Pin Controlled by PB16
#define AT91C_PB16_TK0      (AT91C_PIO_PB16) //  SSC0 Transmit Clock
#define AT91C_PB16_TCLK3    (AT91C_PIO_PB16) //  Timer Counter 3 external clock input
#define AT91C_PIO_PB17       (1 << 17) // Pin Controlled by PB17
#define AT91C_PB17_TF0      (AT91C_PIO_PB17) //  SSC0 Transmit Frame Sync
#define AT91C_PB17_TCLK4    (AT91C_PIO_PB17) //  Timer Counter 4 external clock input
#define AT91C_PIO_PB18       (1 << 18) // Pin Controlled by PB18
#define AT91C_PB18_TD0      (AT91C_PIO_PB18) //  SSC0 Transmit data
#define AT91C_PB18_TIOB4    (AT91C_PIO_PB18) //  Timer Counter 4 Multipurpose Timer I/O Pin B
#define AT91C_PIO_PB19       (1 << 19) // Pin Controlled by PB19
#define AT91C_PB19_RD0      (AT91C_PIO_PB19) //  SSC0 Receive Data
#define AT91C_PB19_TIOB5    (AT91C_PIO_PB19) //  Timer Counter 5 Multipurpose Timer I/O Pin B
#define AT91C_PIO_PB2        (1 <<  2) // Pin Controlled by PB2
#define AT91C_PB2_SPI1_SPCK (AT91C_PIO_PB2) //  SPI 1 Serial Clock
#define AT91C_PB2_TIOA4    (AT91C_PIO_PB2) //  Timer Counter 4 Multipurpose Timer I/O Pin A
#define AT91C_PIO_PB20       (1 << 20) // Pin Controlled by PB20
#define AT91C_PB20_RK0      (AT91C_PIO_PB20) //  SSC0 Receive Clock
#define AT91C_PB20_ISI_D0   (AT91C_PIO_PB20) //  Image Sensor Data 0
#define AT91C_PIO_PB21       (1 << 21) // Pin Controlled by PB21
#define AT91C_PB21_RF0      (AT91C_PIO_PB21) //  SSC0 Receive Frame Sync
#define AT91C_PB21_ISI_D1   (AT91C_PIO_PB21) //  Image Sensor Data 1
#define AT91C_PIO_PB22       (1 << 22) // Pin Controlled by PB22
#define AT91C_PB22_DSR0     (AT91C_PIO_PB22) //  USART 0 Data Set ready
#define AT91C_PB22_ISI_D2   (AT91C_PIO_PB22) //  Image Sensor Data 2
#define AT91C_PIO_PB23       (1 << 23) // Pin Controlled by PB23
#define AT91C_PB23_DCD0     (AT91C_PIO_PB23) //  USART 0 Data Carrier Detect
#define AT91C_PB23_ISI_D3   (AT91C_PIO_PB23) //  Image Sensor Data 3
#define AT91C_PIO_PB24       (1 << 24) // Pin Controlled by PB24
#define AT91C_PB24_DTR0     (AT91C_PIO_PB24) //  USART 0 Data Terminal ready
#define AT91C_PB24_ISI_D4   (AT91C_PIO_PB24) //  Image Sensor Data 4
#define AT91C_PIO_PB25       (1 << 25) // Pin Controlled by PB25
#define AT91C_PB25_RI0      (AT91C_PIO_PB25) //  USART 0 Ring Indicator
#define AT91C_PB25_ISI_D5   (AT91C_PIO_PB25) //  Image Sensor Data 5
#define AT91C_PIO_PB26       (1 << 26) // Pin Controlled by PB26
#define AT91C_PB26_RTS0     (AT91C_PIO_PB26) //  USART 0 Ready To Send
#define AT91C_PB26_ISI_D6   (AT91C_PIO_PB26) //  Image Sensor Data 6
#define AT91C_PIO_PB27       (1 << 27) // Pin Controlled by PB27
#define AT91C_PB27_CTS0     (AT91C_PIO_PB27) //  USART 0 Clear To Send
#define AT91C_PB27_ISI_D7   (AT91C_PIO_PB27) //  Image Sensor Data 7
#define AT91C_PIO_PB28       (1 << 28) // Pin Controlled by PB28
#define AT91C_PB28_RTS1     (AT91C_PIO_PB28) //  USART 1 Ready To Send
#define AT91C_PB28_ISI_PCK  (AT91C_PIO_PB28) //  Image Sensor Data Clock
#define AT91C_PIO_PB29       (1 << 29) // Pin Controlled by PB29
#define AT91C_PB29_CTS1     (AT91C_PIO_PB29) //  USART 1 Clear To Send
#define AT91C_PB29_ISI_VSYNC (AT91C_PIO_PB29) //  Image Sensor Vertical Synchro
#define AT91C_PIO_PB3        (1 <<  3) // Pin Controlled by PB3
#define AT91C_PB3_SPI1_NPCS0 (AT91C_PIO_PB3) //  SPI 1 Peripheral Chip Select 0
#define AT91C_PB3_TIOA5    (AT91C_PIO_PB3) //  Timer Counter 5 Multipurpose Timer I/O Pin A
#define AT91C_PIO_PB30       (1 << 30) // Pin Controlled by PB30
#define AT91C_PB30_PCK0_0   (AT91C_PIO_PB30) //  PMC Programmable Clock Output 0
#define AT91C_PB30_ISI_HSYNC (AT91C_PIO_PB30) //  Image Sensor Horizontal Synchro
#define AT91C_PIO_PB31       (1 << 31) // Pin Controlled by PB31
#define AT91C_PB31_PCK1_0   (AT91C_PIO_PB31) //  PMC Programmable Clock Output 1
#define AT91C_PB31_ISI_MCK  (AT91C_PIO_PB31) //  Image Sensor Reference Clock
#define AT91C_PIO_PB4        (1 <<  4) // Pin Controlled by PB4
#define AT91C_PB4_TXD0     (AT91C_PIO_PB4) //  USART 0 Transmit Data
#define AT91C_PIO_PB5        (1 <<  5) // Pin Controlled by PB5
#define AT91C_PB5_RXD0     (AT91C_PIO_PB5) //  USART 0 Receive Data
#define AT91C_PIO_PB6        (1 <<  6) // Pin Controlled by PB6
#define AT91C_PB6_TXD1     (AT91C_PIO_PB6) //  USART 1 Transmit Data
#define AT91C_PB6_TCLK1    (AT91C_PIO_PB6) //  Timer Counter 1 external clock input
#define AT91C_PIO_PB7        (1 <<  7) // Pin Controlled by PB7
#define AT91C_PB7_RXD1     (AT91C_PIO_PB7) //  USART 1 Receive Data
#define AT91C_PB7_TCLK2    (AT91C_PIO_PB7) //  Timer Counter 2 external clock input
#define AT91C_PIO_PB8        (1 <<  8) // Pin Controlled by PB8
#define AT91C_PB8_TXD2     (AT91C_PIO_PB8) //  USART 2 Transmit Data
#define AT91C_PIO_PB9        (1 <<  9) // Pin Controlled by PB9
#define AT91C_PB9_RXD2     (AT91C_PIO_PB9) //  USART 2 Receive Data
#define AT91C_PIO_PC0        (1 <<  0) // Pin Controlled by PC0
#define AT91C_PC0_AD0      (AT91C_PIO_PC0) //  ADC Analog Input 0
#define AT91C_PC0_SCK3     (AT91C_PIO_PC0) //  USART 3 Serial Clock
#define AT91C_PIO_PC1        (1 <<  1) // Pin Controlled by PC1
#define AT91C_PC1_AD1      (AT91C_PIO_PC1) //  ADC Analog Input 1
#define AT91C_PC1_PCK0     (AT91C_PIO_PC1) //  PMC Programmable Clock Output 0
#define AT91C_PIO_PC10       (1 << 10) // Pin Controlled by PC10
#define AT91C_PC10_A25_CFRNW (AT91C_PIO_PC10) //  Address Bus[25]
#define AT91C_PC10_CTS3     (AT91C_PIO_PC10) //  USART 3 Clear To Send
#define AT91C_PIO_PC11       (1 << 11) // Pin Controlled by PC11
#define AT91C_PC11_NCS2     (AT91C_PIO_PC11) //  Chip Select Line 2
#define AT91C_PC11_SPI0_NPCS1 (AT91C_PIO_PC11) //  SPI 0 Peripheral Chip Select 1
#define AT91C_PIO_PC12       (1 << 12) // Pin Controlled by PC12
#define AT91C_PC12_IRQ0     (AT91C_PIO_PC12) //  External Interrupt 0
#define AT91C_PC12_NCS7     (AT91C_PIO_PC12) //  Chip Select Line 7
#define AT91C_PIO_PC13       (1 << 13) // Pin Controlled by PC13
#define AT91C_PC13_FIQ      (AT91C_PIO_PC13) //  AIC Fast Interrupt Input
#define AT91C_PC13_NCS6     (AT91C_PIO_PC13) //  Chip Select Line 6
#define AT91C_PIO_PC14       (1 << 14) // Pin Controlled by PC14
#define AT91C_PC14_NCS3_NANDCS (AT91C_PIO_PC14) //  Chip Select Line 3
#define AT91C_PC14_IRQ2     (AT91C_PIO_PC14) //  External Interrupt 2
#define AT91C_PIO_PC15       (1 << 15) // Pin Controlled by PC15
#define AT91C_PC15_NWAIT    (AT91C_PIO_PC15) //  External Wait Signal
#define AT91C_PC15_IRQ1     (AT91C_PIO_PC15) //  External Interrupt 1
#define AT91C_PIO_PC16       (1 << 16) // Pin Controlled by PC16
#define AT91C_PC16_D16      (AT91C_PIO_PC16) //  Data Bus[16]
#define AT91C_PC16_SPI0_NPCS2 (AT91C_PIO_PC16) //  SPI 0 Peripheral Chip Select 2
#define AT91C_PIO_PC17       (1 << 17) // Pin Controlled by PC17
#define AT91C_PC17_D17      (AT91C_PIO_PC17) //  Data Bus[17]
#define AT91C_PC17_SPI0_NPCS3 (AT91C_PIO_PC17) //  SPI 0 Peripheral Chip Select 3
#define AT91C_PIO_PC18       (1 << 18) // Pin Controlled by PC18
#define AT91C_PC18_D18      (AT91C_PIO_PC18) //  Data Bus[18]
#define AT91C_PC18_SPI1_NPCS1_1 (AT91C_PIO_PC18) //  SPI 1 Peripheral Chip Select 1
#define AT91C_PIO_PC19       (1 << 19) // Pin Controlled by PC19
#define AT91C_PC19_D19      (AT91C_PIO_PC19) //  Data Bus[19]
#define AT91C_PC19_SPI1_NPCS2_1 (AT91C_PIO_PC19) //  SPI 1 Peripheral Chip Select 2
#define AT91C_PIO_PC2        (1 <<  2) // Pin Controlled by PC2
#define AT91C_PC2_AD2      (AT91C_PIO_PC2) //  ADC Analog Input 2
#define AT91C_PC2_PCK1     (AT91C_PIO_PC2) //  PMC Programmable Clock Output 1
#define AT91C_PIO_PC20       (1 << 20) // Pin Controlled by PC20
#define AT91C_PC20_D20      (AT91C_PIO_PC20) //  Data Bus[20]
#define AT91C_PC20_SPI1_NPCS3_1 (AT91C_PIO_PC20) //  SPI 1 Peripheral Chip Select 3
#define AT91C_PIO_PC21       (1 << 21) // Pin Controlled by PC21
#define AT91C_PC21_D21      (AT91C_PIO_PC21) //  Data Bus[21]
#define AT91C_PC21_EF100    (AT91C_PIO_PC21) //  Ethernet MAC Force 100 Mbits/sec
#define AT91C_PIO_PC22       (1 << 22) // Pin Controlled by PC22
#define AT91C_PC22_D22      (AT91C_PIO_PC22) //  Data Bus[22]
#define AT91C_PC22_TCLK5    (AT91C_PIO_PC22) //  Timer Counter 5 external clock input
#define AT91C_PIO_PC23       (1 << 23) // Pin Controlled by PC23
#define AT91C_PC23_D23      (AT91C_PIO_PC23) //  Data Bus[23]
#define AT91C_PIO_PC24       (1 << 24) // Pin Controlled by PC24
#define AT91C_PC24_D24      (AT91C_PIO_PC24) //  Data Bus[24]
#define AT91C_PIO_PC25       (1 << 25) // Pin Controlled by PC25
#define AT91C_PC25_D25      (AT91C_PIO_PC25) //  Data Bus[25]
#define AT91C_PIO_PC26       (1 << 26) // Pin Controlled by PC26
#define AT91C_PC26_D26      (AT91C_PIO_PC26) //  Data Bus[26]
#define AT91C_PIO_PC27       (1 << 27) // Pin Controlled by PC27
#define AT91C_PC27_D27      (AT91C_PIO_PC27) //  Data Bus[27]
#define AT91C_PIO_PC28       (1 << 28) // Pin Controlled by PC28
#define AT91C_PC28_D28      (AT91C_PIO_PC28) //  Data Bus[28]
#define AT91C_PIO_PC29       (1 << 29) // Pin Controlled by PC29
#define AT91C_PC29_D29      (AT91C_PIO_PC29) //  Data Bus[29]
#define AT91C_PIO_PC3        (1 <<  3) // Pin Controlled by PC3
#define AT91C_PC3_AD3      (AT91C_PIO_PC3) //  ADC Analog Input 3
#define AT91C_PC3_SPI1_NPCS3_0 (AT91C_PIO_PC3) //  SPI 1 Peripheral Chip Select 3
#define AT91C_PIO_PC30       (1 << 30) // Pin Controlled by PC30
#define AT91C_PC30_D30      (AT91C_PIO_PC30) //  Data Bus[30]
#define AT91C_PIO_PC31       (1 << 31) // Pin Controlled by PC31
#define AT91C_PC31_D31      (AT91C_PIO_PC31) //  Data Bus[31]
#define AT91C_PIO_PC4        (1 <<  4) // Pin Controlled by PC4
#define AT91C_PC4_A23      (AT91C_PIO_PC4) //  Address Bus[23]
#define AT91C_PC4_SPI1_NPCS2_0 (AT91C_PIO_PC4) //  SPI 1 Peripheral Chip Select 2
#define AT91C_PIO_PC5        (1 <<  5) // Pin Controlled by PC5
#define AT91C_PC5_A24      (AT91C_PIO_PC5) //  Address Bus[24]
#define AT91C_PC5_SPI1_NPCS1_0 (AT91C_PIO_PC5) //  SPI 1 Peripheral Chip Select 1
#define AT91C_PIO_PC6        (1 <<  6) // Pin Controlled by PC6
#define AT91C_PC6_TIOB2    (AT91C_PIO_PC6) //  Timer Counter 2 Multipurpose Timer I/O Pin B
#define AT91C_PC6_CFCE1    (AT91C_PIO_PC6) //  Compact Flash Enable 1
#define AT91C_PIO_PC7        (1 <<  7) // Pin Controlled by PC7
#define AT91C_PC7_TIOB1    (AT91C_PIO_PC7) //  Timer Counter 1 Multipurpose Timer I/O Pin B
#define AT91C_PC7_CFCE2    (AT91C_PIO_PC7) //  Compact Flash Enable 2
#define AT91C_PIO_PC8        (1 <<  8) // Pin Controlled by PC8
#define AT91C_PC8_NCS4_CFCS0 (AT91C_PIO_PC8) //  Chip Select Line 4
#define AT91C_PC8_RTS3     (AT91C_PIO_PC8) //  USART 3 Ready To Send
#define AT91C_PIO_PC9        (1 <<  9) // Pin Controlled by PC9
#define AT91C_PC9_NCS5_CFCS1 (AT91C_PIO_PC9) //  Chip Select Line 5
#define AT91C_PC9_TIOB0    (AT91C_PIO_PC9) //  Timer Counter 0 Multipurpose Timer I/O Pin B

// *****************************************************************************
//               PERIPHERAL ID DEFINITIONS FOR AT91SAM9XE512
// *****************************************************************************
#define AT91C_ID_FIQ    ( 0) // Advanced Interrupt Controller (FIQ)
#define AT91C_ID_SYS    ( 1) // System Controller
#define AT91C_ID_PIOA   ( 2) // Parallel IO Controller A
#define AT91C_ID_PIOB   ( 3) // Parallel IO Controller B
#define AT91C_ID_PIOC   ( 4) // Parallel IO Controller C
#define AT91C_ID_ADC    ( 5) // ADC
#define AT91C_ID_US0    ( 6) // USART 0
#define AT91C_ID_US1    ( 7) // USART 1
#define AT91C_ID_US2    ( 8) // USART 2
#define AT91C_ID_MCI    ( 9) // Multimedia Card Interface 0
#define AT91C_ID_UDP    (10) // USB Device Port
#define AT91C_ID_TWI0   (11) // Two-Wire Interface 0
#define AT91C_ID_SPI0   (12) // Serial Peripheral Interface 0
#define AT91C_ID_SPI1   (13) // Serial Peripheral Interface 1
#define AT91C_ID_SSC0   (14) // Serial Synchronous Controller 0
#define AT91C_ID_TC0    (17) // Timer Counter 0
#define AT91C_ID_TC1    (18) // Timer Counter 1
#define AT91C_ID_TC2    (19) // Timer Counter 2
#define AT91C_ID_UHP    (20) // USB Host Port
#define AT91C_ID_EMAC   (21) // Ethernet Mac
#define AT91C_ID_HISI   (22) // Image Sensor Interface
#define AT91C_ID_US3    (23) // USART 3
#define AT91C_ID_US4    (24) // USART 4
#define AT91C_ID_TWI1   (25) // Two-Wire Interface 1
#define AT91C_ID_TC3    (26) // Timer Counter 3
#define AT91C_ID_TC4    (27) // Timer Counter 4
#define AT91C_ID_TC5    (28) // Timer Counter 5
#define AT91C_ID_IRQ0   (29) // Advanced Interrupt Controller (IRQ0)
#define AT91C_ID_IRQ1   (30) // Advanced Interrupt Controller (IRQ1)
#define AT91C_ID_IRQ2   (31) // Advanced Interrupt Controller (IRQ2)
#define AT91C_ALL_INT   (0xFFFE7FFF) // ALL VALID INTERRUPTS

// *****************************************************************************
//               BASE ADDRESS DEFINITIONS FOR AT91SAM9XE512
// *****************************************************************************
#define AT91C_BASE_SYS       (AT91_CAST(AT91PS_SYS) 	0xFFFFFD00) // (SYS) Base Address
#define AT91C_BASE_EBI       (AT91_CAST(AT91PS_EBI) 	0xFFFFEA00) // (EBI) Base Address
#define AT91C_BASE_HECC      (AT91_CAST(AT91PS_ECC) 	0xFFFFE800) // (HECC) Base Address
#define AT91C_BASE_SDRAMC    (AT91_CAST(AT91PS_SDRAMC) 	0xFFFFEA00) // (SDRAMC) Base Address
#define AT91C_BASE_SMC       (AT91_CAST(AT91PS_SMC) 	0xFFFFEC00) // (SMC) Base Address
#define AT91C_BASE_MATRIX    (AT91_CAST(AT91PS_MATRIX) 	0xFFFFEE00) // (MATRIX) Base Address
#define AT91C_BASE_CCFG      (AT91_CAST(AT91PS_CCFG) 	0xFFFFEF10) // (CCFG) Base Address
#define AT91C_BASE_PDC_DBGU  (AT91_CAST(AT91PS_PDC) 	0xFFFFF300) // (PDC_DBGU) Base Address
#define AT91C_BASE_DBGU      (AT91_CAST(AT91PS_DBGU) 	0xFFFFF200) // (DBGU) Base Address
#define AT91C_BASE_AIC       (AT91_CAST(AT91PS_AIC) 	0xFFFFF000) // (AIC) Base Address
#define AT91C_BASE_PIOA      (AT91_CAST(AT91PS_PIO) 	0xFFFFF400) // (PIOA) Base Address
#define AT91C_BASE_PIOB      (AT91_CAST(AT91PS_PIO) 	0xFFFFF600) // (PIOB) Base Address
#define AT91C_BASE_PIOC      (AT91_CAST(AT91PS_PIO) 	0xFFFFF800) // (PIOC) Base Address
#define AT91C_BASE_EFC       (AT91_CAST(AT91PS_EFC) 	0xFFFFFA00) // (EFC) Base Address
#define AT91C_BASE_CKGR      (AT91_CAST(AT91PS_CKGR) 	0xFFFFFC20) // (CKGR) Base Address
#define AT91C_BASE_PMC       (AT91_CAST(AT91PS_PMC) 	0xFFFFFC00) // (PMC) Base Address
#define AT91C_BASE_RSTC      (AT91_CAST(AT91PS_RSTC) 	0xFFFFFD00) // (RSTC) Base Address
#define AT91C_BASE_SHDWC     (AT91_CAST(AT91PS_SHDWC) 	0xFFFFFD10) // (SHDWC) Base Address
#define AT91C_BASE_RTTC      (AT91_CAST(AT91PS_RTTC) 	0xFFFFFD20) // (RTTC) Base Address
#define AT91C_BASE_PITC      (AT91_CAST(AT91PS_PITC) 	0xFFFFFD30) // (PITC) Base Address
#define AT91C_BASE_WDTC      (AT91_CAST(AT91PS_WDTC) 	0xFFFFFD40) // (WDTC) Base Address
#define AT91C_BASE_TC0       (AT91_CAST(AT91PS_TC) 	0xFFFA0000) // (TC0) Base Address
#define AT91C_BASE_TC1       (AT91_CAST(AT91PS_TC) 	0xFFFA0040) // (TC1) Base Address
#define AT91C_BASE_TC2       (AT91_CAST(AT91PS_TC) 	0xFFFA0080) // (TC2) Base Address
#define AT91C_BASE_TC3       (AT91_CAST(AT91PS_TC) 	0xFFFDC000) // (TC3) Base Address
#define AT91C_BASE_TC4       (AT91_CAST(AT91PS_TC) 	0xFFFDC040) // (TC4) Base Address
#define AT91C_BASE_TC5       (AT91_CAST(AT91PS_TC) 	0xFFFDC080) // (TC5) Base Address
#define AT91C_BASE_TCB0      (AT91_CAST(AT91PS_TCB) 	0xFFFA0000) // (TCB0) Base Address
#define AT91C_BASE_TCB1      (AT91_CAST(AT91PS_TCB) 	0xFFFDC000) // (TCB1) Base Address
#define AT91C_BASE_PDC_MCI   (AT91_CAST(AT91PS_PDC) 	0xFFFA8100) // (PDC_MCI) Base Address
#define AT91C_BASE_MCI       (AT91_CAST(AT91PS_MCI) 	0xFFFA8000) // (MCI) Base Address
#define AT91C_BASE_PDC_TWI0  (AT91_CAST(AT91PS_PDC) 	0xFFFAC100) // (PDC_TWI0) Base Address
#define AT91C_BASE_TWI0      (AT91_CAST(AT91PS_TWI) 	0xFFFAC000) // (TWI0) Base Address
#define AT91C_BASE_PDC_TWI1  (AT91_CAST(AT91PS_PDC) 	0xFFFD8100) // (PDC_TWI1) Base Address
#define AT91C_BASE_TWI1      (AT91_CAST(AT91PS_TWI) 	0xFFFD8000) // (TWI1) Base Address
#define AT91C_BASE_PDC_US0   (AT91_CAST(AT91PS_PDC) 	0xFFFB0100) // (PDC_US0) Base Address
#define AT91C_BASE_US0       (AT91_CAST(AT91PS_USART) 	0xFFFB0000) // (US0) Base Address
#define AT91C_BASE_PDC_US1   (AT91_CAST(AT91PS_PDC) 	0xFFFB4100) // (PDC_US1) Base Address
#define AT91C_BASE_US1       (AT91_CAST(AT91PS_USART) 	0xFFFB4000) // (US1) Base Address
#define AT91C_BASE_PDC_US2   (AT91_CAST(AT91PS_PDC) 	0xFFFB8100) // (PDC_US2) Base Address
#define AT91C_BASE_US2       (AT91_CAST(AT91PS_USART) 	0xFFFB8000) // (US2) Base Address
#define AT91C_BASE_PDC_US3   (AT91_CAST(AT91PS_PDC) 	0xFFFD0100) // (PDC_US3) Base Address
#define AT91C_BASE_US3       (AT91_CAST(AT91PS_USART) 	0xFFFD0000) // (US3) Base Address
#define AT91C_BASE_PDC_US4   (AT91_CAST(AT91PS_PDC) 	0xFFFD4100) // (PDC_US4) Base Address
#define AT91C_BASE_US4       (AT91_CAST(AT91PS_USART) 	0xFFFD4000) // (US4) Base Address
#define AT91C_BASE_PDC_SSC0  (AT91_CAST(AT91PS_PDC) 	0xFFFBC100) // (PDC_SSC0) Base Address
#define AT91C_BASE_SSC0      (AT91_CAST(AT91PS_SSC) 	0xFFFBC000) // (SSC0) Base Address
#define AT91C_BASE_PDC_SPI0  (AT91_CAST(AT91PS_PDC) 	0xFFFC8100) // (PDC_SPI0) Base Address
#define AT91C_BASE_SPI0      (AT91_CAST(AT91PS_SPI) 	0xFFFC8000) // (SPI0) Base Address
#define AT91C_BASE_PDC_SPI1  (AT91_CAST(AT91PS_PDC) 	0xFFFCC100) // (PDC_SPI1) Base Address
#define AT91C_BASE_SPI1      (AT91_CAST(AT91PS_SPI) 	0xFFFCC000) // (SPI1) Base Address
#define AT91C_BASE_PDC_ADC   (AT91_CAST(AT91PS_PDC) 	0xFFFE0100) // (PDC_ADC) Base Address
#define AT91C_BASE_ADC       (AT91_CAST(AT91PS_ADC) 	0xFFFE0000) // (ADC) Base Address
#define AT91C_BASE_EMACB     (AT91_CAST(AT91PS_EMAC) 	0xFFFC4000) // (EMACB) Base Address
#define AT91C_BASE_UDP       (AT91_CAST(AT91PS_UDP) 	0xFFFA4000) // (UDP) Base Address
#define AT91C_BASE_UHP       (AT91_CAST(AT91PS_UHP) 	0x00500000) // (UHP) Base Address
#define AT91C_BASE_HISI      (AT91_CAST(AT91PS_ISI) 	0xFFFC0000) // (HISI) Base Address

// *****************************************************************************
//               MEMORY MAPPING DEFINITIONS FOR AT91SAM9XE512
// *****************************************************************************
// IROM
#define AT91C_IROM 	 (0x00100000) // Internal ROM base address
#define AT91C_IROM_SIZE	 (0x00008000) // Internal ROM size in byte (32 Kbytes)
// ISRAM
#define AT91C_ISRAM	 (0x00300000) // Maximum IRAM Area : 32Kbyte base address
#define AT91C_ISRAM_SIZE	 (0x00008000) // Maximum IRAM Area : 32Kbyte size in byte (32 Kbytes)
// ISRAM_MIN
#define AT91C_ISRAM_MIN	 (0x00300000) // Minimun IRAM Area : 32Kbyte base address
#define AT91C_ISRAM_MIN_SIZE	 (0x00008000) // Minimun IRAM Area : 32Kbyte size in byte (32 Kbytes)
// IFLASH
#define AT91C_IFLASH	 (0x00200000) // Maximum IFLASH Area : 512Kbyte base address
#define AT91C_IFLASH_SIZE	 (0x00080000) // Maximum IFLASH Area : 512Kbyte size in byte (512 Kbytes)
#define AT91C_IFLASH_PAGE_SIZE	 (512) // Maximum IFLASH Area : 512Kbyte Page Size: 512 bytes
#define AT91C_IFLASH_LOCK_REGION_SIZE	 (16384) // Maximum IFLASH Area : 512Kbyte Lock Region Size: 16 Kbytes
#define AT91C_IFLASH_NB_OF_PAGES	 (1024) // Maximum IFLASH Area : 512Kbyte Number of Pages: 1024 bytes
#define AT91C_IFLASH_NB_OF_LOCK_BITS	 (32) // Maximum IFLASH Area : 512Kbyte Number of Lock Bits: 32 bytes
// EBI_CS0
#define AT91C_EBI_CS0	 (0x10000000) // EBI Chip Select 0 base address
#define AT91C_EBI_CS0_SIZE	 (0x10000000) // EBI Chip Select 0 size in byte (262144 Kbytes)
// EBI_CS1
#define AT91C_EBI_CS1	 (0x20000000) // EBI Chip Select 1 base address
#define AT91C_EBI_CS1_SIZE	 (0x10000000) // EBI Chip Select 1 size in byte (262144 Kbytes)
// EBI_SDRAM
#define AT91C_EBI_SDRAM	 (0x20000000) // SDRAM on EBI Chip Select 1 base address
#define AT91C_EBI_SDRAM_SIZE	 (0x10000000) // SDRAM on EBI Chip Select 1 size in byte (262144 Kbytes)
// EBI_SDRAM_16BIT
#define AT91C_EBI_SDRAM_16BIT	 (0x20000000) // SDRAM on EBI Chip Select 1 base address
#define AT91C_EBI_SDRAM_16BIT_SIZE	 (0x02000000) // SDRAM on EBI Chip Select 1 size in byte (32768 Kbytes)
// EBI_SDRAM_32BIT
#define AT91C_EBI_SDRAM_32BIT	 (0x20000000) // SDRAM on EBI Chip Select 1 base address
#define AT91C_EBI_SDRAM_32BIT_SIZE	 (0x04000000) // SDRAM on EBI Chip Select 1 size in byte (65536 Kbytes)
// EBI_CS2
#define AT91C_EBI_CS2	 (0x30000000) // EBI Chip Select 2 base address
#define AT91C_EBI_CS2_SIZE	 (0x10000000) // EBI Chip Select 2 size in byte (262144 Kbytes)
// EBI_CS3
#define AT91C_EBI_CS3	 (0x40000000) // EBI Chip Select 3 base address
#define AT91C_EBI_CS3_SIZE	 (0x10000000) // EBI Chip Select 3 size in byte (262144 Kbytes)
// EBI_SM
#define AT91C_EBI_SM	 (0x40000000) // SmartMedia on Chip Select 3 base address
#define AT91C_EBI_SM_SIZE	 (0x10000000) // SmartMedia on Chip Select 3 size in byte (262144 Kbytes)
// EBI_CS4
#define AT91C_EBI_CS4	 (0x50000000) // EBI Chip Select 4 base address
#define AT91C_EBI_CS4_SIZE	 (0x10000000) // EBI Chip Select 4 size in byte (262144 Kbytes)
// EBI_CF0
#define AT91C_EBI_CF0	 (0x50000000) // CompactFlash 0 on Chip Select 4 base address
#define AT91C_EBI_CF0_SIZE	 (0x10000000) // CompactFlash 0 on Chip Select 4 size in byte (262144 Kbytes)
// EBI_CS5
#define AT91C_EBI_CS5	 (0x60000000) // EBI Chip Select 5 base address
#define AT91C_EBI_CS5_SIZE	 (0x10000000) // EBI Chip Select 5 size in byte (262144 Kbytes)
// EBI_CF1
#define AT91C_EBI_CF1	 (0x60000000) // CompactFlash 1 on Chip Select 5 base address
#define AT91C_EBI_CF1_SIZE	 (0x10000000) // CompactFlash 1 on Chip Select 5 size in byte (262144 Kbytes)
// EBI_CS6
#define AT91C_EBI_CS6	 (0x70000000) // EBI Chip Select 6 base address
#define AT91C_EBI_CS6_SIZE	 (0x10000000) // EBI Chip Select 6 size in byte (262144 Kbytes)
// EBI_CS7
#define AT91C_EBI_CS7	 (0x80000000) // EBI Chip Select 7 base address
#define AT91C_EBI_CS7_SIZE	 (0x10000000) // EBI Chip Select 7 size in byte (262144 Kbytes)

#endif
