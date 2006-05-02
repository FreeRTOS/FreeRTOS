// ----------------------------------------------------------------------------
//          ATMEL Microcontroller Software Support  -  ROUSSET  -
// ----------------------------------------------------------------------------
//  The software is delivered "AS IS" without warranty or condition of any
//  kind, either express, implied or statutory. This includes without
//  limitation any warranty or condition with respect to merchantability or
//  fitness for any particular purpose, or against the infringements of
//  intellectual property rights of others.
// ----------------------------------------------------------------------------
// File Name           : AT91R40008.h
// Object              : AT91R40008 definitions
// Generated           : AT91 SW Application Group  02/19/2003 (11:13:31)
// 
// CVS Reference       : /AT91R40008.pl/1.3/Tue Nov 12 16:01:52 2002//
// CVS Reference       : /AIC_1246F.pl/1.4/Mon Nov 04 17:51:00 2002//
// CVS Reference       : /WD_1241B.pl/1.1/Mon Nov 04 17:51:00 2002//
// CVS Reference       : /PS_x40.pl/1.2/Tue Nov 12 16:01:52 2002//
// CVS Reference       : /PIO_1321C.pl/1.5/Tue Oct 29 15:50:24 2002//
// CVS Reference       : /TC_1243B.pl/1.4/Tue Nov 05 12:43:10 2002//
// CVS Reference       : /PDC_1363D.pl/1.3/Wed Oct 23 14:49:48 2002//
// CVS Reference       : /US_1242E.pl/1.5/Thu Nov 21 13:37:56 2002//
// CVS Reference       : /SF_x40.pl/1.1/Tue Nov 12 13:27:20 2002//
// CVS Reference       : /EBI_x40.pl/1.5/Wed Feb 19 09:25:22 2003//
// ----------------------------------------------------------------------------

#ifndef AT91R40008_H
#define AT91R40008_H

/* AT91 Register type */
typedef volatile unsigned int AT91_REG;  // Hardware register definition
typedef volatile unsigned int at91_reg;

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Advanced Interrupt Controller
// *****************************************************************************
typedef struct _AT91S_AIC {
	AT91_REG	 AIC_SMR[32]; 	// Source Mode egister
	AT91_REG	 AIC_SVR[32]; 	// Source Vector egister
	AT91_REG	 AIC_IVR; 	// IRQ Vector Register
	AT91_REG	 AIC_FVR; 	// FIQ Vector Register
	AT91_REG	 AIC_ISR; 	// Interrupt Status Register
	AT91_REG	 AIC_IPR; 	// Interrupt Pending Register
	AT91_REG	 AIC_IMR; 	// Interrupt Mask Register
	AT91_REG	 AIC_CISR; 	// Core Interrupt Status Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 AIC_IECR; 	// Interrupt Enable Command Register
	AT91_REG	 AIC_IDCR; 	// Interrupt Disable Command egister
	AT91_REG	 AIC_ICCR; 	// Interrupt Clear Command Register
	AT91_REG	 AIC_ISCR; 	// Interrupt Set Command Register
	AT91_REG	 AIC_EOICR; 	// End of Interrupt Command Register
	AT91_REG	 AIC_SPU; 	// Spurious Vector Register
} AT91S_AIC, *AT91PS_AIC;

// -------- AIC_SMR : (AIC Offset: 0x0) Control Register -------- 
#define AT91C_AIC_PRIOR       ((unsigned int) 0x7 <<  0) // (AIC) Priority Level
#define 	AT91C_AIC_PRIOR_LOWEST               ((unsigned int) 0x0) // (AIC) Lowest priority level
#define 	AT91C_AIC_PRIOR_HIGHEST              ((unsigned int) 0x7) // (AIC) Highest priority level
#define AT91C_AIC_SRCTYPE     ((unsigned int) 0x3 <<  5) // (AIC) Interrupt Source Type
#define 	AT91C_AIC_SRCTYPE_INT_LEVEL_SENSITIVE  ((unsigned int) 0x0 <<  5) // (AIC) Internal Sources Code Label Level Sensitive
#define 	AT91C_AIC_SRCTYPE_INT_EDGE_TRIGGERED   ((unsigned int) 0x1 <<  5) // (AIC) Internal Sources Code Label Edge triggered
#define 	AT91C_AIC_SRCTYPE_EXT_HIGH_LEVEL       ((unsigned int) 0x2 <<  5) // (AIC) External Sources Code Label High-level Sensitive
#define 	AT91C_AIC_SRCTYPE_EXT_POSITIVE_EDGE    ((unsigned int) 0x3 <<  5) // (AIC) External Sources Code Label Positive Edge triggered
// -------- AIC_CISR : (AIC Offset: 0x114) AIC Core Interrupt Status Register -------- 
#define AT91C_AIC_NFIQ        ((unsigned int) 0x1 <<  0) // (AIC) NFIQ Status
#define AT91C_AIC_NIRQ        ((unsigned int) 0x1 <<  1) // (AIC) NIRQ Status

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Watchdog Timer Interface
// *****************************************************************************
typedef struct _AT91S_WD {
	AT91_REG	 WD_OMR; 	// Overflow Mode Register
	AT91_REG	 WD_CMR; 	// Clock Mode Register
	AT91_REG	 WD_CR; 	// Control Register
	AT91_REG	 WD_SR; 	// Status Register
} AT91S_WD, *AT91PS_WD;

// -------- WD_OMR : (WD Offset: 0x0) Overflow Mode Register -------- 
#define AT91C_WD_WDEN         ((unsigned int) 0x1 <<  0) // (WD) Watchdog Enable
#define AT91C_WD_RSTEN        ((unsigned int) 0x1 <<  1) // (WD) Reset Enable
#define AT91C_WD_IRQEN        ((unsigned int) 0x1 <<  2) // (WD) Interrupt Enable
#define AT91C_WD_EXTEN        ((unsigned int) 0x1 <<  3) // (WD) External Signal Enable
#define AT91C_WD_OKEY         ((unsigned int) 0xFFF <<  4) // (WD) Watchdog Enable
// -------- WD_CMR : (WD Offset: 0x4) Clock Mode Register -------- 
#define AT91C_WD_WDCLKS       ((unsigned int) 0x3 <<  0) // (WD) Clock Selection
#define 	AT91C_WD_WDCLKS_MCK32                ((unsigned int) 0x0) // (WD) Master Clock divided by 32
#define 	AT91C_WD_WDCLKS_MCK128               ((unsigned int) 0x1) // (WD) Master Clock divided by 128
#define 	AT91C_WD_WDCLKS_MCK1024              ((unsigned int) 0x2) // (WD) Master Clock divided by 1024
#define 	AT91C_WD_WDCLKS_MCK4096              ((unsigned int) 0x3) // (WD) Master Clock divided by 4096
#define AT91C_WD_HPCV         ((unsigned int) 0xF <<  2) // (WD) High Pre-load Counter Value
#define AT91C_WD_CKEY         ((unsigned int) 0x1FF <<  7) // (WD) Clock Access Key
// -------- WD_CR : (WD Offset: 0x8) Control Register -------- 
#define AT91C_WD_RSTKEY       ((unsigned int) 0xFFFF <<  0) // (WD) Restart Key
// -------- WD_SR : (WD Offset: 0xc) Status Register -------- 
#define AT91C_WD_WDOVF        ((unsigned int) 0x1 <<  0) // (WD) Watchdog Overflow

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Power Saving Controler
// *****************************************************************************
typedef struct _AT91S_PS {
	AT91_REG	 PS_CR; 	// Control Register
	AT91_REG	 PS_PCER; 	// Peripheral Clock Enable Register
	AT91_REG	 PS_PCDR; 	// Peripheral Clock Disable Register
	AT91_REG	 PS_PCSR; 	// Peripheral Clock Status Register
} AT91S_PS, *AT91PS_PS;

// -------- PS_PCER : (PS Offset: 0x4) Peripheral Clock Enable Register -------- 
#define AT91C_PS_US0          ((unsigned int) 0x1 <<  2) // (PS) Usart 0 Clock
#define AT91C_PS_US1          ((unsigned int) 0x1 <<  3) // (PS) Usart 1 Clock
#define AT91C_PS_TC0          ((unsigned int) 0x1 <<  4) // (PS) Timer Counter 0 Clock
#define AT91C_PS_TC1          ((unsigned int) 0x1 <<  5) // (PS) Timer Counter 1 Clock
#define AT91C_PS_TC2          ((unsigned int) 0x1 <<  6) // (PS) Timer Counter 2 Clock
#define AT91C_PS_PIO          ((unsigned int) 0x1 <<  8) // (PS) PIO Clock
// -------- PS_PCDR : (PS Offset: 0x8) Peripheral Clock Disable Register -------- 
// -------- PS_PCSR : (PS Offset: 0xc) Peripheral Clock Satus Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Parallel Input Output Controler
// *****************************************************************************
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
} AT91S_PIO, *AT91PS_PIO;


// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Timer Counter Channel Interface
// *****************************************************************************
typedef struct _AT91S_TC {
	AT91_REG	 TC_CCR; 	// Channel Control Register
	AT91_REG	 TC_CMR; 	// Channel Mode Register
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

// -------- TC_CCR : (TC Offset: 0x0) TC Channel Control Register -------- 
#define AT91C_TC_CLKEN        ((unsigned int) 0x1 <<  0) // (TC) Counter Clock Enable Command
#define AT91C_TC_CLKDIS       ((unsigned int) 0x1 <<  1) // (TC) Counter Clock Disable Command
#define AT91C_TC_SWTRG        ((unsigned int) 0x1 <<  2) // (TC) Software Trigger Command
// -------- TC_CMR : (TC Offset: 0x4) TC Channel Mode Register: Capture Mode / Waveform Mode -------- 
#define AT91C_TC_CPCSTOP      ((unsigned int) 0x1 <<  6) // (TC) Counter Clock Stopped with RC Compare
#define AT91C_TC_CPCDIS       ((unsigned int) 0x1 <<  7) // (TC) Counter Clock Disable with RC Compare
#define AT91C_TC_EEVTEDG      ((unsigned int) 0x3 <<  8) // (TC) External Event Edge Selection
#define 	AT91C_TC_EEVTEDG_NONE                 ((unsigned int) 0x0 <<  8) // (TC) Edge: None
#define 	AT91C_TC_EEVTEDG_RISING               ((unsigned int) 0x1 <<  8) // (TC) Edge: rising edge
#define 	AT91C_TC_EEVTEDG_FALLING              ((unsigned int) 0x2 <<  8) // (TC) Edge: falling edge
#define 	AT91C_TC_EEVTEDG_BOTH                 ((unsigned int) 0x3 <<  8) // (TC) Edge: each edge
#define AT91C_TC_EEVT         ((unsigned int) 0x3 << 10) // (TC) External Event  Selection
#define 	AT91C_TC_EEVT_NONE                 ((unsigned int) 0x0 << 10) // (TC) Signal selected as external event: TIOB TIOB direction: input
#define 	AT91C_TC_EEVT_RISING               ((unsigned int) 0x1 << 10) // (TC) Signal selected as external event: XC0 TIOB direction: output
#define 	AT91C_TC_EEVT_FALLING              ((unsigned int) 0x2 << 10) // (TC) Signal selected as external event: XC1 TIOB direction: output
#define 	AT91C_TC_EEVT_BOTH                 ((unsigned int) 0x3 << 10) // (TC) Signal selected as external event: XC2 TIOB direction: output
#define AT91C_TC_ENETRG       ((unsigned int) 0x1 << 12) // (TC) External Event Trigger enable
#define AT91C_TC_WAVESEL      ((unsigned int) 0x3 << 13) // (TC) Waveform  Selection
#define 	AT91C_TC_WAVESEL_UP                   ((unsigned int) 0x0 << 13) // (TC) UP mode without atomatic trigger on RC Compare
#define 	AT91C_TC_WAVESEL_UP_AUTO              ((unsigned int) 0x1 << 13) // (TC) UP mode with automatic trigger on RC Compare
#define 	AT91C_TC_WAVESEL_UPDOWN               ((unsigned int) 0x2 << 13) // (TC) UPDOWN mode without automatic trigger on RC Compare
#define 	AT91C_TC_WAVESEL_UPDOWN_AUTO          ((unsigned int) 0x3 << 13) // (TC) UPDOWN mode with automatic trigger on RC Compare
#define AT91C_TC_CPCTRG       ((unsigned int) 0x1 << 14) // (TC) RC Compare Trigger Enable
#define AT91C_TC_WAVE         ((unsigned int) 0x1 << 15) // (TC) 
#define AT91C_TC_ACPA         ((unsigned int) 0x3 << 16) // (TC) RA Compare Effect on TIOA
#define 	AT91C_TC_ACPA_NONE                 ((unsigned int) 0x0 << 16) // (TC) Effect: none
#define 	AT91C_TC_ACPA_SET                  ((unsigned int) 0x1 << 16) // (TC) Effect: set
#define 	AT91C_TC_ACPA_CLEAR                ((unsigned int) 0x2 << 16) // (TC) Effect: clear
#define 	AT91C_TC_ACPA_TOGGLE               ((unsigned int) 0x3 << 16) // (TC) Effect: toggle
#define AT91C_TC_ACPC         ((unsigned int) 0x3 << 18) // (TC) RC Compare Effect on TIOA
#define 	AT91C_TC_ACPC_NONE                 ((unsigned int) 0x0 << 18) // (TC) Effect: none
#define 	AT91C_TC_ACPC_SET                  ((unsigned int) 0x1 << 18) // (TC) Effect: set
#define 	AT91C_TC_ACPC_CLEAR                ((unsigned int) 0x2 << 18) // (TC) Effect: clear
#define 	AT91C_TC_ACPC_TOGGLE               ((unsigned int) 0x3 << 18) // (TC) Effect: toggle
#define AT91C_TC_AEEVT        ((unsigned int) 0x3 << 20) // (TC) External Event Effect on TIOA
#define 	AT91C_TC_AEEVT_NONE                 ((unsigned int) 0x0 << 20) // (TC) Effect: none
#define 	AT91C_TC_AEEVT_SET                  ((unsigned int) 0x1 << 20) // (TC) Effect: set
#define 	AT91C_TC_AEEVT_CLEAR                ((unsigned int) 0x2 << 20) // (TC) Effect: clear
#define 	AT91C_TC_AEEVT_TOGGLE               ((unsigned int) 0x3 << 20) // (TC) Effect: toggle
#define AT91C_TC_ASWTRG       ((unsigned int) 0x3 << 22) // (TC) Software Trigger Effect on TIOA
#define 	AT91C_TC_ASWTRG_NONE                 ((unsigned int) 0x0 << 22) // (TC) Effect: none
#define 	AT91C_TC_ASWTRG_SET                  ((unsigned int) 0x1 << 22) // (TC) Effect: set
#define 	AT91C_TC_ASWTRG_CLEAR                ((unsigned int) 0x2 << 22) // (TC) Effect: clear
#define 	AT91C_TC_ASWTRG_TOGGLE               ((unsigned int) 0x3 << 22) // (TC) Effect: toggle
#define AT91C_TC_BCPB         ((unsigned int) 0x3 << 24) // (TC) RB Compare Effect on TIOB
#define 	AT91C_TC_BCPB_NONE                 ((unsigned int) 0x0 << 24) // (TC) Effect: none
#define 	AT91C_TC_BCPB_SET                  ((unsigned int) 0x1 << 24) // (TC) Effect: set
#define 	AT91C_TC_BCPB_CLEAR                ((unsigned int) 0x2 << 24) // (TC) Effect: clear
#define 	AT91C_TC_BCPB_TOGGLE               ((unsigned int) 0x3 << 24) // (TC) Effect: toggle
#define AT91C_TC_BCPC         ((unsigned int) 0x3 << 26) // (TC) RC Compare Effect on TIOB
#define 	AT91C_TC_BCPC_NONE                 ((unsigned int) 0x0 << 26) // (TC) Effect: none
#define 	AT91C_TC_BCPC_SET                  ((unsigned int) 0x1 << 26) // (TC) Effect: set
#define 	AT91C_TC_BCPC_CLEAR                ((unsigned int) 0x2 << 26) // (TC) Effect: clear
#define 	AT91C_TC_BCPC_TOGGLE               ((unsigned int) 0x3 << 26) // (TC) Effect: toggle
#define AT91C_TC_BEEVT        ((unsigned int) 0x3 << 28) // (TC) External Event Effect on TIOB
#define 	AT91C_TC_BEEVT_NONE                 ((unsigned int) 0x0 << 28) // (TC) Effect: none
#define 	AT91C_TC_BEEVT_SET                  ((unsigned int) 0x1 << 28) // (TC) Effect: set
#define 	AT91C_TC_BEEVT_CLEAR                ((unsigned int) 0x2 << 28) // (TC) Effect: clear
#define 	AT91C_TC_BEEVT_TOGGLE               ((unsigned int) 0x3 << 28) // (TC) Effect: toggle
#define AT91C_TC_BSWTRG       ((unsigned int) 0x3 << 30) // (TC) Software Trigger Effect on TIOB
#define 	AT91C_TC_BSWTRG_NONE                 ((unsigned int) 0x0 << 30) // (TC) Effect: none
#define 	AT91C_TC_BSWTRG_SET                  ((unsigned int) 0x1 << 30) // (TC) Effect: set
#define 	AT91C_TC_BSWTRG_CLEAR                ((unsigned int) 0x2 << 30) // (TC) Effect: clear
#define 	AT91C_TC_BSWTRG_TOGGLE               ((unsigned int) 0x3 << 30) // (TC) Effect: toggle
// -------- TC_SR : (TC Offset: 0x20) TC Channel Status Register -------- 
#define AT91C_TC_COVFS        ((unsigned int) 0x1 <<  0) // (TC) Counter Overflow
#define AT91C_TC_LOVRS        ((unsigned int) 0x1 <<  1) // (TC) Load Overrun
#define AT91C_TC_CPAS         ((unsigned int) 0x1 <<  2) // (TC) RA Compare
#define AT91C_TC_CPBS         ((unsigned int) 0x1 <<  3) // (TC) RB Compare
#define AT91C_TC_CPCS         ((unsigned int) 0x1 <<  4) // (TC) RC Compare
#define AT91C_TC_LDRAS        ((unsigned int) 0x1 <<  5) // (TC) RA Loading
#define AT91C_TC_LDRBS        ((unsigned int) 0x1 <<  6) // (TC) RB Loading
#define AT91C_TC_ETRCS        ((unsigned int) 0x1 <<  7) // (TC) External Trigger
#define AT91C_TC_ETRGS        ((unsigned int) 0x1 << 16) // (TC) Clock Enabling
#define AT91C_TC_MTIOA        ((unsigned int) 0x1 << 17) // (TC) TIOA Mirror
#define AT91C_TC_MTIOB        ((unsigned int) 0x1 << 18) // (TC) TIOA Mirror
// -------- TC_IER : (TC Offset: 0x24) TC Channel Interrupt Enable Register -------- 
// -------- TC_IDR : (TC Offset: 0x28) TC Channel Interrupt Disable Register -------- 
// -------- TC_IMR : (TC Offset: 0x2c) TC Channel Interrupt Mask Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Timer Counter Interface
// *****************************************************************************
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

// -------- TCB_BCR : (TCB Offset: 0xc0) TC Block Control Register -------- 
#define AT91C_TCB_SYNC        ((unsigned int) 0x1 <<  0) // (TCB) Synchro Command
// -------- TCB_BMR : (TCB Offset: 0xc4) TC Block Mode Register -------- 
#define AT91C_TCB_TC0XC0S     ((unsigned int) 0x1 <<  0) // (TCB) External Clock Signal 0 Selection
#define 	AT91C_TCB_TC0XC0S_TCLK0                ((unsigned int) 0x0) // (TCB) TCLK0 connected to XC0
#define 	AT91C_TCB_TC0XC0S_NONE                 ((unsigned int) 0x1) // (TCB) None signal connected to XC0
#define 	AT91C_TCB_TC0XC0S_TIOA1                ((unsigned int) 0x2) // (TCB) TIOA1 connected to XC0
#define 	AT91C_TCB_TC0XC0S_TIOA2                ((unsigned int) 0x3) // (TCB) TIOA2 connected to XC0
#define AT91C_TCB_TC1XC1S     ((unsigned int) 0x1 <<  2) // (TCB) External Clock Signal 1 Selection
#define 	AT91C_TCB_TC1XC1S_TCLK1                ((unsigned int) 0x0 <<  2) // (TCB) TCLK1 connected to XC1
#define 	AT91C_TCB_TC1XC1S_NONE                 ((unsigned int) 0x1 <<  2) // (TCB) None signal connected to XC1
#define 	AT91C_TCB_TC1XC1S_TIOA0                ((unsigned int) 0x2 <<  2) // (TCB) TIOA0 connected to XC1
#define 	AT91C_TCB_TC1XC1S_TIOA2                ((unsigned int) 0x3 <<  2) // (TCB) TIOA2 connected to XC1
#define AT91C_TCB_TC2XC2S     ((unsigned int) 0x1 <<  4) // (TCB) External Clock Signal 2 Selection
#define 	AT91C_TCB_TC2XC2S_TCLK2                ((unsigned int) 0x0 <<  4) // (TCB) TCLK2 connected to XC2
#define 	AT91C_TCB_TC2XC2S_NONE                 ((unsigned int) 0x1 <<  4) // (TCB) None signal connected to XC2
#define 	AT91C_TCB_TC2XC2S_TIOA0                ((unsigned int) 0x2 <<  4) // (TCB) TIOA0 connected to XC2
#define 	AT91C_TCB_TC2XC2S_TIOA2                ((unsigned int) 0x3 <<  4) // (TCB) TIOA2 connected to XC2

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Peripheral Data Controller
// *****************************************************************************
typedef struct _AT91S_PDC {
	AT91_REG	 PDC_RPR; 	// Receive Pointer Register
	AT91_REG	 PDC_RCR; 	// Receive Counter Register
	AT91_REG	 PDC_TPR; 	// Transmit Pointer Register
	AT91_REG	 PDC_TCR; 	// Transmit Counter Register
} AT91S_PDC, *AT91PS_PDC;


// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Usart
// *****************************************************************************
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
	AT91_REG	 Reserved0[1]; 	// 
	AT91_REG	 US_RPR; 	// Receive Pointer Register
	AT91_REG	 US_RCR; 	// Receive Counter Register
	AT91_REG	 US_TPR; 	// Transmit Pointer Register
	AT91_REG	 US_TCR; 	// Transmit Counter Register
} AT91S_USART, *AT91PS_USART;

// -------- US_CR : (USART Offset: 0x0) Debug Unit Control Register -------- 
#define AT91C_US_RSTRX        ((unsigned int) 0x1 <<  2) // (USART) Reset Receiver
#define AT91C_US_RSTTX        ((unsigned int) 0x1 <<  3) // (USART) Reset Transmitter
#define AT91C_US_RXEN         ((unsigned int) 0x1 <<  4) // (USART) Receiver Enable
#define AT91C_US_RXDIS        ((unsigned int) 0x1 <<  5) // (USART) Receiver Disable
#define AT91C_US_TXEN         ((unsigned int) 0x1 <<  6) // (USART) Transmitter Enable
#define AT91C_US_TXDIS        ((unsigned int) 0x1 <<  7) // (USART) Transmitter Disable
#define AT91C_US_RSTSTA       ((unsigned int) 0x1 <<  8) // (USART) Reset Status Bits
#define AT91C_US_STTBRK       ((unsigned int) 0x1 <<  9) // (USART) Start Break
#define AT91C_US_STPBRK       ((unsigned int) 0x1 << 10) // (USART) Stop Break
#define AT91C_US_STTTO        ((unsigned int) 0x1 << 11) // (USART) Start Time-out
#define AT91C_US_SENDA        ((unsigned int) 0x1 << 12) // (USART) Send Address
// -------- US_MR : (USART Offset: 0x4) Debug Unit Mode Register -------- 
#define AT91C_US_CLKS         ((unsigned int) 0x3 <<  4) // (USART) Clock Selection (Baud Rate generator Input Clock
#define 	AT91C_US_CLKS_CLOCK                ((unsigned int) 0x0 <<  4) // (USART) Clock
#define 	AT91C_US_CLKS_FDIV1                ((unsigned int) 0x1 <<  4) // (USART) fdiv1
#define 	AT91C_US_CLKS_SLOW                 ((unsigned int) 0x2 <<  4) // (USART) slow_clock (ARM)
#define 	AT91C_US_CLKS_EXT                  ((unsigned int) 0x3 <<  4) // (USART) External (SCK)
#define AT91C_US_CHRL         ((unsigned int) 0x3 <<  6) // (USART) Clock Selection (Baud Rate generator Input Clock
#define 	AT91C_US_CHRL_5_BITS               ((unsigned int) 0x0 <<  6) // (USART) Character Length: 5 bits
#define 	AT91C_US_CHRL_6_BITS               ((unsigned int) 0x1 <<  6) // (USART) Character Length: 6 bits
#define 	AT91C_US_CHRL_7_BITS               ((unsigned int) 0x2 <<  6) // (USART) Character Length: 7 bits
#define 	AT91C_US_CHRL_8_BITS               ((unsigned int) 0x3 <<  6) // (USART) Character Length: 8 bits
#define AT91C_US_SYNC         ((unsigned int) 0x1 <<  8) // (USART) Synchronous Mode Select
#define AT91C_US_PAR          ((unsigned int) 0x7 <<  9) // (USART) Parity type
#define 	AT91C_US_PAR_EVEN                 ((unsigned int) 0x0 <<  9) // (USART) Even Parity
#define 	AT91C_US_PAR_ODD                  ((unsigned int) 0x1 <<  9) // (USART) Odd Parity
#define 	AT91C_US_PAR_SPACE                ((unsigned int) 0x2 <<  9) // (USART) Parity forced to 0 (Space)
#define 	AT91C_US_PAR_MARK                 ((unsigned int) 0x3 <<  9) // (USART) Parity forced to 1 (Mark)
#define 	AT91C_US_PAR_NONE                 ((unsigned int) 0x4 <<  9) // (USART) No Parity
#define 	AT91C_US_PAR_MULTI_DROP           ((unsigned int) 0x6 <<  9) // (USART) Multi-drop mode
#define AT91C_US_NBSTOP       ((unsigned int) 0x3 << 12) // (USART) Number of Stop bits
#define 	AT91C_US_NBSTOP_1_BIT                ((unsigned int) 0x0 << 12) // (USART) 1 stop bit
#define 	AT91C_US_NBSTOP_15_BIT               ((unsigned int) 0x1 << 12) // (USART) Asynchronous (SYNC=0) 2 stop bits Synchronous (SYNC=1) 2 stop bits
#define 	AT91C_US_NBSTOP_2_BIT                ((unsigned int) 0x2 << 12) // (USART) 2 stop bits
#define AT91C_US_CHMODE       ((unsigned int) 0x3 << 14) // (USART) Channel Mode
#define 	AT91C_US_CHMODE_NORMAL               ((unsigned int) 0x0 << 14) // (USART) Normal Mode: The USART channel operates as an RX/TX USART.
#define 	AT91C_US_CHMODE_AUTO                 ((unsigned int) 0x1 << 14) // (USART) Automatic Echo: Receiver Data Input is connected to the TXD pin.
#define 	AT91C_US_CHMODE_LOCAL                ((unsigned int) 0x2 << 14) // (USART) Local Loopback: Transmitter Output Signal is connected to Receiver Input Signal.
#define 	AT91C_US_CHMODE_REMOTE               ((unsigned int) 0x3 << 14) // (USART) Remote Loopback: RXD pin is internally connected to TXD pin.
#define AT91C_US_MODE9        ((unsigned int) 0x1 << 17) // (USART) 9-bit Character length
#define AT91C_US_CKLO         ((unsigned int) 0x1 << 18) // (USART) Clock Output Select
// -------- US_IER : (USART Offset: 0x8) Debug Unit Interrupt Enable Register -------- 
#define AT91C_US_RXRDY        ((unsigned int) 0x1 <<  0) // (USART) RXRDY Interrupt
#define AT91C_US_TXRDY        ((unsigned int) 0x1 <<  1) // (USART) TXRDY Interrupt
#define AT91C_US_RXBRK        ((unsigned int) 0x1 <<  2) // (USART) Break Received/End of Break
#define AT91C_US_ENDRX        ((unsigned int) 0x1 <<  3) // (USART) End of Receive Transfer Interrupt
#define AT91C_US_ENDTX        ((unsigned int) 0x1 <<  4) // (USART) End of Transmit Interrupt
#define AT91C_US_OVRE         ((unsigned int) 0x1 <<  5) // (USART) Overrun Interrupt
#define AT91C_US_FRAME        ((unsigned int) 0x1 <<  6) // (USART) Framing Error Interrupt
#define AT91C_US_PARE         ((unsigned int) 0x1 <<  7) // (USART) Parity Error Interrupt
#define AT91C_US_TIMEOUT      ((unsigned int) 0x1 <<  8) // (USART) Receiver Time-out
#define AT91C_US_TXEMPTY      ((unsigned int) 0x1 <<  9) // (USART) TXEMPTY Interrupt
// -------- US_IDR : (USART Offset: 0xc) Debug Unit Interrupt Disable Register -------- 
// -------- US_IMR : (USART Offset: 0x10) Debug Unit Interrupt Mask Register -------- 
// -------- US_CSR : (USART Offset: 0x14) Debug Unit Channel Status Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Special Function Interface
// *****************************************************************************
typedef struct _AT91S_SF {
	AT91_REG	 SF_CIDR; 	// Chip ID Register
	AT91_REG	 SF_EXID; 	// Chip ID Extension Register
	AT91_REG	 SF_RSR; 	// Reset Status Register
	AT91_REG	 SF_MMR; 	// Memory Mode Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 SF_PMR; 	// Protect Mode Register
} AT91S_SF, *AT91PS_SF;

// -------- SF_CIDR : (SF Offset: 0x0) Chip ID Register -------- 
#define AT91C_SF_VERSION      ((unsigned int) 0x1F <<  0) // (SF) Version of the chip
#define AT91C_SF_BIT5         ((unsigned int) 0x1 <<  5) // (SF) Hardwired at 0
#define AT91C_SF_BIT6         ((unsigned int) 0x1 <<  6) // (SF) Hardwired at 1
#define AT91C_SF_BIT7         ((unsigned int) 0x1 <<  7) // (SF) Hardwired at 0
#define AT91C_SF_NVPSIZ       ((unsigned int) 0xF <<  8) // (SF) Nonvolatile Program Memory Size
#define 	AT91C_SF_NVPSIZ_NONE                 ((unsigned int) 0x0 <<  8) // (SF) None
#define 	AT91C_SF_NVPSIZ_32K                  ((unsigned int) 0x3 <<  8) // (SF) 32K Bytes
#define 	AT91C_SF_NVPSIZ_64K                  ((unsigned int) 0x5 <<  8) // (SF) 64K Bytes
#define 	AT91C_SF_NVPSIZ_128K                 ((unsigned int) 0x7 <<  8) // (SF) 128K Bytes
#define 	AT91C_SF_NVPSIZ_256K                 ((unsigned int) 0x11 <<  8) // (SF) 256K Bytes
#define AT91C_SF_NVDSIZ       ((unsigned int) 0xF << 12) // (SF) Nonvolatile Data Memory Size
#define 	AT91C_SF_NVDSIZ_NONE                 ((unsigned int) 0x0 << 12) // (SF) None
#define AT91C_SF_VDSIZ        ((unsigned int) 0xF << 16) // (SF) Volatile Data Memory Size
#define 	AT91C_SF_VDSIZ_NONE                 ((unsigned int) 0x0 << 16) // (SF) None
#define 	AT91C_SF_VDSIZ_1K                   ((unsigned int) 0x3 << 16) // (SF) 1K Bytes
#define 	AT91C_SF_VDSIZ_2K                   ((unsigned int) 0x5 << 16) // (SF) 2K Bytes
#define 	AT91C_SF_VDSIZ_4K                   ((unsigned int) 0x7 << 16) // (SF) 4K Bytes
#define 	AT91C_SF_VDSIZ_8K                   ((unsigned int) 0x11 << 16) // (SF) 8K Bytes
#define AT91C_SF_ARCH         ((unsigned int) 0xFF << 20) // (SF) Chip Architecture
#define 	AT91C_SF_ARCH_AT91x40              ((unsigned int) 0x28 << 20) // (SF) AT91x40yyy
#define 	AT91C_SF_ARCH_AT91x55              ((unsigned int) 0x37 << 20) // (SF) AT91x55yyy
#define 	AT91C_SF_ARCH_AT91x63              ((unsigned int) 0x3F << 20) // (SF) AT91x63yyy
#define AT91C_SF_NVPTYP       ((unsigned int) 0x7 << 28) // (SF) Nonvolatile Program Memory Type
#define 	AT91C_SF_NVPTYP_NVPTYP_M             ((unsigned int) 0x1 << 28) // (SF) 'M' Series or 'F' Series
#define 	AT91C_SF_NVPTYP_NVPTYP_R             ((unsigned int) 0x4 << 28) // (SF) 'R' Series
#define AT91C_SF_EXT          ((unsigned int) 0x1 << 31) // (SF) Extension Flag
// -------- SF_RSR : (SF Offset: 0x8) Reset Status Information -------- 
#define AT91C_SF_RESET        ((unsigned int) 0xFF <<  0) // (SF) Cause of Reset
#define 	AT91C_SF_RESET_WD                   ((unsigned int) 0x35) // (SF) Internal Watchdog
#define 	AT91C_SF_RESET_EXT                  ((unsigned int) 0x6C) // (SF) External Pin
// -------- SF_MMR : (SF Offset: 0xc) Memory Mode Register -------- 
#define AT91C_SF_RAMWU        ((unsigned int) 0x1 <<  0) // (SF) Internal Extended RAM Write Detection
// -------- SF_PMR : (SF Offset: 0x18) Protection Mode Register -------- 
#define AT91C_SF_AIC          ((unsigned int) 0x1 <<  5) // (SF) AIC Protect Mode Enable
#define AT91C_SF_PMRKEY       ((unsigned int) 0xFFFF << 16) // (SF) Protect Mode Register Key

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR External Bus Interface
// *****************************************************************************
typedef struct _AT91S_EBI {
	AT91_REG	 EBI_CSR[8]; 	// Chip-select Register
	AT91_REG	 EBI_RCR; 	// Remap Control Register
	AT91_REG	 EBI_MCR; 	// Memory Control Register
} AT91S_EBI, *AT91PS_EBI;

// -------- EBI_CSR : (EBI Offset: 0x0) Chip Select Register -------- 
#define AT91C_EBI_DBW         ((unsigned int) 0x3 <<  0) // (EBI) Data Bus Width
#define 	AT91C_EBI_DBW_16                   ((unsigned int) 0x1) // (EBI) 16-bit data bus width
#define 	AT91C_EBI_DBW_8                    ((unsigned int) 0x2) // (EBI) 8-bit data bus width
#define AT91C_EBI_NWS         ((unsigned int) 0x7 <<  2) // (EBI) Number of wait states
#define 	AT91C_EBI_NWS_1                    ((unsigned int) 0x0 <<  2) // (EBI) 1 wait state
#define 	AT91C_EBI_NWS_2                    ((unsigned int) 0x1 <<  2) // (EBI) 2 wait state
#define 	AT91C_EBI_NWS_3                    ((unsigned int) 0x2 <<  2) // (EBI) 3 wait state
#define 	AT91C_EBI_NWS_4                    ((unsigned int) 0x3 <<  2) // (EBI) 4 wait state
#define 	AT91C_EBI_NWS_5                    ((unsigned int) 0x4 <<  2) // (EBI) 5 wait state
#define 	AT91C_EBI_NWS_6                    ((unsigned int) 0x5 <<  2) // (EBI) 6 wait state
#define 	AT91C_EBI_NWS_7                    ((unsigned int) 0x6 <<  2) // (EBI) 7 wait state
#define 	AT91C_EBI_NWS_8                    ((unsigned int) 0x7 <<  2) // (EBI) 8 wait state
#define AT91C_EBI_WSE         ((unsigned int) 0x1 <<  5) // (EBI) Wait State Enable
#define AT91C_EBI_PAGES       ((unsigned int) 0x3 <<  7) // (EBI) Pages Size
#define 	AT91C_EBI_PAGES_1M                   ((unsigned int) 0x0 <<  7) // (EBI) 1M Byte
#define 	AT91C_EBI_PAGES_4M                   ((unsigned int) 0x1 <<  7) // (EBI) 4M Byte
#define 	AT91C_EBI_PAGES_16M                  ((unsigned int) 0x2 <<  7) // (EBI) 16M Byte
#define 	AT91C_EBI_PAGES_64M                  ((unsigned int) 0x3 <<  7) // (EBI) 64M Byte
#define AT91C_EBI_TDF         ((unsigned int) 0x7 <<  9) // (EBI) Data Float Output Time
#define 	AT91C_EBI_TDF_0                    ((unsigned int) 0x0 <<  9) // (EBI) 1 TDF
#define 	AT91C_EBI_TDF_1                    ((unsigned int) 0x1 <<  9) // (EBI) 2 TDF
#define 	AT91C_EBI_TDF_2                    ((unsigned int) 0x2 <<  9) // (EBI) 3 TDF
#define 	AT91C_EBI_TDF_3                    ((unsigned int) 0x3 <<  9) // (EBI) 4 TDF
#define 	AT91C_EBI_TDF_4                    ((unsigned int) 0x4 <<  9) // (EBI) 5 TDF
#define 	AT91C_EBI_TDF_5                    ((unsigned int) 0x5 <<  9) // (EBI) 6 TDF
#define 	AT91C_EBI_TDF_6                    ((unsigned int) 0x6 <<  9) // (EBI) 7 TDF
#define 	AT91C_EBI_TDF_7                    ((unsigned int) 0x7 <<  9) // (EBI) 8 TDF
#define AT91C_EBI_BAT         ((unsigned int) 0x1 << 12) // (EBI) Byte Access Type
#define AT91C_EBI_CSEN        ((unsigned int) 0x1 << 13) // (EBI) Chip Select Enable
#define AT91C_EBI_BA          ((unsigned int) 0xFFF << 20) // (EBI) Base Address
// -------- EBI_RCR : (EBI Offset: 0x20) Remap Control Register -------- 
#define AT91C_EBI_RCB         ((unsigned int) 0x1 <<  0) // (EBI) 0 = No effect. 1 = Cancels the remapping (performed at reset) of the page zero memory devices.
// -------- EBI_MCR : (EBI Offset: 0x24) Memory Control Register -------- 
#define AT91C_EBI_ALE         ((unsigned int) 0x7 <<  0) // (EBI) Address Line Enable
#define 	AT91C_EBI_ALE_16M                  ((unsigned int) 0x0) // (EBI) Valid Address Bits = A20, A21, A22, A23  Max Addressable Space = 16M Bytes Valid Chip Select=None 
#define 	AT91C_EBI_ALE_8M                   ((unsigned int) 0x4) // (EBI) Valid Address Bits = A20, A21, A22  Max Addressable Space = 8M Bytes Valid Chip Select = CS4 
#define 	AT91C_EBI_ALE_4M                   ((unsigned int) 0x5) // (EBI) Valid Address Bits = A20, A21  Max Addressable Space = 4M Bytes Valid Chip Select = CS4, CS5 
#define 	AT91C_EBI_ALE_2M                   ((unsigned int) 0x6) // (EBI) Valid Address Bits = A20  Max Addressable Space = 2M Bytes Valid Chip Select = CS4, CS5, CS6 
#define 	AT91C_EBI_ALE_1M                   ((unsigned int) 0x7) // (EBI) Valid Address Bits = None  Max Addressable Space = 1M Byte Valid Chip Select = CS4, CS5, CS6, CS7 
#define AT91C_EBI_DRP         ((unsigned int) 0x1 <<  4) // (EBI) 

// *****************************************************************************
//               REGISTER ADDRESS DEFINITION FOR AT91R40008
// *****************************************************************************
// ========== Register definition for AIC peripheral ========== 
#define AT91C_AIC_EOICR ((AT91_REG *) 	0xFFFFF130) // (AIC) End of Interrupt Command Register
#define AT91C_AIC_ICCR  ((AT91_REG *) 	0xFFFFF128) // (AIC) Interrupt Clear Command Register
#define AT91C_AIC_IECR  ((AT91_REG *) 	0xFFFFF120) // (AIC) Interrupt Enable Command Register
#define AT91C_AIC_SVR   ((AT91_REG *) 	0xFFFFF080) // (AIC) Source Vector egister
#define AT91C_AIC_SMR   ((AT91_REG *) 	0xFFFFF000) // (AIC) Source Mode egister
#define AT91C_AIC_SPU   ((AT91_REG *) 	0xFFFFF134) // (AIC) Spurious Vector Register
#define AT91C_AIC_FVR   ((AT91_REG *) 	0xFFFFF104) // (AIC) FIQ Vector Register
#define AT91C_AIC_IVR   ((AT91_REG *) 	0xFFFFF100) // (AIC) IRQ Vector Register
#define AT91C_AIC_ISR   ((AT91_REG *) 	0xFFFFF108) // (AIC) Interrupt Status Register
#define AT91C_AIC_IMR   ((AT91_REG *) 	0xFFFFF110) // (AIC) Interrupt Mask Register
#define AT91C_AIC_ISCR  ((AT91_REG *) 	0xFFFFF12C) // (AIC) Interrupt Set Command Register
#define AT91C_AIC_IPR   ((AT91_REG *) 	0xFFFFF10C) // (AIC) Interrupt Pending Register
#define AT91C_AIC_CISR  ((AT91_REG *) 	0xFFFFF114) // (AIC) Core Interrupt Status Register
#define AT91C_AIC_IDCR  ((AT91_REG *) 	0xFFFFF124) // (AIC) Interrupt Disable Command egister
// ========== Register definition for WD peripheral ========== 
#define AT91C_WD_SR     ((AT91_REG *) 	0xFFFF800C) // (WD) Status Register
#define AT91C_WD_CMR    ((AT91_REG *) 	0xFFFF8004) // (WD) Clock Mode Register
#define AT91C_WD_CR     ((AT91_REG *) 	0xFFFF8008) // (WD) Control Register
#define AT91C_WD_OMR    ((AT91_REG *) 	0xFFFF8000) // (WD) Overflow Mode Register
// ========== Register definition for PS peripheral ========== 
#define AT91C_PS_PCDR   ((AT91_REG *) 	0xFFFF4008) // (PS) Peripheral Clock Disable Register
#define AT91C_PS_CR     ((AT91_REG *) 	0xFFFF4000) // (PS) Control Register
#define AT91C_PS_PCSR   ((AT91_REG *) 	0xFFFF400C) // (PS) Peripheral Clock Status Register
#define AT91C_PS_PCER   ((AT91_REG *) 	0xFFFF4004) // (PS) Peripheral Clock Enable Register
// ========== Register definition for PIO peripheral ========== 
#define AT91C_PIO_MDSR  ((AT91_REG *) 	0xFFFF0058) // (PIO) Multi-driver Status Register
#define AT91C_PIO_IFSR  ((AT91_REG *) 	0xFFFF0028) // (PIO) Input Filter Status Register
#define AT91C_PIO_IFER  ((AT91_REG *) 	0xFFFF0020) // (PIO) Input Filter Enable Register
#define AT91C_PIO_OSR   ((AT91_REG *) 	0xFFFF0018) // (PIO) Output Status Register
#define AT91C_PIO_OER   ((AT91_REG *) 	0xFFFF0010) // (PIO) Output Enable Register
#define AT91C_PIO_PSR   ((AT91_REG *) 	0xFFFF0008) // (PIO) PIO Status Register
#define AT91C_PIO_PDSR  ((AT91_REG *) 	0xFFFF003C) // (PIO) Pin Data Status Register
#define AT91C_PIO_CODR  ((AT91_REG *) 	0xFFFF0034) // (PIO) Clear Output Data Register
#define AT91C_PIO_IFDR  ((AT91_REG *) 	0xFFFF0024) // (PIO) Input Filter Disable Register
#define AT91C_PIO_MDER  ((AT91_REG *) 	0xFFFF0050) // (PIO) Multi-driver Enable Register
#define AT91C_PIO_IMR   ((AT91_REG *) 	0xFFFF0048) // (PIO) Interrupt Mask Register
#define AT91C_PIO_IER   ((AT91_REG *) 	0xFFFF0040) // (PIO) Interrupt Enable Register
#define AT91C_PIO_ODSR  ((AT91_REG *) 	0xFFFF0038) // (PIO) Output Data Status Register
#define AT91C_PIO_SODR  ((AT91_REG *) 	0xFFFF0030) // (PIO) Set Output Data Register
#define AT91C_PIO_PER   ((AT91_REG *) 	0xFFFF0000) // (PIO) PIO Enable Register
#define AT91C_PIO_MDDR  ((AT91_REG *) 	0xFFFF0054) // (PIO) Multi-driver Disable Register
#define AT91C_PIO_ISR   ((AT91_REG *) 	0xFFFF004C) // (PIO) Interrupt Status Register
#define AT91C_PIO_IDR   ((AT91_REG *) 	0xFFFF0044) // (PIO) Interrupt Disable Register
#define AT91C_PIO_PDR   ((AT91_REG *) 	0xFFFF0004) // (PIO) PIO Disable Register
#define AT91C_PIO_ODR   ((AT91_REG *) 	0xFFFF0014) // (PIO) Output Disable Registerr
// ========== Register definition for TC2 peripheral ========== 
#define AT91C_TC2_IDR   ((AT91_REG *) 	0xFFFE00A8) // (TC2) Interrupt Disable Register
#define AT91C_TC2_SR    ((AT91_REG *) 	0xFFFE00A0) // (TC2) Status Register
#define AT91C_TC2_RB    ((AT91_REG *) 	0xFFFE0098) // (TC2) Register B
#define AT91C_TC2_CV    ((AT91_REG *) 	0xFFFE0090) // (TC2) Counter Value
#define AT91C_TC2_CCR   ((AT91_REG *) 	0xFFFE0080) // (TC2) Channel Control Register
#define AT91C_TC2_IMR   ((AT91_REG *) 	0xFFFE00AC) // (TC2) Interrupt Mask Register
#define AT91C_TC2_IER   ((AT91_REG *) 	0xFFFE00A4) // (TC2) Interrupt Enable Register
#define AT91C_TC2_RC    ((AT91_REG *) 	0xFFFE009C) // (TC2) Register C
#define AT91C_TC2_RA    ((AT91_REG *) 	0xFFFE0094) // (TC2) Register A
#define AT91C_TC2_CMR   ((AT91_REG *) 	0xFFFE0084) // (TC2) Channel Mode Register
// ========== Register definition for TC1 peripheral ========== 
#define AT91C_TC1_IDR   ((AT91_REG *) 	0xFFFE0068) // (TC1) Interrupt Disable Register
#define AT91C_TC1_SR    ((AT91_REG *) 	0xFFFE0060) // (TC1) Status Register
#define AT91C_TC1_RB    ((AT91_REG *) 	0xFFFE0058) // (TC1) Register B
#define AT91C_TC1_CV    ((AT91_REG *) 	0xFFFE0050) // (TC1) Counter Value
#define AT91C_TC1_CCR   ((AT91_REG *) 	0xFFFE0040) // (TC1) Channel Control Register
#define AT91C_TC1_IMR   ((AT91_REG *) 	0xFFFE006C) // (TC1) Interrupt Mask Register
#define AT91C_TC1_IER   ((AT91_REG *) 	0xFFFE0064) // (TC1) Interrupt Enable Register
#define AT91C_TC1_RC    ((AT91_REG *) 	0xFFFE005C) // (TC1) Register C
#define AT91C_TC1_RA    ((AT91_REG *) 	0xFFFE0054) // (TC1) Register A
#define AT91C_TC1_CMR   ((AT91_REG *) 	0xFFFE0044) // (TC1) Channel Mode Register
// ========== Register definition for TC0 peripheral ========== 
#define AT91C_TC0_IDR   ((AT91_REG *) 	0xFFFE0028) // (TC0) Interrupt Disable Register
#define AT91C_TC0_SR    ((AT91_REG *) 	0xFFFE0020) // (TC0) Status Register
#define AT91C_TC0_RB    ((AT91_REG *) 	0xFFFE0018) // (TC0) Register B
#define AT91C_TC0_CV    ((AT91_REG *) 	0xFFFE0010) // (TC0) Counter Value
#define AT91C_TC0_CCR   ((AT91_REG *) 	0xFFFE0000) // (TC0) Channel Control Register
#define AT91C_TC0_IMR   ((AT91_REG *) 	0xFFFE002C) // (TC0) Interrupt Mask Register
#define AT91C_TC0_IER   ((AT91_REG *) 	0xFFFE0024) // (TC0) Interrupt Enable Register
#define AT91C_TC0_RC    ((AT91_REG *) 	0xFFFE001C) // (TC0) Register C
#define AT91C_TC0_RA    ((AT91_REG *) 	0xFFFE0014) // (TC0) Register A
#define AT91C_TC0_CMR   ((AT91_REG *) 	0xFFFE0004) // (TC0) Channel Mode Register
// ========== Register definition for TCB0 peripheral ========== 
#define AT91C_TCB0_BCR  ((AT91_REG *) 	0xFFFE00C0) // (TCB0) TC Block Control Register
#define AT91C_TCB0_BMR  ((AT91_REG *) 	0xFFFE00C4) // (TCB0) TC Block Mode Register
// ========== Register definition for PDC_US1 peripheral ========== 
#define AT91C_US1_TPR   ((AT91_REG *) 	0xFFFC4038) // (PDC_US1) Transmit Pointer Register
#define AT91C_US1_RPR   ((AT91_REG *) 	0xFFFC4030) // (PDC_US1) Receive Pointer Register
#define AT91C_US1_TCR   ((AT91_REG *) 	0xFFFC403C) // (PDC_US1) Transmit Counter Register
#define AT91C_US1_RCR   ((AT91_REG *) 	0xFFFC4034) // (PDC_US1) Receive Counter Register
// ========== Register definition for US1 peripheral ========== 
#define AT91C_US1_RTOR  ((AT91_REG *) 	0xFFFCC024) // (US1) Receiver Time-out Register
#define AT91C_US1_THR   ((AT91_REG *) 	0xFFFCC01C) // (US1) Transmitter Holding Register
#define AT91C_US1_CSR   ((AT91_REG *) 	0xFFFCC014) // (US1) Channel Status Register
#define AT91C_US1_IDR   ((AT91_REG *) 	0xFFFCC00C) // (US1) Interrupt Disable Register
#define AT91C_US1_MR    ((AT91_REG *) 	0xFFFCC004) // (US1) Mode Register
#define AT91C_US1_TTGR  ((AT91_REG *) 	0xFFFCC028) // (US1) Transmitter Time-guard Register
#define AT91C_US1_BRGR  ((AT91_REG *) 	0xFFFCC020) // (US1) Baud Rate Generator Register
#define AT91C_US1_RHR   ((AT91_REG *) 	0xFFFCC018) // (US1) Receiver Holding Register
#define AT91C_US1_IMR   ((AT91_REG *) 	0xFFFCC010) // (US1) Interrupt Mask Register
#define AT91C_US1_IER   ((AT91_REG *) 	0xFFFCC008) // (US1) Interrupt Enable Register
#define AT91C_US1_CR    ((AT91_REG *) 	0xFFFCC000) // (US1) Control Register
// ========== Register definition for PDC_US0 peripheral ========== 
#define AT91C_US0_TPR   ((AT91_REG *) 	0xFFFC0038) // (PDC_US0) Transmit Pointer Register
#define AT91C_US0_RPR   ((AT91_REG *) 	0xFFFC0030) // (PDC_US0) Receive Pointer Register
#define AT91C_US0_TCR   ((AT91_REG *) 	0xFFFC003C) // (PDC_US0) Transmit Counter Register
#define AT91C_US0_RCR   ((AT91_REG *) 	0xFFFC0034) // (PDC_US0) Receive Counter Register
// ========== Register definition for US0 peripheral ========== 
#define AT91C_US0_RTOR  ((AT91_REG *) 	0xFFFD0024) // (US0) Receiver Time-out Register
#define AT91C_US0_THR   ((AT91_REG *) 	0xFFFD001C) // (US0) Transmitter Holding Register
#define AT91C_US0_CSR   ((AT91_REG *) 	0xFFFD0014) // (US0) Channel Status Register
#define AT91C_US0_IDR   ((AT91_REG *) 	0xFFFD000C) // (US0) Interrupt Disable Register
#define AT91C_US0_MR    ((AT91_REG *) 	0xFFFD0004) // (US0) Mode Register
#define AT91C_US0_TTGR  ((AT91_REG *) 	0xFFFD0028) // (US0) Transmitter Time-guard Register
#define AT91C_US0_BRGR  ((AT91_REG *) 	0xFFFD0020) // (US0) Baud Rate Generator Register
#define AT91C_US0_RHR   ((AT91_REG *) 	0xFFFD0018) // (US0) Receiver Holding Register
#define AT91C_US0_IMR   ((AT91_REG *) 	0xFFFD0010) // (US0) Interrupt Mask Register
#define AT91C_US0_IER   ((AT91_REG *) 	0xFFFD0008) // (US0) Interrupt Enable Register
#define AT91C_US0_CR    ((AT91_REG *) 	0xFFFD0000) // (US0) Control Register
// ========== Register definition for SF peripheral ========== 
#define AT91C_SF_PMR    ((AT91_REG *) 	0xFFF00018) // (SF) Protect Mode Register
#define AT91C_SF_RSR    ((AT91_REG *) 	0xFFF00008) // (SF) Reset Status Register
#define AT91C_SF_CIDR   ((AT91_REG *) 	0xFFF00000) // (SF) Chip ID Register
#define AT91C_SF_MMR    ((AT91_REG *) 	0xFFF0000C) // (SF) Memory Mode Register
#define AT91C_SF_EXID   ((AT91_REG *) 	0xFFF00004) // (SF) Chip ID Extension Register
// ========== Register definition for EBI peripheral ========== 
#define AT91C_EBI_RCR   ((AT91_REG *) 	0xFFE00020) // (EBI) Remap Control Register
#define AT91C_EBI_CSR   ((AT91_REG *) 	0xFFE00000) // (EBI) Chip-select Register
#define AT91C_EBI_MCR   ((AT91_REG *) 	0xFFE00024) // (EBI) Memory Control Register

// *****************************************************************************
//               PIO DEFINITIONS FOR AT91R40008
// *****************************************************************************
#define AT91C_PIO_P0         ((unsigned int) 1 <<  0) // Pin Controlled by P0
#define AT91C_P0_TCLK0    ((unsigned int) AT91C_PIO_P0) //  Timer 0 Clock signal
#define AT91C_PIO_P1         ((unsigned int) 1 <<  1) // Pin Controlled by P1
#define AT91C_P1_TIOA0    ((unsigned int) AT91C_PIO_P1) //  Timer 0 Signal A
#define AT91C_PIO_P10        ((unsigned int) 1 << 10) // Pin Controlled by P10
#define AT91C_P10_IRQ1     ((unsigned int) AT91C_PIO_P10) //  External Interrupt 1
#define AT91C_PIO_P11        ((unsigned int) 1 << 11) // Pin Controlled by P11
#define AT91C_P11_IRQ2     ((unsigned int) AT91C_PIO_P11) //  External Interrupt 2
#define AT91C_PIO_P12        ((unsigned int) 1 << 12) // Pin Controlled by P12
#define AT91C_P12_FIQ      ((unsigned int) AT91C_PIO_P12) //  Fast External Interrupt
#define AT91C_PIO_P13        ((unsigned int) 1 << 13) // Pin Controlled by P13
#define AT91C_P13_SCK0     ((unsigned int) AT91C_PIO_P13) //  USART 0 Serial Clock
#define AT91C_PIO_P14        ((unsigned int) 1 << 14) // Pin Controlled by P14
#define AT91C_P14_TXD0     ((unsigned int) AT91C_PIO_P14) //  USART 0 Transmit Data
#define AT91C_PIO_P15        ((unsigned int) 1 << 15) // Pin Controlled by P15
#define AT91C_P15_RXD0     ((unsigned int) AT91C_PIO_P15) //  USART 0 Receive Data
#define AT91C_PIO_P16        ((unsigned int) 1 << 16) // Pin Controlled by P16
#define AT91C_PIO_P17        ((unsigned int) 1 << 17) // Pin Controlled by P17
#define AT91C_PIO_P18        ((unsigned int) 1 << 18) // Pin Controlled by P18
#define AT91C_PIO_P19        ((unsigned int) 1 << 19) // Pin Controlled by P19
#define AT91C_PIO_P2         ((unsigned int) 1 <<  2) // Pin Controlled by P2
#define AT91C_P2_TIOB0    ((unsigned int) AT91C_PIO_P2) //  Timer 0 Signal B
#define AT91C_PIO_P20        ((unsigned int) 1 << 20) // Pin Controlled by P20
#define AT91C_P20_SCK1     ((unsigned int) AT91C_PIO_P20) //  USART 1 Serial Clock
#define AT91C_PIO_P21        ((unsigned int) 1 << 21) // Pin Controlled by P21
#define AT91C_P21_TXD1     ((unsigned int) AT91C_PIO_P21) //  USART 1 Transmit Data
#define AT91C_P21_NTRI     ((unsigned int) AT91C_PIO_P21) //  Tri-state Mode
#define AT91C_PIO_P22        ((unsigned int) 1 << 22) // Pin Controlled by P22
#define AT91C_P22_RXD1     ((unsigned int) AT91C_PIO_P22) //  USART 1 Receive Data
#define AT91C_PIO_P23        ((unsigned int) 1 << 23) // Pin Controlled by P23
#define AT91C_PIO_P24        ((unsigned int) 1 << 24) // Pin Controlled by P24
#define AT91C_P24_BMS      ((unsigned int) AT91C_PIO_P24) //  Boot Mode Select
#define AT91C_PIO_P25        ((unsigned int) 1 << 25) // Pin Controlled by P25
#define AT91C_P25_MCKO     ((unsigned int) AT91C_PIO_P25) //  Master Clock Out
#define AT91C_PIO_P26        ((unsigned int) 1 << 26) // Pin Controlled by P26
#define AT91C_P26_NCS2     ((unsigned int) AT91C_PIO_P26) //  Chip Select 2
#define AT91C_PIO_P27        ((unsigned int) 1 << 27) // Pin Controlled by P27
#define AT91C_P27_NCS3     ((unsigned int) AT91C_PIO_P27) //  Chip Select 3
#define AT91C_PIO_P28        ((unsigned int) 1 << 28) // Pin Controlled by P28
#define AT91C_P28_A20      ((unsigned int) AT91C_PIO_P28) //  Address line A20
#define AT91C_P28_NCS7     ((unsigned int) AT91C_PIO_P28) //  Chip Select 7
#define AT91C_PIO_P29        ((unsigned int) 1 << 29) // Pin Controlled by P29
#define AT91C_P29_A21      ((unsigned int) AT91C_PIO_P29) //  Address line A21
#define AT91C_P29_NCS6     ((unsigned int) AT91C_PIO_P29) //  Chip Select 6
#define AT91C_PIO_P3         ((unsigned int) 1 <<  3) // Pin Controlled by P3
#define AT91C_P3_TCLK1    ((unsigned int) AT91C_PIO_P3) //  Timer 1 Clock signal
#define AT91C_PIO_P30        ((unsigned int) 1 << 30) // Pin Controlled by P30
#define AT91C_P30_A22      ((unsigned int) AT91C_PIO_P30) //  Address line A22
#define AT91C_P30_NCS5     ((unsigned int) AT91C_PIO_P30) //  Chip Select 5
#define AT91C_PIO_P31        ((unsigned int) 1 << 31) // Pin Controlled by P31
#define AT91C_P31_A23      ((unsigned int) AT91C_PIO_P31) //  Address line A23
#define AT91C_P31_NCS4     ((unsigned int) AT91C_PIO_P31) //  Chip Select 4
#define AT91C_PIO_P4         ((unsigned int) 1 <<  4) // Pin Controlled by P4
#define AT91C_P4_TIOA1    ((unsigned int) AT91C_PIO_P4) //  Timer 1 Signal A
#define AT91C_PIO_P5         ((unsigned int) 1 <<  5) // Pin Controlled by P5
#define AT91C_P5_TIOB1    ((unsigned int) AT91C_PIO_P5) //  Timer 1 Signal B
#define AT91C_PIO_P6         ((unsigned int) 1 <<  6) // Pin Controlled by P6
#define AT91C_P6_TCLK2    ((unsigned int) AT91C_PIO_P6) //  Timer 2 Clock signal
#define AT91C_PIO_P7         ((unsigned int) 1 <<  7) // Pin Controlled by P7
#define AT91C_P7_TIOA2    ((unsigned int) AT91C_PIO_P7) //  Timer 2 Signal A
#define AT91C_PIO_P8         ((unsigned int) 1 <<  8) // Pin Controlled by P8
#define AT91C_P8_TIOB2    ((unsigned int) AT91C_PIO_P8) //  Timer 2 Signal B
#define AT91C_PIO_P9         ((unsigned int) 1 <<  9) // Pin Controlled by P9
#define AT91C_P9_IRQ0     ((unsigned int) AT91C_PIO_P9) //  External Interrupt 0

// *****************************************************************************
//               PERIPHERAL ID DEFINITIONS FOR AT91R40008
// *****************************************************************************
#define AT91C_ID_FIQ    ((unsigned int)  0) // Advanced Interrupt Controller (FIQ)
#define AT91C_ID_SYS    ((unsigned int)  1) // SWI
#define AT91C_ID_US0    ((unsigned int)  2) // USART 0
#define AT91C_ID_US1    ((unsigned int)  3) // USART 1
#define AT91C_ID_TC0    ((unsigned int)  4) // Timer Counter 0
#define AT91C_ID_TC1    ((unsigned int)  5) // Timer Counter 1
#define AT91C_ID_TC2    ((unsigned int)  6) // Timer Counter 2
#define AT91C_ID_WD     ((unsigned int)  7) // Watchdog Timer
#define AT91C_ID_PIO    ((unsigned int)  8) // Parallel IO Controller
#define AT91C_ID_IRQ0   ((unsigned int) 16) // Advanced Interrupt Controller (IRQ0)
#define AT91C_ID_IRQ1   ((unsigned int) 17) // Advanced Interrupt Controller (IRQ1)
#define AT91C_ID_IRQ2   ((unsigned int) 18) // Advanced Interrupt Controller (IRQ2)

// *****************************************************************************
//               BASE ADDRESS DEFINITIONS FOR AT91R40008
// *****************************************************************************
#define AT91C_BASE_AIC       ((AT91PS_AIC) 	0xFFFFF000) // (AIC) Base Address
#define AT91C_BASE_WD        ((AT91PS_WD) 	0xFFFF8000) // (WD) Base Address
#define AT91C_BASE_PS        ((AT91PS_PS) 	0xFFFF4000) // (PS) Base Address
#define AT91C_BASE_PIO       ((AT91PS_PIO) 	0xFFFF0000) // (PIO) Base Address
#define AT91C_BASE_TC2       ((AT91PS_TC) 	0xFFFE0080) // (TC2) Base Address
#define AT91C_BASE_TC1       ((AT91PS_TC) 	0xFFFE0040) // (TC1) Base Address
#define AT91C_BASE_TC0       ((AT91PS_TC) 	0xFFFE0000) // (TC0) Base Address
#define AT91C_BASE_TCB0      ((AT91PS_TCB) 	0xFFFE0000) // (TCB0) Base Address
#define AT91C_BASE_PDC_US1   ((AT91PS_PDC) 	0xFFFC4030) // (PDC_US1) Base Address
#define AT91C_BASE_US1       ((AT91PS_USART) 	0xFFFCC000) // (US1) Base Address
#define AT91C_BASE_PDC_US0   ((AT91PS_PDC) 	0xFFFC0030) // (PDC_US0) Base Address
#define AT91C_BASE_US0       ((AT91PS_USART) 	0xFFFD0000) // (US0) Base Address
#define AT91C_BASE_SF        ((AT91PS_SF) 	0xFFF00000) // (SF) Base Address
#define AT91C_BASE_EBI       ((AT91PS_EBI) 	0xFFE00000) // (EBI) Base Address

// *****************************************************************************
//               MEMORY MAPPING DEFINITIONS FOR AT91R40008
// *****************************************************************************
#define AT91C_SRAM_BEFORE_REMAP	 ((char *) 	0x00300000) // Internal SRAM before remap base address
#define AT91C_SRAM_BEFORE_REMAP_SIZE	 ((unsigned int) 0x00040000) // Internal SRAM before remap size in byte (256 Kbyte)
#define AT91C_SRAM_AFTER_REMAP	 ((char *) 	0x00000000) // Internal SRAM after remap base address
#define AT91C_SRAM_AFTER_REMAP_SIZE	 ((unsigned int) 0x00040000) // Internal SRAM after remap size in byte (256 Kbyte)

#endif
