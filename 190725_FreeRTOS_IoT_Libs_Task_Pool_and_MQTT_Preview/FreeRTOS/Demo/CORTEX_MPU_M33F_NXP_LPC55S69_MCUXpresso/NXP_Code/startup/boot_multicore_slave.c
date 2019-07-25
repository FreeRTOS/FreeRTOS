//*****************************************************************************
// boot_multicore_slave.c
//
// Provides functions to boot slave core in LPC55xx multicore system
//
// Version : 190215
//
//*****************************************************************************
//
// Copyright(C) NXP Semiconductors, 2019
// All rights reserved.
//
// Software that is described herein is for illustrative purposes only
// which provides customers with programming information regarding the
// LPC products.  This software is supplied "AS IS" without any warranties of
// any kind, and NXP Semiconductors and its licensor disclaim any and
// all warranties, express or implied, including all implied warranties of
// merchantability, fitness for a particular purpose and non-infringement of
// intellectual property rights.  NXP Semiconductors assumes no responsibility
// or liability for the use of the software, conveys no license or rights under any
// patent, copyright, mask work right, or any other intellectual property rights in
// or to any products. NXP Semiconductors reserves the right to make changes
// in the software without notification. NXP Semiconductors also makes no
// representation or warranty that such application will be suitable for the
// specified use without further testing or modification.
//
// Permission to use, copy, modify, and distribute this software and its
// documentation is hereby granted, under NXP Semiconductors' and its
// licensor's relevant copyrights in the software, without fee, provided that it
// is used in conjunction with NXP Semiconductors microcontrollers.  This
// copyright, permission, and disclaimer notice must appear in all copies of
// this code.
//*****************************************************************************

#if defined (__MULTICORE_MASTER)

#include <stdint.h>

// ==================================================================
// Define registers related to multicore CPU Control and setup
// ==================================================================
#define SYSCON_BASE				  ((uint32_t) 0x50000000)
#define CPUCTRL                   (((volatile uint32_t *) (SYSCON_BASE + 0x800)))
#define CPBOOT					  (((volatile uint32_t *) (SYSCON_BASE + 0x804)))
#define CPSTACK					  (((volatile uint32_t *) (SYSCON_BASE + 0x808)))
#define CPSTAT					  (((volatile uint32_t *) (SYSCON_BASE + 0x80C)))
#define CPUCTRL_KEY               ((uint32_t)(0x0000C0C4 << 16))
#define CORE1_CLK_ENA             (1<<3)
#define CORE1_RESET_ENA           (1<<5)


// ==================================================================
// Function to boot the slave (core 1)
// ==================================================================
void slave_core1_boot(uint32_t *coentry, uint32_t *costackptr) {

	volatile uint32_t *u32REG, u32Val;

    // Load the slave's stack pointer value
	*CPSTACK = (uint32_t) costackptr;
	// Load address of the slave code in memory (for slave's VTOR)
	*CPBOOT =  (uint32_t) coentry;

	// Read CPU control register and update to start slave execution
    u32REG = (uint32_t *) CPUCTRL;
    u32Val = *u32REG;
    // Enable slave clock and reset
    u32Val |= (CPUCTRL_KEY | ((CORE1_CLK_ENA | CORE1_RESET_ENA) & 0x7F));
    *u32REG = u32Val;
    // Clear slave reset
    u32Val &= ~CORE1_RESET_ENA;
    *u32REG = u32Val;
    // Slave is now executing
}

// ==================================================================
// Address of slave code in memory - provided by linker script
extern uint8_t __core_m33slave_START__;
// ==================================================================

// ==================================================================
// Top level function to boot the slave core
// ==================================================================
void boot_multicore_slave(void) {

	// Get the address of the slave code in memory
	uint32_t *slavevectortable_ptr = (uint32_t *)&__core_m33slave_START__;

    // Get initial address for slave's stack pointer
    volatile  unsigned int spaddr;
    spaddr = *slavevectortable_ptr;

    // Boot the slave - passing address of code and stack pointer
    slave_core1_boot(slavevectortable_ptr, (uint32_t *)spaddr);

}
#endif //defined (__MULTICORE_MASTER)
