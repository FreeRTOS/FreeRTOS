/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Provides the low-level initialization function that called on chip startup.
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "compiler.h"
#include "peripherals/aic.h"
#include "cortexa5_interrupts.h"
#include <stdio.h>

/*----------------------------------------------------------------------------
 *        Constants
 *----------------------------------------------------------------------------*/

/* IFSR status */
static const char* _prefetch_abort_status[32] = {
	NULL,
	NULL,
	"debug event",
	"access flag fault, section",
	NULL,
	"translation fault, section",
	"access flag fault, page",
	"translation fault, page",
	"synchronous external abort",
	"domain fault, section",
	NULL,
	"domain fault, page",
	"L1 translation, synchronous external abort",
	"permission fault, section",
	"L2 translation, synchronous external abort",
	"permission fault, page",
};

/* DFSR status */
static const char* _data_abort_status[32] = {
	NULL,
	"alignment fault",
	"debug event",
	"access flag fault, section",
	"instruction cache maintenance fault",
	"translation fault, section",
	"access flag fault, page",
	"translation fault, page",
	"synchronous external abort, nontranslation",
	"domain fault, section",
	NULL,
	"domain fault, page",
	"1st level translation, synchronous external abort",
	"permission fault, section",
	"2nd level translation, synchronous external abort",
	"permission fault, page",
	NULL,
	NULL,
	NULL,
	NULL,
	NULL,
	NULL,
	"asynchronous external abort"
};

/*----------------------------------------------------------------------------
 *        Functions Prototypes
 *----------------------------------------------------------------------------*/

void default_undefined_instruction_irq_handler(void);
void default_software_interrupt_irq_handler(void);
void default_data_abort_irq_handler(void);
void default_prefetch_abort_irq_handler(void);

#pragma weak undefined_instruction_irq_handler=default_undefined_instruction_irq_handler
#pragma weak software_interrupt_irq_handler=default_software_interrupt_irq_handler
#pragma weak data_abort_irq_handler=default_data_abort_irq_handler
#pragma weak prefetch_abort_irq_handler=default_prefetch_abort_irq_handler

/*----------------------------------------------------------------------------
 *        Functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Default handler for "Undefined Instruction" exception
 */
void default_undefined_instruction_irq_handler(void)
{
	printf("\n\r");
	printf("#####################\n\r");
	printf("Undefined Instruction\n\r");
	printf("#####################\n\r");

	asm("bkpt #0");
	while(1);
}


/**
 * \brief Default handler for "Software Interrupt" exception
 */
void default_software_interrupt_irq_handler(void)
{
	printf("\n\r");
	printf("##################\n\r");
	printf("Software Interrupt\n\r");
	printf("##################\n\r");

	asm("bkpt #0");
	while(1);
}

/**
 * \brief Default handler for "Data Abort" exception
 */
void default_data_abort_irq_handler(void)
{
	uint32_t v1, v2, dfsr;

	asm("mrc p15, 0, %0, c5, c0, 0" : "=r"(v1));
	asm("mrc p15, 0, %0, c6, c0, 0" : "=r"(v2));

	printf("\n\r");
	printf("####################\n\r");
	dfsr = ((v1 >> 4) & 0x0F);
	printf("Data Fault occured in %x domain\n\r", (unsigned int)dfsr);
	dfsr = (((v1 & 0x400) >> 6) | (v1 & 0x0F));
	if (_data_abort_status[dfsr])
		printf("Data Fault reason is: %s\n\r", _data_abort_status[dfsr]);
	else
		printf("Data Fault reason is unknown\n\r");
	printf("Data Fault occured at address: 0x%08x\n\n\r", (unsigned int)v2);
	printf("Data Fault status register value: 0x%x\n\r", (unsigned int)v1);
	printf("####################\n\r");

	asm("bkpt #0");
	while(1);
}

/**
 * \brief Default handler for "Prefetch Abort" exception
 */
void default_prefetch_abort_irq_handler(void)
{
	uint32_t v1, v2, ifsr;

	asm("mrc p15, 0, %0, c5, c0, 1" : "=r"(v1));
	asm("mrc p15, 0, %0, c6, c0, 2" : "=r"(v2));

	printf("\n\r");
	printf("####################\n\r");
	ifsr = (((v1 & 0x400) >> 6) | (v1 & 0x0F));
	if (_prefetch_abort_status[ifsr])
		printf("Prefetch Fault reason is: %s\n\r", _prefetch_abort_status[ifsr]);
	else
		printf("Prefetch Fault reason is unknown\n\r");
	printf("prefetch Fault occured at address: 0x%08x\n\n\r", (unsigned int)v2);
	printf("Prefetch Fault status register value: 0x%x\n\r", (unsigned int)v1);
	printf("####################\n\r");

	asm("bkpt #0");
	while(1);
}
