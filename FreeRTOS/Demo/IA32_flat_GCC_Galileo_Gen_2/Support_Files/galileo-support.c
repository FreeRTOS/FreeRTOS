/*--------------------------------------------------------------------
 Copyright(c) 2015 Intel Corporation. All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions
 are met:

 * Redistributions of source code must retain the above copyright
 notice, this list of conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright
 notice, this list of conditions and the following disclaimer in
 the documentation and/or other materials provided with the
 distribution.
 * Neither the name of Intel Corporation nor the names of its
 contributors may be used to endorse or promote products derived
 from this software without specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 --------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
 * Any required includes
 *------------------------------------------------------------------------
 */
#include "multiboot.h"
#include "galileo_support.h"

/*-----------------------------------------------------------------------
 * Any required local definitions
 *------------------------------------------------------------------------
 */
#ifndef NULL
	#define NULL (void *)0
#endif

#define MUTEX_WAIT_TIME	(( TickType_t ) 8 )

/*-----------------------------------------------------------------------
 * Function prototypes
 *------------------------------------------------------------------------
 */
extern void *memcpy( void *pvDest, const void *pvSource, unsigned long ulBytes );

/*-----------------------------------------------------------------------
 * Global variables
 *------------------------------------------------------------------------
 */
uint32_t bootinfo = 1UL;
uint32_t bootsign = 1UL;

/*-----------------------------------------------------------------------
 * Static variables
 *------------------------------------------------------------------------
 */
static uint32_t bGalileoSerialPortInitialized = FALSE;
static uint32_t uiLEDBlinkState = LED_OFF;
static uint16_t usIRQMask = 0xfffb;
static uint32_t UART_PCI_Base = 0UL;
static uint32_t UART_MMIO_Base = 0UL;
static SemaphoreHandle_t semPrintfGate = 0;

/*------------------------------------------------------------------------
 * GDT default entries (used in GDT setup code)
 *------------------------------------------------------------------------
 */
static struct sd gdt_default[NGDE] =
{
	/*   sd_lolimit  sd_lobase   sd_midbase  sd_access   sd_hilim_fl sd_hibase */
	/* 0th entry NULL */
	{            0,          0,           0,         0,            0,        0, },
	/* 1st, Kernel Code Segment */
	{       0xffff,          0,           0,      0x9a,         0xcf,        0, },
	/* 2nd, Kernel Data Segment */
	{       0xffff,          0,           0,      0x92,         0xcf,        0, },
	/* 3rd, Kernel Stack Segment */
	{       0xffff,          0,           0,      0x92,         0xcf,        0, },
	/* 4st, Boot Code Segment */
	{       0xffff,          0,           0,      0x9a,         0xcf,        0, },
	/* 5th, Code Segment for BIOS32 request */
	{       0xffff,          0,           0,      0x9a,         0xcf,        0, },
	/* 6th, Data Segment for BIOS32 request */
	{       0xffff,          0,           0,      0x92,         0xcf,        0, },
};

extern struct sd gdt[];	/* Global segment table (defined in startup.S) */

/*------------------------------------------------------------------------
 * Set segment registers (used in GDT setup code)
 *------------------------------------------------------------------------
 */
void setsegs()
{
	extern int	__text_end;
	struct sd	*psd;
	uint32_t	np, ds_end;

	ds_end = 0xffffffff/PAGE_SIZE; 		/* End page number */

	psd = &gdt_default[1];				/* Kernel code segment */
	np = ((int)&__text_end - 0 + PAGE_SIZE-1) / PAGE_SIZE;	/* Number of code pages */
	psd->sd_lolimit = np;
	psd->sd_hilim_fl = FLAGS_SETTINGS | ((np >> 16) & 0xff);

	psd = &gdt_default[2];				/* Kernel data segment */
	psd->sd_lolimit = ds_end;
	psd->sd_hilim_fl = FLAGS_SETTINGS | ((ds_end >> 16) & 0xff);

	psd = &gdt_default[3];				/* Kernel stack segment */
	psd->sd_lolimit = ds_end;
	psd->sd_hilim_fl = FLAGS_SETTINGS | ((ds_end >> 16) & 0xff);

	psd = &gdt_default[4];				/* Boot code segment */
	psd->sd_lolimit = ds_end;
	psd->sd_hilim_fl = FLAGS_SETTINGS | ((ds_end >> 16) & 0xff);

	memcpy(gdt, gdt_default, sizeof(gdt_default));
}
/*-----------------------------------------------------------*/

/*-----------------------------------------------------------------------
  * Debug serial port display update functions
  *------------------------------------------------------------------------
  */
 static void vCreatePrintfSemaphore( void )
 {
	if (semPrintfGate == 0)
	{
		semPrintfGate = xSemaphoreCreateRecursiveMutex();
		vQueueAddToRegistry( ( QueueHandle_t ) semPrintfGate, "g_printf_Mutex" );
	}
 }
 /*-----------------------------------------------------------*/

 void ClearScreen(void)
 {
	g_printf(ANSI_CLEAR_SB);
	g_printf(ANSI_CLEAR_SCREEN);
 }
 /*-----------------------------------------------------------*/

 void MoveToScreenPosition(uint8_t row, uint8_t col)
 {
	g_printf("%c[%d;%dH", (char) 0x1B, row, col);
 }
 /*-----------------------------------------------------------*/

 void UngatedMoveToScreenPosition(uint8_t row, uint8_t col)
 {
	printf("%c[%d;%dH", (char) 0x1B, row, col);
 }
/*-----------------------------------------------------------*/

 void SetScreenColor(const char *color)
 {
	 g_printf("%s", color);
 }
 /*-----------------------------------------------------------*/

 void g_printf(const char *format, ...)
 {

	 if (semPrintfGate == 0)
		 vCreatePrintfSemaphore();

	 if (xSemaphoreTakeRecursive(semPrintfGate, MUTEX_WAIT_TIME))
	 {
	     va_list arguments;
	     va_start(arguments,format);
	     print(0, format, arguments);
	     xSemaphoreGiveRecursive(semPrintfGate);
	 }
 }
 /*-----------------------------------------------------------*/

 void g_printf_rcc(uint8_t row, uint8_t col, const char *color, const char *format, ...)
 {
	 if (semPrintfGate == 0)
		 vCreatePrintfSemaphore();

	 if (xSemaphoreTakeRecursive(semPrintfGate, MUTEX_WAIT_TIME ))
	 {
		 UngatedMoveToScreenPosition(row, col);
		 printf("%s",color);
	     va_list arguments;
	     va_start(arguments,format);
	     print(0, format, arguments);
		 xSemaphoreGiveRecursive(semPrintfGate);
	 }
}
 /*-----------------------------------------------------------*/

 void vPrintBanner( void )
 {
	 if (bGalileoSerialPortInitialized)
	 {
		/* Print an RTOSDemo Loaded message */
		ClearScreen();
		g_printf_rcc(1, 2, DEFAULT_BANNER_COLOR,
		"%c[1mHELLO from the multiboot compliant FreeRTOS kernel!%c[0m",
		(char) 0x1B, (char) 0x1B );
		printf(ANSI_HIDE_CURSOR);
	 }
 }
 /*-----------------------------------------------------------*/

/*------------------------------------------------------------------------
 * Multiboot support (show parameters passed back from GRUB)
 *------------------------------------------------------------------------
 */
void show_kernel_parameters( unsigned long magic, unsigned long addr )
{
	/* Set to 0 to quiet display. */
	uint8_t print_values = 1;

	/* Initialise serial port if necessary. */
	vInitializeGalileoSerialPort(DEBUG_SERIAL_PORT);

	if (print_values != 0)
	{
		ClearScreen();
		g_printf(DEFAULT_SCREEN_COLOR);
		MoveToScreenPosition(1, 2);
		g_printf ("\n\r ...MULTIBOOT VALUES RETURNED FROM GRUB...\n\n\r");
		g_printf(ANSI_COLOR_WHITE);
	}

	if (magic != MULTIBOOT_BOOTLOADER_MAGIC)
	{
		printf(ANSI_COLOR_RED);
		if (print_values != 0)
			g_printf (" Invalid magic number returned: 0x%08x\n\r", (unsigned) magic);
		g_printf(ANSI_COLOR_RESET);
	}
	else
	{
	   multiboot_info_t *mbi;
	   /* Set MBI to the address of the Multiboot information structure. */
	   mbi = (multiboot_info_t *) addr;

	   /* Is the command line passed? */
	   if (CHECK_FLAG (mbi->flags, 2))
			if (print_values != 0)
				g_printf (" cmdline = %s\n\r", (char *) mbi->cmdline);

	   /* Print out the flags. */
	   if (print_values != 0)
		   g_printf (" flags = 0x%08x\n\r", (unsigned) mbi->flags);

	   /* Are mem_* valid? */
	   if (CHECK_FLAG (mbi->flags, 0))
			if (print_values != 0)
				g_printf (" mem_lower = %u KB, mem_upper = %u KB\n\r",
				(unsigned) mbi->mem_lower, (unsigned) mbi->mem_upper);

	   /* Is boot_device valid? */
	   if (CHECK_FLAG (mbi->flags, 1))
			if (print_values != 0)
				g_printf (" boot_device = 0x%08x\n\r", (unsigned) mbi->boot_device);

	   if (CHECK_FLAG (mbi->flags, 3))
	   {
		   module_t *mod;
		   int i;
		   if (print_values != 0)
			   g_printf (" mods_count = %d, mods_addr = 0x%08x\n\r",
				(int) mbi->mods_count, (int) mbi->mods_addr);
		   for (i = 0, mod = (module_t *) mbi->mods_addr;
				i < (int)mbi->mods_count;
			    i++, mod++)
		   {
				if (print_values != 0)
					g_printf ("    mod_start = 0x%08x, mod_end = 0x%08x, cmdline = %s\n\r",
					(unsigned) mod->mod_start,
					(unsigned) mod->mod_end,
					(char *) mod->string);
		   }
	   }

       /* Bits 4 and 5 are mutually exclusive! */
       if (CHECK_FLAG (mbi->flags, 4) && CHECK_FLAG (mbi->flags, 5))
       {
    	   if (print_values != 0)
    		   g_printf (" Both bits 4 and 5 are set.\n\r");
       }
       else
       {
           /* Is the symbol table of a.out valid? */
           if (CHECK_FLAG (mbi->flags, 4))
           {
        	   aout_symbol_table_t *multiboot_aout_sym = &(mbi->u.aout_sym);
        	   if (print_values != 0)
        		   g_printf (" multiboot_aout_symbol_table: tabsize = 0x%08x, "
        		    "strsize = 0x%08x, addr = 0x%08x\n\r",
    				(unsigned) multiboot_aout_sym->tabsize,
    				(unsigned) multiboot_aout_sym->strsize,
    				(unsigned) multiboot_aout_sym->addr);
           }

           /* Is the section header table of ELF valid? */
           if (CHECK_FLAG (mbi->flags, 5))
           {
        	   elf_section_header_table_t *multiboot_elf_sec = &(mbi->u.elf_sec);
        	   if (print_values != 0)
        		    g_printf (" multiboot_elf_sec: num = %u, size = 0x%08x,"
    				" addr = 0x%08x, shndx = 0x%04x\n\r",
    				(unsigned) multiboot_elf_sec->num, (unsigned) multiboot_elf_sec->size,
    				(unsigned) multiboot_elf_sec->addr, (unsigned) multiboot_elf_sec->shndx);
           }

           /* Are mmap_* valid? */
           if (CHECK_FLAG (mbi->flags, 6))
           {
        	   memory_map_t *mmap;
        	   if (print_values != 0)
        		   g_printf (" mmap_addr = 0x%08x, mmap_length = 0x%08x\n\r",
    			   (unsigned) mbi->mmap_addr, (unsigned) mbi->mmap_length);
               for (mmap = (memory_map_t *) mbi->mmap_addr;
                    (unsigned long) mmap < mbi->mmap_addr + mbi->mmap_length;
                    mmap = (memory_map_t *) ((unsigned long) mmap
                    + mmap->size + sizeof (mmap->size)))
               {
            	   if (print_values != 0)
            		   g_printf ("    size = 0x%08x, base_addr = 0x%04x%04x,"
    				   " length = 0x%04x%04x, type = 0x%04x\n\r",
    				   (unsigned) mmap->size,
    				   (uint16_t) mmap->base_addr_high,
    				   (uint16_t)mmap->base_addr_low,
    				   (uint16_t)mmap->length_high,
    				   (uint16_t)mmap->length_low,
    				   (unsigned) mmap->type);
               }
           }

    	   if (print_values != 0)
    	   {
    		   g_printf(DEFAULT_SCREEN_COLOR);
    		   g_printf ("\n\r Press any key to continue.\n\r");
			   while (ucGalileoGetchar() == 0)
			   {
					__asm volatile( "NOP" );
			   }
    	   }
           main();
       }
	}
}
/*-----------------------------------------------------------*/

/*------------------------------------------------------------------------
 * 8259 PIC initialization and support code
 *------------------------------------------------------------------------
 */
 void vInitialize8259Chips(void)
 {
	/* Set interrupt mask */
	uint16_t IRQMask = 0xffff;
	outb(IMR1, (uint8_t) (IRQMask & 0xff));
	outb(IMR2, (uint8_t) ((IRQMask >> 8) & 0xff));

	/* Initialise the 8259A interrupt controllers */

	/* Master device */
	outb(ICU1, 0x11);       /* ICW1: icw4 needed            */
	outb(ICU1+1, 0x20);     /* ICW2: base ivec 32           */
	outb(ICU1+1, 0x4);      /* ICW3: cascade on irq2        */
	outb(ICU1+1, 0x1);      /* ICW4: buf. master, 808x mode */

	/* Slave device */
	outb(ICU2, 0x11);       /* ICW1: icw4 needed            */
	outb(ICU2+1, 0x28);     /* ICW2: base ivec 40           */
	outb(ICU2+1, 0x2);      /* ICW3: slave on irq2          */
	outb(ICU2+1, 0xb);      /* ICW4: buf. slave, 808x mode  */

	vMicroSecondDelay (100);

	/* always read ISR */
	outb(ICU1, 0xb);        /* OCW3: set ISR on read        */
	outb(ICU2, 0xb);        /* OCW3: set ISR on read        */

	/* Set interrupt mask - leave bit 2 enabled for IC cascade */
	IRQMask = 0xfffb;
	outb(IMR1, (uint8_t) (IRQMask & 0xff));
	outb(IMR2, (uint8_t) ((IRQMask >> 8) & 0xff));
 }
 /*-----------------------------------------------------------*/

 void vClearIRQMask(uint8_t IRQNumber)
 {
	 if( ( IRQNumber > 31 ) && ( IRQNumber < 48 ) )
	 {
		usIRQMask &= ~( 1 << (IRQNumber - 32 ) );
		usIRQMask &= 0xfffb;  	// bit 2 is slave cascade
		usIRQMask |= 0x0200;	// bit 14 is reserved
		outb(IMR1, (uint8_t) (usIRQMask & 0xff));
		outb(IMR2, (uint8_t) ((usIRQMask >> 8) & 0xff));
	 }
 }
 /*-----------------------------------------------------------*/

 void vSetIRQMask(uint8_t IRQNumber)
 {
	 if( ( IRQNumber > 31 ) && ( IRQNumber < 48 ) )
	 {
		usIRQMask |= ( 1 << (IRQNumber - 32 ) );
		usIRQMask &= 0xfffb;  	// bit 2 is slave cascade
		usIRQMask |= 0x0200;	// bit 14 is reserved
		outb(IMR1, (uint8_t) (usIRQMask & 0xff));
		outb(IMR2, (uint8_t) ((usIRQMask >> 8) & 0xff));
	 }
 }
 /*-----------------------------------------------------------*/

 /*-----------------------------------------------------------------------
  * 82C54 PIT (programmable interval timer) initialization
  *------------------------------------------------------------------------
  */
 void vInitializePIT(void)
 {
	/* Set the hardware clock: timer 0, 16-bit counter, rate                */
	/* generator mode, and counter runs in binary		                    */
	outb(CLKCNTL, 0x34);

	/* Set the clock rate to 1.193 Mhz, this is 1 ms interrupt rate         */
	uint16_t intrate = 1193;
	/* Must write LSB first, then MSB                                       */
	outb(CLKBASE, (char) (intrate & 0xff));
	outb(CLKBASE, (char) ((intrate >> 8) & 0xff));
 }
 /*-----------------------------------------------------------*/

 /*-----------------------------------------------------------------------
  * LED support for main_blinky()
  *------------------------------------------------------------------------
  */
 uint32_t ulBlinkLED(void)
 {
	 if( uiLEDBlinkState == LED_OFF )
	 {
		 uiLEDBlinkState = LED_ON;
	 }
	 else
	 {
		 uiLEDBlinkState = LED_OFF;
	 }

	 vGalileoBlinkLEDUsingLegacyGPIO(uiLEDBlinkState);

	 return uiLEDBlinkState;
 }
 /*-----------------------------------------------------------*/

 /*-----------------------------------------------------------------------
  * Serial port initialization code
  *------------------------------------------------------------------------
  */
 static void vInitializeGalileoUART(uint32_t portnumber)
 {
	volatile uint8_t divisor = 24;
	volatile uint8_t output_data = 0x3 & 0xFB & 0xF7;
	volatile uint8_t input_data = 0;
	volatile uint8_t lcr = 0;

	if (portnumber == DEBUG_SERIAL_PORT)
		UART_PCI_Base = MMIO_PCI_ADDRESS(0, 20, 5, 0);
	else
		UART_PCI_Base = MMIO_PCI_ADDRESS(0, 20, 1, 0);

	uint32_t base = mem_read(UART_PCI_Base, 0x10, 4);
	UART_MMIO_Base = base;

	mem_write(base, R_UART_SCR, 1, 0xAB);

	mem_write(base, R_UART_LCR, 1, output_data | B_UARY_LCR_DLAB);

	mem_write(base, R_UART_BAUD_HIGH, 1, (uint8_t)(divisor >> 8));
	mem_write(base, R_UART_BAUD_LOW, 1, (uint8_t)(divisor & 0xff));

	mem_write(base, R_UART_LCR, 1, output_data);

	mem_write(base, R_UART_FCR, 1, (uint8_t)(B_UARY_FCR_TRFIFIE |
		B_UARY_FCR_RESETRF | B_UARY_FCR_RESETTF | 0x30));

	input_data = mem_read(base, R_UART_MCR, 1);
	input_data |= BIT1;
	input_data &= ~BIT5;
	mem_write(base, R_UART_MCR, 1, input_data);

	lcr = mem_read(base, R_UART_LCR, 1);
	mem_write(base, R_UART_LCR, 1, (uint8_t) (lcr & ~B_UARY_LCR_DLAB));

	mem_write(base, R_UART_IER, 1, 0);
 }
 /*-----------------------------------------------------------*/

 void vInitializeGalileoSerialPort(uint32_t portnumber)
 {
  	if( bGalileoSerialPortInitialized == FALSE )
 	{
		/* Initialise for 115200, 8, 1, none and no handshaking */
  		vInitializeGalileoUART(portnumber);
		bGalileoSerialPortInitialized = TRUE;
 	}
 }
 /*-----------------------------------------------------------*/

 /*-----------------------------------------------------------------------
  * Serial port support functions
  *------------------------------------------------------------------------
  */
 void vGalileoPrintc(char c)
 {
	if (bGalileoSerialPortInitialized)
	{
		while((mem_read(UART_MMIO_Base, R_UART_LSR, 1) & B_UART_LSR_TXRDY) == 0);
	 	mem_write(UART_MMIO_Base, R_UART_BAUD_THR, 1, c);
	}
 }
 /*-----------------------------------------------------------*/

 uint8_t ucGalileoGetchar()
 {
	uint8_t c = 0;
	if (bGalileoSerialPortInitialized)
	{
		if((mem_read(UART_MMIO_Base, R_UART_LSR, 1) & B_UART_LSR_RXRDY) != 0)
		 	c  = mem_read(UART_MMIO_Base, R_UART_BAUD_THR, 1);
	}
	  return c;
 }
 /*-----------------------------------------------------------*/

 void vGalileoPuts(const char *string)
 {
	if (bGalileoSerialPortInitialized)
	{
	    while(*string)
	    	vGalileoPrintc(*string++);
	}
 }
 /*-----------------------------------------------------------*/
