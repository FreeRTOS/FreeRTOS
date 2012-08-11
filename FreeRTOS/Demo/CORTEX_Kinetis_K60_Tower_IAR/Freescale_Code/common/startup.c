/*
 * File:    startup.c
 * Purpose: Generic Kinetis startup code
 *
 * Notes:
 */

#include "common.h"

#if (defined(IAR))
	#pragma section = ".data"
	#pragma section = ".data_init"
	#pragma section = ".bss"
	#pragma section = "CodeRelocate"
	#pragma section = "CodeRelocateRam"
#endif

/********************************************************************/
void
common_startup(void)
{

#if (defined(CW))	
    extern char __START_BSS[];
    extern char __END_BSS[];
    extern uint32 __DATA_ROM[];
    extern uint32 __DATA_RAM[];
    extern char __DATA_END[];
#endif

    /* Declare a counter we'll use in all of the copy loops */
    uint32 n;

    /* Declare pointers for various data sections. These pointers
     * are initialized using values pulled in from the linker file
     */
    uint8 * data_ram, * data_rom, * data_rom_end;
    uint8 * bss_start, * bss_end;


    /* Get the addresses for the .data section (initialized data section) */
	#if (defined(CW))
        data_ram = (uint8 *)__DATA_RAM;
	    data_rom = (uint8 *)__DATA_ROM;
	    data_rom_end  = (uint8 *)__DATA_END; /* This is actually a RAM address in CodeWarrior */
	    n = data_rom_end - data_ram;
    #elif (defined(IAR))
		data_ram = __section_begin(".data");
		data_rom = __section_begin(".data_init");
		data_rom_end = __section_end(".data_init");
		n = data_rom_end - data_rom;
	#endif		
		
	/* Copy initialized data from ROM to RAM */
	while (n--)
		*data_ram++ = *data_rom++;
	
	
    /* Get the addresses for the .bss section (zero-initialized data) */
	#if (defined(CW))
		bss_start = (uint8 *)__START_BSS;
		bss_end = (uint8 *)__END_BSS;
	#elif (defined(IAR))
		bss_start = __section_begin(".bss");
		bss_end = __section_end(".bss");
	#endif
		
		
	

    /* Clear the zero-initialized data section */
    n = bss_end - bss_start;
    while(n--)
      *bss_start++ = 0;

	/* Get addresses for any code sections that need to be copied from ROM to RAM.
	 * The IAR tools have a predefined keyword that can be used to mark individual
	 * functions for execution from RAM. Add "__ramfunc" before the return type in
	 * the function prototype for any routines you need to execute from RAM instead
	 * of ROM. ex: __ramfunc void foo(void);
	 */
	#if (defined(IAR))
		uint8* code_relocate_ram = __section_begin("CodeRelocateRam");
		uint8* code_relocate = __section_begin("CodeRelocate");
		uint8* code_relocate_end = __section_end("CodeRelocate");

		/* Copy functions from ROM to RAM */
		n = code_relocate_end - code_relocate;
		while (n--)
			*code_relocate_ram++ = *code_relocate++;
	#endif
}
/********************************************************************/
