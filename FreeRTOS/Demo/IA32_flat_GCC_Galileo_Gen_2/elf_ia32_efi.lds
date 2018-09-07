OUTPUT_FORMAT("elf32-i386")
OUTPUT_ARCH(i386)
ENTRY(_start)

physbase = 0x00100000;

SECTIONS
{	
 	. = physbase;
	. = ALIGN(4096);
 	.text :
	{
	    __text_start =  ABSOLUTE(.);
	    *(.text.entry)
	    *(.text)
	    *(.text.last)
	    *(.text.*)
	    . = ALIGN(4);
		*(.rodata)
		*( .rodata.*)
 	    __text_end =  ABSOLUTE(.);
  		. = ALIGN(4096);
	}
	
	/* Read-write data (initialised) */
 	.data :
	{
 		__data_start = ABSOLUTE(.);
  		__data_lma = LOADADDR(.data); 
  		__data_vma =  ABSOLUTE(.);
 		*(.data)
 		*(.data.*)
 		__data_end = ABSOLUTE(.);
 		. = ALIGN(4096);
 	}

	/* Read-write data (uninitialised) */
 	.bss :
	{
    	__bss_start =  ABSOLUTE(.);
    	*(.bss)
     	*(COMMON)
    	__bss_end =  ABSOLUTE(.);
   		. = ALIGN(1024);
 	}
	
	/* stack used before the scheduler starts */
 	.boot_stack :
	{
		/* 2K for the boot stack.  This could be avoided by using the same RAM
		as used by the FreeRTOS system/interrupt stack. */
		. += 2048;
    	__stack_for_main = ABSOLUTE( . );
   		. = ALIGN(1024);
 	}

	/*exception unwinding and source language information */
	.eh_frame : { KEEP (*(.eh_frame)) . = ALIGN(4); }

	/* function exports */
 	.drectve : { KEEP (*(.drectve)) }
  	
   	.comment 0 : { *(.comment) }

}