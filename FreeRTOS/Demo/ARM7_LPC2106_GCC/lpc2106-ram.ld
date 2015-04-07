MEMORY 
{
	flash	: ORIGIN = 0, LENGTH = 120K
	ram		: ORIGIN = 0x40000000, LENGTH = 64K
}

__stack_end__ = 0x40000000 + 64K - 4;

SECTIONS 
{
	. = 0;
	startup : { *(.startup)} >ram

	prog : 
	{
		*(.text)
		*(.rodata)
		*(.rodata*)
		*(.glue_7)
		*(.glue_7t)
	} >ram

	__end_of_text__ = .;

	.data : 
	{
		__data_beg__ = .;
		__data_beg_src__ = __end_of_text__;
		*(.data)
		__data_end__ = .;
	} >ram

	.bss : 
	{
		__bss_beg__ = .;
		*(.bss)
	} >ram

	. = ALIGN(4);
	.eh_frame :
	{
		 KEEP (*(.eh_frame))
	} > ram
	
	/* Align here to ensure that the .bss section occupies space up to
	_end.  Align after .bss to ensure correct alignment even if the
	.bss section disappears because there are no input sections.  */
	. = ALIGN(32 / 8);
}
	. = ALIGN(32 / 8);
	_end = .;
	_bss_end__ = . ; __bss_end__ = . ; __end__ = . ;
	PROVIDE (end = .);


