MEMORY
{
    RAM (xrw)  : ORIGIN = 0x00000000,  LENGTH = 4M
/*    FLASH (rx) : ORIGIN = 0x4000000,   LENGTH = 512K */
}

_Min_Heap_Size = 0x200 ;        /* Required amount of heap. */
_Min_Stack_Size = 0x400 ;       /* Required amount of stack. */

_estack = ORIGIN(RAM) + LENGTH(RAM);

SECTIONS
{
    .text : {
        . = ALIGN(4);
        KEEP(*(.isr_vector))
        *(.text*)
        KEEP (*(.init))
        KEEP (*(.fini))
        . = ALIGN(4);
        _etext = .;
        _sidata = _etext;
    } > RAM

    .data : AT ( _sidata )
    {
        . = ALIGN(4);
        _sdata = .;
        *(.data*)
        *(.rodata*)
        KEEP(*(.eh_frame))
        . = ALIGN(4);
        _edata = .;
    } >RAM

    .bss :
    {
        . = ALIGN(4);
        _sbss = .;
        __bss_start__ = _sbss;
        *(.bss*)
        *(COMMON)
        . = ALIGN(4);
        _ebss = .;
        __bss_end__ = _ebss;
    } >RAM

    ._user_heap_stack :
    {
        . = ALIGN(8);
        PROVIDE ( end = . );
        PROVIDE ( _end = . );
        _heap_bottom = .;
        . = . + _Min_Heap_Size;
        _heap_top = .;
        . = . + _Min_Stack_Size;
        . = ALIGN(8);
       } >RAM

	.ARM.extab :
	{
		. = ALIGN(4);
		*(.ARM.extab* .gnu.linkonce.armextab.*)
		. = ALIGN(4);
	} >RAM

	.ARM :
	{
		. = ALIGN(4);
		__exidx_start = .;
		*(.ARM.exidx*)
		__exidx_end = .;
		. = ALIGN(4);
	} >RAM
}

