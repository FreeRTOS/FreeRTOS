MEMORY
{
	RAM : ORIGIN = 0x0, LENGTH = 524288
	ROM : ORIGIN = 0xFFC00000, LENGTH = 4194304
}

SECTIONS
{
	.fvectors 0xFFFFFF80 : AT (0xFFFFFF80)
	{
		KEEP(*(.fvectors))
	} > ROM
	.text 0xFFC00000 : AT (0xFFC00000)
	{
		*(.text)
		*(.text.*)
		*(P)
		etext = .;
	} > ROM
	.rvectors : 
	{
		_rvectors_start = .;
		*(.rvectors)
		_rvectors_end = .;
	} > ROM
	.init : 
	{
		*(.init)
		__preinit_array_start = .;
		*(.preinit_array)
		__preinit_array_end = .;
		__init_array_start = (. + 3) & ~ 3;
		*(.init_array)
		*(SORT(.init_array.*))
		__init_array_end = .;
		__fini_array_start = .;
		*(.fini_array)
		*(SORT(.fini_array.*))
		__fini_array_end = .;
	} > ROM
	.fini : 
	{
		*(.fini)
	} > ROM
	.got : 
	{
		*(.got)
		*(.got.plt)
	} > ROM
	.rodata : 
	{
		*(.rodata)
		*(.rodata.*)
		*(C_1)
		*(C_2)
		*(C)
		_erodata = .;
	} > ROM
	.eh_frame_hdr : 
	{
		*(.eh_frame_hdr)
	} > ROM
	.eh_frame : 
	{
		*(.eh_frame)
	} > ROM
	.jcr : 
	{
		*(.jcr)
	} > ROM
	.tors : 
	{
		__CTOR_LIST__ = .;
		. = ALIGN(2);
		___ctors = .;
		*(.ctors)
		___ctors_end = .;
		__CTOR_END__ = .;
		__DTOR_LIST__ = .;
		___dtors = .;
		*(.dtors)
		___dtors_end = .;
		__DTOR_END__ = .;
		. = ALIGN(2);
		_mdata = .;
	} > ROM
	.data 0x404 : AT (_mdata)
	{
		_data = .;
		*(.data)
		*(.data.*)
		*(D)
		*(D_1)
		*(D_2)
		_edata = .;
	} > RAM
	.gcc_exc : 
	{
		*(.gcc_exc)
	} > RAM
	.bss : 
	{
		_bss = .;
		*(.bss)
		*(.bss.**)
		*(COMMON)
		*(B)
		*(B_1)
		*(B_2)
		_ebss = .;
		_end = .;
	} > RAM
	.ustack 0x400 : AT (0x400)
	{
		_ustack = .;
	} > RAM
	.istack 0x200 : AT (0x200)
	{
		_istack = .;
	} > RAM
}
