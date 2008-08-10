/* Linker script for m5282evb
 *
 * Version:Sourcery G++ Lite 4.2-125
 * BugURL:https://support.codesourcery.com/GNUToolchain/
 *
 *  Copyright 2007, 2008 CodeSourcery.
 *
 * The authors hereby grant permission to use, copy, modify, distribute,
 * and license this software and its documentation for any purpose, provided
 * that existing copyright notices are retained in all copies and that this
 * notice is included verbatim in any distributions. No written agreement,
 * license, or royalty fee is required for any of the authorized uses.
 * Modifications to this software may be copyrighted by their authors
 * and need not follow the licensing terms described here, provided that
 * the new terms are clearly indicated on the first page of each file where
 * they apply. */

OUTPUT_ARCH(m68k)
ENTRY(_start)
SEARCH_DIR(.)
GROUP(-lgcc -lc -lcs3 -lcs3hosted -lcs3coldfire)

MEMORY
{
  ram (rwx) : ORIGIN = 0x00000000, LENGTH = 16M
  rom (rx) : ORIGIN = 0xFFE00000, LENGTH = 2M
  rombar (rx) : ORIGIN = 0xf0000000, LENGTH = 512K
  rambar (rwx) : ORIGIN = 0x20000000, LENGTH = 64K
  ipsbar (rw) : ORIGIN = 0x40000000, LENGTH = 0x20000000
}

/* These force the linker to search for particular symbols from
 * the start of the link process and thus ensure the user's
 * overrides are picked up
 */
EXTERN(__cs3_reset_m5282evb)
INCLUDE coldfire-names.inc
EXTERN(__cs3_interrupt_vector_coldfire)
EXTERN(__cs3_start_c main __cs3_stack __cs3_heap_end)
EXTERN(_start)
/* force exit to be picked up in a hosted or os environment */
EXTERN(exit atexit)

PROVIDE(__cs3_heap_start = _end);
PROVIDE(__cs3_heap_end = __cs3_region_start_ram + __cs3_region_size_ram);
PROVIDE(__cs3_region_num = (__cs3_regions_end - __cs3_regions) / 20);
PROVIDE(__cs3_stack = __cs3_region_start_ram + __cs3_region_size_ram);

SECTIONS
{

  .text :
  {
    CREATE_OBJECT_SYMBOLS
    __cs3_region_start_ram = .;
    *(.cs3.region-head.ram)
    ASSERT (. == __cs3_region_start_ram, ".cs3.region-head.ram not permitted");
    __cs3_interrupt_vector = __cs3_interrupt_vector_coldfire;
    *(.cs3.interrupt_vector)
    /* Make sure we pulled in an interrupt vector.  */
    ASSERT (. != __cs3_interrupt_vector_coldfire, "No interrupt vector");

    PROVIDE(__cs3_reset_m5282evb = _start);
    __cs3_reset = __cs3_reset_m5282evb;
    *(.cs3.reset)

    *(.text .text.* .gnu.linkonce.t.*)

    . = ALIGN(0x4);
    KEEP (*crtbegin.o(.jcr))
    KEEP (*(EXCLUDE_FILE (*crtend.o) .jcr))
    KEEP (*crtend.o(.jcr))

    . = ALIGN(0x4);
    *(.gcc_except_table .gcc_except_table.*)
  } >ram
  .eh_frame_hdr : ALIGN (4)
  {
    KEEP (*(.eh_frame_hdr))
  } >ram
  .eh_frame : ALIGN (4)
  {
    KEEP (*(.eh_frame))
  } >ram
  .rodata : ALIGN (4)
  {
    *(.rodata .rodata.* .gnu.linkonce.r.*)

    . = ALIGN(4);
    _init = .;
    LONG (0x4e560000)	/* linkw %fp,#0 */
    KEEP(*(.init))
    SHORT (0x4e5e)	/* unlk %fp */
    SHORT (0x4e75)	/* rts */

    . = ALIGN(4);
    __preinit_array_start = .;
    KEEP (*(.preinit_array))
    __preinit_array_end = .;

    . = ALIGN(4);
    __init_array_start = .;
    KEEP (*(SORT(.init_array.*)))
    KEEP (*(.init_array))
    __init_array_end = .;

    . = ALIGN(4);
    _fini = .;
    LONG (0x4e560000)	/* linkw %fp,#0 */
    KEEP(*(.fini))
    SHORT (0x4e5e)	/* unlk %fp */
    SHORT (0x4e75)	/* rts */

    . = ALIGN(4);
    __fini_array_start = .;
    KEEP (*(.fini_array))
    KEEP (*(SORT(.fini_array.*)))
    __fini_array_end = .;

    . = ALIGN(0x4);
    KEEP (*crtbegin.o(.ctors))
    KEEP (*(EXCLUDE_FILE (*crtend.o) .ctors))
    KEEP (*(SORT(.ctors.*)))
    KEEP (*crtend.o(.ctors))

    . = ALIGN(0x4);
    KEEP (*crtbegin.o(.dtors))
    KEEP (*(EXCLUDE_FILE (*crtend.o) .dtors))
    KEEP (*(SORT(.dtors.*)))
    KEEP (*crtend.o(.dtors))

    *(.lit)

    . = ALIGN(4);
    __cs3_regions = .;
    LONG (0)
    LONG (__cs3_region_init_ram)
    LONG (__cs3_region_start_ram)
    LONG (__cs3_region_init_size_ram)
    LONG (__cs3_region_zero_size_ram)
    LONG (0)
    LONG (__cs3_region_init_rombar)
    LONG (__cs3_region_start_rombar)
    LONG (__cs3_region_init_size_rombar)
    LONG (__cs3_region_zero_size_rombar)
    LONG (0)
    LONG (__cs3_region_init_rambar)
    LONG (__cs3_region_start_rambar)
    LONG (__cs3_region_init_size_rambar)
    LONG (__cs3_region_zero_size_rambar)
    __cs3_regions_end = .;

    . = ALIGN (8);
    . = ALIGN (8);
    _etext = .;
  } >ram

  .cs3.rom : ALIGN (8)
  {
    __cs3_region_start_rom = .;
    *(.cs3.region-head.rom)
    *(.rom)
    . = ALIGN (8);
  } >rom
  .cs3.rom.bss :
  {
    *(.rom.b)
    . = ALIGN (8);
  } >rom
  /* __cs3_region_end_rom is deprecated */
  __cs3_region_end_rom = __cs3_region_start_rom + LENGTH(rom);
  __cs3_region_size_rom = LENGTH(rom);
  __cs3_region_init_rom = LOADADDR (.cs3.rom);
  __cs3_region_init_size_rom = LOADADDR (.cs3.rom.bss) - LOADADDR (.cs3.rom);
  __cs3_region_zero_size_rom = SIZEOF(.cs3.rom.bss);

  .cs3.rombar : ALIGN (8)
  {
    __cs3_region_start_rombar = .;
    *(.cs3.region-head.rombar)
    *(.rombar)
    . = ALIGN (8);
  } >rombar
  .cs3.rombar.bss :
  {
    *(.rombar.b)
    . = ALIGN (8);
  } >rombar
  /* __cs3_region_end_rombar is deprecated */
  __cs3_region_end_rombar = __cs3_region_start_rombar + LENGTH(rombar);
  __cs3_region_size_rombar = LENGTH(rombar);
  __cs3_region_init_rombar = LOADADDR (.cs3.rombar);
  __cs3_region_init_size_rombar = LOADADDR (.cs3.rombar.bss) - LOADADDR (.cs3.rombar);
  __cs3_region_zero_size_rombar = SIZEOF(.cs3.rombar.bss);

  .cs3.rambar : ALIGN (8)
  {
    __cs3_region_start_rambar = .;
    *(.cs3.region-head.rambar)
    *(.rambar)
    . = ALIGN (8);
  } >rambar
  .cs3.rambar.bss :
  {
    *(.rambar.b)
    . = ALIGN (8);
  } >rambar
  /* __cs3_region_end_rambar is deprecated */
  __cs3_region_end_rambar = __cs3_region_start_rambar + LENGTH(rambar);
  __cs3_region_size_rambar = LENGTH(rambar);
  __cs3_region_init_rambar = LOADADDR (.cs3.rambar);
  __cs3_region_init_size_rambar = LOADADDR (.cs3.rambar.bss) - LOADADDR (.cs3.rambar);
  __cs3_region_zero_size_rambar = SIZEOF(.cs3.rambar.bss);

  .cs3.ipsbar :
  {
    __cs3_region_start_ipsbar = .;
    *(.cs3.region-head.ipsbar)
    . = ALIGN (8);
  } >ipsbar
  /* __cs3_region_end_ipsbar is deprecated */
  __cs3_region_end_ipsbar = __cs3_region_start_ipsbar + LENGTH(ipsbar);
  __cs3_region_size_ipsbar = LENGTH(ipsbar);

  .data : ALIGN (8)
  {

    *(.got.plt) *(.got)
    *(.shdata)
    *(.data .data.* .gnu.linkonce.d.*)
    . = ALIGN (8);
    *(.ram)
    _edata = .;
  } >rambar
  .bss :
  {
    *(.shbss)
    *(.bss .bss.* .gnu.linkonce.b.*)
    *(COMMON)
    . = ALIGN (8);
    *(.ram.b)
    _end = .;
    __end = .;
  } >rambar
  /* __cs3_region_end_ram is deprecated */
  __cs3_region_end_ram = __cs3_region_start_ram + LENGTH(ram);
  __cs3_region_size_ram = LENGTH(ram);
  __cs3_region_init_ram = LOADADDR (.text);
  __cs3_region_init_size_ram = _edata - ADDR (.text);
  __cs3_region_zero_size_ram = _end - _edata;

  .stab 0 (NOLOAD) : { *(.stab) }
  .stabstr 0 (NOLOAD) : { *(.stabstr) }
  /* DWARF debug sections.
   * Symbols in the DWARF debugging sections are relative to the beginning
   * of the section so we begin them at 0.  */
  /* DWARF 1 */
  .debug          0 : { *(.debug) }
  .line           0 : { *(.line) }
  /* GNU DWARF 1 extensions */
  .debug_srcinfo  0 : { *(.debug_srcinfo) }
  .debug_sfnames  0 : { *(.debug_sfnames) }
  /* DWARF 1.1 and DWARF 2 */
  .debug_aranges  0 : { *(.debug_aranges) }
  .debug_pubnames 0 : { *(.debug_pubnames) }
  /* DWARF 2 */
  .debug_info     0 : { *(.debug_info .gnu.linkonce.wi.*) }
  .debug_abbrev   0 : { *(.debug_abbrev) }
  .debug_line     0 : { *(.debug_line) }
  .debug_frame    0 : { *(.debug_frame) }
  .debug_str      0 : { *(.debug_str) }
  .debug_loc      0 : { *(.debug_loc) }
  .debug_macinfo  0 : { *(.debug_macinfo) }
  /* SGI/MIPS DWARF 2 extensions */
  .debug_weaknames 0 : { *(.debug_weaknames) }
  .debug_funcnames 0 : { *(.debug_funcnames) }
  .debug_typenames 0 : { *(.debug_typenames) }
  .debug_varnames  0 : { *(.debug_varnames) }
}
