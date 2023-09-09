/* Linker script for MC689S12DP256 Flash 
   rom banks.
   
   Author Jefferson L Smith; Robotronics, Inc.  2006
 */
OUTPUT_FORMAT("elf32-m68hc12", "elf32-m68hc12",
	      "elf32-m68hc12")
OUTPUT_ARCH(m68hc12)
ENTRY(_start)

/* Get memory banks definition from some user configuration file.
   This file must be located in some linker directory (search path
   with -L<dir>). See fixed memory banks emulation script.  */
INCLUDE memory.x;

SECTIONS
{
  /* Concatenate .page0 sections.  Put them in the page0 memory bank
     unless we are creating a relocatable file.  */
  .page0 :
  {
    *(.page0)
  }  > page0
  
  /* PPAGE memory banks */

  .bank0 :
  {
    *(.bank0)
    . = ALIGN(2);
  } > bank0  =0xff
  .bank1 :
  {
    *(.bank1)
    . = ALIGN(2);
  } > bank1  =0xff
  .bank2 :
  {
    *(.bank2)
    . = ALIGN(2);
  } > bank2  =0xff
  .bank3 :
  {
    *(.bank3)
    . = ALIGN(2);
  } > bank3  =0xff
  .bank4 :
  {
    *(.bank4)
    . = ALIGN(2);
  } > bank4  =0xff
  .bank5 :
  {
    *(.bank5)
    . = ALIGN(2);
  } > bank5  =0xff
  .bank6 :
  {
    *(.bank6)
    . = ALIGN(2);
  } > bank6  =0xff
  .bank7 :
  {
    *(.bank7)
    . = ALIGN(2);
  } > bank7  =0xff
  .bank8 :
  {
    *(.bank8)
    . = ALIGN(2);
  } > bank8  =0xff
  .bank9 :
  {
    *(.bank9)
    . = ALIGN(2);
  } > bank9  =0xff
  .bank10 :
  {
    *(.bank10)
    . = ALIGN(2);
  } > bank10  =0xff
  .bank11 :
  {
    *(.bank11)
    . = ALIGN(2);
  } > bank11  =0xff
  .bank12 :
  {
    *(.bank12)
    . = ALIGN(2);
  } > bank12  =0xff
  .bank13 :
  {
    *(.bank13)
    . = ALIGN(2);
  } > bank13  =0xff
  
  /* Start of text section.  */
  .text : 
  {
    /* Put startup code at beginning so that _start keeps same address.  */
    /* Startup code.  */
    KEEP (*(.install0))	/* Section should setup the stack pointer.  */
    KEEP (*(.install1))	/* Place holder for applications.  */
    KEEP (*(.install2))	/* Optional installation of data sections in RAM.  */
    KEEP (*(.install3))	/* Place holder for applications.  */
    KEEP (*(.install4))	/* Section that calls the main.  */
    *(.init)
    *(.text)
    *(.text.*)
    *(.text_c)
    /* .gnu.warning sections are handled specially by elf32.em.  */
    *(.gnu.warning)
    *(.gnu.linkonce.t.*)
    *(.tramp)
    *(.tramp.*)
    /* Finish code.  */
    KEEP (*(.fini0))	/* Beginning of finish code (_exit symbol).  */
    KEEP (*(.fini1))	/* Place holder for applications.  */
    KEEP (*(.fini2))	/* C++ destructors.  */
    KEEP (*(.fini3))	/* Place holder for applications.  */
    KEEP (*(.fini4))	/* Runtime exit.  */
    _etext = .;
    PROVIDE (etext = .);
    . = ALIGN(2);
  }  > text AT>bank14  =0xff
  
  .text_h : 
  {
    *(.text_h)           /* Bootloader; high Flash area unbanked */
    . = ALIGN(2);
  }  > text_h AT>bank15  =0xff
  .rodata : 
  {
    *(.rodata)
    *(.rodata.*)
    *(.gnu.linkonce.r*)
    . = ALIGN(2);
  }  > text_h AT>bank15  =0xff
  .eh_frame : 
  {
    KEEP (*(.eh_frame))
    . = ALIGN(2);
  }  > text_h AT>bank15  =0xff
  
  /* Constructor and destructor tables are in ROM.  */
  .ctors : 
  {
     PROVIDE (__CTOR_LIST__ = .);
    KEEP (*(.ctors))
     PROVIDE(__CTOR_END__ = .);
     . = ALIGN(2);
  }  > text_h AT>bank15  =0xff
  .dtors : 
  {
     PROVIDE(__DTOR_LIST__ = .);
    KEEP (*(.dtors))
     PROVIDE(__DTOR_END__ = .);
     . = ALIGN(2);
  }  > text_h AT>bank15  =0xff
  
  /* Start of the data section image in ROM.  */
  __data_image = .;
  PROVIDE (__data_image = .);
  
  /* All read-only sections that normally go in PROM must be above.
     We construct the DATA image section in PROM at end of all these
     read-only sections.  The data image must be copied at init time.
     Refer to GNU ld, Section 3.6.8.2 Output Section LMA.  */
  .data :
  {
    __data_section_start = .;
    PROVIDE (__data_section_start = .);
    *(.sdata)
    *(.data)
    *(.data.*)
    *(.data1)
    *(.gnu.linkonce.d.*)
    CONSTRUCTORS
    _edata  =  .;
    PROVIDE (edata = .);
    . = ALIGN(2);
  }  > data AT>bank15  =0xff
  __data_section_size = SIZEOF(.data);
  __data_image_end = __data_image + __data_section_size;
  PROVIDE (__data_section_size = SIZEOF(.data));
  /* .install  :
  {
    . = _data_image_end;
  }  > text */
  /* Relocation for some bss and data sections.  */
  .softregs   :
  {
    __softregs_section_start = .;
    *(.softregs)
    __softregs_section_end = .;
  }  > data
  __softregs_section_size = SIZEOF(.softregs); 
  .bss   :
  {
    __bss_start = .;
    *(.sbss)
    *(.scommon)
    *(.dynbss)
    *(.bss)
    *(.bss.*)
    *(.gnu.linkonce.b.*)
    *(COMMON)
    PROVIDE (_end = .);
  }  > data
  __bss_size = SIZEOF(.bss);
  PROVIDE (__bss_size = SIZEOF(.bss));
  .eeprom   :
  {
    *(.eeprom)
    *(.eeprom.*)
    . = ALIGN(2);
  }  > eeprom  =0xff

  /* If the 'vectors_addr' symbol is defined, it indicates the start address
     of interrupt vectors.  This depends on the 9S12 operating mode:
		Addr
     Hardware location	LMA 0x10ff80, mirror 0xff80
     Called by dbug12	LMA 0x10ef80, mirror 0xef80
     Ram called by dbug12	0x3e00
     The default vectors address is (LMA) 0x10ff80.  This can be overriden
     with the '-defsym vectors_addr=0x...' ld option.
  */
  PROVIDE (_vectors_addr = DEFINED (vectors_addr) ? vectors_addr : 0x10ff80);
  .vectors DEFINED (vectors_addr) ? vectors_addr : 0x10ff80 :
  {
    KEEP (*(.vectors))
  }
  /* Stabs debugging sections.  */
  .stab		 0 : { *(.stab) }
  .stabstr	 0 : { *(.stabstr) }
  .stab.excl	 0 : { *(.stab.excl) }
  .stab.exclstr	 0 : { *(.stab.exclstr) }
  .stab.index	 0 : { *(.stab.index) }
  .stab.indexstr 0 : { *(.stab.indexstr) }
  .comment	 0 : { *(.comment) }
  /* DWARF debug sections.
     Symbols in the DWARF debugging sections are relative to the beginning
     of the section so we begin them at 0.
     Treatment of DWARF debug section must be at end of the linker
     script to avoid problems when there are undefined symbols. It's necessary
     to avoid that the DWARF section is relocated before such undefined
     symbols are found.  */
  /* DWARF 1 */
  .debug	 0 : { *(.debug) }
  .line		 0 : { *(.line) }
  /* GNU DWARF 1 extensions */
  .debug_srcinfo 0 : { *(.debug_srcinfo) }
  .debug_sfnames 0 : { *(.debug_sfnames) }
  /* DWARF 1.1 and DWARF 2 */
  .debug_aranges  0 : { *(.debug_aranges) }
  .debug_pubnames 0 : { *(.debug_pubnames) }
  /* DWARF 2 */
  .debug_info     0 : { *(.debug_info) *(.gnu.linkonce.wi.*) }
  .debug_abbrev   0 : { *(.debug_abbrev) }
  .debug_line     0 : { *(.debug_line) }
  .debug_frame    0 : { *(.debug_frame) }
  .debug_str      0 : { *(.debug_str) }
  .debug_loc      0 : { *(.debug_loc) }
  .debug_macinfo  0 : { *(.debug_macinfo) }
}
