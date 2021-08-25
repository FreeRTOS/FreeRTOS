/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*******************************************************************************
 * 
 * file name : mpfs_envm.ld
 * Use with Bare metal startup code.
 * Startup code runs from envm on MSS reset
 *
 * You can find details on the PolarFireSoC Memory map in the mpfs-memory-hierarchy.md
 * which can be found under the link below:
 * https://github.com/polarfire-soc/polarfire-soc-documentation
 * 
 */
 
OUTPUT_ARCH( "riscv" )
ENTRY(_start)

/*-----------------------------------------------------------------------------

-- MSS hart Reset vector

The MSS reset vector for each hart is stored securely in the MPFS.
The most common usage will be where the reset vector for each hart will be set
to the start of the envm at address 0x2022_0100, giving 128K-256B of contiguous
non-volatile storage. Normally this is where the initial boot-loader will 
reside. (Note: The first 256B page of envm is used for metadata associated with 
secure boot. When not using secure boot (mode 0,1), this area is still reserved 
by convention. It allows easier transition from non-secure to secure boot flow
during the development process.
When debugging a bare metal program that is run out of reset from envm, a linker 
script will be used whereby the program will run from LIM instead of envm.
In this case, the reset vector in the linker script is normally set to the 
start of LIM, 0x0800_0000.
This means you are not continually programming the envm each time you load a 
program and there is no limitation with break points when debugging.
See the mpfs-lim.ld example linker script when runing from LIM.

------------------------------------------------------------------------------*/


MEMORY
{
    /* In this example, our reset vector is set to point to the */
    /* start at page 1 of the envm */
    envm (rx) : ORIGIN  = 0x20220100, LENGTH = 128k - 0x100
    dtim (rwx) : ORIGIN  = 0x01000000, LENGTH = 7k       
    e51_itim (rwx)     : ORIGIN = 0x01800000, LENGTH = 28k
    u54_1_itim (rwx)   : ORIGIN = 0x01808000, LENGTH = 28k
    u54_2_itim (rwx)   : ORIGIN = 0x01810000, LENGTH = 28k
    u54_3_itim (rwx)   : ORIGIN = 0x01818000, LENGTH = 28k
    u54_4_itim (rwx)   : ORIGIN = 0x01820000, LENGTH = 28k
    l2lim (rwx)        : ORIGIN = 0x08000000, LENGTH = 256k
    scratchpad(rwx)    : ORIGIN = 0x0A000000, LENGTH = 256k
    /* This 1K of DTIM is used to run code when switching the envm clock */
    switch_code_dtim (rx) : ORIGIN = 0x01001c00, LENGTH = 1k 
    /* DDR sections example */
    ddr_cached_32bit (rwx) : ORIGIN  = 0x80000000, LENGTH = 768M
    ddr_non_cached_32bit (rwx) : ORIGIN  = 0xC0000000, LENGTH = 256M
    ddr_wcb_32bit (rwx) : ORIGIN  = 0xD0000000, LENGTH = 256M
    ddr_cached_38bit (rwx) : ORIGIN  = 0x1000000000, LENGTH = 1024M
    ddr_non_cached_38bit (rwx) : ORIGIN  = 0x1400000000, LENGTH = 0k
    ddr_wcb_38bit (rwx) : ORIGIN  = 0x1800000000, LENGTH  = 0k
}
                               
HEAP_SIZE           = 8k;   /* needs to be calculated for your application */

/* STACK_SIZE_PER_HART needs to be calculated for your */
/* application. Must be aligned */
/* Also Thread local storage (AKA hart local storage) allocated for each hart */
/* as part of the stack
/* So memory map will look like once apportion in startup code: */
/*   */
/* stack hart0  Actual Stack size = (STACK_SIZE_PER_HART - HLS_DEBUG_AREA_SIZE) */
/* TLS hart 0   */
/* stack hart1  */
/* TLS hart 1   */
/* etc */
/* note: HLS_DEBUG_AREA_SIZE is defined in mss_sw_config.h */
STACK_SIZE_PER_HART = 8k;                     

/*
 * Stack size for each hart's application.
 * These are the stack sizes that will be allocated to each hart before starting
 * each hart's application function, e51(), u54_1(), u54_2(), u54_3(), u54_4().
 */
STACK_SIZE_E51_APPLICATION = 8k;
STACK_SIZE_U54_1_APPLICATION = 8k;
STACK_SIZE_U54_2_APPLICATION = 8k;
STACK_SIZE_U54_3_APPLICATION = 8k;
STACK_SIZE_U54_4_APPLICATION = 8k;

SECTIONS
{
    PROVIDE(__envm_start = ORIGIN(envm));
    PROVIDE(__envm_end = ORIGIN(envm) + LENGTH(envm));
    PROVIDE(__l2lim_start = ORIGIN(l2lim));
    PROVIDE(__l2lim_end = ORIGIN(l2lim) + LENGTH(l2lim));
    PROVIDE(__ddr_cached_32bit_start = ORIGIN(ddr_cached_32bit));
    PROVIDE(__ddr_cached_32bit_end = ORIGIN(ddr_cached_32bit) + LENGTH(ddr_cached_32bit));
    PROVIDE(__ddr_non_cached_32bit_start = ORIGIN(ddr_non_cached_32bit));
    PROVIDE(__ddr_non_cached_32bit_end = ORIGIN(ddr_non_cached_32bit) + LENGTH(ddr_non_cached_32bit));
    PROVIDE(__ddr_wcb_32bit_start = ORIGIN(ddr_wcb_32bit));
    PROVIDE(__ddr_wcb_32bit_end = ORIGIN(ddr_wcb_32bit) + LENGTH(ddr_wcb_32bit));
    PROVIDE(__ddr_cached_38bit_start = ORIGIN(ddr_cached_38bit));
    PROVIDE(__ddr_cached_38bit_end = ORIGIN(ddr_cached_38bit) + LENGTH(ddr_cached_38bit));
    PROVIDE(__ddr_non_cached_38bit_start = ORIGIN(ddr_non_cached_38bit));
    PROVIDE(__ddr_non_cached_38bit_end = ORIGIN(ddr_non_cached_38bit) + LENGTH(ddr_non_cached_38bit));
    PROVIDE(__ddr_wcb_38bit_start = ORIGIN(ddr_wcb_38bit));
    PROVIDE(__ddr_wcb_38bit_end = ORIGIN(ddr_wcb_38bit) + LENGTH(ddr_wcb_38bit));
    PROVIDE(__dtim_start = ORIGIN(dtim));
    PROVIDE(__dtim_end = ORIGIN(dtim) + LENGTH(dtim));
    PROVIDE(__e51itim_start = ORIGIN(e51_itim));
    PROVIDE(__e51itim_end = ORIGIN(e51_itim) + LENGTH(e51_itim));
    PROVIDE(__u54_1_itim_start = ORIGIN(u54_1_itim));
    PROVIDE(__u54_1_itim_end = ORIGIN(u54_1_itim) + LENGTH(u54_1_itim));
    PROVIDE(__u54_2_itim_start = ORIGIN(u54_2_itim));
    PROVIDE(__u54_2_itim_end = ORIGIN(u54_2_itim) + LENGTH(u54_2_itim));
    PROVIDE(__u54_3_itim_start = ORIGIN(u54_3_itim));
    PROVIDE(__u54_3_itim_end = ORIGIN(u54_3_itim) + LENGTH(u54_3_itim));
    PROVIDE(__u54_4_itim_start = ORIGIN(u54_4_itim));
    PROVIDE(__u54_4_itim_end = ORIGIN(u54_4_itim) + LENGTH(u54_4_itim));
    
    . = __envm_start;
    .text : ALIGN(0x10)
    {
        __text_load = LOADADDR(.text);
        __text_start = .; 
        *(.text.init)
        /*  *entry.o(.text); */
        . = ALIGN(0x10);
        *(.text .text.* .gnu.linkonce.t.*)
        *(.plt)
        . = ALIGN(0x10);

        KEEP (*crtbegin.o(.ctors))
        KEEP (*(EXCLUDE_FILE (*crtend.o) .ctors))
        KEEP (*(SORT(.ctors.*)))
        KEEP (*crtend.o(.ctors))
        KEEP (*crtbegin.o(.dtors))
        KEEP (*(EXCLUDE_FILE (*crtend.o) .dtors))
        KEEP (*(SORT(.dtors.*)))
        KEEP (*crtend.o(.dtors))

        *(.rodata .rodata.* .gnu.linkonce.r.*)
        *(.sdata2 .sdata2.* .gnu.linkonce.s2.*)
        *(.gcc_except_table) 
        *(.eh_frame_hdr)
        *(.eh_frame)

        KEEP (*(.init))
        KEEP (*(.fini))

        PROVIDE_HIDDEN (__preinit_array_start = .);
        KEEP (*(.preinit_array))
        PROVIDE_HIDDEN (__preinit_array_end = .);
        PROVIDE_HIDDEN (__init_array_start = .);
        KEEP (*(SORT(.init_array.*)))
        KEEP (*(.init_array))
        PROVIDE_HIDDEN (__init_array_end = .);
        PROVIDE_HIDDEN (__fini_array_start = .);
        KEEP (*(.fini_array))
        KEEP (*(SORT(.fini_array.*)))
        PROVIDE_HIDDEN (__fini_array_end = .);
        
        *(.srodata.cst16) *(.srodata.cst8) *(.srodata.cst4) *(.srodata.cst2)
        *(.srodata*)
        
        . = ALIGN(0x10);
        __text_end = .;
    } > envm

    .l2_scratchpad : ALIGN(0x10)
    { 
        __l2_scratchpad_load = LOADADDR(.l2_scratchpad);
        __l2_scratchpad_start = .;
        __l2_scratchpad_vma_start = .; 
        *(.l2_scratchpad)
        . = ALIGN(0x10);
        __l2_scratchpad_end = .;
        __l2_scratchpad_vma_end = .;
    } >scratchpad AT> envm
  
    /* 
     *   The .ram_code section will contain the code that is run from RAM.
     *   We are using this code to switch the clocks including envm clock.
     *   This can not be done when running from envm
     *   This will need to be copied to ram, before any of this code is run.
     */
    .ram_code :
    {
        . = ALIGN (4);
        __sc_load = LOADADDR (.ram_code);
        __sc_start = .;
        *(.ram_codetext)        /* .ram_codetext sections (code) */
        *(.ram_codetext*)       /* .ram_codetext* sections (code)  */
        *(.ram_coderodata)      /* read-only data (constants) */
        *(.ram_coderodata*)
        . = ALIGN (4);
        __sc_end = .;
    } >switch_code_dtim AT>envm
    
    /* 
    *   The .ddr_code section will contain the code that is run from DDR.
    *   This is to verify DDR working as expeted
    */
    .ddr_code :
    {
        . = ALIGN (4);
        __ddr_load = LOADADDR (.ram_code);
        __ddr_start = .;
        *(.ddr_codetext)        /* .ram_codetext sections (code) */
        *(.ddr_codetext*)       /* .ram_codetext* sections (code)  */
        *(.ddr_coderodata)      /* read-only data (constants) */
        *(.ddr_coderodata*)
        . = ALIGN (4);
        __ddr_end = .;
    } >ddr_cached_32bit AT>envm

    /* short/global data section */
    .sdata : ALIGN(0x10)
    {
        __sdata_load = LOADADDR(.sdata);
        __sdata_start = .; 
        /* offset used with gp(gloabl pointer) are +/- 12 bits, so set 
           point to middle of expected sdata range */
        /* If sdata more than 4K, linker used direct addressing. 
           Perhaps we should add check/warning to linker script if sdata is > 4k */
        __global_pointer$ = . + 0x800;
        *(.sdata .sdata.* .gnu.linkonce.s.*)
        . = ALIGN(0x10);
        __sdata_end = .;
    } > l2lim AT > envm
    
    /* data section */
    .data : ALIGN(0x10)
    { 
        __data_load = LOADADDR(.data);
        __data_start = .; 
        *(.got.plt) *(.got)
        *(.shdata)
        *(.data .data.* .gnu.linkonce.d.*)
        . = ALIGN(0x10);
        __data_end = .;
    } > l2lim AT > envm

    /* sbss section */
    .sbss : ALIGN(0x10)
    {
        __sbss_start = .;
        *(.sbss .sbss.* .gnu.linkonce.sb.*)
        *(.scommon)
        . = ALIGN(0x10);
        __sbss_end = .;
    } > l2lim
  
    /* sbss section */
    .bss : ALIGN(0x10)
    { 
        __bss_start = .;
        *(.shbss)
        *(.bss .bss.* .gnu.linkonce.b.*)
        *(COMMON)
        . = ALIGN(0x10);
        __bss_end = .;
    } > l2lim

    /* End of uninitialized data segment */
    _end = .;
  
    .heap : ALIGN(0x10)
    {
        __heap_start = .;
        . += HEAP_SIZE;
        __heap_end = .;
        . = ALIGN(0x10);
        _heap_end = __heap_end;
    } > l2lim
   
    /* must be on 4k boundary (0x1000) - corresponds to page size, when using 
       memory mem */
    /* protection */
    /* .stack : ALIGN(0x1000) */
    .stack : ALIGN(0x10)
    {
        PROVIDE(__stack_bottom_h0$ = .);
        PROVIDE(__app_stack_bottom_h0 = .);
        . += STACK_SIZE_E51_APPLICATION;
        PROVIDE(__app_stack_top_h0 = .);
        PROVIDE(__stack_top_h0$ = .);
    
        PROVIDE(__stack_bottom_h1$ = .);
        PROVIDE(__app_stack_bottom_h1$ = .);
        . += STACK_SIZE_U54_1_APPLICATION;
        PROVIDE(__app_stack_top_h1 = .);
        PROVIDE(__stack_top_h1$ = .);
    
        PROVIDE(__stack_bottom_h2$ = .);
        PROVIDE(__app_stack_bottom_h2 = .);
        . += STACK_SIZE_U54_2_APPLICATION;
        PROVIDE(__app_stack_top_h2 = .);
        PROVIDE(__stack_top_h2$ = .);
    
        PROVIDE(__stack_bottom_h3$ = .);
        PROVIDE(__app_stack_bottom_h3 = .);
        . += STACK_SIZE_U54_3_APPLICATION;
        PROVIDE(__app_stack_top_h3 = .);
        PROVIDE(__stack_top_h3$ = .);
    
        PROVIDE(__stack_bottom_h4$ = .);
        PROVIDE(__app_stack_bottom_h4 = .);
        . += STACK_SIZE_U54_4_APPLICATION;
        PROVIDE(__app_stack_top_h4 = .);
        PROVIDE(__stack_top_h4$ = .);
        /* place __start_of_free_lim$ after last allocation of l2_lim */
        . = ALIGN(0x10);
        PROVIDE(__start_of_free_lim$ = .);
    } > l2lim
}

