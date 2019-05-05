GROUP (
    "libgcc.a"
    "libc_nano.a"
    "libm.a"
    "libcr_newlib_semihost.a"
)

MEMORY
{
    /* Define each memory region. */
    PROGRAM_FLASH (rx)  : ORIGIN = 0x10000000, LENGTH = 0xfe00 /* 63.5K bytes (alias Flash). */
    veneer_table (rx)   : ORIGIN = 0x1000fe00, LENGTH = 0x200  /* 0.5K bytes (alias Flash2). */
    Ram0 (rwx)          : ORIGIN = 0x30000000, LENGTH = 0x8000 /* 32K bytes (alias RAM). */
}

/* Define a symbol for the top of each memory region. */
__base_PROGRAM_FLASH    = 0x10000000;           /* PROGRAM_FLASH. */
__base_Flash            = 0x10000000;           /* Flash. */
__top_PROGRAM_FLASH     = 0x10000000 + 0xfe00;  /* 63.5K bytes */
__top_Flash             = 0x10000000 + 0xfe00;  /* 63.5K bytes */

__base_veneer_table     = 0x1000fe00;           /* veneer_table. */
__base_Flash2           = 0x1000fe00;           /* Flash2. */
__top_veneer_table      = 0x1000fe00 + 0x200;   /* 0.5K bytes. */
__top_Flash2            = 0x1000fe00 + 0x200;   /* 0.5K bytes. */

__base_Ram0             = 0x30000000;           /* Ram0. */
__base_RAM              = 0x30000000;           /* RAM. */
__top_Ram0              = 0x30000000 + 0x8000;  /* 32K bytes. */
__top_RAM               = 0x30000000 + 0x8000;  /* 32K bytes. */

/* Entry point. */
ENTRY(ResetISR)

SECTIONS
{
    /* Veneer Table Section (Non-Secure Callable). */
    .text_Flash2 : ALIGN(4)
    {
        FILL(0xff)
        *(.text_Flash2*) /* For compatibility with previous releases. */
        *(.text_veneer_table*) /* For compatibility with previous releases. */
        *(.text.$Flash2*)
        *(.text.$veneer_table*)
        *(.rodata.$Flash2*)
        *(.rodata.$veneer_table*)
    } > veneer_table

    /* Vector Table Section. */
    .text : ALIGN(4)
    {
        FILL(0xff)
        __vectors_start__ = ABSOLUTE(.);
        KEEP(*(.isr_vector))

        /* Global Section Table. */
        . = ALIGN(4);
        __section_table_start = .;

        __data_section_table = .;
        LONG(LOADADDR(.data));
        LONG(    ADDR(.data));
        LONG(  SIZEOF(.data));
        __data_section_table_end = .;

        __bss_section_table = .;
        LONG(    ADDR(.bss));
        LONG(  SIZEOF(.bss));
        __bss_section_table_end = .;

        __section_table_end = .;
        /* End of Global Section Table. */

        *(.after_vectors*)
    } > PROGRAM_FLASH

    /* Main Text Section. */
    .text : ALIGN(4)
    {
        *(.text*)
        *(.rodata .rodata.* .constdata .constdata.*)
        . = ALIGN(4);
    } > PROGRAM_FLASH

    /* For exception handling/unwind - some Newlib functions (in common
     * with C++ and STDC++) use this. */
    .ARM.extab : ALIGN(4)
    {
        *(.ARM.extab* .gnu.linkonce.armextab.*)
    } > PROGRAM_FLASH

    __exidx_start = .;
    .ARM.exidx : ALIGN(4)
    {
        *(.ARM.exidx* .gnu.linkonce.armexidx.*)
    } > PROGRAM_FLASH
    __exidx_end = .;

    /* TrustZone Secure Gateway Stubs Section. */
    .gnu.sgstubs : ALIGN (32)
    {
        . = ALIGN(32);
        _start_sg = .;
        *(.gnu.sgstubs*)
        . = ALIGN(32);
        _end_sg = .;
    } > PROGRAM_FLASH

    /* Text Section End. */
    _etext = .;

    /* Uninit Reserved Section. */
    .uninit_RESERVED : ALIGN(4)
    {
        KEEP(*(.bss.$RESERVED*))
        . = ALIGN(4);
        _end_uninit_RESERVED = .;
    } > Ram0

    /* Main Data section (Ram0). */
    .data : ALIGN(4)
    {
        FILL(0xff)
        _data = .;
        *(vtable)
        *(.ramfunc*)
        *(.data*)
        . = ALIGN(4);
        _edata = .;
    } > Ram0 AT>PROGRAM_FLASH

    /* Main BSS Section. */
    .bss : ALIGN(4)
    {
        _bss = .;
        *(.bss*)
        *(COMMON)
        . = ALIGN(4);
        _ebss = .;
        PROVIDE(end = .);
    } > Ram0

    /* Default Noinit Section. */
    .noinit (NOLOAD) : ALIGN(4)
    {
        _noinit = .;
        *(.noinit*)
        . = ALIGN(4);
        _end_noinit = .;
    } > Ram0

    /* Reserve space and place heap in memory map. */
    _HeapSize = 0x800;
    .heap : ALIGN(4)
    {
        _pvHeapStart = .;
        . += _HeapSize;
        . = ALIGN(4);
        _pvHeapLimit = .;
    } > Ram0

    /* Reserve space for stack in memory. */
    _StackSize = 0x800;
    .heap2stackfill :
    {
        . += _StackSize;
    } > Ram0

    /* Place actual stack in memory map. */
    .stack ORIGIN(Ram0) + LENGTH(Ram0) - _StackSize - 0 :  ALIGN(4)
    {
        _vStackBase = .;
        . = ALIGN(4);
        _vStackTop = . + _StackSize;
    } > Ram0

    /* Create checksum value (used in startup). */
    PROVIDE(__valid_user_code_checksum = 0 -
                                         (_vStackTop
                                         + (ResetISR + 1)
                                         + (NMI_Handler + 1)
                                         + (HardFault_Handler + 1)
                                         + (( DEFINED(MemManage_Handler) ? MemManage_Handler : 0 ) + 1)   /* MemManage_Handler may not be defined. */
                                         + (( DEFINED(BusFault_Handler) ? BusFault_Handler : 0 ) + 1)     /* BusFault_Handler may not be defined. */
                                         + (( DEFINED(UsageFault_Handler) ? UsageFault_Handler : 0 ) + 1) /* UsageFault_Handler may not be defined. */
                                         ) );

    /* Provide basic symbols giving location and size of main text block,
     * including initial values of RW data sections. Note that these will need
     * extending to give a complete picture with complex images
     * (e.g multiple Flash banks). */
    _image_start    = LOADADDR(.text);
    _image_end      = LOADADDR(.data) + SIZEOF(.data);
    _image_size     = _image_end - _image_start;
}
