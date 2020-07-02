GROUP (
    "libgcc.a"
    "libc_nano.a"
    "libm.a"
    "libcr_newlib_semihost.a"
)

MEMORY
{
    /* Define each memory region. */
    PROGRAM_FLASH (rx)  : ORIGIN = 0x00010000, LENGTH = 0x72000 /* 456K bytes (alias Flash). */
    Ram0 (rwx)          : ORIGIN = 0x20008000, LENGTH = 0x2b000 /* 172K bytes (alias RAM). */
}

/* Define a symbol for the top of each memory region. */
__base_PROGRAM_FLASH  = 0x00010000;             /* PROGRAM_FLASH. */
__base_Flash          = 0x00010000;             /* Flash. */
__top_PROGRAM_FLASH   = 0x00010000 + 0x72000;   /* 456K bytes. */
__top_Flash           = 0x00010000 + 0x72000;   /* 456K bytes. */

__base_Ram0           = 0x20008000;             /* Ram0. */
__base_RAM            = 0x20008000;             /* RAM. */
__top_Ram0            = 0x20008000 + 0x2b000;   /* 172K bytes. */
__top_RAM             = 0x20008000 + 0x2b000;   /* 172K bytes. */

/* Entry point. */
ENTRY(ResetISR)

SECTIONS
{
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

    /* Privileged functions - Section needs to be 32 byte aligned to satisfy MPU requirements. */
    .privileged_functions : ALIGN(32)
    {
        . = ALIGN(32);
        __privileged_functions_start__ = .;
        *(privileged_functions)
        . = ALIGN(32);
        /* End address must be the last address in the region, therefore, -1. */
        __privileged_functions_end__ = . - 1;
    } > PROGRAM_FLASH

    /* FreeRTOS System calls - Section needs to be 32 byte aligned to satisfy MPU requirements. */
    .freertos_system_calls : ALIGN(32)
    {
        . = ALIGN(32);
        __syscalls_flash_start__ = .;
        *(freertos_system_calls)
        . = ALIGN(32);
        /* End address must be the last address in the region, therefore, -1. */
        __syscalls_flash_end__ = . - 1;
    } > PROGRAM_FLASH

    /* Main Text Section - Section needs to be 32 byte aligned to satisfy MPU requirements. */
    .text : ALIGN(32)
    {
        . = ALIGN(32);
        __unprivileged_flash_start__ = .;
        *(.text*)
        *(.rodata .rodata.* .constdata .constdata.*)
        . = ALIGN(32);
        /* End address must be the last address in the region, therefore, -1. */
        __unprivileged_flash_end__ = . - 1;
    } > PROGRAM_FLASH

    /* For exception handling/unwind - some Newlib functions (in common
     * with C++ and StdC++) use this. */
    .ARM.extab : ALIGN(4)
    {
        *(.ARM.extab* .gnu.linkonce.armextab.*)
    } > PROGRAM_FLASH

    .ARM.exidx : ALIGN(4)
    {
        __exidx_start = .;
        *(.ARM.exidx* .gnu.linkonce.armexidx.*)
        __exidx_end = .;
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
        PROVIDE(__start_data_RAM = .);
        PROVIDE(__start_data_Ram0 = .);

        /* Privileged data - It needs to be 32 byte aligned to satisfy MPU requirements. */
        . = ALIGN(32);
        __privileged_sram_start__ = .;
        *(privileged_data)
        . = ALIGN(32);
        /* End address must be the last address in the region, therefore, -1. */
        __privileged_sram_end__ = . - 1;

        *(vtable)
        *(.ramfunc*)
        *(.data*)
        _edata = .;
        PROVIDE(__end_data_RAM = .);
        PROVIDE(__end_data_Ram0 = .);
    } > Ram0 AT>PROGRAM_FLASH

    /* Main BSS Section. */
    .bss : ALIGN(4)
    {
        _bss = .;
        PROVIDE(__start_bss_RAM = .);
        PROVIDE(__start_bss_Ram0 = .);
        *(.bss*)
        *(COMMON)
        . = ALIGN(4);
        _ebss = .;
        PROVIDE(__end_bss_RAM = .);
        PROVIDE(__end_bss_Ram0 = .);
        PROVIDE(end = .);
    } > Ram0 AT>Ram0

    /* Default Noinit Section. */
    .noinit (NOLOAD) : ALIGN(4)
    {
        _noinit = .;
        PROVIDE(__start_noinit_RAM = .);
        PROVIDE(__start_noinit_Ram0 = .);
        *(.noinit*)
        . = ALIGN(4);
        _end_noinit = .;
        PROVIDE(__end_noinit_RAM = .);
        PROVIDE(__end_noinit_Ram0 = .);
    } > Ram0 AT>Ram0

    /* Reserve space and place heap in memory map. */
    _HeapSize = 0x1000;
    .heap : ALIGN(4)
    {
        _pvHeapStart = .;
        . += _HeapSize;
        . = ALIGN(4);
        _pvHeapLimit = .;
    } > Ram0

    /* Reserve space for stack in memory. */
    _StackSize = 0x1000;
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
