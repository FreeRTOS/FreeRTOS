GROUP (
    "libcr_nohost_nf.a"
    "libcr_c.a"
    "libcr_eabihelpers.a"
    "libgcc.a"
)

MEMORY
{
    /* Define each memory region. */
    PROGRAM_FLASH (rx) : ORIGIN = 0x0,        LENGTH = 0x98000 /* 608K bytes. */
    SRAM (rwx) :         ORIGIN = 0x20000000, LENGTH = 0x40000 /* 256K bytes. */
    SRAMX (rwx) :        ORIGIN = 0x4000000,  LENGTH = 0x8000  /* 32K bytes. */
    USB_RAM (rwx) :      ORIGIN = 0x40100000, LENGTH = 0x4000  /* 16K bytes. */
    SRAM4 (rwx) :        ORIGIN = 0x20040000, LENGTH = 0x4000  /* 16K bytes. */
}

    /* Define a symbol for the top of each memory region. */
    __base_PROGRAM_FLASH    = 0x0  ;                 /* PROGRAM_FLASH. */
    __base_Flash            = 0x0 ;                  /* Flash. */
    __top_PROGRAM_FLASH     = 0x0 + 0x98000 ;        /* 608K bytes. */
    __top_Flash             = 0x0 + 0x98000 ;        /* 608K bytes. */

    __base_SRAM             = 0x20000000  ;          /* SRAM. */
    __base_RAM              = 0x20000000 ;           /* RAM. */
    __top_SRAM              = 0x20000000 + 0x40000 ; /* 256K bytes. */
    __top_RAM               = 0x20000000 + 0x40000 ; /* 256K bytes. */

    __base_SRAMX            = 0x4000000  ;           /* SRAMX. */
    __base_RAM2             = 0x4000000 ;            /* RAM2. */
    __top_SRAMX             = 0x4000000 + 0x8000 ;   /* 32K bytes. */
    __top_RAM2              = 0x4000000 + 0x8000 ;   /* 32K bytes. */

    __base_USB_RAM          = 0x40100000  ;          /* USB_RAM. */
    __base_RAM3             = 0x40100000 ;           /* RAM3. */
    __top_USB_RAM           = 0x40100000 + 0x4000 ;  /* 16K bytes. */
    __top_RAM3              = 0x40100000 + 0x4000 ;  /* 16K bytes. */

    __base_SRAM4            = 0x20040000  ;          /* SRAM4. */
    __base_RAM4             = 0x20040000 ;           /* RAM4. */
    __top_SRAM4             = 0x20040000 + 0x4000 ;  /* 16K bytes. */
    __top_RAM4              = 0x20040000 + 0x4000 ;  /* 16K bytes. */

/* Entry point. */
ENTRY(ResetISR)

SECTIONS
{
    /* Vector Table Section. */
    .text : ALIGN(4)
    {
        FILL(0xff)
        __vectors_start__ = ABSOLUTE(.) ;
        KEEP(*(.isr_vector))

        /* Global Section Table. */
        . = ALIGN(4) ;
        __section_table_start = .;

        __data_section_table = .;
        LONG(LOADADDR(.data));
        LONG(    ADDR(.data));
        LONG(  SIZEOF(.data));
        LONG(LOADADDR(.data_RAM2));

        LONG(    ADDR(.data_RAM2));
        LONG(  SIZEOF(.data_RAM2));
        LONG(LOADADDR(.data_RAM3));
        LONG(    ADDR(.data_RAM3));

        LONG(  SIZEOF(.data_RAM3));
        LONG(LOADADDR(.data_RAM4));
        LONG(    ADDR(.data_RAM4));
        LONG(  SIZEOF(.data_RAM4));
        __data_section_table_end = .;

        __bss_section_table = .;
        LONG(    ADDR(.bss));
        LONG(  SIZEOF(.bss));

        LONG(    ADDR(.bss_RAM2));
        LONG(  SIZEOF(.bss_RAM2));

        LONG(    ADDR(.bss_RAM3));
        LONG(  SIZEOF(.bss_RAM3));

        LONG(    ADDR(.bss_RAM4));
        LONG(  SIZEOF(.bss_RAM4));
        __bss_section_table_end = .;

        __section_table_end = . ;
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
       KEEP(*freertos*/tasks.o(.rodata*)) /* FreeRTOS Debug Config */
       *(.rodata .rodata.* .constdata .constdata.*)
       . = ALIGN(32);
       /* End address must be the last address in the region, therefore, -1. */
        __unprivileged_flash_end__ = . - 1;
    } > PROGRAM_FLASH

    /*
     * For exception handling/unwind - some Newlib functions (in common
     * with C++ and STDC++) use this.
     */
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

    _etext = .;

    /* USB_RAM. */
    .m_usb_data (NOLOAD) :
    {
        *(m_usb_global)
    } > USB_RAM AT> USB_RAM

    /* DATA section for SRAMX. */
    .data_RAM2 : ALIGN(4)
    {
        FILL(0xff)
        PROVIDE(__start_data_RAM2 = .) ;
        PROVIDE(__start_data_SRAMX = .) ;
        *(.ramfunc.$RAM2)
        *(.ramfunc.$SRAMX)
        *(.data.$RAM2)
        *(.data.$SRAMX)
        *(.data.$RAM2.*)
        *(.data.$SRAMX.*)
        . = ALIGN(4) ;
        PROVIDE(__end_data_RAM2 = .) ;
        PROVIDE(__end_data_SRAMX = .) ;
     } > SRAMX AT>PROGRAM_FLASH

    /* DATA section for USB_RAM. */
    .data_RAM3 : ALIGN(4)
    {
        FILL(0xff)
        PROVIDE(__start_data_RAM3 = .) ;
        PROVIDE(__start_data_USB_RAM = .) ;
        *(.ramfunc.$RAM3)
        *(.ramfunc.$USB_RAM)
        *(.data.$RAM3)
        *(.data.$USB_RAM)
        *(.data.$RAM3.*)
        *(.data.$USB_RAM.*)
        . = ALIGN(4) ;
        PROVIDE(__end_data_RAM3 = .) ;
        PROVIDE(__end_data_USB_RAM = .) ;
     } > USB_RAM AT>PROGRAM_FLASH

    /* DATA section for SRAM4. */
    .data_RAM4 : ALIGN(4)
    {
        FILL(0xff)
        PROVIDE(__start_data_RAM4 = .) ;
        PROVIDE(__start_data_SRAM4 = .) ;
        *(.ramfunc.$RAM4)
        *(.ramfunc.$SRAM4)
        *(.data.$RAM4)
        *(.data.$SRAM4)
        *(.data.$RAM4.*)
        *(.data.$SRAM4.*)
        . = ALIGN(4) ;
        PROVIDE(__end_data_RAM4 = .) ;
        PROVIDE(__end_data_SRAM4 = .) ;
     } > SRAM4 AT>PROGRAM_FLASH

    /* Uninit Reserved Section. */
    .uninit_RESERVED (NOLOAD) : ALIGN(4)
    {
        _start_uninit_RESERVED = .;
        KEEP(*(.bss.$RESERVED*))
        . = ALIGN(4) ;
        _end_uninit_RESERVED = .;
    } > SRAM AT> SRAM

    /* Main Data section (SRAM). */
    .data : ALIGN(4)
    {
        FILL(0xff)
        _data = . ;
        PROVIDE(__start_data_RAM = .) ;
        PROVIDE(__start_data_SRAM = .) ;

        /* Privileged data - It needs to be 32 byte aligned to satisfy MPU requirements. */
        . = ALIGN(32);
        __privileged_sram_start__ = .;
        *(privileged_data)
        . = ALIGN(32);
        /* End address must be the last address in the region, therefore, -1. */
        __privileged_sram_end__ = . - 1;

        /* Shared data between UserIrqHandler and application tasks. */
        /* It needs to be 32 byte aligned to satisfy MPU requirements. */
        __user_irq_shared_memory_start__ = .;
        *(user_irq_shared_memory)
        . = ALIGN(32);
        /* End address must be the last address in the region, therefore, -1. */
        __user_irq_shared_memory_end__ = . - 1;

        *(vtable)
        *(.ramfunc*)
        KEEP(*(CodeQuickAccess))
        KEEP(*(DataQuickAccess))
        *(RamFunction)
        *(.data*)
        . = ALIGN(4) ;
        _edata = . ;
        PROVIDE(__end_data_RAM = .) ;
        PROVIDE(__end_data_SRAM = .) ;
    } > SRAM AT>PROGRAM_FLASH

    /* BSS section for SRAMX. */
    .bss_RAM2 : ALIGN(4)
    {
        PROVIDE(__start_bss_RAM2 = .) ;
        PROVIDE(__start_bss_SRAMX = .) ;
        *(.bss.$RAM2)
        *(.bss.$SRAMX)
        *(.bss.$RAM2.*)
        *(.bss.$SRAMX.*)
        . = ALIGN (. != 0 ? 4 : 1) ; /* Avoid empty segment. */
        PROVIDE(__end_bss_RAM2 = .) ;
        PROVIDE(__end_bss_SRAMX = .) ;
    } > SRAMX AT> SRAMX

    /* BSS section for USB_RAM. */
    .bss_RAM3 : ALIGN(4)
    {
        PROVIDE(__start_bss_RAM3 = .) ;
        PROVIDE(__start_bss_USB_RAM = .) ;
        *(.bss.$RAM3)
        *(.bss.$USB_RAM)
        *(.bss.$RAM3.*)
        *(.bss.$USB_RAM.*)
        . = ALIGN (. != 0 ? 4 : 1) ; /* Avoid empty segment. */
        PROVIDE(__end_bss_RAM3 = .) ;
        PROVIDE(__end_bss_USB_RAM = .) ;
    } > USB_RAM AT> USB_RAM

    /* BSS section for SRAM4. */
    .bss_RAM4 : ALIGN(4)
    {
        PROVIDE(__start_bss_RAM4 = .) ;
        PROVIDE(__start_bss_SRAM4 = .) ;
        *(.bss.$RAM4)
        *(.bss.$SRAM4)
        *(.bss.$RAM4.*)
        *(.bss.$SRAM4.*)
        . = ALIGN (. != 0 ? 4 : 1) ; /* Avoid empty segment. */
        PROVIDE(__end_bss_RAM4 = .) ;
        PROVIDE(__end_bss_SRAM4 = .) ;
    } > SRAM4 AT> SRAM4

    /* Main BSS Section. */
    .bss : ALIGN(4)
    {
        _bss = .;
        PROVIDE(__start_bss_RAM = .) ;
        PROVIDE(__start_bss_SRAM = .) ;
        *(.bss*)
        *(COMMON)
        . = ALIGN(4) ;
        _ebss = .;
        PROVIDE(__end_bss_RAM = .) ;
        PROVIDE(__end_bss_SRAM = .) ;
        PROVIDE(end = .);
    } > SRAM AT> SRAM

    /* NOINIT section for SRAMX. */
    .noinit_RAM2 (NOLOAD) : ALIGN(4)
    {
        PROVIDE(__start_noinit_RAM2 = .) ;
        PROVIDE(__start_noinit_SRAMX = .) ;
        *(.noinit.$RAM2)
        *(.noinit.$SRAMX)
        *(.noinit.$RAM2.*)
        *(.noinit.$SRAMX.*)
        . = ALIGN(4) ;
        PROVIDE(__end_noinit_RAM2 = .) ;
        PROVIDE(__end_noinit_SRAMX = .) ;
    } > SRAMX AT> SRAMX

    /* NOINIT section for USB_RAM. */
    .noinit_RAM3 (NOLOAD) : ALIGN(4)
    {
        PROVIDE(__start_noinit_RAM3 = .) ;
        PROVIDE(__start_noinit_USB_RAM = .) ;
        *(.noinit.$RAM3)
        *(.noinit.$USB_RAM)
        *(.noinit.$RAM3.*)
        *(.noinit.$USB_RAM.*)
        . = ALIGN(4) ;
        PROVIDE(__end_noinit_RAM3 = .) ;
        PROVIDE(__end_noinit_USB_RAM = .) ;
    } > USB_RAM AT> USB_RAM

    /* NOINIT section for SRAM4. */
    .noinit_RAM4 (NOLOAD) : ALIGN(4)
    {
        PROVIDE(__start_noinit_RAM4 = .) ;
        PROVIDE(__start_noinit_SRAM4 = .) ;
        *(.noinit.$RAM4)
        *(.noinit.$SRAM4)
        *(.noinit.$RAM4.*)
        *(.noinit.$SRAM4.*)
        . = ALIGN(4) ;
        PROVIDE(__end_noinit_RAM4 = .) ;
        PROVIDE(__end_noinit_SRAM4 = .) ;
    } > SRAM4 AT> SRAM4

    /* Default NOINIT section. */
    .noinit (NOLOAD): ALIGN(4)
    {
        _noinit = .;
        PROVIDE(__start_noinit_RAM = .) ;
        PROVIDE(__start_noinit_SRAM = .) ;
        *(.noinit*)
         . = ALIGN(4) ;
        _end_noinit = .;
        PROVIDE(__end_noinit_RAM = .) ;
        PROVIDE(__end_noinit_SRAM = .) ;
    } > SRAM AT> SRAM

    /* Reserve and place Heap within memory map. */
    _HeapSize = 0x1000;
    .heap :  ALIGN(4)
    {
        _pvHeapStart = .;
        . += _HeapSize;
        . = ALIGN(4);
        _pvHeapLimit = .;
    } > SRAM

     /* Reserve space in memory for Stack. */
     _StackSize = 0x1000;
    .heap2stackfill  :
    {
        . += _StackSize;
    } > SRAM

    /* Locate actual Stack in memory map. */
    .stack ORIGIN(SRAM) + LENGTH(SRAM) - _StackSize - 0:  ALIGN(4)
    {
        _vStackBase = .;
        . = ALIGN(4);
        _vStackTop = . + _StackSize;
    } > SRAM

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

    /* Provide basic symbols giving location and size of main text
     * block, including initial values of RW data sections. Note that
     * these will need extending to give a complete picture with
     * complex images (e.g multiple Flash banks). */
    _image_start    = LOADADDR(.text);
    _image_end      = LOADADDR(.data) + SIZEOF(.data);
    _image_size     = _image_end - _image_start;
}
