GROUP (
  "libcr_semihost_nf.a"
  "libcr_c.a"
  "libcr_eabihelpers.a"
  "libgcc.a"
)

/*
 *   LPC54018 does not execute from Flash but from RAM (SRAMX). As a result, the
 *   MPU needs to be programmed to set the portion of SRAMX containing kernel
 *   code as privileged Read Only and the portion of SRAMX containing remaining
 *   of the code as Read Only. To facilitate this, SRAMX is divided into two
 *   parts:
 *       1. SRAMX_CODE - 128KB. Contains code.
 *       2. SRAMX_DATA - 64 KB. Contains data (only stack and heap as of now).
 *
 *   SRAM_0_1_2_3 is of size 160 KB which is not a power of 2. ARM v7 MPU requires
 *   the size of an MPU region to be a power of two. Since FreeRTOS Cortex M4 MPU
 *   port programs MPU to grant access to all SRAM (for tasks created using
 *   xTaskCreate), we need to ensure that the size of SRAM region is a power of
 *   two. This is why SRAM_0_1_2_3 is divided into two parts:
 *       1. SRAM_0_1_2_3 - 128 KB. Contains data. Since the size is now a power
 *          of two, an MPU region can be used to grant access to it.
 *       2. SRAM_0_1_2_3_UNUSED - 32 KB. Unused.
 */
MEMORY
{
    /* Define each memory region. */
    BOARD_FLASH (rx)            : ORIGIN = 0x10000000, LENGTH = 0x1000000 /* 16M bytes (alias Flash). */
    SRAMX_CODE (rwx)            : ORIGIN = 0x0,        LENGTH = 0x20000   /* 128K bytes. */
    SRAMX_DATA (rwx)            : ORIGIN = 0x20000,    LENGTH = 0x10000   /* 64K bytes (alias RAM). */
    SRAM_0_1_2_3 (rwx)          : ORIGIN = 0x20000000, LENGTH = 0x20000   /* 128K bytes (alias RAM2). */
    SRAM_0_1_2_3_UNUSED (rwx)   : ORIGIN = 0x20020000, LENGTH = 0x8000    /* 32K bytes. */
    USB_RAM (rwx)               : ORIGIN = 0x40100000, LENGTH = 0x2000    /* 8K bytes (alias RAM3). */
}

/* Initial 32K SRAMX_CODE is used to store kernel functions and
 * initial 512 bytes of SRAM_0_1_2_3 is used to store kernel data. */
__privileged_functions_region_size__  = 32K;
__privileged_data_region_size__       = 512;

/* Symbols needed by the MPU setup code. */
__FLASH_segment_start__ = ORIGIN( SRAMX_CODE );
__FLASH_segment_end__   = __FLASH_segment_start__ + LENGTH( SRAMX_CODE );
__SRAM_segment_start__  = ORIGIN( SRAM_0_1_2_3 );
__SRAM_segment_end__    = __SRAM_segment_start__ + LENGTH( SRAM_0_1_2_3 );

/* Entry point. */
ENTRY(ResetISR)

/* Sections. */
SECTIONS
{
    /* The startup code and FreeRTOS kernel code are placed at the beginning
     * of SRAMX_CODE. */
    .privileged_functions : ALIGN(4)
    {
        FILL(0xff)
        __vectors_start__ = ABSOLUTE(.);
        __FLASH_segment_start__ = __vectors_start__;
        __privileged_functions_start__ = __vectors_start__;
        KEEP(*(.isr_vector))

        /* Global Section Table. */
        . = ALIGN(4);
        __section_table_start = .;

        __data_section_table = .;
        LONG((LOADADDR(.data_RAM) - LOADADDR(.privileged_functions)) + ORIGIN(SRAMX_CODE));
        LONG(     ADDR(.data_RAM));
        LONG(   SIZEOF(.data_RAM));

        LONG((LOADADDR(.data) - LOADADDR(.privileged_functions)) + ORIGIN(SRAMX_CODE));
        LONG(     ADDR(.data));
        LONG(   SIZEOF(.data));

        LONG((LOADADDR(.data_RAM3) - LOADADDR(.privileged_functions)) + ORIGIN(SRAMX_CODE));
        LONG(     ADDR(.data_RAM3));
        LONG(   SIZEOF(.data_RAM3));
        __data_section_table_end = .;

        __bss_section_table = .;
        LONG(    ADDR(.bss_RAM));
        LONG(  SIZEOF(.bss_RAM));

        LONG(    ADDR(.bss));
        LONG(  SIZEOF(.bss));

        LONG(    ADDR(.bss_RAM3));
        LONG(  SIZEOF(.bss_RAM3));
        __bss_section_table_end = .;

        __section_table_end = .;
        /* End of Global Section Table. */

        /* Functions placed after vector table. */
        *(.after_vectors*)

        /* Kernel code. */
        *(privileged_functions)

        FILL(0xDEAD);
        /* Ensure that non-privileged code is placed after the region reserved for
         * privileged kernel code. */
        /* Note that dot (.) actually refers to the byte offset from the start of
         * the current section (.privileged_functions in this case). As a result,
         * setting dot (.) to a value sets the size of the section. */
        . = __privileged_functions_region_size__;
        __privileged_functions_end__ = .;
    } > SRAMX_CODE AT> BOARD_FLASH

    /* Text Section. */
    .text : ALIGN(4)
    {
        /* Place the FreeRTOS System Calls first in the unprivileged region. */
        __syscalls_flash_start__ = .;
        *(freertos_system_calls)
        __syscalls_flash_end__ = .;

        /* Unprivileged code and RO data. */
       *(.text*)
        KEEP(*freertos*/tasks.o(.rodata*)) /* FreeRTOS Debug Config. */
       *(.rodata .rodata.* .constdata .constdata.*)
       . = ALIGN(4);
    } > SRAMX_CODE AT> BOARD_FLASH

    /* For exception handling/unwind - some Newlib functions (in common
     * with C++ and STDC++) use this. */
    .ARM.extab : ALIGN(4)
    {
        *(.ARM.extab* .gnu.linkonce.armextab.*)
    } > SRAMX_CODE AT> BOARD_FLASH

    __exidx_start = .;

    .ARM.exidx : ALIGN(4)
    {
        *(.ARM.exidx* .gnu.linkonce.armexidx.*)
    } > SRAMX_CODE AT> BOARD_FLASH

    __exidx_end = .;

    /* End of text section. */
    _etext = .;

    /* USB_RAM. */
    .m_usb_data (NOLOAD) :
    {
        *(m_usb_global)
    } > USB_RAM AT> USB_RAM

    /* Data section for SRAMX_DATA. */
    .data_RAM : ALIGN(4)
    {
        FILL(0xff)
        PROVIDE(__start_data_RAM = .);
        PROVIDE(__start_data_SRAMX_DATA = .);
        *(.ramfunc.$RAM)
        *(.ramfunc.$SRAMX)
        *(.data.$RAM)
        *(.data.$SRAMX)
        *(.data.$RAM.*)
        *(.data.$SRAMX.*)
        . = ALIGN(4);
        PROVIDE(__end_data_RAM = .);
        PROVIDE(__end_data_SRAMX_DATA = .);
    } > SRAMX_DATA AT>BOARD_FLASH

    /* Data section for USB_RAM. */
    .data_RAM3 : ALIGN(4)
    {
        FILL(0xff)
        PROVIDE(__start_data_RAM3 = .);
        PROVIDE(__start_data_USB_RAM = .);
        *(.ramfunc.$RAM3)
        *(.ramfunc.$USB_RAM)
        *(.data.$RAM3)
        *(.data.$USB_RAM)
        *(.data.$RAM3.*)
        *(.data.$USB_RAM.*)
        . = ALIGN(4);
        PROVIDE(__end_data_RAM3 = .);
        PROVIDE(__end_data_USB_RAM = .);
     } > USB_RAM AT>BOARD_FLASH

    /* Main Data Section - Reserved. */
    .uninit_RESERVED (NOLOAD) : ALIGN(4)
    {
        _start_uninit_RESERVED = .;
        __privileged_data_start__ = _start_uninit_RESERVED;

        KEEP(*(.bss.$RESERVED*))
       . = ALIGN(4);

        _end_uninit_RESERVED = .;
    } > SRAM_0_1_2_3 AT> SRAM_0_1_2_3

    /* Main DATA section (SRAM_0_1_2_3). */
    .data : ALIGN(4)
    {
        _data = .;
        PROVIDE(__start_data_RAM2 = .);
        PROVIDE(__start_data_SRAM_0_1_2_3 = .);

        /* FreeRTOS kernel data. */
        *(privileged_data)
        FILL(0xDEAD);
        /* Ensure that non-privileged data is placed after the region reserved for
         * privileged kernel data. */
        /* Note that dot (.) actually refers to the byte offset from the start of
         * the current section (.data in this case). As a result, setting
         * dot (.) to a value extends the size of the section. */
        . = __privileged_data_region_size__;
        __privileged_data_end__ = .;

        FILL(0xff)
        *(vtable)
        *(.ramfunc*)
        KEEP(*(CodeQuickAccess))
        KEEP(*(DataQuickAccess))
        *(RamFunction)
        *(.data*)
        . = ALIGN(4);
        _edata = .;
        PROVIDE(__end_data_RAM2 = .);
        PROVIDE(__end_data_SRAM_0_1_2_3 = .);
    } > SRAM_0_1_2_3 AT>BOARD_FLASH

    /* BSS section for SRAMX_DATA. */
    .bss_RAM : ALIGN(4)
    {
        PROVIDE(__start_bss_RAM = .);
        PROVIDE(__start_bss_SRAMX_DATA = .);
        *(.bss.$RAM)
        *(.bss.$SRAMX)
        *(.bss.$RAM.*)
        *(.bss.$SRAMX.*)
        . = ALIGN (. != 0 ? 4 : 1); /* Avoid empty segment. */
        PROVIDE(__end_bss_RAM = .);
        PROVIDE(__end_bss_SRAMX_DATA = .);
    } > SRAMX_DATA AT> SRAMX_DATA

    /* BSS section for USB_RAM. */
    .bss_RAM3 : ALIGN(4)
    {
        PROVIDE(__start_bss_RAM3 = .);
        PROVIDE(__start_bss_USB_RAM = .);
        *(.bss.$RAM3)
        *(.bss.$USB_RAM)
        *(.bss.$RAM3.*)
        *(.bss.$USB_RAM.*)
        . = ALIGN (. != 0 ? 4 : 1); /* Avoid empty segment. */
        PROVIDE(__end_bss_RAM3 = .);
        PROVIDE(__end_bss_USB_RAM = .);
    } > USB_RAM AT> USB_RAM

    /* Main BSS Section. */
    .bss : ALIGN(4)
    {
        _bss = .;
        PROVIDE(__start_bss_RAM2 = .);
        PROVIDE(__start_bss_SRAM_0_1_2_3 = .);
        *(.bss*)
        *(COMMON)
        . = ALIGN(4);
        _ebss = .;
        PROVIDE(__end_bss_RAM2 = .);
        PROVIDE(__end_bss_SRAM_0_1_2_3 = .);
        PROVIDE(end = .);
    } > SRAM_0_1_2_3 AT> SRAM_0_1_2_3

    /* NOINIT section for SRAMX_DATA. */
    .noinit_RAM (NOLOAD) : ALIGN(4)
    {
        PROVIDE(__start_noinit_RAM = .);
        PROVIDE(__start_noinit_SRAMX_DATA = .);
        *(.noinit.$RAM)
        *(.noinit.$SRAMX)
        *(.noinit.$RAM.*)
        *(.noinit.$SRAMX.*)
        . = ALIGN(4);
        PROVIDE(__end_noinit_RAM = .);
        PROVIDE(__end_noinit_SRAMX_DATA = .);
    } > SRAMX_DATA AT> SRAMX_DATA

    /* NOINIT section for USB_RAM. */
    .noinit_RAM3 (NOLOAD) : ALIGN(4)
    {
        PROVIDE(__start_noinit_RAM3 = .);
        PROVIDE(__start_noinit_USB_RAM = .);
        *(.noinit.$RAM3)
        *(.noinit.$USB_RAM)
        *(.noinit.$RAM3.*)
        *(.noinit.$USB_RAM.*)
        . = ALIGN(4);
        PROVIDE(__end_noinit_RAM3 = .);
        PROVIDE(__end_noinit_USB_RAM = .);
    } > USB_RAM AT> USB_RAM

    /* Default NOINIT Section. */
    .noinit (NOLOAD): ALIGN(4)
    {
        _noinit = .;
        PROVIDE(__start_noinit_RAM2 = .);
        PROVIDE(__start_noinit_SRAM_0_1_2_3 = .);
        *(.noinit*)
         . = ALIGN(4);
        _end_noinit = .;
       PROVIDE(__end_noinit_RAM2 = .);
       PROVIDE(__end_noinit_SRAM_0_1_2_3 = .);
    } > SRAM_0_1_2_3 AT> SRAM_0_1_2_3

    /* Reserve and place Heap within memory map. */
    _HeapSize = 0x1000;
    .heap : ALIGN(4)
    {
        _pvHeapStart = .;
        . += _HeapSize;
        . = ALIGN(4);
        _pvHeapLimit = .;
    } > SRAMX_DATA

     /* Reserve space in memory for Stack. */
     _StackSize = 0x1000;
    .heap2stackfill  :
    {
        . += _StackSize;
    } > SRAMX_DATA

    /* Locate actual Stack in memory map. */
    .stack ORIGIN(SRAMX_DATA) + LENGTH(SRAMX_DATA) - _StackSize - 0:  ALIGN(4)
    {
        _vStackBase = .;
        . = ALIGN(4);
        _vStackTop = . + _StackSize;
    } > SRAMX_DATA

    /* ## Create checksum value (used in startup). ## */
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
    _image_start = LOADADDR(.privileged_functions);
    _image_end = LOADADDR(.data) + SIZEOF(.data);
    _image_size = _image_end - _image_start;

    /* Provide symbols for LPC540xx parts for startup code to use
     * to set image to be plain load image or XIP.
     * Config : Plain load image = true. */
    __imghdr_loadaddress = ADDR(.privileged_functions);
    __imghdr_imagetype = 1;
}