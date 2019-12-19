ENTRY(_start)
MEMORY
{
    FLASH : ORIGIN = 0x10001000, LENGTH = 0x00006000
    ISRAM : ORIGIN = 0x60000000, LENGTH = 0x00001000
}
SECTIONS
{
    .text : {
        . = ALIGN(0x4);
        __text_start = .;
        *(.text)
        *(.text*)
        . = ALIGN(0x4);
        __text_end = .;
    } > FLASH
    .rodata : {
        . = ALIGN(0x4);
        __rodata_start = .;
        KEEP(*(.rodata))
        KEEP(*(.rodata*))
        . = ALIGN(0x4);
        KEEP(*(SORT(.table.*)))
        . = ALIGN(0x4);
        __srvdata_start = .;
        KEEP(*(.srv.data))
        KEEP(*(.srv.data*))
        __srvdata_end = .;
        . = ALIGN(0x4);
        __rodata_end = .;
    } > FLASH
    __data_copy_start = .;
    .data : AT(__data_copy_start) {
        . = ALIGN(0x4);
        __data_start = .;
        KEEP(*(.exp_table))
        KEEP(*(.data))
        KEEP(*(.data*))
        . = ALIGN(0x4);
        __data_end = .;
    } > ISRAM
    .bss : AT(ADDR(.data) + SIZEOF(.data)) {
        . = ALIGN(0x4);
        __bss_start = .;
        KEEP(*(.bss))
        KEEP(*(.bss*))
        *(COMMON*)
        . = ALIGN(0x4);
        __bss_end = .;
    } > ISRAM
}
