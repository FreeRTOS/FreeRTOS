/*
 * Multiboot OS definitions and structures.
 */

#ifndef _MULTIBOOT_H_
#define _MULTIBOOT_H_

#define MULTIBOOT_HEADER_MAGIC          0x1BADB002
#define MULTIBOOT_HEADER_FLAGS          0x00010003
#define MULTIBOOT_BOOTLOADER_MAGIC      0x2BADB002

typedef unsigned long t_32 ;

typedef struct multiboot_header
 {
        t_32 Magic;
        t_32 flags;
        t_32 checksum;
        t_32 header_addr;
        t_32 load_addr;
        t_32 load_end_addr;
        t_32 bss_end_addr;
        t_32 entry_addr;
        t_32 video_mode;
        t_32 width;
        t_32 height;
        t_32 depth;
} multiboot_header_t;

/* Symbol table for a.out. */
typedef struct aout_symbol_table
{
        t_32 tabsize;
        t_32 strsize;
        t_32 addr;
        t_32 reserved;
} aout_symbol_table_t;

/* Section header table for ELF. */
typedef struct elf_section_header_table
{
        t_32 num;
        t_32 size;
        t_32 addr;
        t_32 shndx;
} elf_section_header_table_t;

/* Multiboot information. */
typedef struct multiboot_info
{
        t_32 flags;
        t_32 mem_lower;
        t_32 mem_upper;
        t_32 boot_device;
        t_32 cmdline;
        t_32 mods_count;
        t_32 mods_addr;
        union
        {
        	aout_symbol_table_t aout_sym;
            elf_section_header_table_t elf_sec;
        } u;
        t_32 mmap_length;
        t_32 mmap_addr;
} multiboot_info_t;

/* Module structure. */
typedef struct module
{
        t_32 mod_start;
        t_32 mod_end;
        t_32 string;
        t_32 reserved;
} module_t;

/* Memory map. Offset 0 is base_addr_low -no size. */
typedef struct memory_map
{
        t_32 size;
        t_32 base_addr_low;
        t_32 base_addr_high;
        t_32 length_low;
        t_32 length_high;
        t_32 type;
} memory_map_t;

#define CHECK_FLAG(flags,bit)    ((flags) & (1 << (bit)))

#endif /* _MULTIBOOT_H_ */
