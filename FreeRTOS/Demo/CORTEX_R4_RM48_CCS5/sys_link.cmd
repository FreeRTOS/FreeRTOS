/*----------------------------------------------------------------------------*/
/* sys_link.cmd                                                               */
/*                                                                            */

/*----------------------------------------------------------------------------*/
/* Linker Settings                                                            */

/*----------------------------------------------------------------------------*/
/* Memory Map                                                                 */

MEMORY
{
    VECTORS (X)  : origin=0x00000000 length=0x00000020
    FLASH0  (RX) : origin=0x00000020 length=0x0017FFE0
    FLASH1  (RX) : origin=0x00180000 length=0x00180000
    STACKS  (RW) : origin=0x08000000 length=0x00000200
    RAM     (RW) : origin=0x08000200 length=0x0003FE00
 }

/*----------------------------------------------------------------------------*/
/* Section Configuration                                                      */

SECTIONS
{
    .intvecs : {} > VECTORS
    .text    : {} > FLASH0 | FLASH1
    .const   : {} > FLASH0 | FLASH1
    .cinit   : {} > FLASH0 | FLASH1
    .pinit   : {} > FLASH0 | FLASH1
    .heap    : {} > RAM
    .bss     : {} > RAM
    .data    : {} > RAM
    .sysmem  : {} > RAM
}

/*----------------------------------------------------------------------------*/

