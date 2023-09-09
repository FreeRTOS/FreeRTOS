/* Flash Memory Banks
   For Wytec Dragon12, Technological Arts Adapt9S12DP256
   with DBug12 v4 bootloader
   
   Author Jefferson L Smith; Robotronics, Inc.
  */

MEMORY
{
  page0 (rwx) : ORIGIN = 0x0, LENGTH = 256

  /* RAM */
  data (rwx)  : ORIGIN = 0x1000, LENGTH = 12k

  eeprom (rx): ORIGIN = 0x0400, LENGTH = 3k
  text (rx)  : ORIGIN = 0x4000, LENGTH = 16k
  
  /* high fixed bank, reserve 0x100 vectors and security. */
  text_h (rx)  : ORIGIN = 0xc000, LENGTH = 16k-0x100
  
  /* Flash memory banks */
  bank0  (rx)   : ORIGIN = 0x0d0000, LENGTH = 16k
  bank1  (rx)   : ORIGIN = 0x0d4000, LENGTH = 16k
  bank2  (rx)   : ORIGIN = 0x0d8000, LENGTH = 16k
  bank3  (rx)   : ORIGIN = 0x0dc000, LENGTH = 16k
  bank4  (rx)   : ORIGIN = 0x0e0000, LENGTH = 16k
  bank5  (rx)   : ORIGIN = 0x0e4000, LENGTH = 16k
  bank6  (rx)   : ORIGIN = 0x0e8000, LENGTH = 16k
  bank7  (rx)   : ORIGIN = 0x0ec000, LENGTH = 16k
  bank8  (rx)   : ORIGIN = 0x0f0000, LENGTH = 16k
  bank9  (rx)   : ORIGIN = 0x0f4000, LENGTH = 16k
  bank10 (rx)   : ORIGIN = 0x0f8000, LENGTH = 16k
  bank11 (rx)   : ORIGIN = 0x0fc000, LENGTH = 16k
  bank12 (rx)   : ORIGIN = 0x100000, LENGTH = 16k
  bank13 (rx)   : ORIGIN = 0x104000, LENGTH = 16k
  
  bank14 (rx)   : ORIGIN = 0x108000, LENGTH = 16k
  bank15 (rx)   : ORIGIN = 0x10c000, LENGTH = 16k-0x100
}
/* Setup the stack on the top of the data memory bank.  */
PROVIDE (_stack = 0x1000+12k);

/* interrupt/reset vectors*/
vectors_addr = 0x10ff80;

SECTIONS
{
  /* PPAGE memory banks */

  .bank2 :
  {
    ../Common/Minimal/flash.o(.text .rodata)
    *(.bank2)
  } > bank2

  .bank3 :
  {
    ParTest.o(.text .rodata)
    *(.bank3)
  } > bank3

}

