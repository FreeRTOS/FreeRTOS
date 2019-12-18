This directory contains projects for GCC/IAR/Keil compilers. The targeted MCU is NXP LPC51U68, which is CM0+. 

todo:
- clean up IAR compiler warnings. (Though the warnings are in vendor's driver code, see if we can clean it up. )
- finalize Keil linker script.(Two heap blocks shall be placed in intended RAM banks. Currently, both goes to a same RAM bank.)
- GCC project folder directory name is not consistent with the other two. 
