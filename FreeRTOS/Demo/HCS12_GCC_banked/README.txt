##-------------------------------------------------------------------
## Readme.txt
##
## FreeRTOS Port Example for GCC/HCS12, called "Demo/HCS12_GCC_banked"
## Author Jefferson L Smith
##
##-------------------------------------------------------------------
This project stationery is designed to get you up and running quickly with GCC for MC9S12.

This port is tested with the development board Dragon12 (http://www.evbplus.com/ ).

This GCC release has been tested:
  gnu-m68hc1x 3.1 from http://m68hc11.serveftp.org/

The following folders are derived from GEL 1.6 (http://gel.sourceforge.net/ ):
- sys: starting point for GEL system includes
- asm-m68hcs12: specific 9S12 support, mostly referenced by sys

The demo was partially derived from Demo HCS12_CodeWarrior_banked.


##------------------------------------------------------------------------
##  Getting Started
##------------------------------------------------------------------------

---
The COM (SCI) port to use can be changed in the Makefile. Change this parameter in
CPPFLAGS: -DM6812_DEF_SCI=1
0 uses SCI0
1 uses SCI1

---
The LED port address can be changed in the Makefile. Change this parameter in
CPPFLAGS: -DPORT_LED=M6811_PORTB

The known ports are: M6811_PORTA, M6811_PORTB, M6811_PTT, M6811_PTP, M6811_PTM, and M6811_PTH. Any other port address could be used.

If a known port (above) is used, "startup.c" will initialize the correct port. If any other port is used (by typing the port address), it will need to be manually configured as outputs.


##------------------------------------------------------------------------
##  Memory Banks (PPAGE)
##------------------------------------------------------------------------

---
HCS12_GCC_banked uses two methods of placing certain code/data into PPAGE banks. The simple way is to edit each function's prototype or definition with an attribute macro ATTR_BANKn as defined in "cpu.h". Replace the 'n' with the number of the bank [0..13].

Also see "memory.x" sections .bank2 and .bank3 for examples of linking .text and .rodata of a specific ".o" object file into a specific bank.


##------------------------------------------------------------------------
##  Technical Issues
##------------------------------------------------------------------------

---
Passing a function pointer to vCreateTasks() does not include the PPAGE value. The result is that it's stack is initialized with PPAGE 0x30. That is not a problem because GCC generates a "trampoline" routine in unbanked memory which will bounce to the far address of the target function. The 16-bit function pointer passed is actually pointing to that trampoline. The trampoline would only be called once--when starting the task.

---
Here are three aspects to consider when defining ISR:

1. The ISR might be simple enough to not generate header code such as saving _.frame and has no local variables. This type can be defined as a normal routine (no interrupt attribute) or "naked" if it were implemented in this GCC. IMPORTANT: Use these special port macros defined in "portmacro.h". They go at the beginning and end of the function:

portISR_HEAD()  First line of the ISR
portISR_TAIL()  Last line of the ISR

This ensures all the needed softregs (pseudo CPU registers) are saved on the stack in case of a task swap within the ISR. Because this sets up the stack for a task swap, portTASK_SWITCH_FROM_ISR() could also be used in the ISR to save time and stack space.

2. The ISR may have one or more local variables. Define it using the interrupt attribute. The special portTASK_SWITCH_FROM_ISR() won't work. If a task is awakened within this ISR, use taskYIELD() which completely saves the appropriate softregs again and uses more stack.

3. Writing an ISR in assembly avoids the challenges with compiler-generated code. The steps would have to execute the way they execute in the C ISR.

---
If editing "startup.c", note that the function __premain() executes before global variables are initialized, and before the BSS section is cleared. So using any global variables may have unexpected results.

---
If you need to use other softregs, edit "portmacro.h" and "port.c" to save/restore them For example _.d1, _.d2, enabled by "-msoft-reg-count=2" on gcc commandline.

This port expects "-msoft-reg-count=0". This might be the gcc default, but is specified to be certain.


##------------------------------------------------------------------------
##  TODO
##------------------------------------------------------------------------

---
