
#                        mpfs-mss-uart-example

This example project demonstrates the use of the MPFS HAL using the 
MSS UART. This project is targeted at the Microchip Icicle kit.
It provides an example of how to share a peripheral, in this cases a UART 
between code running on separate harts.

Detail:
On reset, the hard reset vector points to code in the 
mpfs_hal\entry.S
The reset vector is pointed to by the following label
_start
as the is address is dictated in the associated linker script
\config\linker_scipts\aloe_bare_metal_ram.ld

In brief, the code run on reset in entry.S doe the following:

   - Initializes the trap vector
   - Initializes x0-x31 registers to zero
   - Enables the Floating Point Unit if preset ( FPU on U54's)
   - Verifies compiler used is 64 bit
   - Sets the GP (global pointer) This is used when code compiled using relax 
      mode.
   - Align on a 64 Byte boundary
   - Read hart ID - Set the SP (stack pointer) so each hart allocated 128K 
      between stack and TLS
   - Check hartID. If hartID == 0 ( the E51), jump to main_first_hart in 
      system_startup.c
   - Check hartID. If hartID != 0, run the wfi instruction. The code will wait 
      here until hart0 wakes up this hart using a software interrupt directed to 
      the hart it wishes to wake.
   - Note: When running in the debugger, the wfi instruction should be treated 
      as a no op.
      A loop is implemented after the wfi which will remain looping until an 
      actual software interrupt 
      occurrence is detected by reading the mip register.
      
E51 code:

   - At this point the E51 code is running in the main_first_hart() in 
      system_startup.c by default.
   - The routines in system_startup are all given the attribute weak. They 
      should not be edited.
   - If you want to write your own versions, please do so in a user code 
      directory. e.g. \hart0
   - main_first_hart() 
            initializes memory
            calls the e51() routine in \hart0\e51()
   - The \e51 contains code associated with the E51.
   - In general, on startup
        
        1. main system clock is switch in  from default startup clock
        2. peripherals are initialized using associated drivers
        3. Other harts are started as required.
        4. E51 code enters infinite loop, and services can be added as required 
          here.
        
   - In our example, uart is initialized
   - hart1 is started
   - The example demonstrates using the uart to write to an attached terminal 
      using hart0 and hart 1.
   - There is a CLI driven from hart0. This allows the user to wake hart 1,2,3 
      and 4.
   - Hart 1,2,3 and 4 write out to the terminal interface demonstrating the use 
      of a shared peripheral.
   - The uart polled tx is protected using a mutex, to allow each hart write to 
      it independently.
      
#### Libero Design:

The Libero design used with this project can be found here :

https://github.com/polarfire-soc/icicle-kit-reference-design.git

## How to use this example

This example project demonstrates sharing a UART across multiple harts.

To use this example:

 - Generate the project into a workspace directory from the softconsole version
   you are using. This point is very important. fro instance :
   SoftConsole_v6.1\extras\workspace.empty
   (Note: you can copy workspace.empty and rename as required)
 - Open the project in SoftConsole
 - Compile the project
 - Open the Remode debugger script bundled in the root of the directory and read
   the document Working_withRenode.md found in the project root directory.
 - Execute the example software project.
The software will display a menu on the command line.

From the menu you can start the U54 harts and observe output on the terminal 
window in Renode. This demonstrates that the harts are running independently.

## UART configuration

On connecting Icicle kit J11 to the host PC, you should see four COM port 
interfaces connected. This example project requires MMUART0. To use this 
project the host PCmust connect to the COM port interface0 using a terminal 
emulator such as HyperTerminal or PuTTY configured as follows:

   - 57600 baud
   - 8 data bits
   - 1 stop bit
   - no parity
   - no flow control

## Target hardware

This example project is targeted at the Icicle kit.
Details are available at the following link:

https://www.microsemi.com/existing-parts/parts/152514

## SoftConsole details

SoftConsole version used to test this project is available at link below:

https://www.microsemi.com/product-directory/design-tools/4879-softconsole#downloads

