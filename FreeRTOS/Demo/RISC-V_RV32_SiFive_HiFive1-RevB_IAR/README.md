# RISC-V SiFive HiFive1 Rev B Demo

## Requirements
To run this demo, you'll need a few things...

**First** is to download IAR Embedded Workbench for RISC-V. The trial version can be requested [here](https://www.iar.com/products/architectures/risc-v/iar-embedded-workbench-for-risc-v/evaluate-iar-embedded-workbench-for-risc-v/). Once approved you'll be sent an installer and a 14 day evaluation license.

**Second** is to clone this repository including submodules - notably the copy of FreeRTOS/Kernel found under the FreeRtos/Source directory. The RISC-V port files are
used in the demo.

## How to Build
1. Open up IAR Embedded Workbench for RISC-V
2. Click "File" then "Open Workspace"
3. Locate the RTOSDemo.eww file through the file explorer and open
   1. Note - This will load the project into the IDE
4. Click "Project", "Clean" to clean the project
5. Click "Project", "Make" to build the project
   1. Note: F7 will also make the project

## How to Run
To be completed - waiting on board to arrive.

## Troubleshooting
### IAR EW Version
This demo was most recently built on IAR EW for RISC-V version 3.10.1. If your version is older than this, you may have compatability issues.
The version of IAR EW will be displayed on the top of the window. Otherwise, you can view it by navigating to "Help" -> "About" -> "Product Info".