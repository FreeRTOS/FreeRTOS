# RISC-V PMP Lab

## Introduction

This is a lab demo showing how to utilize the RISC-V PMP to prevent executing data.  In the case of some kind of data overflow attack, this technique will precent the data overflow from being executable.
Additionally, this demo shows how to write-protect the executable memory so that the data overflow cannot overflow into an executable region.

## Operation

You should compare this demo to the demo located at RISC-V_RV32_SiFive_HiFive1-RevB_FreedomStudio.  The other demo does not utilize any of the PMP features so it is easy to compare the configuration between the two demonstrations.

The special features of this demo occur in the linker script and prvSetupHardware.  In the linker script, addition regions are created so the code will link into the different regions.  These regions must be created according to the alignment and size rules of the PMP.  The linker script is found in bsp/metal.pmp.lds.  The prvSetupHardware function has 3 functions.
 1. it counts a variable from a function in the program memory and a "function" in an array.  This is done here: main:222-230.
 2. The PMP is configured.
 3. The original test is executed to increment the variable in the program memory and the "function" in the data array at lines main:304-307.  There will be an exception from the data execution and the counter will not be incremented.



