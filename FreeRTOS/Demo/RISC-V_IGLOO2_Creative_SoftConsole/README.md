## FreeRTOS port for Mi-V Soft Processor

### HW Platform and FPGA design:
This project is tested on following hardware platforms:

RISCV-Creative-Board
- [RISC-V Creative board Mi-V Sample Design](https://github.com/RISCV-on-Microsemi-FPGA/RISC-V-Creative-Board/tree/master/Programming_The_Target_Device/PROC_SUBSYSTEM_MIV_RV32IMA_BaseDesign)

PolarFire-Eval-Kit
- [PolarFire Eval Kit RISC-V Sample Design](https://github.com/RISCV-on-Microsemi-FPGA/PolarFire-Eval-Kit/tree/master/Programming_The_Target_Device/MIV_RV32IMA_L1_AHB_BaseDesign)

SmartFusion2-Advanced-Dev-Kit
- [SmartFusion2 Advanced Development Kit RISC-V Sample Design](https://github.com/RISCV-on-Microsemi-FPGA/SmartFusion2-Advanced-Dev-Kit/tree/master/Programming_The_Target_Device/PROC_SUBSYSTEM_BaseDesign)

### How to run the FreeRTOS RISC-V port:
To know how to use the SoftConsole workspace, please refer the [Readme.md](https://github.com/RISCV-on-Microsemi-FPGA/SoftConsole/blob/master/README.md)

The miv-rv32im-freertos-port-test is a self contained project. This project demonstrates 
the FreeRTOS running with Microsemi RISC-V processor. This project creates  two 
tasks and runs them at regular intervals.
    
This example project requires USB-UART interface to be connected to a host PC. 
The host PC must connect to the serial port using a terminal emulator such as 
TeraTerm or PuTTY configured as follows:
    
        - 115200 baud
        - 8 data bits
        - 1 stop bit
        - no parity
        - no flow control
    
The ./hw_platform.h file contains the design related information that is required 
for this project. If you update the design, the hw_platform.h must be updated 
accordingly.

### FreeRTOS Configurations
You must configure the FreeRTOS as per your applications need. Please read and modify FreeRTOSConfig.h.
E.g. You must set configCPU_CLOCK_HZ parameter in FreeRTOSConfig.h according to the hardware platform 
design that you are using. 

The RISC-V creative board design uses 66Mhz processor clock. The PolarFire Eval Kit design uses 50Mhz processor clock. The SmartFusion2 Adv. Development kit design uses 83Mhz processor clock.

### Microsemi SoftConsole Toolchain
To know more please refer: [SoftConsole](https://github.com/RISCV-on-Microsemi-FPGA/SoftConsole)

### Documentation for Microsemi RISC-V processor, SoftConsole toochain, Debug Tools, FPGA design etc.
To know more please refer: [Documentation](https://github.com/RISCV-on-Microsemi-FPGA/Documentation)
    
