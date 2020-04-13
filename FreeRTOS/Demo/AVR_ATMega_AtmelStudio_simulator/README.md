### Introduction
This demo project is trying to verify FreeRTOS ATmegaxxxx port implementation in the absense of hardware. Atmel Studio simulator is used in this project to verify clock/timing and task stack implementation. The focus is to ensure register value correctness, instead of high level software behavior correctness, since the simulation runs relatively slow. 

The simulator does not yet provide UART console simulation. Thus to verify point of interests user needs to set break points. 


#### Setting up environment
Download Atmel Studio IDE. Once finish IDE installation, also consider installing FreeRTOS Viewer plugin. 

#### To debug
Double click on ```AVR_ATMega_AtmelStudio_Simulator.atsln```. Follow instructions in AVR MCU Simulator debugging. 


#### To update target and/or peripherals
In Solution Explorer window, right click on RTOSDemo project --> Re-Configure Atmel Start Project. 

### Reference
- [Atmel Studio IDE](https://www.microchip.com/mplab/avr-support/atmel-studio-7)
- [FreeRTOS Viewer plugin](http://atmel-studio-doc.s3-website-us-east-1.amazonaws.com/webhelp/GUID-03D128BB-5CF6-42CB-8787-CB9A863C8F09-en-US-1/index.html)
- [AVR MCU Simulator debugging](http://atmel-studio-doc.s3-website-us-east-1.amazonaws.com/webhelp/GUID-54E8AE06-C4C4-430C-B316-1C19714D122B-en-US-1/index.html?GUID-C73F1111-250E-4106-B5E5-85A512B75E8B)