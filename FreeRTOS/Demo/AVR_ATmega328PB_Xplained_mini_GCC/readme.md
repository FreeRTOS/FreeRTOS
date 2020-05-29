### Overview
This directory contains a demo project for ATmega328PB Xplained Mini. 

ATmega328PB has 2KB SRAM. Thus the number of demo tasks we put in this demo project is very limited. At minimum, these are included for now: 
- register tasks to verify context switch
- queue consumer-producer tasks to verify kernel primitives
- an integer math task
- a user task to blink on-board LED periodically
- a check task to monitor if all tasks are running

### Jump start
To run the demo:
- Install Atmel Studio IDE.
- Open project file ```AVR_ATmega328PB_Xplained_mini_GCC.atsln```.
- Build and debug. Could either debug with simulator or debugWIRE interface. 

Note that avrdude can be used to program device as well. Though you'll need to manually add external tool, and it does not have debug capability. 

### Reference
- Board details https://www.microchip.com/DevelopmentTools/ProductDetails/atmega328pb-xmini
- Development environment https://www.microchip.com/mplab/avr-support/atmel-studio-7