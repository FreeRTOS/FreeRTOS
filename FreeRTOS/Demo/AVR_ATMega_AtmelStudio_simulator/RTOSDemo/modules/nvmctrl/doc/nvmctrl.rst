===============
NVMCTRL driver
===============
The NVM Controller (NVMCTRL) is the interface between the device, the Flash, and the EEPROM. The
Flash and EEPROM are reprogrammable memory blocks that retain their values even with power off. The
Flash is mainly used for program storage, but can also be used for data storage. The EEPROM is used
for data storage and can be programmed while the CPU is running the program from the Flash.

Features
--------
* Initialization

Applications
------------
* Bootloader application

Dependencies
------------
* CLKCTRL for clock
* CPUINT for interrupts
* UPDI for debug

Note
----
* ISR will be generated only when Global Interrupt checkbox and driver_isr Harness checkbox are enabled

Concurrency
-----------
N/A

Limitations
-----------
N/A

Knows issues and workarounds
----------------------------
N/A

