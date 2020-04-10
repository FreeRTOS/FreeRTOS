======================
SPI driver
======================
Serial Peripheral Interface(SPI) driver Full duplex, Three-wire Synchronous Data Trasnfer in Master or Slave mode of operation.
Peripheral is clocked by the peripheral clock and supports seven programmable bit rated. Optional Clock double option is also available in Master mode

Features
--------
* Initialization

Applications
------------
* Fast communication between an AVR device and peripheral devices or several microcontrollers.

Dependencies
------------
* CLKCTRL for clock
* CPUINT for Interrupt
* PORT for I/O Lines and Connections
* UPDI for debug

Concurrency
-----------
N/A

Limitations
-----------
N/A

Known issues and workarounds
----------------------------
N/A

Important Note on CS pin selection:
------------------------------------

To configure CS pin for SPI master, 
* Go to PINMUX UI
* Assign any of the available Output pins for CS

For Clickboards,
Slave select or Chip select can be any of the IO pins. To provide the support,a middleware called "SPI Master with Custom CS" has been added.
To select the CS/SS pin,

* Click on Add Component
* Expand Middleware  
* Click on Interface and select "SPI Master with Custom CS"