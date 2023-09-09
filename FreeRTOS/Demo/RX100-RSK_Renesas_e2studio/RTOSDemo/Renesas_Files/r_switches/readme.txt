PLEASE REFER TO THE APPLICATION NOTE FOR THIS MIDDLEWARE FOR MORE INFORMATION

Switches
========

Document Number 
---------------
N/A

Version
-------
v1.40

Overview
--------
Configures port pins for switches and calls user defined function on switch press. Switch presses can be detected using 
IRQ interrupts or by polling. The benefit of using interrupts is that no extra processing is used for polling and the 
use of a system timer tick is not a requirement. The downside of using interrupts is that callback functions are called 
from within an interrupt so if your ISR is long then it can degrade the real-time response of your system. The benefit 
of polling is that functions are called at the application level and debouncing is supported. The downside to polling is 
that your system must call the R_SWITCHES_Update() on a regular basis which requires extra processing.

Features
--------
* Call one function to setup switches.
* Define function to call when switch is pressed.
* Can be configured to be interrupt or poll driven.

Supported MCUs
--------------
* RX610 Group
* RX621, RX62N Group
* RX62T Group
* RX630 Group
* RX631, RX63N Group
* RX210 Group
* RX111 Group

Boards Tested On
----------------
* RSKRX610
* RSK+RX62N
* RSKRX62T
* RDKRX62N
* RSKRX630
* RSKRX63N
* RDKRX63N
* RSKRX111

Limitations
-----------
* None

Peripherals Used Directly
-------------------------
* None

Required Packages
-----------------
* None

How to add to your project
--------------------------
* Add src\r_switches.c to your project.
* Add an include path to the 'r_switches' directory. 
* Add an include path to the 'r_switches\src' directory.
* Configure middleware through r_switches_config.h.
* Add a #include for r_switches_if.h to files that need to use this package. 

Toolchain(s) Used
-----------------
* Renesas RX v1.02

File Structure
--------------
r_switches
|   readme.txt
|   r_switches_config.h
|   r_switches_if.h
|
\---src
        r_switches.c
                
