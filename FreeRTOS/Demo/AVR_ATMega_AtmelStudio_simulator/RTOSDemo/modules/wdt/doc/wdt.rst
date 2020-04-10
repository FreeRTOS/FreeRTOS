======================
WDT driver
======================
The Watchdog Timer (WDT) is a system function for monitoring correct program operation. It allows to
recover from error situations such as runaway or deadlocked code.  The WDT is a timer, configured to a
predefined timeout period, and is constantly running when enabled. If the WDT is not Reset within the
timeout period, it will issue a System Reset. The WDT is reset by executing the WDR (Watchdog Timer
Reset) instruction from the application code.

Features
--------
* Initialization

Applications
------------
* Recover MCU from deadlock condition 

Dependencies
------------
* CLK for clock
* CPUINT/PMIC for Interrupt

Security
--------
* Configuration Change Protection
* Lock bit in the Status register

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