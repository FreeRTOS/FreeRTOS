r_bsp Package
=============

Overview
--------
The r_bsp package provides a foundation for code to be built on top of. It provides startup code, iodefines, and MCU
information for different boards. There are 2 folders that make up the r_bsp package. The 'mcu' folder contains files 
that are common to a MCU group. These files provide functionality such as easy register access, CPU functions,
and a file named 'mcu_info.h' for each MCU group. The 'mcu_info.h' file has information about the MCU on the board
and is configured based on the information given in r_bsp_config.h. The information in 'mcu_info.h' is used to help 
configure Renesas middleware that uses the r_bsp package. The 'board' folder has a folder with startup code for each 
supported board.  Which MCU and board is chosen is decided by the settings in 'platform.h'. The user can choose which 
board they are using by uncommenting the include path that applies to their board. For example, if you are using the 
RSK+RX62N then you would uncomment the #include "./board/rskrx62n/r_bsp.h" include path. Users are encouraged to add 
their own boards to the 'board' directory. BSPs are configured by using the r_bsp_config.h file. Each board will have a 
reference configuration file named r_bsp_config_reference.h. The user should copy this file to their project, rename it 
to r_bsp_config.h, and use the options inside the file to configure the BSP for their project.


Features
--------
* Provides foundation to build code on top of.
* Provides MCU startup code.
* Provides SFR access through iodefine.h
* Stores details of MCU in 'mcu_info.h' to help configure Renesas middleware.
* Easily configure BSP through r_bsp_config.h.
* Choose MCU easily by inputting part number details in r_bsp_config.h.
* Provides callbacks for MCU exceptions and the bus error interrupt.
* Supports initializing non-bonded out pins to reduce power
* Provides API to control CPU functions such as setting the IPL, enabling/disabling interrupts, and controlling 
  register protection
 


File Structure
--------------
r_bsp
|   platform.h 
|   readme.txt
|
+---board
|   +---generic_rx111
|   |    :
|   :
|   \---user
|
+---doc
|   +---en
|       r01an1685ej{VERSION_NUMBER}-rx-bsp.pdf
|   +---ja
|       r01an1685jj{VERSION_NUMBER}-rx-bsp.pdf
|
\---mcu
    +---all
    +---rx111
    |    :
    :