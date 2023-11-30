r_bsp Package
=============

Document Number
---------------
N/A

Version
-------
v1.60

Overview
--------
The r_bsp package provides a foundation for code to be built on top of. It provides startup code, iodefines, and MCU
information for different boards. There are 2 folders that make up the r_bsp package. The 'mcu' folder has iodefine
files and a file named 'mcu_info.h' for each MCU group. The 'mcu_info.h' file has information about the MCU on the board
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
 
Limitations
-----------
N/A

Peripherals Used Directly
-------------------------
N/A

Required Packages
-----------------
* r_glyph [required if you want to use LCD for RDK boards]
* r_rspi_rx [required if you want to use LCD for RDK boards]

How to add to your project
--------------------------
* Copy the r_bsp folder to your project.
* Add an include path to the 'r_bsp' directory. 
* Add all of the source files for your board from the 'r_bsp\board\--YOUR_BOARD--' directory to your project. 
* Uncomment the include path for your board in 'platform.h' which is located in the 'r_bsp' directory.
* Copy the file r_bsp_config_reference.h from the 'r_bsp\board\--YOUR_BOARD--' directory and copy it to your project's
  source code directory. Rename the file r_bsp_config.h.
* Open r_bsp_config.h and use the macros to configure the BSP for your project.

File Structure
--------------
r_bsp
|   platform.h (choose which board is being used)
|   readme.txt
|
+---board (contains supported boards)
|   +---rdkrx62n (contains BSP source and header files)
|   |
|   +---rdkrx63n
|   |
|	+---rskrx111
|	|
|   +---rskrx210
|   |
|   +---rskrx610
|   |
|   +---rskrx62n
|   |
|   +---rskrx62t
|   |
|   +---rskrx630
|   |
|   +---rskrx63n
|   |
|   \---user
|
\---mcu
	+---rx111 (contains common files to this MCU group, e.g. iodefine.h)
	|
    +---rx210 
    |
    +---rx610
    |
    +---rx62n
    |
    +---rx62t
    |
    +---rx630
    |
    \---rx63n

