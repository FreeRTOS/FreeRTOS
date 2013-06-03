== LPCUSBlib software package ==  (http://www.lpcware.com/content/project/LPCUSBlib)

Top level directories:

applications/examples
A collection of several example applications based on host/device mode and USB class

applications/projects
A collection of custom applications using the LPCUSBlib, BSP, and CDL libraries

libraries/BSP - Board Support Package
includes common code in bsp.c and bsp.h and a separate set of files for each support board

libraries/CDL - Common Driver Library
includes CMSIS and driver library files for multiple MCUs

libraries/LPCUSBlib - NXP's USB library
USB class and driver software for NXP USB controllers


==========================================================================================
Build instructions


LPCXpresso 4 IDE (Code Red)


1. Start up the IDE
2. Choose a workspace folder
3. Click File->Import->General->Existing Projects into Workspace->Next
4. Browse to the base of your LPCUSBlib release (the location of this file)
5. Click Finish

At this point the Project Explorer should show the following projects:

BSP                 (Board Support Package)
CDL                 (Common Driver Library)
Example_<app name>  (Example applications)
LPCUSBlib           (NXP's USB library)
Project_<proj name> (Miscellaneous projects)

6. Right click on BSP->Build Configurations->Set Active and select your development board
7. Right click on CDL->Build Configurations->Set Active and select your MCU
8. Right click on LPCUSBlib->Build Configurations->Set Active and select your MCU
9. Right click on Example_<app name>->Build Configurations->Set Active and select your MCU
10. Right click on Example_<app name>->Properties->C/C++ Build->MCU Settings and select your MCU
11. Right click on Example_<app name>->Build Project

 


tips:

To reset the IDE to its default look and feel, right click on the Develop box in the upper right hand corner of the tool and select Reset


-----------------------------------------------------------------------
uVision 4 (Keil)

1. Start up the IDE
2. Open the workspace at Demos\keil_workspace.uvmpw
3. Click Projects->Batch Build...
4. Select your board and MCU in the 6 projects. 

To build a mass storage device example for the MCB1700 click DelectAll and select:
	BSP                       = MCB1700
	CDL                       = LPC17xx
	Example_MassStorageDevice = MCB1700
	LPCUSBlib_Device          = LPC17xx_Device
5. Click Build