Prerequisites:
- Keil MDK release 5.38a or 5.37

Notes:
The demo has been updated to work with latest MDK release 5.38a. From Keil MDK version 5.37, Arm Virtual Hardware (AVH)
models Version 11.17.40 are replacing the FVP models.
 
Instructions to Build and Run:
 - The Keil multi-project workspace FreeRTOSDemo.uvmpw contains projects for both the secure project, and non secure project.
 - Set the FreeRTOSDemo_s project as Active - Right click on "Project: FreeRTOSDemo_s" and select "Set as Active Project".
 - Build the FreeRTOSDemo_s project using "Project --> Build" or by pressing F7.
 - Set the FreeRTOSDemo_ns project as Active - Right click on "Project: FreeRTOSDemo_ns" and select "Set as Active Project".
 - Build the FreeRTOSDemo_ns project using "Project --> Build" or by pressing "F7".
 - Start Debug Session using "Debug -> Start/Stop Debug Session" or by pressing "Ctrl+F5".

