*** INTRODUCTION ***

Development is now underway that will enable us to provide long-term support (LTS) 
releases of FreeRTOS. An LTS release is maintained separately from the main 
codebase. Typically, no new features are added after release, but critical bugs 
and security vulnerabilities are patched for years after launch.

We are currently working to improve modularity and memory usage of FreeRTOS 
libraries to ensure the FreeRTOS LTS release helps our users cover a wider set of use cases.

For additional details on LTS and the supported libraries,
refer to https://freertos.org/ltsroadmap.html

*** INSTRUCTIONS ***
The pre-configured projects use the FreeRTOS kernel Windows port (often
called the Windows simulator) to enable their evaluation using the free Visual
Studio tools and without needing specific microcontroller hardware.

Additional details can be found at: 
https://www.freertos.org/FreeRTOS-Windows-Simulator-Emulator-for-Visual-Studio-and-Eclipse-MingW.html

Instructions for configuring and using the FreeRTOS IoT libraries are in the
following links:

  + https://www.FreeRTOS.org/mqtt/
  + https://www.FreeRTOS.org/https/
  + https://www.FreeRTOS.org/shadow/
  + https://www.FreeRTOS.org/jobs/
  + https://www.FreeRTOS.org/ota/
  + https://www.FreeRTOS.org/pkcs11/


*** LOCATING THE EXAMPLE PROJECTS ***

The Visual Studio projects for each of the FreeRTOS IoT library examples are
located in sub-directories of the following top-level directories:

  + /FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/mqtt
  + /FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/https
  + /FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/shadow
  + /FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/jobs
  + /FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/ota
  + /FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/pkcs11


*** ADDITIONAL INFORMATION ***

See http://www.freertos.org/a00017.html for full details of the FreeRTOS
directory structure

See also -
http://www.freertos.org/FreeRTOS-quick-start-guide.html
http://www.freertos.org/FAQHelp.html
