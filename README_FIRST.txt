*** INTRODUCTION ***

We are currently working to improve the modularity and memory usage of new
FreeRTOS IoT libraries before releasing the libraries into the main FreeRTOS
download with long term support (LTS).  https://freertos.org/ltsroadmap.html
contains a description of the libraries that target modularity and code quality
criteria.  An LTS release is only updated with bug and vulnerability patches,
not new features.  This zip file contains (among other updates) a
work-in-progress snapshot of the MQTT library, which is near completion.  The
MQTT library is now much easier to bring into any project, including projects
that do not use FreeRTOS.

The zip file also contains significant enhancements to the over the air (OTA)
update agent.  Specifically, it is now possible to pause and resume an
in-progress update.

*** INSTRUCTIONS ***
The pre-configured projects use the FreeRTOS kernel Windows port (often
called the Windows simulator) to enable their evaluation using the free Visual
Studio tools and without needing specific microcontroller hardware.
https://www.freertos.org/FreeRTOS-Windows-Simulator-Emulator-for-Visual-Studio-and-Eclipse-MingW.html
provides additional information on using the Windows port.

The following links provide instructions on using the FreeRTOS IoT
libraries:

  + https://www.FreeRTOS.org/mqtt/
  + https://www.FreeRTOS.org/https/
  + https://www.FreeRTOS.org/shadow/
  + https://www.FreeRTOS.org/jobs/
  + https://www.FreeRTOS.org/ota/
  + https://www.FreeRTOS.org/pkcs11/
  + https://www.FreeRTOS.org/mqtt_lts/


*** LOCATING THE EXAMPLE PROJECTS ***

The Visual Studio projects for each of the FreeRTOS IoT library examples are
located in sub-directories of the following top-level directories:

  Demos using the refactored MQTT library:
  + /FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta2/mqtt/mqtt_plain_text
  + /FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta2/mqtt/mqtt_light_weight
  + /FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta2/pkcs11/mqtt_mutal_auth_with_pkcs11

  Demos not yet updated to the refactored MQTT library:
  + /FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/mqtt
  + /FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/https
  + /FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/shadow
  + /FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/jobs
  + /FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/ota
  + /FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/pkcs11


*** ADDITIONAL INFORMATION ***

See http://www.freertos.org/a00017.html for full details of the FreeRTOS
directory structure

See also -
http://www.freertos.org/FreeRTOS-quick-start-guide.html
http://www.freertos.org/FAQHelp.html
