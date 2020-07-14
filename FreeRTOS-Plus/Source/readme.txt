*** INTRODUCTION ***

We are currently working to improve the modularity and memory usage of new
FreeRTOS IoT libraries before releasing the libraries into the main FreeRTOS
download with long term support (LTS).  https://freertos.org/ltsroadmap.html
contains a description of the libraries target modularity and code quality
criteria.  An LTS release is only updated with bug and vulnerability patches,
not new features.  This zip file contains (among other updates) a
work-in-progress snapshot of the MQTT library, which is near completion.  The
MQTT library is now much easier to bring into any project, including projects
that do not use FreeRTOS.

The /FreeRTOS-Plus/Source/FreeRTOS-IoT-Libraries-LTS-Beta1 directory contains
the source code of the libraries that are being refactored.

The /FreeRTOS-Plus/Source/FreeRTOS-IoT-Libraries-LTS-Beta2 directory contains
the work-in-progress source code of libraries that have already been refactored
(currently the MQTT library).