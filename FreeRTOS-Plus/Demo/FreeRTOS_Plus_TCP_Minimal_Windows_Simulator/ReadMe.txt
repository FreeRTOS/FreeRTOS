The FreeRTOS+TCP source code and example projects are currently provided in
their own .zip file download, but using the directory structure of the official
FreeRTOS .zip file download.  This allow the projects to be seamlessly moved
from one download to the other, but can seem strange when the files are viewed
in isolation.

The minimal FreeRTOS+TCP Visual Studio project file is in the following directory:
FreeRTOS-Plus\Demo\FreeRTOS_Plus_TCP_Minimal_Windows_Simulator

The minimal project is a cut down version of the full Windows demo that only
includes examples of simple TCP and UDP clients.  The instructions for the full 
Windows demo are still relevant though as they describe how to set up the 
WinPCap development environment, how to set the IP address, and other such 
items.  Note that, as delivered, configUSE_DHCP is set to 0, so a static IP 
address is used.  The instructions are provided on the following URL:
http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html

The UDP client example included in the minimal project is described on the 
following URL:
http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/UDP_client_server.html

The TCP client example included in the minimal project is described on the
following URL:
http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_Echo_Clients.html

A description of the FreeRTOS+TCP source code directory is provided on the
following URL:
http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_Networking_Tutorial_Source_Code_Organisation.html

A description of the way the main FreeRTOS .zip file download source code is
organised is provided on the following URL:
http://www.freertos.org/a00017.html


