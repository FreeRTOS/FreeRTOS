The FreeRTOS+TCP source code and example projects are currently provided in
their own .zip file download, but using the directory structure of the official
FreeRTOS .zip file download.  This allow the projects to be seamlessly moved
from one download to the other, but can seem strange when the files are viewed
in isolation.

The FreeRTOS+TCP test suite Visual Studio project file is in the following
directory: FreeRTOS-Plus\Test\FreeRTOS-Plus-TCP\Integration\Full-TCP-Suite

This project is a version of the standard FreeRTOS demos that includes the
integration tests of +TCP. It tests the +TCP stack through the use of FreeRTOS_Sockets
API. To Run this project, make sure that the computer is connected to a network
via ethernet cable.
- Open the project (using file named `Full-TCP-Suite.sln`) and
choose the required network interface by modifying this line `#define
configNETWORK_INTERFACE_TO_USE` in FreeRTOSConfig.h.
- Modify the `tcptestECHO_SERVER_ADDR[0-3]` and `tcptestECHO_PORT` in the file
`test_tcp.h` according to the address of the unsecure echo server of your choosing.
An implementation of echo server is provided here:
https://docs.aws.amazon.com/freertos/latest/portingguide/afr-echo-server.html

Once these changes are made, just build and run the project. It should run 23 test
of which all should pass with a proper connection.
