The FreeRTOS+TCP source code and example projects are currently provided in
their own .zip file download, but using the directory structure of the official
FreeRTOS .zip file download.  This allow the projects to be seamlessly moved
from one download to the other, but can seem strange when the files are viewed
in isolation.

The FreeRTOS+TCP Integration Tests Visual Studio project file is in the following
directory: FreeRTOS-Plus\Tests\FreeRTOS_Plus_TCP_Integration_Tests

This project is a version of the standard FreeRTOS demos that includes the
integration tests of +TCP. It tests 4 functions in the TCP source code. To Run this
project, make sure that the computer is connected to a network via ethernet cable.
Open the project (using file named "FreeRTOS_Plus_TCP_Integration_Tests.sln") and
choose the required network interface by modifying this line #define 
configNETWORK_INTERFACE_TO_USE in FreeRTOSConfig.h.

Once these changes are made, just build and run the project. It should run 4 test
of which all should pass.
