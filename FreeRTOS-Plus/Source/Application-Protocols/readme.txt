The 'core' branded application protocols are 'standalone' in that they do not
have any dependencies outside of the C library.  They use a simple transport
interface definition to ensure they are not dependent on the underlying TCP/IP
stack.  This directory collects together the application protocols that all use
the same transport interface definition.

Directories:

+ coreMQTT contains the implementation of the coreMQTT library. 
+ coreMQTT-Agent contains the implementation of the coreMQTT Agent library.
+ coreHTTP contains the implementation of the coreHTTP library.
+ coreSNTP contains the implementation of the coreSNTP library.
+ network_transport contains multiple implementations for the transport interface.   

For more details on the above libraries, see: https://www.freertos.org/application-protocols.html.
