The 'core' branded application protocols are 'standalone' in that they do not
have any dependencies outside of the C library.  They use a simple transport
interface definition to ensure they are not dependent on the underlying TCP/IP
stack.  This directory collects together the application protocols that all use
the same transport interface definition.

Directories:

+ coreMQTT contains the implementation of the coreMQTT library.  See:
  https://www.freertos.org/mqtt

+ network_transport contains the transport interface definition.  See the
  comment above and https://www.freertos.org/network-interface.html
  
+ coreHTTP contains the implementation of the coreHTTP library.  See:
  https://www.freertos.org/http

