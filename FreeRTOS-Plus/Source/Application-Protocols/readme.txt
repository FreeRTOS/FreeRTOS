The 'core' branded application protocols are 'standalone' in that they do not
have any dependencies outside of the C library.  They use a simple transport
interface definition to ensure they are not dependent on the underlying TCP/IP
stack.  This directory collects together the application protocols that all use
the same transport interface definition (only coreMQTT at the time of writing,
soon to also include coreHTTP).

Directories:

+ coreMQTT contains the implementation of the coreMQTT library.  See:
  https://www.FreeRTOS.org/coremqtt

+ network_transport contains the transport interface definition.  See the
  comment above and https://www.freertos.org/transportinterface.html

