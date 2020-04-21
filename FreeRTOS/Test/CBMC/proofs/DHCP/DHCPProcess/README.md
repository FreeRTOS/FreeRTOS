This is the memory safety proof for DHCPProcess function, which is the
function that triggers the DHCP protocol.

The main stubs in this proof deal with buffer management, which assume
that the buffer is large enough to accomodate a DHCP message plus a
few additional bytes for options (which is the last, variable-sized
field in a DHCP message). We have abstracted away sockets, concurrency
and third-party code. For more details, please check the comments on
the harness file.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* FreeRTOS_sendto
* FreeRTOS_setsockopt
* FreeRTOS_socket
* ulRand
* vARPSendGratuitous
* vApplicationIPNetworkEventHook
* vLoggingPrintf
* vPortEnterCritical
* vPortExitCritical
* vReleaseNetworkBufferAndDescriptor
* vSocketBind
* vSocketClose

