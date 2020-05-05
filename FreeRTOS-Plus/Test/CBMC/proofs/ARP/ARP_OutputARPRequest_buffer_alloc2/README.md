This is the memory safety proof for FreeRTOS_OutputARPRequest
method combined with the BufferAllocation_2.c allocation strategy.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
* vAssertCalled
* xTaskGetSchedulerState
* pvTaskIncrementMutexHeldCount
* xTaskRemoveFromEventList
* xTaskPriorityDisinherit

* pvPortMalloc
* pvPortFree
* xNetworkInterfaceOutput
* vNetworkInterfaceAllocateRAMToBuffers

This proof disables the tracing library in the header.

This proof checks FreeRTOS_OutputARPRequest in multiple configuration:

* The proof in the directory config_minimal_configuration guarantees
  that the implementation and interaction between
  FreeRTOS_OutputARPRequest and
  FreeRTOS-Plus-TCP/source/portable/BufferManagement/BufferAllocation_2.c
  are memory save.  This proof depends entirely of the implementation
  correctness of vNetworkInterfaceAllocateRAMToBuffers.
* The proof in directory minimal_configuration_minimal_packet_size
  guarantees that using
  FreeRTOS-Plus-TCP/source/portable/BufferManagement/BufferAllocation_2.c
  along with the ipconfigETHERNET_MINIMUM_PACKET_BYTES is memory save
  as long as TCP is enabled ( ipconfigUSE_TCP 1 ) and
  ipconfigETHERNET_MINIMUM_PACKET_BYTES < sizeof( TCPPacket_t ).
* The directory minimal_configuration_minimal_packet_size_no_tcp
  reminds that ipconfigETHERNET_MINIMUM_PACKET_BYTES must not be used
  if TCP is disabled ( ipconfigUSE_TCP 1 ) along with the
  FreeRTOS-Plus-TCP/source/portable/BufferManagement/BufferAllocation_2.c
  allocator.
* The proof in directory
  config_minimal_configuration_linked_rx_messages guarantees that the
  ipconfigUSE_LINKED_RX_MESSAGES define does not interfere with the
  memory safety claim.

All harnesses include the queue.c file, but test only for the happy path.
