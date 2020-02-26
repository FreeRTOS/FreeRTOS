This is the memory safety proof for prvTCPHandleState.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* prvTCPPrepareSend (proved independently)
* prvTCPReturnPacket (proved independently)

* lTCPAddRxdata
* lTCPWindowRxCheck
* lTCPWindowTxAdd
* ulTCPWindowTxAck
* vTCPWindowInit
* xTCPWindowRxEmpty
* xTCPWindowTxDone

* uxStreamBufferGet
* vReleaseNetworkBufferAndDescriptor
* vSocketWakeUpUser
* xTaskGetTickCount
