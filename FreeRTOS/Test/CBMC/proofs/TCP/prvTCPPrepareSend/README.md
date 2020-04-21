This is the memory safety proof for prvTCPPrepareSend.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* ulTCPWindowTxGet
* xTCPWindowTxDone

* xTaskGetTickCount

* uxStreamBufferGet
* vReleaseNetworkBufferAndDescriptor
* vSocketWakeUpUser
