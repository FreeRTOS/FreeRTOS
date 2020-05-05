This is the memory safety proof for FreeRTOS_OutputARPRequest.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* xNetworkInterfaceOutput

This proof checks FreeRTOS_OutputARPRequest in multiple configuration:

* The config_CBMC_PROOF_ASSUMPTION_HOLDS_no_packet_bytes proof
  guarantees that for a buffer allocated to xDataLength,
  the code executed by the FreeRTOS_OutputARPRequest function
  call of FreeRTOS_ARP.c is memory safe.
* If the ipconfigETHERNET_MINIMUM_PACKET_BYTES is set and the
  buffer allocated by pxGetNetworkBufferWithDescriptor allocates
  a buffer of at least ipconfigETHERNET_MINIMUM_PACKET_BYTES,
  the config_CBMC_PROOF_ASSUMPTION_HOLDS_Packet_bytes proof
  guarantees that the code executed by the
  FreeRTOS_OutputARPRequest function call
  of FreeRTOS_ARP.c is memory safe.
* The third configuration in the subdirectory
  config_CBMC_PROOF_ASSUMPTION_DOES_NOT_HOLD demonstrates
  that the code is not memory safe, if the allocation
  code violates our assumption.
* All proofs mock the pxGetNetworkBufferWithDescriptor
  function for modelling the assumptions about the
  buffer management layer.
