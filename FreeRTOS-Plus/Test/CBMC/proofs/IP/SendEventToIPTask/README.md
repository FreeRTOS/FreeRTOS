This is the memory safety proof for xSendEventToIPTask, a function used
for sending different events to IP-Task.  We have abstracted away queues.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* uxQueueMessagesWaiting
* xQueueGenericSend

The coverage is imperfect (97%) because xSendEventToIPTask always
calls xSendEventStructToIPTask with xTimeout==0.
