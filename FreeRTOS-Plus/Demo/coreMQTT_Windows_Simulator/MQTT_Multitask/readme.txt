The multi threaded example creates an MQTT agent (or daemon task).  It is thread
safe because only the agent task is allowed to access the coreMQTT API - hence
the API is only accessed from one FreeRTOS task.  Other tasks and interrupts
needing to interact with the MQTT agent do so through a thread safe queue.
We are generalising this technique for future coreMQTT releases, which will have
a re-usable agent component.

! Plain text examples are for ease of evaluation only - product devices should
! always use authenticated and encrypted communication.  Never send private or
! sensitive data on an unencrypted connection.

