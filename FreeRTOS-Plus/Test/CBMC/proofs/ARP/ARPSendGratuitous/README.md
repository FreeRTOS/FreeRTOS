Abstracting xQueueGenericSend away
and including tasks.c and FreeRTOS_IP.c:
The ARPSendGratutious function is memory safe,
if xQueueGenericSend is memory safe.

queue.c is not compiled into the proof binary.