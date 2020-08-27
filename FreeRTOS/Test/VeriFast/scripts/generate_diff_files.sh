#!/bin/bash -eu

FUNCS=(
  prvCopyDataFromQueue
  prvCopyDataToQueue
  prvInitialiseNewQueue
  prvIsQueueEmpty
  prvIsQueueFull
  prvUnlockQueue
  uxQueueMessagesWaiting
  uxQueueSpacesAvailable
  vQueueDelete
  xQueueGenericCreate
  xQueueGenericReset
  xQueueGenericSend
  xQueueGenericSendFromISR
  xQueueIsQueueEmptyFromISR
  xQueueIsQueueFullFromISR
  xQueuePeek
  xQueuePeekFromISR
  xQueueReceive
  xQueueReceiveFromISR
)

if [ ! -d "FreeRTOS-Kernel" ]; then
    git clone https://github.com/FreeRTOS/FreeRTOS-Kernel.git
fi
pushd FreeRTOS-Kernel > /dev/null
rm -rf tags generated
ctags --excmd=number queue.c
mkdir generated
for f in ${FUNCS[@]}; do
  ../extract.py tags $f > generated/$f.c
done
popd > /dev/null
echo "created: FreeRTOS-Kernel/generated"

ln -fs ../queue .
pushd queue > /dev/null
rm -rf tags generated
ctags --excmd=number *.c
mkdir generated
for f in ${FUNCS[@]}; do
  ../scripts/extract.py tags $f > generated/$f.c
done
popd > /dev/null
echo "created: queue/generated"
