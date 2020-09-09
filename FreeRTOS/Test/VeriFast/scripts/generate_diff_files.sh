#!/bin/bash -eu

QUEUE_FUNCS=(
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

LIST_FUNCS=(
  uxListRemove
  vListInitialise
  vListInitialiseItem
  vListInsertEnd
  vListInsert
)

if [ ! -d "FreeRTOS-Kernel" ]; then
    git clone https://github.com/FreeRTOS/FreeRTOS-Kernel.git
fi
pushd FreeRTOS-Kernel > /dev/null
rm -rf tags generated
ctags --excmd=number queue.c
mkdir generated
for f in ${QUEUE_FUNCS[@]}; do
  ../extract.py tags $f > generated/$f.c
done
ctags --excmd=number list.c
for f in ${LIST_FUNCS[@]}; do
  ../extract.py tags $f > generated/$f.c
done
popd > /dev/null
echo "created: FreeRTOS-Kernel/generated"

ln -fs ../queue .
pushd queue > /dev/null
rm -rf tags generated
ctags --excmd=number *.c
mkdir generated
for f in ${QUEUE_FUNCS[@]}; do
  ../scripts/extract.py tags $f > generated/$f.c
done
popd > /dev/null
echo "created: queue/generated"

ln -fs ../list .
pushd list > /dev/null
rm -rf tags generated
ctags --excmd=number *.c
mkdir generated
for f in ${LIST_FUNCS[@]}; do
  ../scripts/extract.py tags $f > generated/$f.c
done
popd > /dev/null
echo "created: list/generated"
