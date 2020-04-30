#!/bin/sh
BASE_DIR=../../..

FILE1=$(BASE_DIR)/FreeRTOS/Test/CBMC/patches/FreeRTOSConfig.h
FILE2=$(BASE_DIR)/FreeRTOS-Plus/Test/CBMC/patches/FreeRTOSConfig.h

.PHONY: Check clean

Check:
	@rm -rf cbmc.txt
	@cmp -s $(FILE1) $(FILE2);					\
	RETVAL=$$?;							\
	if [ $$RETVAL -eq 0 ]; then					\
		echo "VERIFICATION SUCCESSFUL">cbmc.txt;		\
	else								\
		echo "VERIFICATION FAILED">cbmc.txt;			\
	fi


clean:
	rm -rf cbmc.txt

