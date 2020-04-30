#!/bin/sh
BASE_DIR=../../..

#FILE1=$(BASE_DIR)/FreeRTOS/Test/CBMC/patches/FreeRTOSConfig.h
FILE2=$(BASE_DIR)/FreeRTOS-Plus/Test/CBMC/patches/FreeRTOSConfig.h
FILE1=$(BASE_DIR)/FreeRTOS/Test/CBMC/patches/FreeRTOSConfig.h

FILE1_BCKUP=$(FILE1)

.PHONY: report clean

report:
	@rm -rf cbmc.txt
	@cmp -s $(FILE2) $(FILE1);						\
	RETVAL=$$?;								\
	if [ $$RETVAL -eq 0 ]; then						\
		echo "$(FILE2) and $(FILE1) match\n\n">>cbmc.txt;		\
		echo "VERIFICATION SUCCESSFUL">>cbmc.txt;			\
	else									\
		echo "$(FILE2) and $(FILE1) DO NOT match\n\n">>cbmc.txt;	\
		echo "VERIFICATION FAILED">>cbmc.txt;				\
	fi


clean:
	rm -rf cbmc.txt

