tcp_mem_stats.c : FreeRTOS+TCP Memory Statistics

This module can be used in any project on any platform that uses FreeRTOS+TCP.

It creates an overview of the memory usage of FreeRTOS+TCP.
It reports the static use of RAM, and also the dynamic usage ( heap ).
It relates these numbers to the macro's defined `FreeRTOSIPConfig.h`.

It writes CSV records to the logging with configPRINTF().

The resulting log can be filtered by e.g.:

	cat logging.txt | grep ".*TCPMemStat," | sed "s/.*TCPMemStat,//"

The resulting text can be imported into any spreadsheet at cell "A1" ( top-left ):

    ipconfig item,Value,PerUnit,Total
    NUM_NETWORK_BUFFER_DESCRIPTORS,12,60,=B13*C13,Descriptors only
    TCP_WIN_SEG_COUNT,32,64,=B14*C14
    EVENT_QUEUE_LENGTH,17,8,=B15*C15
    IP_TASK_STACK_SIZE_WORDS,300,4,=B16*C16

When the CSV-records are imported at another row or column than "A1", the formulas will be incorrect.

How to include 'tcp_mem_stats' into a project:

● Add tools/tcp_mem_stats.c to the sources
● Add the following lines to FreeRTOSIPConfig.h :
	#define ipconfigUSE_TCP_MEM_STATS					( 1 )
	#define ipconfigTCP_MEM_STATS_MAX_ALLOCATION		( 128 )
	#include "../tools/tcp_mem_stats.h"

Later on, the module can disabled by setting `#define ipconfigUSE_TCP_MEM_STATS 0`.

`ipconfigTCP_MEM_STATS_MAX_ALLOCATION` is the maximum number of objects that can be followed at any time.
A socket that has 2 stream buffers counts as 3 objects ( needing 3 x 16 = 48 bytes to store their properties ).

The **summary** at the bottom will only be written when `iptraceMEM_STATS_CLOSE()` is called.
The application is responsible for calling `iptraceMEM_STATS_CLOSE()`.
The summary at the bottom looks like this:

	Totals,,,=MAX(D25:D31),,=MIN(F25:F31),=MAX(G25:G31)
	Maximum RAM usage:,,,=SUM(D20;D32)

The spreadsheet can be edited further to make estimations with different macro values.
