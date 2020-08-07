

NetworkInterface for Xilinx' Zynq

Please include the following source files:

	$(PLUS_TCP_PATH)/portable/NetworkInterface/Zynq/NetworkInterface.c
	$(PLUS_TCP_PATH)/portable/NetworkInterface/Zynq/uncached_memory.c
	$(PLUS_TCP_PATH)/portable/NetworkInterface/Zynq/x_emacpsif_dma.c
	$(PLUS_TCP_PATH)/portable/NetworkInterface/Zynq/x_emacpsif_physpeed.c
	$(PLUS_TCP_PATH)/portable/NetworkInterface/Zynq/x_emacpsif_hw.c

The file uncached_memory.c can also be found in:

	vendors\xilinx\boards\microzed\aws_demos\application_code\xilinx_code
	vendors\xilinx\boards\microzed\aws_tests\application_code\xilinx_code

And include the following source files from the Xilinx library:

	$(CPU_PATH)/$(PROCESSOR)/libsrc/emacps_v2_0/src/xemacps.c
	$(CPU_PATH)/$(PROCESSOR)/libsrc/emacps_v2_0/src/xemacps_control.c
	$(CPU_PATH)/$(PROCESSOR)/libsrc/emacps_v2_0/src/xemacps_g.c
	$(CPU_PATH)/$(PROCESSOR)/libsrc/emacps_v2_0/src/xemacps_intr.c

	E.g. ps7_cortexa9_0/libsrc/emacps_v2_0/src/xemacps_intr.c

The following source files are NOT used for the FreeRTOS+TCP interface:

	$(CPU_PATH)/$(PROCESSOR)/libsrc/emacps_v2_0/src/xemacps_bdring.c
	$(CPU_PATH)/$(PROCESSOR)/libsrc/emacps_v2_0/src/xemacps_hw.c
	$(CPU_PATH)/$(PROCESSOR)/libsrc/emacps_v2_0/src/xemacps_sinit.c

It is recommended to have these defined :

#define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM    1
#define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM    1
#define ipconfigUSE_LINKED_RX_MESSAGES            1

It is obligatory to define:

#define ipconfigZERO_COPY_RX_DRIVER               1
#define ipconfigZERO_COPY_TX_DRIVER               1
