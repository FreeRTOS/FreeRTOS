NetworkInterface for Xilinx' UltraScale+, running on Cortex A53, 64-bits

Please include the following source files:

	$(PLUS_TCP_PATH)/portable/NetworkInterface/xilinx_ultrascale/NetworkInterface.c
	$(PLUS_TCP_PATH)/portable/NetworkInterface/xilinx_ultrascale/uncached_memory.c
	$(PLUS_TCP_PATH)/portable/NetworkInterface/xilinx_ultrascale/x_emacpsif_dma.c
	$(PLUS_TCP_PATH)/portable/NetworkInterface/xilinx_ultrascale/x_emacpsif_physpeed.c
	$(PLUS_TCP_PATH)/portable/NetworkInterface/xilinx_ultrascale/x_emacpsif_hw.c

And include the following source files from the Xilinx library:

	$(PROCESSOR)/libsrc/emacps_v3_9/src/xemacps.c
	$(PROCESSOR)/libsrc/emacps_v3_9/src/xemacps_control.c
	$(PROCESSOR)/libsrc/emacps_v3_9/src/xemacps_g.c
	$(PROCESSOR)/libsrc/emacps_v3_9/src/xemacps_intr.c

	E.g. psu_cortexa53_0/libsrc/emacps_v3_9/src/xemacps_intr.c

The following source files are NOT used for the FreeRTOS+TCP interface:

	$(PROCESSOR)/libsrc/emacps_v3_9/src/xemacps_bdring.c
	$(PROCESSOR)/libsrc/emacps_v3_9/src/xemacps_hw.c
	$(PROCESSOR)/libsrc/emacps_v3_9/src/xemacps_sinit.c


It is recommended to have these defined :

#define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM    1

#define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM    1


It is obligatory to define these in your FreeRTOSIPConfig.h :

#define ipconfigZERO_COPY_RX_DRIVER               1

#define ipconfigZERO_COPY_TX_DRIVER               1


Please link you project with BufferAllocation_1.c ( not xxx_2.c ).

The following option causes the memory of the network packets to be allocated
in normal ( cached ) memory.  With this option, TCP processing seems a faster
than without this option.

#define nicUSE_UNCACHED_MEMORY   0
