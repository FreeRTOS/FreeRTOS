TEE_INC += -I$(CSI_DIR)/csi_driver/csky/phobos/include
TEE_SRC += \
	$(CSI_DIR)/csi_driver/csky/phobos/devices.c \
	$(CSI_DIR)/csi_driver/csky/phobos/isr.c \
	$(CSI_DIR)/csi_driver/csky/phobos/pinmux.c