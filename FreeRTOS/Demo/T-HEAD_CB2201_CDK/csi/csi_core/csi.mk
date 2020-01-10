TEE_INC += \
	-I$(CSI_DIR)/csi_core/include \
	-I$(CSI_DIR)/csi_core/ck802 \
	-I$(CSI_DIR)/csi_core/include/csi-gcc

TEE_SRC += \
	$(CSI_DIR)/csi_core/ck802/core_ck802.c