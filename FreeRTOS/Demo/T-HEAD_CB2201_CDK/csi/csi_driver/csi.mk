TEE_INC += -I$(CSI_DIR)/csi_driver/include

ifeq ($(CONFIG_CSKY), y)
include $(CSI_DIR)/csi_driver/csky/csi.mk
endif

ifeq ($(CONFIG_SANECHIPS), y)
include $(CSI_DIR)/csi_driver/sanechips/csi.mk
endif