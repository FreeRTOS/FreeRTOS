ifeq ($(CONFIG_PLATFORM_PHOBOS), y)
include $(CSI_DIR)/csi_driver/csky/phobos/csi.mk
endif

ifeq ($(CONFIG_PLATFORM_HOBBIT1_2), y)
include $(CSI_DIR)/csi_driver/csky/hobbit1_2/csi.mk
endif

ifeq ($(CONFIG_PLATFORM_HOBBIT3), y)
include $(CSI_DIR)/csi_driver/csky/hobbit3/csi.mk
endif

include $(CSI_DIR)/csi_driver/csky/common/csi.mk

