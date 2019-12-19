ifeq ($(CONFIG_SHA), y)
TEE_INC += -I$(CSI_DIR)/csi_driver/csky/common/sha/
ifeq ($(CONFIG_PLATFORM_PHOBOS), y)
TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/sha/ck_sha_v2.c
endif
ifeq ($(CONFIG_PLATFORM_HOBBIT3), y)
TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/sha/ck_sha_v2.c
endif
ifeq ($(CONFIG_PLATFORM_HOBBIT1_2), y)
TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/sha/ck_sha_v1.c
endif
endif

ifeq ($(CONFIG_TRNG), y)
ifeq ($(CONFIG_PLATFORM_HOBBIT3), y)
TEE_INC += -I$(CSI_DIR)/csi_driver/csky/common/trng/
TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/trng/osr_trng.c
endif
ifeq ($(CONFIG_PLATFORM_PHOBOS), y)
TEE_INC += -I$(CSI_DIR)/csi_driver/csky/common/trng/
TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/trng/ck_trng.c
endif
ifeq ($(CONFIG_PLATFORM_HOBBIT1_2), y)
TEE_INC += -I$(CSI_DIR)/csi_driver/csky/common/trng/
TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/trng/ck_trng.c
endif
endif

ifeq ($(CONFIG_AES), y)
TEE_INC += -I$(CSI_DIR)/csi_driver/csky/common/aes/
TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/aes/ck_aes.c
endif

ifeq ($(CONFIG_RSA), y)
TEE_INC += -I$(CSI_DIR)/csi_driver/csky/common/rsa/
TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/rsa/ck_rsa.c
endif

ifeq ($(CONFIG_USART), y)
TEE_INC += -I$(CSI_DIR)/csi_driver/csky/common/usart/
TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/usart/dw_usart.c
endif

ifeq ($(CONFIG_PMU), y)
TEE_INC += -I$(CSI_DIR)/csi_driver/csky/common/pmu/
TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/pmu/ck_pmu.c
endif

TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/wdt/dw_wdt.c

TEE_SRC += $(CSI_DIR)/csi_driver/csky/common/eflash/ck_eflash.c

