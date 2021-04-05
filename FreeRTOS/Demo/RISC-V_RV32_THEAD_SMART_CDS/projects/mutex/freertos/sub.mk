##
 # Copyright (C) 2017-2019 Alibaba Group Holding Limited
##

ifeq ($(KERNEL), freertos)
INCLUDEDIRS += -I$(ROOTDIR)/csi_kernel/freertosv10.3.1/include/
INCLUDEDIRS += -I$(ROOTDIR)/../../Source/include
INCLUDEDIRS += -I$(ROOTDIR)/../../Source/portable/GCC/RISC-V/chip_specific_extensions/thead/
INCLUDEDIRS += -I$(ROOTDIR)/../../Source/portable/GCC/RISC-V

CSRC += $(ROOTDIR)/../../Source/portable/GCC/RISC-V/port.c
SSRC += $(ROOTDIR)/../../Source/portable/GCC/RISC-V/portASM.S

CSRC += $(ROOTDIR)/csi_kernel/freertosv10.3.1/adapter/csi_freertos.c
CSRC += $(ROOTDIR)/../../Source/croutine.c
CSRC += $(ROOTDIR)/../../Source/event_groups.c
CSRC += $(ROOTDIR)/../../Source/list.c
CSRC += $(ROOTDIR)/../../Source/portable/MemMang/heap_4.c
CSRC += $(ROOTDIR)/../../Source/queue.c
CSRC += $(ROOTDIR)/../../Source/stream_buffer.c
CSRC += $(ROOTDIR)/../../Source/tasks.c
CSRC += $(ROOTDIR)/../../Source/timers.c
endif


ifeq ($(HELIX), y)
INCLUDEDIRS += -I$(ROOTDIR)/projects/benchmark/helix/real
INCLUDEDIRS += -I$(ROOTDIR)/projects/benchmark/helix/testwrap
INCLUDEDIRS += -I$(ROOTDIR)/projects/benchmark/helix/pub
endif

ifeq ($(findstring y,$(SD)$(MMC)),y)
INCLUDEDIRS += -I$(ROOTDIR)/libs/sdmmc/core
INCLUDEDIRS += -I$(ROOTDIR)/libs/sdmmc/host

CSRC += $(ROOTDIR)/libs/sdmmc/core/sdmmc_common.c
CSRC += $(ROOTDIR)/libs/sdmmc/host/sdmmc_event.c
CSRC += $(ROOTDIR)/libs/sdmmc/host/sdmmc_host.c

ifeq ($(SD), y)
CSRC += $(ROOTDIR)/libs/sdmmc/core/sd.c
endif
ifeq ($(MMC), y)
CSRC += $(ROOTDIR)/libs/sdmmc/core/mmc.c
endif
endif

ifeq ($(FATFS), y)
INCLUDEDIRS += -I$(ROOTDIR)/projects/examples/fs/lib/fatfs/src
INCLUDEDIRS += -I$(ROOTDIR)/projects/examples/fs/lib/fatfs/src/sd_disk

CSRC += $(ROOTDIR)/projects/examples/fs/lib/fatfs/src/diskio.c
CSRC += $(ROOTDIR)/projects/examples/fs/lib/fatfs/src/ff.c
CSRC += $(ROOTDIR)/projects/examples/fs/lib/fatfs/src/ffsystem.c
CSRC += $(ROOTDIR)/projects/examples/fs/lib/fatfs/src/ffunicode.c
CSRC += $(ROOTDIR)/projects/examples/fs/lib/fatfs/src/sd_disk/sd_disk.c
endif
