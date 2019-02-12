#
# File: FreeRTOS.mk
# Copyright (c) 2019, Dornerworks Ltd.
#

-include BuildEnvironment.mk

FREERTOS_DIR = ../..
FREERTOS_SOURCE_DIR = $(FREERTOS_DIR)/Source

FREERTOS_SRC = \
	$(FREERTOS_SOURCE_DIR)/croutine.c \
	$(FREERTOS_SOURCE_DIR)/list.c \
	$(FREERTOS_SOURCE_DIR)/queue.c \
	$(FREERTOS_SOURCE_DIR)/tasks.c \
	$(FREERTOS_SOURCE_DIR)/timers.c \
	$(FREERTOS_SOURCE_DIR)/event_groups.c \
	$(FREERTOS_SOURCE_DIR)/stream_buffer.c \
	$(FREERTOS_SOURCE_DIR)/portable/MemMang/heap_4.c

FREERTOS_INC = $(FREERTOS_SOURCE_DIR)/include

FREERTOS_INCLUDES := \
	-I $(FREERTOS_INC)

INTERRUPT_HANDLER = main_blinky

FREERTOS_BUILD_DIR = $(BUILD_DIR)/FreeRTOS
FREERTOS_OBJS = $(patsubst %.c,$(FREERTOS_BUILD_DIR)/%.o,$(notdir $(FREERTOS_SRC)))
VPATH += \
	$(FREERTOS_SOURCE_DIR) \
	$(FREERTOS_SOURCE_DIR)/portable/MemMang
