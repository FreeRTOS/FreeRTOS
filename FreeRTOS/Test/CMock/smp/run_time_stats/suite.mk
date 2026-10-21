# Reuse one test source with independent single-core/SMP and 32/64-bit builds.
include ../../makefile.in

PROJECT_SRC         := tasks.c
PROJECT_DEPS_SRC    := list.c
PROJECT_HEADER_DEPS := FreeRTOS.h
SUITE_UT_SRC        := run_time_stats_utest.c
MOCK_FILES_FP      += $(UT_ROOT_DIR)/config/fake_assert.h
MOCK_FILES_FP      += $(UT_ROOT_DIR)/config/fake_port.h

PROJECT := smp
SUITE := $(notdir $(CURDIR))
# Keep each configuration's FreeRTOSConfig.h on the include path while sharing
# the test source. testdir.mk uses SUITE_DIR for source and runner generation.
override SUITE_DIR := $(abspath ../run_time_stats)
export
include ../../testdir.mk
