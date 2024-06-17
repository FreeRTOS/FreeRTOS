# Change according to what your  unit test directory is.
# For example if testing queue.c your directory should be called queue
# and the project name should be queue
# if testing list.c your directory should be called list
# and the project name should be list

include ../makefile.in

PROJECT          :=     tasks
# SUITES lists the suites contained in subdirectories of this directory
#
# Test/CMock/tasks
PROJECT_DIR      :=     $(abspath .)
PROJ_DIR         :=     $(abspath .)

# List the dependency files you wish to mock
MOCK_FILES_FP    :=   $(KERNEL_DIR)/include/timers.h
MOCK_FILES_FP    +=   $(KERNEL_DIR)/include/list.h
MOCK_FILES_FP    +=   $(KERNEL_DIR)/include/portable.h
MOCK_FILES_FP    +=   $(PROJECT_DIR)/list_macros.h
MOCK_FILES_FP    +=   $(PROJECT_DIR)/../config/fake_assert.h
MOCK_FILES_FP    +=   $(PROJECT_DIR)/../config/fake_infiniteloop.h

UNDEF_MOCKED_HEADER_MACROS := -UlistLIST_IS_EMPTY -UlistGET_OWNER_OF_HEAD_ENTRY\
                    -UlistIS_CONTAINED_WITHIN -UlistGET_LIST_ITEM_VALUE        \
                    -UlistSET_LIST_ITEM_VALUE                                  \
                    -UlistLIST_ITEM_CONTAINER -UlistCURRENT_LIST_LENGTH

# List special compilation flags for this module
CFLAGS           +=     -Wno-unused-function

# List special preprocessing flags for this module
CPPFLAGS         +=

# List special linking flags for this module
LDFLAGS          +=

# Makefile Debug Flags (if needed)
#MAKEFLAGS += -rR

# Try not to edit beyond this line

COVERAGE_OPTS    :=     -fprofile-arcs -ftest-coverage -fprofile-generate

# build/generated/queue
SCRATCH_DIR      :=   $(GENERATED_DIR)/$(PROJECT)

# list.h   timers.h   portable.h
MOCK_FILES       :=   $(notdir $(MOCK_FILES_FP))

# ...tasks/%/mocks/mock_list.o   tasks/%/mocks/mock_timers.o
MOCK_OBJS        :=   $(addprefix $(SCRATCH_DIR)/%/mocks/mock_,$(MOCK_FILES:.h=.o))

# ...tasks/%/mocks/mock_list.c   tasks/%/mocks/mock_timers.c
MOCK_SRC_LIST    :=   $(addprefix $(SCRATCH_DIR)/%/mocks/,$(addprefix mock_,$(MOCK_FILES:.h=.c)))

# tasks/%/cpp/timers.h   tasks/%/cpp/list.h
CPP_FILES        :=   $(addprefix $(SCRATCH_DIR)/%/cpp/,$(notdir $(MOCK_FILES_FP)))
DEP_FILES        :=   $(addsuffix .d,$(addprefix $(SCRATCH_DIR)/%/cpp/,$(notdir $(MOCK_FILES_FP))))

# tasks_1_utest.c   tasks_2_utest.c ...
PROJ_SRC_LIST          :=   $(sort $(wildcard $(PROJECT)_*_utest.c))

# 1_utest.c dynamic_utest.c
SUITE_UT_SRC     :=   $(subst $(PROJECT)_,,$(PROJ_SRC_LIST))

# 1 2 3 config1 assert ...
DISCRIMINATOR    :=   $(subst _utest,,$(subst .c,,$(subst $(PROJECT)_,,$(PROJ_SRC_LIST))))

# tasks/1/mocks   tasks/2/mocks
MOCK_DIRS        :=   $(addsuffix /mocks,$(addprefix $(SCRATCH_DIR)/,$(DISCRIMINATOR)))

# queue/1/cpp   queue/2/cpp
CPP_DIRS         :=   $(addsuffix /cpp,$(addprefix $(SCRATCH_DIR)/,$(DISCRIMINATOR)))

# tasks/1/include   tasks/2/include
INCLUDE_DIRS     :=   $(addsuffix /include,$(addprefix $(SCRATCH_DIR)/,$(DISCRIMINATOR)))

#list/1   list/2 ....
CONFIG_DIRS      := $(addprefix $(SCRATCH_DIR)/,$(DISCRIMINATOR))

ifeq ($(MOCK_FILES_FP),)
     $(shell mkdir -p  $(MOCK_DIRS))
     $(shell for n in $(MOCK_DIRS) ; do touch -a $(n)/mock_dummy.c)
endif

EXEC_LIST        := $(addprefix $(BIN_DIR)/,$(patsubst %.c,%,$(PROJ_SRC_LIST)))
EXEC_PATH        := $(addsuffix _%_utest,$(addprefix $(BIN_DIR)/,$(PROJECT)))
PROJ_OBJ_LIST  := $(EXEC_LIST)

.PHONY: all Makefile directories

all : directories $(EXEC_LIST) run

# Build the executables 1 per configuration
$(EXEC_PATH) : $(MOCK_OBJS)                                                    \
               $(SCRATCH_DIR)/%/test_runner.o                                  \
               $(SCRATCH_DIR)/%/$(PROJECT).o                                   \
               $(SCRATCH_DIR)/%/$(PROJECT)_utest.o                             \
               | libs directories
        $(CC) $+ $(LDFLAGS) -o $@

# Mock All preprocessed header files
$(MOCK_SRC_LIST) : $(CPP_FILES)                                                \
                   Makefile                                                    \
                   $(PROJECT_DIR)/$(PROJECT).yml                               \
                   | directories
        cd $(@D) && cd .. &&                                                   \
            ruby $(CMOCK_EXEC_DIR)/cmock.rb -o$(PROJECT_DIR)/$(PROJECT).yml    \
            $(<D)/*

# Copy FreeRTOSConfig_$(DISCRIMINATOR).h to the apropriate directory and remove
# its guard ( FREERTOS_CONFIG_H ) to be able to be ingested into unifdef
$(CPP_FILES) : | directories
        cp $(PROJECT_DIR)/FreeRTOSConfig_$*.h $(SCRATCH_DIR)/$*/include/FreeRTOSConfig.h
        cp $(PROJECT_DIR)/FreeRTOSConfig_$*.h $(SCRATCH_DIR)/$*/include/FreeRTOSConfig.def
        sed -i '/#ifndef FREERTOS_CONFIG_H/d' $(SCRATCH_DIR)/$*/include/FreeRTOSConfig.def
        sed -i '/#define FREERTOS_CONFIG_H/d' $(SCRATCH_DIR)/$*/include/FreeRTOSConfig.def
        sed -i '/#endif/d' $(SCRATCH_DIR)/$*/include/FreeRTOSConfig.def
        sed -i '/#include/d' $(SCRATCH_DIR)/$*/include/FreeRTOSConfig.def
        for h_file in $(MOCK_FILES_FP) ; do                                    \
              unifdef -f $(SCRATCH_DIR)/$*/include/FreeRTOSConfig.def $$h_file \
                > $(SCRATCH_DIR)/$*/cpp/$$(basename $$h_file) ;                \
        done

# Build ALL the mock objects for the config
# This target is called ONLY once per configuration pattern (%)
$(MOCK_OBJS) : $(MOCK_SRC_LIST)
        $(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)
        $(eval INCLUDE += -I$(SCRATCH_DIR)/$*/mocks)                           \
        $(eval INCLUDE += -I$(KERNEL_DIR)/include)                             \
        for files in $^ ; do                                                   \
                   new_name=$${files%.c}.o;                                    \
            $(CC) -c $$files $(INCLUDE) $(CPPFLAGS) $(CFLAGS) -fPIC            \
                  -DUNITY_EXCLUDE_MATH_H -DUNITY_EXCLUDE_STDINT_H              \
                  -DUNITY_OUTPUT_CHAR -o $$new_name ;                          \
        done

# Build test_runner.o from test_runner.c
$(SCRATCH_DIR)/%/test_runner.o : $(SCRATCH_DIR)/%/test_runner.c                \
                                 $(SCRATCH_DIR)/%/$(PROJECT).o
        $(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)
        $(eval INCLUDE += -I$(SCRATCH_DIR)/$*/mocks)
        $(eval INCLUDE += -I$(KERNEL_DIR)/include)
        $(CC) -c $< $(INCLUDE) $(CPPFLAGS) $(CFLAGS) -o $@

# Build tasks_utest.o from tasks_utest_%.c
$(SCRATCH_DIR)/%/$(PROJECT)_utest.o : $(PROJECT_DIR)/$(PROJECT)_%_utest.c      \
                                      global_vars.h                            \
                                      | directories
        $(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)
        $(eval INCLUDE += -I$(SCRATCH_DIR)/$*/mocks)
        $(eval INCLUDE += -I$(KERNEL_DIR)/include)
        $(CC) -c $< $(INCLUDE) $(CPPFLAGS)  $(CFLAGS) -o $@

# Build tasks.o from tasks.i with the custom FreeRTOSConfig.h and place it in
# its configuration directory
$(SCRATCH_DIR)/%/$(PROJECT).o : $(SCRATCH_DIR)/%/$(PROJECT).i | directories
        $(CC) -c $< $(CFLAGS) $(COVERAGE_OPTS) -o $@

# Build tasks.i from tasks.c with the custom FreeRTOSConfig.h and place it in
# its configuration directory
$(SCRATCH_DIR)/%/$(PROJECT).i : $(KERNEL_DIR)/$(PROJECT).c | directories
        $(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)
        $(eval INCLUDE += -I$(SCRATCH_DIR)/$*/mocks)                           \
        $(eval INCLUDE += -I$(KERNEL_DIR)/include)                             \
        $(CC) -E $< $(INCLUDE) $(CPPFLAGS) -include list_macros.h -o $@

# Generate test_runner.c which contains the main function from the test file
$(SCRATCH_DIR)/%/test_runner.c : $(PROJECT_DIR)/$(PROJECT)_%_utest.c           \
                                 Makefile | directories
        ruby $(UNITY_BIN_DIR)/generate_test_runner.rb "--use_param_tests=1"    \
             $(PROJECT)_$*_utest.c $(PROJECT_DIR)/$(PROJECT).yml  $@

# Create needed directories
directories :
        -mkdir   -p  $(SCRATCH_DIR)
        -mkdir   -p  $(CONFIG_DIRS)
        -mkdir   -p  $(MOCK_DIRS)
        -mkdir   -p  $(CPP_DIRS)
        -mkdir   -p  $(INCLUDE_DIRS)
        -mkdir   -p  $(BIN_DIR)
        -mkdir   -p  $(LIB_DIR)

EXEC_PREFIX     :=  $(PROJECT)

include ../coverage.mk


# Indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)
# Do not move this line below the include
MAKEFILE_ABSPATH     := $(abspath $(lastword $(MAKEFILE_LIST)))

SUITES	+=	 tasks_freertos
# run each suite and leave gcda / gcov files in place
run:
    $(foreach suite,$(SUITES),make -C $(suite) run;)

#bin: $(EXEC_LIST)

#include ../subdir.mk
