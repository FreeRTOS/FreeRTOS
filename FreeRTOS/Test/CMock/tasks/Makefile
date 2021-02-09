# Change according to what your  unit test directory is.
# For example if testing queue.c your directory should be called queue
# and the project name should be queue
# if testing list.c your directory should be called list
# and the project name should be list

PROJECT          :=   tasks

# List the dependency files you wish to mock
MOCK_FILES_FP    :=   $(KERNEL_DIR)/include/timers.h
MOCK_FILES_FP    +=   $(KERNEL_DIR)/include/list.h
MOCK_FILES_FP    +=   $(KERNEL_DIR)/include/portable.h

# List special compilation flags for this module
CFLAGS += -Wno-error=pointer-to-int-cast -Wno-pointer-to-int-cast
CFLAGS += -Wno-error=int-to-pointer-cast -Wno-int-to-pointer-cast

# List special preprocessing flags for this module
CPPFLAGS         +=

# List special linker flags for this module
LDFLAGS          +=   -Wl,--allow-multiple-definition 

# Makefile Flags (if needed)
#MAKEFLAGS += -rR

# Try not to edit beyond this line

COVERAGE_OPTS    :=   -fprofile-arcs -ftest-coverage -fprofile-generate

# build/generated/queue
SCRATCH_DIR      :=   $(GENERATED_DIR)/$(PROJECT)

# list.h   timers.h   portable.h
MOCK_FILES       :=   $(notdir $(MOCK_FILES_FP))

# ...tasks/%/mocks/mock_list.o   tasks/%/mocks/mock_timers.o
MOCK_OBJS        :=   $(addprefix $(SCRATCH_DIR)/%/mocks/mock_,$(MOCK_FILES:.h=.o))

# ...tasks/%/mocks/mock_list.c   tasks/%/mocks/mock_timers.c
MOCK_SRC_LIST    :=   $(addprefix $(SCRATCH_DIR)/%/mocks/,$(addprefix mock_,$(MOCK_FILES:.h=.c)))

# executable generic name queue_utest without the _num
EXEC             :=   $(PROJECT)_utest

# Test/CMock/tasks
PROJECT_DIR      :=   $(abspath .)

# tasks/%/cpp/timers.h   tasks/%/cpp/list.h
CPP_FILES        :=   $(addprefix $(SCRATCH_DIR)/%/cpp/,$(notdir $(MOCK_FILES_FP)))

# tasks_utest_1.c   tasks_utest_2.c ...
SOURCES          :=   $(sort $(wildcard $(PROJECT)_utest_*.c))

# 1 2 3...
PROJECT_NUMBERS  :=   $(subst .c,,$(subst $(PROJECT)_utest_,,$(SOURCES)))

# tasks/1/mocks   tasks/2/mocks
MOCK_DIRS        :=   $(addsuffix /mocks,$(addprefix $(SCRATCH_DIR)/,$(PROJECT_NUMBERS)))
# queue/1/cpp   queue/2/cpp
CPP_DIRS         :=   $(addsuffix /cpp,$(addprefix $(SCRATCH_DIR)/,$(PROJECT_NUMBERS)))
# tasks/1/include   tasks/2/include
INCLUDE_DIRS     :=   $(addsuffix /include,$(addprefix $(SCRATCH_DIR)/,$(PROJECT_NUMBERS)))
#list/1   list/2 ....
CONFIG_DIRS := $(addprefix $(SCRATCH_DIR)/,$(PROJECT_NUMBERS))

ifeq ($(MOCK_FILES_FP),)
     $(shell mkdir -p  $(MOCK_DIRS))
     $(shell for n in $(MOCK_DIRS) ; do touch -a $(n)/mock_dummy.c)
endif

EXECUTABLES := $(addprefix $(BIN_DIR)/,$(patsubst %.c,%,$(SOURCES)))
EXEC_PATH := $(addprefix $(BIN_DIR)/,$(EXEC))

.PHONY: all Makefile directories

.SECONDEXPANSION:
all : directories $(EXECUTABLES)

.SECONDARY:
# Build the executables 1 per configuration
$(EXEC_PATH)_% : $(MOCK_OBJS)                                                  \
		 $(SCRATCH_DIR)/%/test_runner.o                                \
                 $(SCRATCH_DIR)/%/$(PROJECT).o                                 \
		 $(SCRATCH_DIR)/%/$(PROJECT)_utest.o                           \
		 $(SCRATCH_DIR)/%/heap_3.o                                     \
		 $(SCRATCH_DIR)/%/port.o                                       \
		 | directories
	$(CC) $+ $(LDFLAGS) -o $@ 

.SECONDARY:
# Mock All preprocessed header files
$(MOCK_SRC_LIST) : $(CPP_FILES)                                                \
		   Makefile $(PROJECT_DIR)/$(PROJECT).yml                      \
		  | directories
	cd $(@D) && cd .. &&                                                   \
	    ruby $(CMOCK_EXEC_DIR)/cmock.rb -o$(PROJECT_DIR)/$(PROJECT).yml    \
	    $(<D)/*

.SECONDARY:
# Preprocess ALL the headers
# This target is called ONLY once per configuration (%)
$(CPP_FILES) : $(MOCK_FILES_FP) $(SCRATCH_DIR)/%/cpp | directories
	cp $(PROJECT_DIR)/FreeRTOSConfig_$*.h                                  \
	   $(SCRATCH_DIR)/$*/include/FreeRTOSConfig.h
	$(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)
	for files in $(MOCK_FILES_FP) ; do                                     \
	    $(CC) -E $$files  $(INCLUDE) $(CPPFLAGS) $(CFLAGS)                 \
		  -include FreeRTOSConfig.h -include FreeRTOS.h                \
		  -o $(@D)/$$(basename $$files);                               \
        done


.SECONDARY:
# Build ALL the mock objects for the config
# This target is called ONLY once per configuration (%)
$(MOCK_OBJS) : $(MOCK_SRC_LIST)
	$(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)
	for files in $^ ; do                                                   \
	    OBJECTS=$(patsubst %.c,%.o,$$files);                               \
       	    new_name=$${files%.c}.o;                                           \
	    $(CC) -c $$files $(INCLUDE) -fPIC $(CFLAGS) -DUNITY_EXCLUDE_MATH_H \
		-DUNITY_EXCLUDE_STDINT_H -DUNITY_OUTPUT_CHAR -o $$new_name ;   \
        done

.SECONDARY:
# Build test_runner.o from test_runner.c
$(SCRATCH_DIR)/%/test_runner.o : $(SCRATCH_DIR)/%/test_runner.c                \
                                 $(SCRATCH_DIR)/%/$(PROJECT).o
	$(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)                          \
	$(CC) -c $< $(INCLUDE) $(CPPFLAGS)  $(CFLAGS) -o $@

.SECONDARY:
# Build tasks_utest.o from tasks_utest_%.c
$(SCRATCH_DIR)/%/$(PROJECT)_utest.o : $(PROJECT_DIR)/$(PROJECT)_utest_%.c      \
                                      | directories
	$(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)
	$(CC) -c $< $(INCLUDE) $(CPPFLAGS)  $(CFLAGS) -o $@

.SECONDARY:
# Build tasks.so from tasks.c with the custom FreeRTOSConfig.h and place it in
# its configuration directory
$(SCRATCH_DIR)/%/$(PROJECT).o : $(KERNEL_DIR)/$(PROJECT).c | directories
	$(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)
	$(CC) -c $< $(INCLUDE) $(CPPFLAGS)  $(CFLAGS) $(COVERAGE_OPTS) -o $@

.SECONDARY:
# Build the unit tests with heap3 as it uses the standard malloc and free
$(SCRATCH_DIR)/%/heap_3.o : $(KERNEL_DIR)/portable/MemMang/heap_3.c
	$(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)
	$(CC) -c $< $(INCLUDE) $(CPPFLAGS) $(CFLAGS) -o $@

.SECONDARY:
# Buld port.o from port.c
$(SCRATCH_DIR)/%/port.o : $(UT_ROOT_DIR)/config/port.c
	$(eval INCLUDE = -I$(SCRATCH_DIR)/$*/include)
	$(CC) -c $< $(INCLUDE) $(CPPFLAGS) $(CFLAGS) -o $@

.SECONDARY:
# Generate test_runner.c which contains the main function from the test file
$(SCRATCH_DIR)/%/test_runner.c : $(PROJECT_DIR)/$(PROJECT)_utest_%.c           \
                                 Makefile | directories
	ruby $(UNITY_BIN_DIR)/generate_test_runner.rb $(EXEC)_$*.c             \
                       $(PROJECT_DIR)/$(PROJECT).yml $@

# Create needed directories
directories :
	-mkdir   $(SCRATCH_DIR)
	-mkdir   $(CONFIG_DIRS)
	-mkdir   $(MOCK_DIRS)
	-mkdir   $(CPP_DIRS)
	-mkdir   $(INCLUDE_DIRS)

.PRECIOUS: build/%.o
.PRECIOUS: build/%.c
.PRECIOUS: build/%.h
