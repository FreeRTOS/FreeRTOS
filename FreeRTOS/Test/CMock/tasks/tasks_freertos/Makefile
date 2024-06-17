SHELL += -x

# Indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)

# Do not move this line below the include
MAKEFILE_ABSPATH    :=    $(abspath $(lastword $(MAKEFILE_LIST)))

#PROJECT        := tasks
# Project / Suite are determined based on path: $(UT_ROOT_DIR)/$(PROJECT)/$(SUITE)
PROJECT         :=  $(lastword $(subst /, ,$(dir $(abspath $(MAKEFILE_ABSPATH)/../))))
SUITE           :=  $(lastword $(subst /, ,$(dir $(MAKEFILE_ABSPATH))))

SCRATCH_DIR      :=   $(GENERATED_DIR)/$(PROJECT)/$(SUITE)

include ../../makefile.in

# PROJECT_SRC lists the .c files under test
PROJECT_SRC         +=   tasks.c
PROJECT_DIR         :=   $(abspath ../)
LOCAL_DIR           :=   $(abspath .)

# PROJECT_DEPS_SRC list the .c file that are dependencies of PROJECT_SRC files
# Files in PROJECT_DEPS_SRC are excluded from coverage measurements
PROJECT_DEPS_SRC    +=

# PROJECT_HEADER_DEPS: headers that should be excluded from coverage measurements.
PROJECT_HEADER_DEPS +=  FreeRTOS.h

# SUITE_UT_SRC: .c files that contain test cases (must end in _utest.c)
SUITE_UT_SRC        :=  tasks_utest.c

# SUITE_SUPPORT_SRC: .c files used for testing that do not contain test cases.
# Paths are relative to PROJECT_DIR
SUITE_SUPPORT_SRC   +=

# List the headers used by PROJECT_SRC that you would like to mock
MOCK_FILES_ORIG     :=   $(KERNEL_DIR)/include/timers.h
MOCK_FILES_ORIG     +=   $(KERNEL_DIR)/include/list.h
MOCK_FILES_ORIG     +=   $(KERNEL_DIR)/include/portable.h
MOCK_FILES_ORIG     +=   $(PROJECT_DIR)/list_macros.h
MOCK_FILES_ORIG     +=   $(PROJECT_DIR)/../config/fake_assert.h

MOCK_FILES_FP      :=   $(GENERATED_DIR)/$(PROJECT)/tasks_freertos/timers.h
MOCK_FILES_FP      +=   $(GENERATED_DIR)/$(PROJECT)/tasks_freertos/list.h
MOCK_FILES_FP      +=   $(GENERATED_DIR)/$(PROJECT)/tasks_freertos/portable.h
MOCK_FILES_FP      +=   $(GENERATED_DIR)/$(PROJECT)/tasks_freertos/list_macros.h
MOCK_FILES_FP      +=   $(GENERATED_DIR)/$(PROJECT)/tasks_freertos/fake_assert.h

# List any addiitonal flags needed by the preprocessor
CPPFLAGS           :=   -I $(GENERATED_DIR)/$(PROJECT)/tasks_freertos/include $(CPPFLAGS)
CPPFLAGS           +=   -I .
CPPFLAGS           +=   -I ../

# List any addiitonal flags needed by the compiler
CFLAGS             +=

export
# Make variables available to included makefile

include ../../testdir.mk

$(MOCK_FILES_FP) :
    -mkdir -p $(SCRATCH_DIR)/include
    -mkdir -p $(SCRATCH_DIR)/cpp
    cp $(LOCAL_DIR)/FreeRTOSConfig.h $(SCRATCH_DIR)/include/FreeRTOSConfig.h
    cp $(LOCAL_DIR)/FreeRTOSConfig.h $(SCRATCH_DIR)/include/FreeRTOSConfig.def
    cp $(LOCAL_DIR)/FreeRTOS.h $(SCRATCH_DIR)/include/
    sed -i '/#ifndef FREERTOS_CONFIG_H/d' $(SCRATCH_DIR)/include/FreeRTOSConfig.def
    sed -i '/#define FREERTOS_CONFIG_H/d' $(SCRATCH_DIR)/include/FreeRTOSConfig.def
    sed -i '/#endif/d' $(SCRATCH_DIR)/include/FreeRTOSConfig.def
    sed -i '/#include/d' $(SCRATCH_DIR)/include/FreeRTOSConfig.def
    for h_file in $(MOCK_FILES_ORIG) ; do                                    \
        unifdef -f $(SCRATCH_DIR)/include/FreeRTOSConfig.def $$h_file \
                > $(SCRATCH_DIR)/$$(basename $$h_file) ;                \
        done

