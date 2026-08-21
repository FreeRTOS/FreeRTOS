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

# sed script which comments out a member of xSTATIC_TCB, and the pattern used
# to confirm that it was applied to the generated FreeRTOS.h.
TCB_MEMBER         :=   StaticListItem_t xDummy3\[ 2 \];
TCB_SHRINK_SED     :=   /^typedef struct xSTATIC_TCB$$/,/^} StaticTask_t;$$/s|^\( *\)\($(TCB_MEMBER)\)$$|\1/* \2 */|
TCB_SHRINK_CHECK   :=   /\* $(TCB_MEMBER) \*/

export
# Make variables available to included makefile

include ../../testdir.mk

$(MOCK_FILES_FP) :
    -mkdir -p $(SCRATCH_DIR)/include
    -mkdir -p $(SCRATCH_DIR)/cpp
    cp $(LOCAL_DIR)/FreeRTOSConfig.h $(SCRATCH_DIR)/include/FreeRTOSConfig.h
    cp $(LOCAL_DIR)/FreeRTOSConfig.h $(SCRATCH_DIR)/include/FreeRTOSConfig.def
    # This suite covers the configASSERT in xTaskCreateStatic which verifies
    # that sizeof( StaticTask_t ) equals sizeof( TCB_t ). Generate FreeRTOS.h
    # from the kernel one with a member of xSTATIC_TCB commented out so that
    # the two sizes differ. Generating this header, instead of keeping a
    # modified copy of it in this directory, keeps the suite from breaking
    # every time FreeRTOS.h changes in the kernel.
    sed '$(TCB_SHRINK_SED)' $(KERNEL_DIR)/include/FreeRTOS.h > $(SCRATCH_DIR)/include/FreeRTOS.h
    grep -q '$(TCB_SHRINK_CHECK)' $(SCRATCH_DIR)/include/FreeRTOS.h || { echo 'Failed to shrink StaticTask_t in the generated FreeRTOS.h - has xSTATIC_TCB changed in the kernel?' ; exit 1 ; }
    sed -i '/#ifndef FREERTOS_CONFIG_H/d' $(SCRATCH_DIR)/include/FreeRTOSConfig.def
    sed -i '/#define FREERTOS_CONFIG_H/d' $(SCRATCH_DIR)/include/FreeRTOSConfig.def
    sed -i '/#endif/d' $(SCRATCH_DIR)/include/FreeRTOSConfig.def
    sed -i '/#include/d' $(SCRATCH_DIR)/include/FreeRTOSConfig.def
    for h_file in $(MOCK_FILES_ORIG) ; do                                    \
        unifdef -f $(SCRATCH_DIR)/include/FreeRTOSConfig.def $$h_file \
                > $(SCRATCH_DIR)/$$(basename $$h_file) ;                \
        done

