# indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)

# Do not move this line below the include
MAKEFILE_ABSPATH    :=  $(abspath $(lastword $(MAKEFILE_LIST)))
include ../makefile.in

# PROJECT_SRC lists the .c files under test
PROJECT_SRC         :=  stream_buffer.c

# PROJECT_DEPS_SRC list the .c file that are dependencies of PROJECT_SRC files
# Files in PROJECT_DEPS_SRC are excluded from coverage measurements
PROJECT_DEPS_SRC    :=

# PROJECT_HEADER_DEPS: headers that should be excluded from coverage measurements.
PROJECT_HEADER_DEPS :=  FreeRTOS.h

# SUITE_UT_SRC: .c files that contain test cases (must end in _utest.c)
SUITE_UT_SRC        :=  stream_buffer_utest.c

# SUITE_SUPPORT_SRC: .c files used for testing that do not contain test cases.
# Paths are relative to PROJECT_DIR
SUITE_SUPPORT_SRC   :=

# List the headers used by PROJECT_SRC that you would like to mock
MOCK_FILES_FP      :=  $(KERNEL_DIR)/include/task.h
MOCK_FILES_FP      +=  $(UT_ROOT_DIR)/config/fake_assert.h
MOCK_FILES_FP      +=  $(UT_ROOT_DIR)/config/fake_port.h

# List any addiitonal flags needed by the preprocessor
CPPFLAGS            +=  -DportUSING_MPU_WRAPPERS=0

# List any addiitonal flags needed by the compiler
CFLAGS              +=

# Try not to edit beyond this line unless necessary.

# Project is determined based on path: $(UT_ROOT_DIR)/$(PROJECT)
PROJECT         :=  $(lastword $(subst /, ,$(dir $(abspath $(MAKEFILE_ABSPATH)))))

export

include ../testdir.mk
