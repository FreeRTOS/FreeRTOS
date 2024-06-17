# Indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)

# Do not move this line below the include
MAKEFILE_ABSPATH    :=    $(abspath $(lastword $(MAKEFILE_LIST)))
include ../../makefile.in

# PROJECT_SRC lists the .c files under test
PROJECT_SRC         +=  queue.c

# PROJECT_DEPS_SRC list the .c file that are dependencies of PROJECT_SRC files
# Files in PROJECT_DEPS_SRC are excluded from coverage measurements
PROJECT_DEPS_SRC    +=  list.c

# PROJECT_HEADER_DEPS: headers that should be excluded from coverage measurements.
PROJECT_HEADER_DEPS +=  FreeRTOS.h

# SUITE_UT_SRC: .c files that contain test cases (must end in _utest.c)
SUITE_UT_SRC        +=  queue_create_dynamic_utest.c
SUITE_UT_SRC        +=  queue_create_static_utest.c
SUITE_UT_SRC        +=  queue_delete_dynamic_utest.c
SUITE_UT_SRC        +=  queue_delete_static_utest.c
SUITE_UT_SRC        +=  queue_reset_utest.c
SUITE_UT_SRC        +=  queue_receive_nonblocking_utest.c
SUITE_UT_SRC        +=  queue_receive_blocking_utest.c
SUITE_UT_SRC        +=  queue_send_nonblocking_utest.c
SUITE_UT_SRC        +=  queue_send_blocking_utest.c
SUITE_UT_SRC        +=  queue_status_utest.c
SUITE_UT_SRC		+=  queue_get_static_buffers_utest.c

# SUITE_SUPPORT_SRC: .c files used for testing that do not contain test cases.
# Paths are relative to PROJECT_DIR
SUITE_SUPPORT_SRC   +=  queue_utest_common.c
SUITE_SUPPORT_SRC   +=  td_task.c
SUITE_SUPPORT_SRC   +=  td_port.c

# List the headers used by PROJECT_SRC that you would like to mock
MOCK_FILES_FP   +=  $(KERNEL_DIR)/include/task.h
MOCK_FILES_FP   +=  $(UT_ROOT_DIR)/config/fake_assert.h
MOCK_FILES_FP   +=  $(UT_ROOT_DIR)/config/fake_port.h

# List any additional flags needed by the preprocessor
CPPFLAGS        +=  -DportUSING_MPU_WRAPPERS=0

# List any additional flags needed by the compiler
CFLAGS          += -O1 -fno-omit-frame-pointer -fno-optimize-sibling-calls -fno-exceptions

# Try not to edit beyond this line unless necessary.

# Project / Suite are determined based on path: $(UT_ROOT_DIR)/$(PROJECT)/$(SUITE)
PROJECT         :=  $(lastword $(subst /, ,$(dir $(abspath $(MAKEFILE_ABSPATH)/../))))
SUITE           :=  $(lastword $(subst /, ,$(dir $(MAKEFILE_ABSPATH))))

# Make variables available to included makefile
export

include ../../testdir.mk
