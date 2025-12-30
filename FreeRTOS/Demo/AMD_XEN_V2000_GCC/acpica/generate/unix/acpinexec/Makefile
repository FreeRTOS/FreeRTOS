#
# acpiexec: ACPI execution simulator. Runs ACPICA code in user
# space. Loads ACPI tables, displays the namespace, and allows
# execution of control methods.
#

#
# Note: This makefile is intended to be used from within the native
# ACPICA directory structure, from under generate/unix. It specifically
# places all object files in a generate/unix subdirectory, not within
# the various ACPICA source directories. This prevents collisions
# between different compilations of the same source file with different
# compile options, and prevents pollution of the source code.
#
include ../Makefile.config
FINAL_PROG = ../$(BINDIR)/acpinexec
PROG = $(OBJDIR)/acpinexec

#
# Search paths for source files
#
vpath %.c \
    $(ACPIEXEC)

HEADERS = \
    $(wildcard $(ACPIEXEC)/*.h)

OBJECTS = \
	$(OBJDIR)/aeexec.o\
	$(OBJDIR)/aeexception.o\
	$(OBJDIR)/aehandlers.o\
	$(OBJDIR)/aeinitfile.o\
	$(OBJDIR)/aeinstall.o\
	$(OBJDIR)/aemain.o\
	$(OBJDIR)/aeregion.o\
	$(OBJDIR)/aetables.o\
	$(OBJDIR)/aetests.o

#
# Flags specific to acpiexec utility
#
CFLAGS += \
    -DACPI_EXEC_APP\
    -I$(ACPIEXEC)

ifeq ($(ASLTS),TRUE)
CFLAGS += \
    -DACPI_CHECKSUM_ABORT=TRUE
endif

LDFLAGS += -lacpi -L../libacpi/obj
ifneq ($(ACPI_HOST),_QNX)
LDFLAGS += -lpthread
endif

ifneq ($(ACPI_HOST),_APPLE)
ifneq ($(ACPI_HOST),_QNX)
ifneq ($(ACPI_HOST),_HAIKU)
LDFLAGS += -lrt
endif
endif
endif

#
# Common Rules
#
include ../Makefile.rules
