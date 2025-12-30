#
# efihello - ACPI EFI demo
#

#
# Note: This makefile is intended to be used from within the native
# ACPICA directory structure, from under generate/efi. It specifically
# places all object files in a generate/efi subdirectory, not within
# the various ACPICA source directories. This prevents collisions
# between different compilations of the same source file with different
# compile options, and prevents pollution of the source code.
#
include ../Makefile.config
PROG = $(OBJDIR)/efihello

#
# Search paths for source files
#
vpath %.c \
	$(EFIHELLO)\
	$(ACPICA_UTILITIES)\
	$(ACPICA_COMMON)\
	$(ACPICA_OSL)\
	$(ACPICA_EFI)

HEADERS = \
	$(wildcard $(EFIHELLO)/*.h)

OBJECTS = \
	$(OBJDIR)/efihello.o\
	$(OBJDIR)/getopt.o\
	$(OBJDIR)/oseficlib.o\
	$(OBJDIR)/osefixf.o\
	$(OBJDIR)/utascii.o\
	$(OBJDIR)/utbuffer.o\
	$(OBJDIR)/utdebug.o\
	$(OBJDIR)/utclib.o\
	$(OBJDIR)/utexcep.o\
	$(OBJDIR)/utglobal.o\
	$(OBJDIR)/utmath.o\
	$(OBJDIR)/utprint.o\
	$(OBJDIR)/utstring.o\
	$(OBJDIR)/utxferror.o

#
# Flags specific to efihello
#
CFLAGS += \
	-DACPI_EFI_HELLO\
	-I$(EFIHELLO)

#
# Common Rules
#
include ../Makefile.rules
