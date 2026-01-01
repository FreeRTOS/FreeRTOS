#
# acpidump - ACPI table dump utility (binary to ascii hex)
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
PROG = $(OBJDIR)/acpidump

#
# Search paths for source files
#
vpath %.c \
	$(ACPIDUMP)\
	$(ACPICA_TABLES)\
	$(ACPICA_UTILITIES)\
	$(ACPICA_COMMON)\
	$(ACPICA_OSL)\
	$(ACPICA_EFI)

HEADERS = \
	$(wildcard $(ACPIDUMP)/*.h)

OBJECTS = \
	$(OBJDIR)/apdump.o\
	$(OBJDIR)/apfiles.o\
	$(OBJDIR)/apmain.o\
	$(OBJDIR)/cmfsize.o\
	$(OBJDIR)/getopt.o\
	$(OBJDIR)/oseficlib.o\
	$(OBJDIR)/osefitbl.o\
	$(OBJDIR)/osefixf.o\
	$(OBJDIR)/tbprint.o\
	$(OBJDIR)/tbxfroot.o\
	$(OBJDIR)/utascii.o\
	$(OBJDIR)/utbuffer.o\
	$(OBJDIR)/utclib.o\
	$(OBJDIR)/utdebug.o\
	$(OBJDIR)/utexcep.o\
	$(OBJDIR)/utglobal.o\
	$(OBJDIR)/uthex.o\
	$(OBJDIR)/utmath.o\
	$(OBJDIR)/utnonansi.o\
	$(OBJDIR)/utprint.o\
	$(OBJDIR)/utstring.o\
	$(OBJDIR)/utstrsuppt.o\
	$(OBJDIR)/utstrtoul64.o\
	$(OBJDIR)/utxferror.o

#
# Flags specific to acpidump
#
CFLAGS += \
	-DACPI_DUMP_APP\
	-I$(ACPIDUMP)

#
# Common Rules
#
include ../Makefile.rules
