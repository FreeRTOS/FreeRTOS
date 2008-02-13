#
# FreeRTOS 4.1.0 - MCF5235 Coldfire Port
#
# Copyright (c) 2006 Christian Walter, Vienna 2006.
#
# $Id: Makefile,v 1.4 2006/09/06 19:55:07 wolti Exp $
#
# ---------------------------------------------------------------------------
BASE        = /opt/gcc-m68k/bin
CC	        = $(BASE)/m68k-elf-gcc
CXX	        = $(BASE)/m68k-elf-g++
OBJCOPY	    = $(BASE)/m68k-elf-objcopy
SIZE	    = $(BASE)/m68k-elf-size
INSIGHT     = $(BASE)/m68k-bdm-elf-insight
BDMFLASH    = $(BASE)/bdmflash

#CFLAGS	    = -MD -gdwarf-2 -g3 -m528x -Wall 
CFLAGS	    = -MD -O2 -m528x -Wall \
			  -D'GCC_MCF5235=1' -D'_GCC_USES_FP=1' \
			  -D'__IPSBAR=((vuint8 *) 0x40000000)' -D'FSYS_2=25000000UL' \
			  -I. -Iinclude -Iinclude/arch -Ifec \
			  -I../../Source/include -I../Common/include \
              -Ilwip/src/include -Ilwip/src/include/ipv4 \
              -Ilwip/contrib/port/FreeRTOS/MCF5235 \
              -Ilwip/contrib/port/FreeRTOS/MCF5235/netif

ASFLAGS     = -MD -gdwarf-2 -g3 -m528x -Wa,--register-prefix-optional \
              -Wa,--bitwise-or -Wa,--defsym,IPSBAR=0x40000000
LDSCRIPT    = m5235-ram.ld
LDFLAGS	    = -nostartfiles -m528x -Wl,--script=$(LDSCRIPT)

TGT         = demo
OTHER_CSRC  = 
OTHER_ASRC  = $(addprefix system/, crt0.S vector.S)
CSRC        = demo.c web.c \
              $(addprefix system/, init.c newlib.c serial.c) \
              $(addprefix ../Common/Minimal/, PollQ.c integer.c flop.c BlockQ.c semtest.c dynamic.c ) \
			  $(addprefix ../../Source/, tasks.c queue.c list.c) \
			  $(addprefix ../../Source/portable/MemMang/, heap_3.c) \
			  $(addprefix ../../Source/portable/GCC/MCF5235/, port.c) \
              $(addprefix lwip/src/core/, tcp_out.c inet.c mem.c memp.c netif.c pbuf.c raw.c stats.c sys.c tcp.c tcp_in.c udp.c ipv4/ip.c ipv4/ip_addr.c ipv4/icmp.c ipv4/ip_frag.c) \
              $(addprefix lwip/src/api/, tcpip.c api_msg.c err.c api_lib.c ) \
              $(addprefix lwip/src/netif/, etharp.c ) \
              $(addprefix lwip/contrib/port/FreeRTOS/MCF5235/, sys_arch.c netif/fec.c netif/nbuf.c) 

ASRC        = $(addprefix system/, mcf5xxx.S ) 
OBJS        = $(CSRC:.c=.o) $(ASRC:.S=.o)
NOLINK_OBJS = $(OTHER_CSRC:.c=.o) $(OTHER_ASRC:.S=.o)
DEPS        = $(OBJS:.o=.d) $(NOLINK_OBJS:.o=.d)
BIN         = $(TGT).elf

.PHONY: clean all

all: $(BIN)

flash-programm: $(TGT).elf
	$(OBJCOPY) -O binary $(TGT).elf $(TGT).bin
	@BIN_SIZE=`du -b $(TGT).bin | awk '//{ print $$1; }'`; \
	echo "programming $(TGT).bin with size $$BIN_SIZE to flash..."; \
	$(BDMFLASH) /dev/bdmcf20 0x00000000 1 2 write $(TGT).bin 0

flash-verify:
	@BIN_SIZE=`du -b $(TGT).bin | awk '//{ print $$1; }'`; \
	echo "loading $$BIN_SIZE bytes from target into $(TGT).vrf..."; \
	$(BDMFLASH) /dev/bdmcf20 0x00000000 1 2 read $(TGT).vrf 0 $$BIN_SIZE

flash-erase:
	$(BDMFLASH) /dev/bdmcf20 0x00000000 1 2 erase

debug:
	$(INSIGHT) --command=m5235.gdb --se=$(TGT).elf

$(BIN): $(OBJS) $(NOLINK_OBJS)
	$(CC) $(LDFLAGS) -Wl,-Map=$(TGT).map $(OBJS) $(LDLIBS) -o $@

clean:
	rm -f $(DEPS)
	rm -f $(OBJS) $(NOLINK_OBJS)
	rm -f $(BIN) $(TGT).map

# ---------------------------------------------------------------------------
# rules for code generation
# ---------------------------------------------------------------------------
%.o:    %.c
	$(CC) $(CFLAGS) -o $@ -c $<

%.o:    %.S
	$(CC) $(ASFLAGS) -o $@ -c $<

# ---------------------------------------------------------------------------
#  # compiler generated dependencies
# ---------------------------------------------------------------------------
-include $(DEPS)

