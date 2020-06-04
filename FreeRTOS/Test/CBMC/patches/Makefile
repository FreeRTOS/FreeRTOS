BRANCH=freertos

PATCHED=patched

default:
	git format-patch $(BRANCH)..$(BRANCH)-cbmc-patches

patch:
	if [ ! -f $(PATCHED) ]; then \
	  for p in *.patch; do \
	    (cd ../../..; patch -p1 < CBMC/patches/$${p}) \
	  done; \
	  cat > $(PATCHED) < /dev/null; \
	fi

unpatch:
	git checkout ../../../lib
	$(RM) $(PATCHED)

#patching file lib/FreeRTOS-Plus-TCP/include/FreeRTOS_IP_Private.h
#patching file lib/include/private/list.h
#patching file lib/FreeRTOS-Plus-TCP/source/FreeRTOS_DHCP.c
#patching file lib/FreeRTOS-Plus-TCP/source/FreeRTOS_DNS.c
#patching file lib/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_WIN.c
