CC = arm-none-eabi-gcc
BIN := freertos_mqtts_mps2_demo.axf

BUILD_DIR := build

FREERTOS_DIR_REL := ../../../FreeRTOS
FREERTOS_DIR := $(abspath $(FREERTOS_DIR_REL))
KERNEL_DIR := $(FREERTOS_DIR)/Source

FREERTOS_PLUS_DIR_REL := ../../../FreeRTOS-Plus
FREERTOS_PLUS_DIR := $(abspath $(FREERTOS_PLUS_DIR_REL))

FREERTOS_TCP = ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP
MBEDTLS = ${FREERTOS_PLUS_DIR}/ThirdParty/mbedtls
FREERTOS_MBEDTLS_WRAPPER = ${FREERTOS_PLUS_DIR}/Source/Application-Protocols/network_transport
COREMQTT = ${FREERTOS_PLUS_DIR}/Source/Application-Protocols/coreMQTT
UTILITIES = ${FREERTOS_PLUS_DIR}/Source/Utilities

# demo headers
INCLUDE_DIRS += -I.

# demo sources
SOURCE_FILES += startup.c
SOURCE_FILES += syscall.c
SOURCE_FILES += main.c
SOURCE_FILES += main_networking.c
SOURCE_FILES += MutualAuthMQTTExample.c

# CMSIS
INCLUDE_DIRS += -ICMSIS

# FreeRTOS Kernel headers
INCLUDE_DIRS += -I$(KERNEL_DIR)/include

# FreeRTOS Kernel sources
SOURCE_FILES += $(KERNEL_DIR)/tasks.c
SOURCE_FILES += $(KERNEL_DIR)/list.c
SOURCE_FILES += $(KERNEL_DIR)/queue.c
SOURCE_FILES += $(KERNEL_DIR)/timers.c
SOURCE_FILES += $(KERNEL_DIR)/event_groups.c

# FreeRTOS Kernel ARM Cortex-M3 port headers
INCLUDE_DIRS += -I$(KERNEL_DIR)/portable/GCC/ARM_CM3

# FreeRTOS Kernel ARM Cortex-M3 port sources
SOURCE_FILES += $(KERNEL_DIR)/portable/GCC/ARM_CM3/port.c
SOURCE_FILES += ${KERNEL_DIR}/portable/MemMang/heap_3.c

# FreeRTOS+TCP headers
INCLUDE_DIRS += -I${FREERTOS_TCP}/source/include/

# FreeRTOS+TCP sources
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_ARP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DHCP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DNS.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DNS_Cache.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DNS_Callback.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DNS_Networking.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DNS_Parser.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_ICMP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_IP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_IP_Timers.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_IP_Utils.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_Sockets.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_Stream_Buffer.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_IP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_Reception.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_State_Handling.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_Transmission.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_Utils.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_WIN.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_Tiny_TCP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_UDP_IP.c

# FreeRTOS+TCP port for ARM MPS2 SoC headers
INCLUDE_DIRS += -I${FREERTOS_TCP}/source/portable/NetworkInterface/MPS2_AN385/ether_lan9118
INCLUDE_DIRS += -I${FREERTOS_TCP}/source/portable/Compiler/GCC

# FreeRTOS+TCP port for ARM MPS2 SoC sources
SOURCE_FILES += ${FREERTOS_TCP}/source/portable/BufferManagement/BufferAllocation_2.c
SOURCE_FILES += ${FREERTOS_TCP}/source/portable/NetworkInterface/MPS2_AN385/NetworkInterface.c
SOURCE_FILES += ${FREERTOS_TCP}/source/portable/NetworkInterface/MPS2_AN385/ether_lan9118/smsc9220_eth_drv.c

# mbedTLS headers
INCLUDE_DIRS += -I${MBEDTLS}/include
INCLUDE_DIRS += -I${MBEDTLS}/library

# mbedTLS sources
SOURCE_FILES += ${MBEDTLS}/library/aes.c 
SOURCE_FILES += ${MBEDTLS}/library/aesni.c
SOURCE_FILES += ${MBEDTLS}/library/aria.c
SOURCE_FILES += ${MBEDTLS}/library/asn1parse.c
SOURCE_FILES += ${MBEDTLS}/library/asn1write.c
SOURCE_FILES += ${MBEDTLS}/library/base64.c
SOURCE_FILES += ${MBEDTLS}/library/bignum.c
SOURCE_FILES += ${MBEDTLS}/library/camellia.c
SOURCE_FILES += ${MBEDTLS}/library/ccm.c
SOURCE_FILES += ${MBEDTLS}/library/chacha20.c
SOURCE_FILES += ${MBEDTLS}/library/chachapoly.c
SOURCE_FILES += ${MBEDTLS}/library/cipher.c
SOURCE_FILES += ${MBEDTLS}/library/cipher_wrap.c
SOURCE_FILES += ${MBEDTLS}/library/cmac.c
SOURCE_FILES += ${MBEDTLS}/library/constant_time.c
SOURCE_FILES += ${MBEDTLS}/library/ctr_drbg.c
SOURCE_FILES += ${MBEDTLS}/library/debug.c
SOURCE_FILES += ${MBEDTLS}/library/des.c
SOURCE_FILES += ${MBEDTLS}/library/dhm.c
SOURCE_FILES += ${MBEDTLS}/library/ecdh.c
SOURCE_FILES += ${MBEDTLS}/library/ecdsa.c
SOURCE_FILES += ${MBEDTLS}/library/ecjpake.c
SOURCE_FILES += ${MBEDTLS}/library/ecp.c
SOURCE_FILES += ${MBEDTLS}/library/ecp_curves.c
SOURCE_FILES += ${MBEDTLS}/library/entropy.c
SOURCE_FILES += ${MBEDTLS}/library/entropy_poll.c
SOURCE_FILES += ${MBEDTLS}/library/error.c
SOURCE_FILES += ${MBEDTLS}/library/gcm.c
SOURCE_FILES += ${MBEDTLS}/library/hkdf.c
SOURCE_FILES += ${MBEDTLS}/library/hmac_drbg.c
SOURCE_FILES += ${MBEDTLS}/library/md.c
SOURCE_FILES += ${MBEDTLS}/library/md5.c
SOURCE_FILES += ${MBEDTLS}/library/memory_buffer_alloc.c
SOURCE_FILES += ${MBEDTLS}/library/mps_reader.c
SOURCE_FILES += ${MBEDTLS}/library/mps_trace.c
SOURCE_FILES += ${MBEDTLS}/library/net_sockets.c
SOURCE_FILES += ${MBEDTLS}/library/nist_kw.c
SOURCE_FILES += ${MBEDTLS}/library/oid.c
SOURCE_FILES += ${MBEDTLS}/library/padlock.c
SOURCE_FILES += ${MBEDTLS}/library/pem.c
SOURCE_FILES += ${MBEDTLS}/library/pk.c
SOURCE_FILES += ${MBEDTLS}/library/pkcs5.c
SOURCE_FILES += ${MBEDTLS}/library/pkcs12.c
SOURCE_FILES += ${MBEDTLS}/library/pkparse.c
SOURCE_FILES += ${MBEDTLS}/library/pk_wrap.c
SOURCE_FILES += ${MBEDTLS}/library/pkwrite.c
SOURCE_FILES += ${MBEDTLS}/library/platform.c
SOURCE_FILES += ${MBEDTLS}/library/platform_util.c
SOURCE_FILES += ${MBEDTLS}/library/poly1305.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_aead.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_cipher.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_client.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_driver_wrappers.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_ecp.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_hash.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_mac.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_rsa.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_se.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_slot_management.c
SOURCE_FILES += ${MBEDTLS}/library/psa_crypto_storage.c
SOURCE_FILES += ${MBEDTLS}/library/psa_its_file.c
SOURCE_FILES += ${MBEDTLS}/library/ripemd160.c
SOURCE_FILES += ${MBEDTLS}/library/rsa.c
SOURCE_FILES += ${MBEDTLS}/library/rsa_alt_helpers.c
SOURCE_FILES += ${MBEDTLS}/library/sha1.c
SOURCE_FILES += ${MBEDTLS}/library/sha256.c
SOURCE_FILES += ${MBEDTLS}/library/sha512.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_cache.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_ciphersuites.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_client.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_cookie.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_debug_helpers_generated.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_msg.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_ticket.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_tls.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_tls12_client.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_tls12_server.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_tls13_client.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_tls13_generic.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_tls13_keys.c
SOURCE_FILES += ${MBEDTLS}/library/ssl_tls13_server.c
SOURCE_FILES += ${MBEDTLS}/library/threading.c
SOURCE_FILES += ${MBEDTLS}/library/timing.c
SOURCE_FILES += ${MBEDTLS}/library/version.c
SOURCE_FILES += ${MBEDTLS}/library/version_features.c
SOURCE_FILES += ${MBEDTLS}/library/x509.c
SOURCE_FILES += ${MBEDTLS}/library/x509_create.c
SOURCE_FILES += ${MBEDTLS}/library/x509_crl.c
SOURCE_FILES += ${MBEDTLS}/library/x509_crt.c
SOURCE_FILES += ${MBEDTLS}/library/x509_csr.c
SOURCE_FILES += ${MBEDTLS}/library/x509write_crt.c
SOURCE_FILES += ${MBEDTLS}/library/x509write_csr.c

# FreeRTOS+TCP mbedtls wrapper headers
INCLUDE_DIRS += -I${FREERTOS_MBEDTLS_WRAPPER}
INCLUDE_DIRS += -I${FREERTOS_MBEDTLS_WRAPPER}/tcp_sockets_wrapper/include
INCLUDE_DIRS += -I${FREERTOS_MBEDTLS_WRAPPER}/tcp_sockets_wrapper/ports/freertos_plus_tcp

# FreeRTOS+TCP mbedtls wrapper sources 
SOURCE_FILES += ${FREERTOS_MBEDTLS_WRAPPER}/transport_mbedtls.c
SOURCE_FILES += ${FREERTOS_MBEDTLS_WRAPPER}/mbedtls_bio_tcp_sockets_wrapper.c
SOURCE_FILES += ${FREERTOS_MBEDTLS_WRAPPER}/tcp_sockets_wrapper/ports/freertos_plus_tcp/sockets_wrapper.c
SOURCE_FILES += ${FREERTOS_MBEDTLS_WRAPPER}/tcp_sockets_wrapper/ports/freertos_plus_tcp/tcp_sockets_wrapper.c

# FreeRTOS mbedtls port headers
INCLUDE_DIRS += -I${FREERTOS_PLUS_DIR}/VisualStudio_StaticProjects/MbedTLS

# FreeRTOS mbedtls port sources
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/VisualStudio_StaticProjects/MbedTLS/mbedtls_freertos_port.c

# coreMQTT headers
INCLUDE_DIRS += -I${COREMQTT}/source/include
INCLUDE_DIRS += -I${COREMQTT}/source/interface

# coreMQTT sources 
SOURCE_FILES += $(COREMQTT)/source/core_mqtt_serializer.c
SOURCE_FILES += $(COREMQTT)/source/core_mqtt_state.c
SOURCE_FILES += $(COREMQTT)/source/core_mqtt.c

# Misc. utilities headers
INCLUDE_DIRS += -I${UTILITIES}/logging
INCLUDE_DIRS += -I${UTILITIES}/backoff_algorithm/source/include

# Misc. utilities sources
SOURCE_FILES += $(UTILITIES)/backoff_algorithm/source/backoff_algorithm.c

# networking specific cflags
CFLAGS := -DmainCREATE_NETWORKING_DEMO_ONLY=1
CFLAGS += -DmainCREATE_MQTT_TASKS_SINGLE=1

DEFINES := -DprojCOVERAGE_TEST -DQEMU_SOC_MPS2 -DHEAP3 -DMBEDTLS_CONFIG_FILE=\"demo_mbedtls_config.h\"

LDFLAGS = -T ./mps2_m3.ld -specs=nano.specs --specs=rdimon.specs -lc -lrdimon
LDFLAGS += -Xlinker -Map=${BUILD_DIR}/output.map

CFLAGS += -nostartfiles -mthumb -mcpu=cortex-m3 -Wno-error=implicit-function-declaration
CFLAGS += -Wno-builtin-declaration-mismatch -Werror

ifeq ($(DEBUG), 1)
    CFLAGS += -ggdb3 -Og
else
    CFLAGS += -O3
endif
    CFLAGS += -fstrict-aliasing -Wstrict-aliasing -Wno-error=address-of-packed-member

OBJ_FILES := $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.o)

CPPFLAGS += $(DEFINES)
CFLAGS += $(INCLUDE_DIRS)

.PHONY: clean

$(BUILD_DIR)/$(BIN) : $(OBJ_FILES)
	$(CC) -ffunction-sections -fdata-sections $(CFLAGS) $(LDFLAGS) $+ -o $(@)

%.d: %.c
	@set -e; rm -f $@; \
	$(CC) -M $(CPPFLAGS) $< > $@.$$$$; \
	sed 's,\($*\)\.o[ :]*,\1.o $@ : ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$

INCLUDES := $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.d)
-include $(INCLUDES)

${BUILD_DIR}/%.o : %.c Makefile
	-mkdir -p $(@D)
	$(CC)  $(CPPFLAGS) $(CFLAGS) -MMD -c $< -o $@

clean:
	-rm -rf build
