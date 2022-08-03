CC = arm-none-eabi-gcc
BIN := RTOSDemo.axf

BUILD_DIR := build

FREERTOS_DIR_REL := ../../../FreeRTOS
FREERTOS_DIR := $(abspath $(FREERTOS_DIR_REL))
KERNEL_DIR := $(FREERTOS_DIR)/Source

FREERTOS_PLUS_DIR_REL := ../../../FreeRTOS-Plus
FREERTOS_PLUS_DIR := $(abspath $(FREERTOS_PLUS_DIR_REL))

SOURCE_FILES += init/startup.c  syscall.c main.c
SOURCE_FILES += $(KERNEL_DIR)/portable/GCC/ARM_CM3/port.c
SOURCE_FILES += $(KERNEL_DIR)/tasks.c
SOURCE_FILES += $(KERNEL_DIR)/list.c
SOURCE_FILES += $(KERNEL_DIR)/queue.c
SOURCE_FILES += $(KERNEL_DIR)/timers.c
SOURCE_FILES += $(KERNEL_DIR)/event_groups.c
SOURCE_FILES += ${KERNEL_DIR}/portable/MemMang/heap_3.c

INCLUDE_DIRS += -I$(FREERTOS_PLUS_DIR)/Demo/MQTT_Mutual_Auth_Qemu_mps2
INCLUDE_DIRS += -I$(FREERTOS_PLUS_DIR)/Demo/MQTT_Mutual_Auth_Qemu_mps2/CMSIS
INCLUDE_DIRS += -I$(KERNEL_DIR)/include
INCLUDE_DIRS += -I$(KERNEL_DIR)/portable/GCC/ARM_CM3
INCLUDE_DIRS += -I.

FREERTOS_TCP = ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP
MBED_TLS = ${FREERTOS_PLUS_DIR}/ThirdParty/mbedtls
MBED_TLS_UTIL = ${FREERTOS_PLUS_DIR}/Source/Application-Protocols/network_transport
COREMQTT = ${FREERTOS_PLUS_DIR}/Source/Application-Protocols/coreMQTT
UTILITIES = ${FREERTOS_PLUS_DIR}/Source/Utilities

# FreeRTOS networking header directories
INCLUDE_DIRS += -I${FREERTOS_TCP}/include
INCLUDE_DIRS += -I${FREERTOS_TCP}/portable/Compiler/GCC


# mbedTLS header directories
INCLUDE_DIRS += -I${MBED_TLS_UTIL}/using_mbedtls
INCLUDE_DIRS += -I${MBED_TLS_UTIL}/sockets_wrapper/freertos_plus_tcp
INCLUDE_DIRS += -I${MBED_TLS}/include
INCLUDE_DIRS += -I${MBED_TLS}/library
INCLUDE_DIRS += -I${UTILITIES}/mbedtls_freertos 


# coreMQTT header directories 
INCLUDE_DIRS += -I${COREMQTT}/source/include
INCLUDE_DIRS += -I${COREMQTT}/source/interface
INCLUDE_DIRS += -I${UTILITIES}/backoff_algorithm/source/include
INCLUDE_DIRS += -I${UTILITIES}/logging



# FreeRTOS networking sources
SOURCE_FILES +=  main_networking.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_DNS.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_DHCP.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_ARP.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_TCP_WIN.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_Stream_Buffer.c
SOURCE_FILES += ${FREERTOS_TCP}/portable/BufferManagement/BufferAllocation_2.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_IP.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_TCP_IP.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_UDP_IP.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_Sockets.c
SOURCE_FILES += ${FREERTOS_TCP}/portable/NetworkInterface/MPS2_AN385/NetworkInterface.c
SOURCE_FILES += ${FREERTOS_TCP}/portable/NetworkInterface/MPS2_AN385/ether_lan9118/smsc9220_eth_drv.c
SOURCE_FILES += DemoTasks/MutualAuthMQTTExample.c


# mbedTLS sources
SOURCE_FILES += mbedtls_freertos_port.c 
SOURCE_FILES += ${UTILITIES}/mbedtls_freertos/mbedtls_bio_freertos_plus_tcp.c
SOURCE_FILES += ${MBED_TLS_UTIL}/using_mbedtls/using_mbedtls.c
SOURCE_FILES += ${MBED_TLS_UTIL}/sockets_wrapper/freertos_plus_tcp/sockets_wrapper.c
SOURCE_FILES += ${MBED_TLS}/library/threading.c 
SOURCE_FILES += ${MBED_TLS}/library/aes.c 
SOURCE_FILES += ${MBED_TLS}/library/aesni.c
SOURCE_FILES += ${MBED_TLS}/library/arc4.c
SOURCE_FILES += ${MBED_TLS}/library/aria.c
SOURCE_FILES += ${MBED_TLS}/library/asn1parse.c 
SOURCE_FILES += ${MBED_TLS}/library/asn1write.c 
SOURCE_FILES += ${MBED_TLS}/library/base64.c 
SOURCE_FILES += ${MBED_TLS}/library/bignum.c 
SOURCE_FILES += ${MBED_TLS}/library/blowfish.c
SOURCE_FILES += ${MBED_TLS}/library/camellia.c
SOURCE_FILES += ${MBED_TLS}/library/ccm.c
SOURCE_FILES += ${MBED_TLS}/library/certs.c
SOURCE_FILES += ${MBED_TLS}/library/chacha20.c 
SOURCE_FILES += ${MBED_TLS}/library/chachapoly.c
SOURCE_FILES += ${MBED_TLS}/library/cipher_wrap.c
SOURCE_FILES += ${MBED_TLS}/library/cipher.c 
SOURCE_FILES += ${MBED_TLS}/library/cmac.c 
SOURCE_FILES += ${MBED_TLS}/library/constant_time.c
SOURCE_FILES += ${MBED_TLS}/library/ctr_drbg.c 
SOURCE_FILES += ${MBED_TLS}/library/debug.c 
SOURCE_FILES += ${MBED_TLS}/library/des.c 
SOURCE_FILES += ${MBED_TLS}/library/dhm.c 
SOURCE_FILES += ${MBED_TLS}/library/ecdh.c 
SOURCE_FILES += ${MBED_TLS}/library/ecdsa.c 
SOURCE_FILES += ${MBED_TLS}/library/ecjpake.c
SOURCE_FILES += ${MBED_TLS}/library/ecp_curves.c 
SOURCE_FILES += ${MBED_TLS}/library/ecp.c 
SOURCE_FILES += ${MBED_TLS}/library/entropy_poll.c
SOURCE_FILES += ${MBED_TLS}/library/entropy.c 
SOURCE_FILES += ${MBED_TLS}/library/error.c 
SOURCE_FILES += ${MBED_TLS}/library/gcm.c 
SOURCE_FILES += ${MBED_TLS}/library/havege.c
SOURCE_FILES += ${MBED_TLS}/library/hkdf.c 
SOURCE_FILES += ${MBED_TLS}/library/hmac_drbg.c 
SOURCE_FILES += ${MBED_TLS}/library/md.c 
SOURCE_FILES += ${MBED_TLS}/library/md2.c
SOURCE_FILES += ${MBED_TLS}/library/md4.c 
SOURCE_FILES += ${MBED_TLS}/library/md5.c 
SOURCE_FILES += ${MBED_TLS}/library/memory_buffer_alloc.c
SOURCE_FILES += ${MBED_TLS}/library/net_sockets.c
SOURCE_FILES += ${MBED_TLS}/library/nist_kw.c
SOURCE_FILES += ${MBED_TLS}/library/oid.c 
SOURCE_FILES += ${MBED_TLS}/library/padlock.c
SOURCE_FILES += ${MBED_TLS}/library/pem.c 
SOURCE_FILES += ${MBED_TLS}/library/pk_wrap.c
SOURCE_FILES += ${MBED_TLS}/library/pk.c 
SOURCE_FILES += ${MBED_TLS}/library/pkcs5.c 
SOURCE_FILES += ${MBED_TLS}/library/pkcs11.c 
SOURCE_FILES += ${MBED_TLS}/library/pkcs12.c 
SOURCE_FILES += ${MBED_TLS}/library/pkparse.c 
SOURCE_FILES += ${MBED_TLS}/library/pkwrite.c 
SOURCE_FILES += ${MBED_TLS}/library/platform_util.c 
SOURCE_FILES += ${MBED_TLS}/library/platform.c 
SOURCE_FILES += ${MBED_TLS}/library/poly1305.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto_aead.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto_cipher.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto_client.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto_driver_wrappers.c
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto_ecp.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto_hash.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto_mac.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto_rsa.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto_se.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto_storage.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_crypto.c 
SOURCE_FILES += ${MBED_TLS}/library/psa_its_file.c 
SOURCE_FILES += ${MBED_TLS}/library/ripemd160.c 
SOURCE_FILES += ${MBED_TLS}/library/rsa_internal.c 
SOURCE_FILES += ${MBED_TLS}/library/rsa.c 
SOURCE_FILES += ${MBED_TLS}/library/sha1.c 
SOURCE_FILES += ${MBED_TLS}/library/sha256.c 
SOURCE_FILES += ${MBED_TLS}/library/sha512.c
SOURCE_FILES += ${MBED_TLS}/library/ssl_cache.c 
SOURCE_FILES += ${MBED_TLS}/library/ssl_ciphersuites.c 
SOURCE_FILES += ${MBED_TLS}/library/ssl_cli.c 
SOURCE_FILES += ${MBED_TLS}/library/ssl_cookie.c 
SOURCE_FILES += ${MBED_TLS}/library/ssl_tls.c 
SOURCE_FILES += ${MBED_TLS}/library/ssl_msg.c
SOURCE_FILES += ${MBED_TLS}/library/ssl_srv.c 
SOURCE_FILES += ${MBED_TLS}/library/ssl_ticket.c 
SOURCE_FILES += ${MBED_TLS}/library/ssl_tls13_keys.c
SOURCE_FILES += ${MBED_TLS}/library/timing.c 
SOURCE_FILES += ${MBED_TLS}/library/version_features.c 
SOURCE_FILES += ${MBED_TLS}/library/version.c 
SOURCE_FILES += ${MBED_TLS}/library/x509_create.c 
SOURCE_FILES += ${MBED_TLS}/library/x509_crl.c 
SOURCE_FILES += ${MBED_TLS}/library/x509_crt.c 
SOURCE_FILES += ${MBED_TLS}/library/x509_csr.c 
SOURCE_FILES += ${MBED_TLS}/library/x509.c 
SOURCE_FILES += ${MBED_TLS}/library/x509write_crt.c 
SOURCE_FILES += ${MBED_TLS}/library/x509write_csr.c 
SOURCE_FILES += ${MBED_TLS}/library/xtea.c 


# coreMQTT sources 
SOURCE_FILES += $(COREMQTT)/source/core_mqtt_serializer.c
SOURCE_FILES += $(COREMQTT)/source/core_mqtt_state.c
SOURCE_FILES += $(COREMQTT)/source/core_mqtt.c 
SOURCE_FILES += $(UTILITIES)/backoff_algorithm/source/backoff_algorithm.c


# networking specific cflags
CFLAGS := -DmainCREATE_NETWORKING_DEMO_ONLY=1
CFLAGS += -DmainCREATE_MQTT_TASKS_SINGLE=1

DEFINES := -DprojCOVERAGE_TEST -DQEMU_SOC_MPS2 -DHEAP3 -DMBEDTLS_CONFIG_FILE=\"mbedtls_config.h\"

LDFLAGS = -T ./scripts/mps2_m3.ld -specs=nano.specs --specs=rdimon.specs -lc -lrdimon
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