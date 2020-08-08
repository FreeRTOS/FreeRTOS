/* esp32_util.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */
#include <wolfssl/wolfcrypt/settings.h>

#if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
  (!defined(NO_AES)        || !defined(NO_SHA) || !defined(NO_SHA256) ||\
   defined(WOLFSSL_SHA384) || defined(WOLFSSL_SHA512))

#include <wolfssl/wolfcrypt/wc_port.h>
#include <wolfssl/wolfcrypt/error-crypt.h>

int esp_CryptHwMutexInit(wolfSSL_Mutex* mutex) {
    return wc_InitMutex(mutex);
}

int esp_CryptHwMutexLock(wolfSSL_Mutex* mutex, TickType_t xBlockTime) {
#ifdef SINGLE_THREADED
    return wc_LockMutex(mutex);
#else
    return ((xSemaphoreTake( *mutex, xBlockTime ) == pdTRUE) ? 0 : BAD_MUTEX_E);
#endif
}

int esp_CryptHwMutexUnLock(wolfSSL_Mutex* mutex) {
    return wc_UnLockMutex(mutex);
}

#endif

#ifdef WOLFSSL_ESP32WROOM32_CRYPT_DEBUG

#include "esp_timer.h"
#include "esp_log.h"

static uint64_t startTime = 0;


void wc_esp32TimerStart()
{
    startTime = esp_timer_get_time();
}

uint64_t  wc_esp32elapsedTime()
{
    /* return elapsed time since wc_esp32AesTimeStart() is called in us */
    return esp_timer_get_time() - startTime;
}

#endif /*WOLFSSL_ESP32WROOM32_CRYPT_DEBUG */
