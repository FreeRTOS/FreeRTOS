/* config.h
 *
 * Copyright (C) 2006-2013 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#define __CORTEX_M3__
#define CYASSL_MDK_ARM
#define CYASSL_MDK5
#define CYASSL_CMSIS_RTOS

#define NO_WRITEV
#define NO_CYASSL_DIR
#define BENCH_EMBEDDED

#define CYASSL_DER_LOAD
#define HAVE_NULL_CIPHER
#define NO_MAIN_DRIVER

#if  defined(MDK_CONF_CYASSL)
#define CYASSL_MDK_SHELL
#include "config-Crypt.h"
#include "config-CyaSSL.h"
#elif  defined(MDK_CONF_SimpleClient)
#include "config-Crypt.h"
#include "config-CyaSSL.h"
#elif  defined(MDK_CONF_SimpleServer)
#include "config-Crypt.h"
#include "config-CyaSSL.h"
#elif  defined(MDK_CONF_EchoClient)
#include "config-Crypt.h"
#include "config-CyaSSL.h"
#elif  defined(MDK_CONF_EchoServer)
#include "config-Crypt.h"
#include "config-CyaSSL.h"
#elif  defined(MDK_CONF_Benchmark)
#define SINGLE_THREADED
#define NO_INLINE
#include "config-Crypt.h"
#elif  defined(MDK_CONF_CryptTest)
#define SINGLE_THREADED
#define NO_INLINE
#include "config-Crypt.h"

#endif


