/*
 * FreeRTOS+FAT build 191128 - Note:  FreeRTOS+FAT is still in the lab!
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Authors include James Walmsley, Hein Tibosch and Richard Barry
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 *
 */

#ifndef PLUS_FAT_H
#define PLUS_FAT_H

#include <string.h>

#ifdef	__cplusplus
extern "C" {
#endif

#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

#include "FreeRTOSFATConfig.h"
#include "FreeRTOSFATConfigDefaults.h"
#include "ff_error.h"
#include "ff_ioman.h"
#include "ff_fat.h"
#include "ff_fatdef.h"
#include "ff_memory.h"
#include "ff_time.h"
#include "ff_crc.h"
#include "ff_file.h"
#include "ff_dir.h"
#include "ff_string.h"
#include "ff_format.h"
#include "ff_locking.h"

/* See if any older defines with a prefix "FF_" are still defined: */
#include "ff_old_config_defines.h"

#ifdef	__cplusplus
}	// extern "C"
#endif

#endif
