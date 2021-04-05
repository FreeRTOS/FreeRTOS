/*
 * Copyright (C) 2016 YunOS Project. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <csi_config.h>
#include "mm.h"
#include "umm_heap.h"
#include <stdio.h>

int32_t mm_get_mallinfo(int32_t *total, int32_t *used, int32_t *free, int32_t *peak)
{
    struct mallinfo info;
    mm_mallinfo(USR_HEAP, &info);
	*total = info.arena;
	*used = info.uordblks;
	*free = info.fordblks;
#if (CONFIG_MM_MAX_USED)
	*peak = mm_get_max_usedsize();
#endif
    return 0;
}


