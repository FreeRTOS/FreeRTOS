/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited. All rights reserved.
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



#ifndef _PRIV_STDINT_H_
#define _PRIV_STDINT_H_
#ifdef __cplusplus
extern "C" {
#endif


/* For newlib and minilibc utint32_t are not same */
#undef _UINT32_T_DECLARED
#define _UINT32_T_DECLARED
typedef unsigned int uint32_t;

#undef _INT32_T_DECLARED
#define _INT32_T_DECLARED
typedef signed int int32_t;

#include_next <sys/_stdint.h>

#ifdef __cplusplus
}
#endif

#endif
