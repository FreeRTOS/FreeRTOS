/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
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
#ifndef _CKLDDATA_H_
#define _CKLDDATA_H_


.macro csky_load_data saddr eaddr eeaddr
    lrw     a3, \saddr      /* Get start of data from linking script file */
    lrw     a1, \eaddr      /* Get end of data from linking script file */
    cmphs   a3, a1          /* Calculate size of data */
    lrw     a2, \eeaddr     /* Get end of rodata from linking script file */
.L_load_data:
    ld.w    a0, (a2, 0)     /* Load data from flash */
    st.w    a0, (a3, 0)     /* Store data to SSRAM */
    addi    a3, 4           /* Increase data pointer of flash */
    addi    a2, 4           /* Increase data pointer of SSRAM */
    cmphs   a3, a1
    bf      .L_load_data    /* Repeat for all data */

.endm

#endif
