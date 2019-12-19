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
#ifndef _BSS_H_
#define _BSS_H_

.macro  csky_bss_init sadr eadr
    /*Zero out the bss region.
     * NOTE: __sbss and __ebss must align 4
     */
    lrw     r7, \sadr       /* Get start of bss from linking script file */
    lrw     r6, \eadr       /* Get end of bss from linking script file */
    subu    r6, r7           /* Calculate size of bss */
    lsri    r6, r6, 2        /* Size of whole words */
    cmpnei  r6, 0
    bf      .L_bss_init_end
    movi    r5, 0            /* Set zero value to write */

.L_bss_init_loop:
    stw     r5, (r7)         /* Zero next word */
    addi    r7, 4            /* Increase bss pointer */
    subi    r6, 1            /* Decrease counter */
    cmpnei  r6, 0
    bt      .L_bss_init_loop  /* Repeat for all bss */

.L_bss_init_end:

.endm

#endif
