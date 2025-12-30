    /*
     * Some or all of this work - Copyright (c) 2006 - 2021, Intel Corp.
     * All rights reserved.
     *
     * Redistribution and use in source and binary forms, with or without modification,
     * are permitted provided that the following conditions are met:
     *
     * Redistributions of source code must retain the above copyright notice,
     * this list of conditions and the following disclaimer.
     * Redistributions in binary form must reproduce the above copyright notice,
     * this list of conditions and the following disclaimer in the documentation
     * and/or other materials provided with the distribution.
     * Neither the name of Intel Corporation nor the names of its contributors
     * may be used to endorse or promote products derived from this software
     * without specific prior written permission.
     *
     * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
     * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
     * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
     * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
     * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
     * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
     * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
     * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
     * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
     * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
     */
    /*
     * Data type conversion and manipulation
     */
    /* Convert String to UUID Macro */
    Name (P356, Package (0x02)
    {
        Buffer (0x10)
        {
            /* 0000 */  0x3D, 0x2C, 0x1B, 0x0A, 0x5F, 0x4E, 0x71, 0x60,  // =,.._Nq`
            /* 0008 */  0x82, 0x93, 0xA4, 0xB5, 0xC6, 0xD7, 0xE8, 0xF9   // ........
        },

        Buffer (0x10)
        {
            /* 0000 */  0xD3, 0xC2, 0xB1, 0xA0, 0xF5, 0xE4, 0x17, 0x06,  // ........
            /* 0008 */  0x28, 0x39, 0x4A, 0x5B, 0x6C, 0x7D, 0x8E, 0x9F   // (9J[l}..
        }
    })
    Name (P357, Package (0x02)
    {
        Buffer (0x10)
        {
            /* 0000 */  0x3D, 0x2C, 0x1B, 0x0A, 0x5F, 0x4E, 0x71, 0x60,  // =,.._Nq`
            /* 0008 */  0x82, 0x93, 0xA4, 0xB5, 0xC6, 0xD7, 0xE8, 0xF9   // ........
        },

        Buffer (0x10)
        {
            /* 0000 */  0xD3, 0xC2, 0xB1, 0xA0, 0xF5, 0xE4, 0x17, 0x06,  // ........
            /* 0008 */  0x28, 0x39, 0x4A, 0x5B, 0x6C, 0x7D, 0x8E, 0x9F   // (9J[l}..
        }
    })
    /* Run-method */

    Method (TOU0, 0, Serialized)
    {
        Debug = "TEST: TOU0, Convert String to UUID Macro"
        M302 (__METHOD__, 0x02, "p356", P356, P357, 0x07)
    }
