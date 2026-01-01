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
     * Bug 0044:
     *
     * SUMMARY: The ToUUID Macro loses the high hex-digit of each byte
     */
    Method (MDD5, 0, NotSerialized)
    {
        Local0 = Buffer (0x10)
            {
                /* 0000 */  0x3D, 0x2C, 0x1B, 0x0A, 0x5F, 0x4E, 0x71, 0x60,  // =,.._Nq`
                /* 0008 */  0x82, 0x93, 0xA4, 0xB5, 0xC6, 0xD7, 0xE8, 0xF9   // ........
            }
        Local1 = Buffer (0x10)
            {
                /* 0000 */  0x3D, 0x2C, 0x1B, 0x0A, 0x5F, 0x4E, 0x71, 0x60,  // =,.._Nq`
                /* 0008 */  0x82, 0x93, 0xA4, 0xB5, 0xC6, 0xD7, 0xE8, 0xF9   // ........
            }
        If ((Local0 != Local1))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Local1)
        }
    }
