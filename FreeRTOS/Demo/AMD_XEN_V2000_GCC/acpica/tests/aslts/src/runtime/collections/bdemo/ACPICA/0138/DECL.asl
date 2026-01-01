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
     * Bug 138:
     *
     * SUMMARY: 8 bytes but not 4 expected ones are written to BufferField in 32-bit mode
     *
     * ROOT CAUSE
     */
    Method (MF29, 0, Serialized)
    {
        Name (B000, Buffer (0x0C){})
        CreateField (B000, 0x00, 0x48, BF00)
        BF00 = 0xFEDCBA9876543210
        If ((BF00 != Buffer (0x09)
                    {
                        /* 0000 */  0x10, 0x32, 0x54, 0x76, 0x00, 0x00, 0x00, 0x00,  // .2Tv....
                        /* 0008 */  0x00                                             // .
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF00, Buffer (0x09)
                {
                    /* 0000 */  0x10, 0x32, 0x54, 0x76, 0x00, 0x00, 0x00, 0x00,  // .2Tv....
                    /* 0008 */  0x00                                             // .
                })
        }
    }
