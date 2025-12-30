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
     * Bug 274:
     *
     * SUMMARY: Named object as element of Package is handled by ACPICA differently than by MS
     */
    Method (MC74, 0, Serialized)
    {
        Name (I000, 0xABCD0000)
        Name (I001, 0xABCD0001)
        Name (I002, 0xABCD0002)
        Name (I003, 0xABCD0003)
        Name (II00, 0x11112222)
        Name (P000, Package (0x06)
        {
            I000,
            I001,
            I002,
            "i000",
            \MC74.I003,
            0xABCD0004
        })
        Method (CHCK, 4, NotSerialized)
        {
            Local0 = DerefOf (Arg1 [Arg2])
            If ((Local0 != Arg0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, Local0)
            }
        }

        /* Choose benchmark package */

        If (SLCK)
        {
            Local2 = Package (0x06)
                {
                    "I000",
                    "I001",
                    "I002",
                    "i000",
                    "I003",
                    0xABCD0004
                }
        }
        Else
        {
            Local2 = Package (0x06)
                {
                    0xABCD0000,
                    0xABCD0001,
                    0xABCD0002,
                    "i000",
                    0xABCD0003,
                    0xABCD0004
                }
        }

        Local0 = DerefOf (P000 [0x00])
        CHCK (Local0, Local2, 0x00, 0x01)
        Local0 = DerefOf (P000 [0x01])
        CHCK (Local0, Local2, 0x01, 0x02)
        Local0 = DerefOf (P000 [0x02])
        CHCK (Local0, Local2, 0x02, 0x03)
        Local0 = DerefOf (P000 [0x03])
        CHCK (Local0, Local2, 0x03, 0x04)
        Local0 = DerefOf (P000 [0x04])
        CHCK (Local0, Local2, 0x04, 0x05)
        Local0 = DerefOf (P000 [0x05])
        CHCK (Local0, Local2, 0x05, 0x06)
    }
