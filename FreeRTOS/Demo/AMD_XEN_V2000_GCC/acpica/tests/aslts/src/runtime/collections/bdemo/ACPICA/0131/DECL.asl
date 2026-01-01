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
     * Bug 131:
     *
     * SUMMARY: Store to the Index reference immediately returned by Method doesn't work
     */
    Method (M126, 0, Serialized)
    {
        Name (P000, Package (0x08)
        {
            0x01,
            0x02,
            0x03,
            0x04,
            0x05,
            0x06,
            0x07,
            0x08
        })
        Method (M002, 0, NotSerialized)
        {
            Debug = "m002 started"
            Return (P000 [0x01])
        }

        Method (M003, 0, NotSerialized)
        {
            Debug = "m003 started"
            Store (P000 [0x01], Local0)
            Return (Local0)
        }

        Method (M004, 1, NotSerialized)
        {
            Debug = "m004 started"
            Store (P000 [Arg0], Local0)
            Return (Local0)
        }

        Method (M005, 0, NotSerialized)
        {
            P000 [0x00] = 0xABCD0001
            Local0 = DerefOf (P000 [0x00])
            If ((Local0 != 0xABCD0001))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCD0001)
            }
                /*
         // Removed 09/2015
         Store to method invocation is not supported
         Store(0xabcd0004, m002())
         Store(DerefOf(Index(p000, 1)), Local0)
         if (LNotEqual(Local0, 0xabcd0004)) {
         err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0004)
         }
         Store(0xabcd0005, m003())
         Store(DerefOf(Index(p000, 1)), Local0)
         if (LNotEqual(Local0, 0xabcd0005)) {
         err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0005)
         }
         Store(0xabcd0006, m004(1))
         Store(DerefOf(Index(p000, 1)), Local0)
         if (LNotEqual(Local0, 0xabcd0006)) {
         err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0006)
         }
         */
        }

        M005 ()
    }
