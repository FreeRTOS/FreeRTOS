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
     * Bug 275:
     *
     * SUMMARY: pop result from bottom principle doesn't work
     */
    Method (MC75, 0, Serialized)
    {
        Name (I000, 0x11000000)
        Name (I001, 0x00220000)
        Name (P000, Package (0x03)
        {
            0xABCD0000,
            0xABCD0001,
            0xABCD0002
        })
        Method (M000, 0, NotSerialized)
        {
            Return (P000) /* \MC75.P000 */
        }

        Method (M001, 1, NotSerialized)
        {
            Return (0xABCD0003)
        }

        Method (M002, 2, NotSerialized)
        {
            Local0 = Arg0 [0x01]
            If (CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x01))
            {
                Return (Zero)
            }

            Local1 = DerefOf (Local0)
            If (CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x01))
            {
                Return (Zero)
            }

            If ((Local1 != 0xABCD0001))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0xABCD0001)
            }

            Return (Zero)
        }

        /* ################################## How it should work */
        /* ================================== Example 0: */
        M002 (P000, 0xABCD0004)
        /* ================================== Example 1: */

        M002 (M000 (), 0xABCD0004)
        /* ================================== Example 2: */

        M002 (P000, M001 ((I000 + I001)))
        /* ################################## How it actually works: */

        M002 (M000 (), M001 ((I000 + I001)))
    }
