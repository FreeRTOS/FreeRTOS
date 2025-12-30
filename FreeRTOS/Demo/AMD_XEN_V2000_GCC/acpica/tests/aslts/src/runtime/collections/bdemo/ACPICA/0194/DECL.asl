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
     * Bug 194:
     *
     * SUMMARY: Incorrect length of result of ToBuffer in case it is stored into a Named Buffer
     */
    Method (BCMP, 2, NotSerialized)
    {
        Local0 = SizeOf (Arg0)
        Local1 = SizeOf (Arg1)
        If ((Local0 > Local1))
        {
            Local0 = Local1
        }

        While (Local0)
        {
            Local0--
            Debug = Local0
            Local1 = DerefOf (Arg0 [Local0])
            Local2 = DerefOf (Arg1 [Local0])
            If ((Local1 != Local2))
            {
                Return (0x00)
            }
        }

        Return (0x01)
    }

    Method (MFA7, 1, Serialized)
    {
        Name (B000, Buffer (0x01)
        {
             0x3C                                             // <
        })
        Name (B001, Buffer (0x03)
        {
             0x01, 0x02, 0x03                                 // ...
        })
        Name (BB00, Buffer (0x01)
        {
             0x3C                                             // <
        })
        Name (BB01, Buffer (0x03)
        {
             0x01, 0x02, 0x03                                 // ...
        })
        If (Arg0)
        {
            Debug = "ToBuffer(b001, b000)"
            ToBuffer (B001, B000) /* \MFA7.B000 */
            If (!BCMP (B000, BB01))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, B000, BB01)
            }
        }
        Else
        {
            Debug = "ToBuffer(b000, b001)"
            ToBuffer (B000, B001) /* \MFA7.B001 */
            If (!BCMP (B001, BB00))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, B001, BB00)
            }
        }
    }

    Method (MFA8, 0, NotSerialized)
    {
        MFA7 (0x00)
        MFA7 (0x01)
    }
