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
     * Bug 293:
     *
     * SUMMARY: Incorrect zero-length Buffer to String conversion
     */
    Method (M293, 0, NotSerialized)
    {
        /* Prepare zero-length Buffer */

        Local0 = 0x00
        Local1 = Buffer (Local0){}
        Local2 = ToHexString (Local1)
        Debug = Local2
        Debug = SizeOf (Local2)
        Local3 = ToDecimalString (Local1)
        Debug = Local3
        Debug = SizeOf (Local3)
        If ((SizeOf (Local2) != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, SizeOf (Local2), 0x00)
        }

        If ((SizeOf (Local3) != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, SizeOf (Local3), 0x00)
        }

        If (("" != Local1))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "", Local1)
        }

        If (("" != Local2))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "", Local2)
        }

        If (("" != Local3))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "", Local3)
        }

        If ((Local2 != Local3))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local2, Local3)
        }

        If ((Local2 != Local1))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local2, Local1)
        }

        If ((Local3 != Local1))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local3, Local1)
        }
    }
