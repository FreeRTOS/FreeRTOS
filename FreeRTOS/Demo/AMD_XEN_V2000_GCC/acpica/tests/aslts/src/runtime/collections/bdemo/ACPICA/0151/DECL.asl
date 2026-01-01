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
     * Bug 151:
     *
     * SUMMARY: The zero-length resulting String of Mid operator passed to Concatenate operator causes crash
     *
     * Check absence of crash..
     */
    Method (MF3F, 1, Serialized)
    {
        Name (B000, Buffer (Arg0){})
        Name (B001, Buffer (0x07)
        {
             0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07         // .......
        })
        Name (B002, Buffer (0x07)
        {
             0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E         // .......
        })
        Debug = "Buffer case"
        Debug = B000 /* \MF3F.B000 */
        Debug = SizeOf (B000)
        /* 1. */

        Local1 = Concatenate (B000, B001)
        Debug = "Ok: Concatenate(<Default empty buffer>, ...)"
        Concatenate (B000, B001, Local0)
        If ((Local0 != Buffer (0x07)
                    {
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07         // .......
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x07)
                {
                     0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07         // .......
                })
        }

        /* 2. */

        Local0 = Mid (B002, 0x07, 0x01)
        Debug = Local0
        Debug = SizeOf (Local0)
        Debug = "Try: Concatenate(<Mid empty buffer result object>, ...)"
        Local1 = Concatenate (Local0, B001)
        Debug = "Ok: Concatenate(<Mid empty buffer result object>, ...)"
        Concatenate (Local0, B001, Local0)
        If ((Local0 != Buffer (0x07)
                    {
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07         // .......
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x07)
                {
                     0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07         // .......
                })
        }
    }

    Method (MF40, 0, Serialized)
    {
        Name (S000, "")
        Name (S001, "String1")
        Name (S002, "String2")
        Debug = "String case"
        Debug = S000 /* \MF40.S000 */
        Debug = SizeOf (S000)
        /* 3. */

        Local1 = Concatenate (S000, S001)
        Debug = "Ok: Concatenate(<Default empty string>, ...)"
        Concatenate (S000, S001, Local0)
        If ((Local0 != "String1"))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, "String1")
        }

        /* 4. */

        Local0 = Mid (S002, 0x07, 0x01)
        Debug = Local0
        Debug = SizeOf (Local0)
        Debug = "Try: Concatenate(<Mid empty string result object>, ...)"
        Local1 = Concatenate (Local0, S001)
        Debug = "Ok: Concatenate(<Mid empty string result object>, ...)"
        Concatenate (Local0, S001, Local0)
        If ((Local0 != "String1"))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, "String1")
        }
    }

    Method (MF41, 0, NotSerialized)
    {
        MF3F (0x00)
        MF40 ()
    }
