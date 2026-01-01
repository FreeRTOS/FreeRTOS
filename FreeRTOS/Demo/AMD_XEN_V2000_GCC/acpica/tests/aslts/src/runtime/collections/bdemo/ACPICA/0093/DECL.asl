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
     * Bug 0093:
     *
     * SUMMARY: Invalid result of Index operator passed with the immediate image of Buffer
     */
    Method (ME42, 1, Serialized)
    {
        Name (B000, Buffer (0x08)
        {
             0x0B, 0x16, 0x21, 0x2C, 0x37, 0x42, 0x4D, 0x58   // ..!,7BMX
        })
        If ((Arg0 == 0x00))
        {
            Debug = "Buffer as a named object:"
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = DerefOf (B000 [0x05])
            If ((Local0 != 0x42))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x42)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }
        ElseIf ((Arg0 == 0x01))
        {
            Debug = "The same Buffer but substituted immediately:"
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Store (Index (Buffer (0x08)
                    {
                         0x0B, 0x16, 0x21, 0x2C, 0x37, 0x42, 0x4D, 0x58   // ..!,7BMX
                    }, 0x05), Local1)
            If (Y900)
            {
                Local0 = DerefOf (Local1)
                If ((Local0 != 0x42))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x42)
                }

                CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            }
            Else
            {
                CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }
        }
        Else
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = DerefOf (Index (Buffer (0x08)
                        {
                             0x0B, 0x16, 0x21, 0x2C, 0x37, 0x42, 0x4D, 0x58   // ..!,7BMX
                        }, 0x05))
            If (Y900)
            {
                If ((Local0 != 0x42))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x42)
                }

                CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            }
            Else
            {
                CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }
        }
    }

    Method (ME43, 0, NotSerialized)
    {
        /* 0,1 - success,   2 - crash */

        ME42 (0x00)
        ME42 (0x01)
        ME42 (0x02)
        Return (0x00)
    }
