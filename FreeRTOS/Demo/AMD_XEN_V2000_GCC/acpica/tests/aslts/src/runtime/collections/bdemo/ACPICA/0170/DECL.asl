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
     * Bug 170:
     *
     * SUMMARY: identical to bug 191
     *
     *          see if to rewrite it for Fields but not for BufferFields
     */
    Method (MF5C, 0, Serialized)
    {
        Name (B010, Buffer (0x04)
        {
             0x01, 0x77, 0x03, 0x04                           // .w..
        })
        CreateField (B010, 0x08, 0x08, BF90)
        Local0 = ObjectType (BF90)
        If ((Local0 != 0x0E))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0E)
        }
        Else
        {
            BF90 = 0x9999992B
            Local1 = ObjectType (BF90)
            If ((Local1 != Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
            }
            ElseIf ((BF90 != Buffer(){0x2B}))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF90, Buffer(){0x2B})
            }
        }
    }
