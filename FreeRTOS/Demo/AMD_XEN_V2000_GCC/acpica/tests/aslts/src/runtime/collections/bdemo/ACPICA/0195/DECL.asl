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
     * Bug 195 (local-bugzilla-353):
     *
     * SUMMARY: Increment and Decrement of String or Buffer changes the type of operand
     *
     * Increment and Decrement of either String or Buffer Object
     * unexpectedly change the type of operand (Addend and Minuend
     * respectively) to Integer. Operands should preserve the initial
     * types.
     *
     * By the way, the relevant "equivalent" operations
     * Add(Addend, 1, Addend) and Subtract(Minuend, 1, Minuend)
     * don't change the type of Addend and Minuend respectively.
     */
    Method (MFAF, 0, Serialized)
    {
        Name (S000, "0321")
        Name (S001, "0321")
        Name (B000, Buffer (0x03)
        {
             0x21, 0x03, 0x00                                 // !..
        })
        Name (B001, Buffer (0x03)
        {
             0x21, 0x03, 0x00                                 // !..
        })
        S000--
        S001 -= 0x01
        Debug = "======== :"
        Debug = S000 /* \MFAF.S000 */
        Debug = S001 /* \MFAF.S001 */
        Debug = "========."
        Local0 = ObjectType (S000)
        Local1 = ObjectType (S001)
        If ((Local0 != Local1))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Local1)
        }
        ElseIf ((S000 != S001))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, S000, S001)
        }

        If ((Local0 != 0x02))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x02)
        }

        If ((Local1 != 0x02))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0x02)
        }

        B000++
        B001 += 0x01
        Debug = "======== :"
        Debug = B000 /* \MFAF.B000 */
        Debug = B001 /* \MFAF.B001 */
        Debug = "========."
        Local0 = ObjectType (B000)
        Local1 = ObjectType (B001)
        If ((Local0 != Local1))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Local1)
        }
        ElseIf ((B000 != B001))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, B000, B001)
        }

        If ((Local0 != 0x03))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x03)
        }

        If ((Local1 != 0x03))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0x03)
        }
    }
