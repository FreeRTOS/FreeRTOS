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
     * Bug 193 (local-bugzilla-354):
     *
     * SUMMARY: storing opt. results of Not/NAnd/NOr into Buffer Field in 32-bit mode can soil the higher bits of BF
     *
     * In 32-bit mode optional storing of the result of any of
     * Not, NAnd, and NOr ASL operators to Buffer Field of more
     * than 4 bytes in length can produce non-zero bits outside
     * the first 32 bits (though zeros are expected):
     */
    Method (MFA5, 1, Serialized)
    {
        /* Source Named Object */

        Name (SRC0, 0xFEDCBA9876543210)
        /* Target Buffer Field Object */

        CreateField (BD0F, 0x00, 0x45, BFL1)
        /* Explicit storing */

        BFL1 = 0x00
        If ((Arg0 == 0x00))
        {
            Store (~SRC0, BFL1) /* \MFA5.BFL1 */
        }
        ElseIf ((Arg0 == 0x01))
        {
            BFL1 = NAnd (SRC0, Ones)
        }
        ElseIf ((Arg0 == 0x02))
        {
            BFL1 = NOr (SRC0, Zero)
        }

        If ((BFL1 == BD10))
        {
            Debug = "Ok 1"
        }
        Else
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BFL1, BD10)
        }

        /* Optional storing */

        BFL1 = 0x00
        If ((Arg0 == 0x00))
        {
            BFL1 = ~SRC0 /* \MFA5.SRC0 */
        }
        ElseIf ((Arg0 == 0x01))
        {
            NAnd (SRC0, Ones, BFL1) /* \MFA5.BFL1 */
        }
        ElseIf ((Arg0 == 0x02))
        {
            NOr (SRC0, Zero, BFL1) /* \MFA5.BFL1 */
        }

        If ((BFL1 == BD10))
        {
            Debug = "Ok 2"
        }
        Else
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BFL1, BD10)
        }
    }

    Method (MFA6, 0, NotSerialized)
    {
        Store (~0xFEDCBA9876543210, BD10) /* \BD10 */
        Debug = "Not operator"
        MFA5 (0x00)
        Debug = "NAnd operator"
        MFA5 (0x01)
        Debug = "NOr operator"
        MFA5 (0x01)
    }
