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
    Name (Z066, 0x42)
    /* Verify result */
    /* */
    /* arg0 - name of test */
    /* arg1 - results Package */
    /* arg2 - index of four results */
    /* arg3 - indication of Result */
    /* arg4 - indication of ComputationalData */
    /* arg5 - Result */
    /* arg6 - ComputationalData */
    Method (M4C1, 7, Serialized)
    {
        Name (TMP0, 0x00)
        Name (TMP1, 0x00)
        Name (LPC0, 0x00)
        LPC0 = (Arg2 * 0x04)
        If (Arg3)
        {
            /* Result */
            /* Benchmark of Result */
            Local0 = DerefOf (Arg1 [LPC0])
            LPC0++
            Local1 = DerefOf (Arg1 [LPC0])
            TMP0 = ObjectType (Arg5)
            If (F64)
            {
                TMP1 = ObjectType (Local0)
                If ((TMP0 != TMP1))
                {
                    ERR (Arg0, Z066, __LINE__, 0x00, 0x00, TMP0, TMP1)
                }
                ElseIf ((Arg5 != Local0))
                {
                    ERR (Arg0, Z066, __LINE__, 0x00, 0x00, Arg5, Local0)
                }
            }
            Else
            {
                TMP1 = ObjectType (Local1)
                If ((TMP0 != TMP1))
                {
                    ERR (Arg0, Z066, __LINE__, 0x00, 0x00, TMP0, TMP1)
                }
                ElseIf ((Arg5 != Local1))
                {
                    ERR (Arg0, Z066, __LINE__, 0x00, 0x00, Arg5, Local1)
                }
            }
        }
        Else
        {
            LPC0++
        }

        If (Arg4)
        {
            /* ComputationalData */
            /* Benchmark of ComputationalData */
            LPC0++
            Local2 = DerefOf (Arg1 [LPC0])
            LPC0++
            Local3 = DerefOf (Arg1 [LPC0])
            TMP0 = ObjectType (Arg6)
            If (F64)
            {
                TMP1 = ObjectType (Local2)
                If ((TMP0 != TMP1))
                {
                    ERR (Arg0, Z066, __LINE__, 0x00, 0x00, TMP0, TMP1)
                }
                ElseIf ((Arg6 != Local2))
                {
                    ERR (Arg0, Z066, __LINE__, 0x00, 0x00, Arg6, Local2)
                }
            }
            Else
            {
                TMP1 = ObjectType (Local3)
                If ((TMP0 != TMP1))
                {
                    ERR (Arg0, Z066, __LINE__, 0x00, 0x00, TMP0, TMP1)
                }
                ElseIf ((Arg6 != Local3))
                {
                    ERR (Arg0, Z066, __LINE__, 0x00, 0x00, Arg6, Local3)
                }
            }
        }
    }
