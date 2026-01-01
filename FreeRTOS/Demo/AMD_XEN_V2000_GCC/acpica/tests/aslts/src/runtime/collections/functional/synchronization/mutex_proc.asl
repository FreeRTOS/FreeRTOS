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
     * Auxiliary routines to access mutexes
     */
    Name (Z151, 0x97)
    /*
     * For debugging:
     *
     * FL02 - print out Acquire/Release
     * im00 - imitation of Acquire/Release (don't really run Acquire/Release)
     */
    Name (FL02, 0x00)
    Name (IM00, 0x00)
    /*
     * Acquire interval of mutexes
     *
     * arg0 - number of mutexes to Acquire (use not less than 1)
     */
    Method (M36D, 1, Serialized)
    {
        If ((Arg0 == 0x00))
        {
            Return (Zero)
        }

        Local0 = Acquire (T000, 0xFFFF)
        If (Local0)
        {
            ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
        }
        Else
        {
            If ((Arg0 == 0x01))
            {
                Return (Zero)
            }

            Local0 = Acquire (\_GL, 0xFFFF)
            If (Local0)
            {
                ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
            }
            Else
            {
                If ((Arg0 == 0x02))
                {
                    Return (Zero)
                }

                Local0 = Acquire (T100, 0xFFFF)
                If (Local0)
                {
                    ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
                Else
                {
                    If ((Arg0 == 0x03))
                    {
                        Return (Zero)
                    }

                    Local0 = Acquire (T200, 0xFFFF)
                    If (Local0)
                    {
                        ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                    }
                    Else
                    {
                        If ((Arg0 == 0x04))
                        {
                            Return (Zero)
                        }

                        Local0 = Acquire (T300, 0xFFFF)
                        If (Local0)
                        {
                            ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                        }
                        Else
                        {
                            If ((Arg0 == 0x05))
                            {
                                Return (Zero)
                            }

                            Local0 = Acquire (T400, 0xFFFF)
                            If (Local0)
                            {
                                ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                            }
                            Else
                            {
                                If ((Arg0 == 0x06))
                                {
                                    Return (Zero)
                                }

                                Local0 = Acquire (T500, 0xFFFF)
                                If (Local0)
                                {
                                    ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                }
                                Else
                                {
                                    If ((Arg0 == 0x07))
                                    {
                                        Return (Zero)
                                    }

                                    Local0 = Acquire (T600, 0xFFFF)
                                    If (Local0)
                                    {
                                        ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                    }
                                    Else
                                    {
                                        If ((Arg0 == 0x08))
                                        {
                                            Return (Zero)
                                        }

                                        Local0 = Acquire (T700, 0xFFFF)
                                        If (Local0)
                                        {
                                            ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                        }
                                        Else
                                        {
                                            If ((Arg0 == 0x09))
                                            {
                                                Return (Zero)
                                            }

                                            Local0 = Acquire (T800, 0xFFFF)
                                            If (Local0)
                                            {
                                                ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                            }
                                            Else
                                            {
                                                If ((Arg0 == 0x0A))
                                                {
                                                    Return (Zero)
                                                }

                                                Local0 = Acquire (T900, 0xFFFF)
                                                If (Local0)
                                                {
                                                    ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                }
                                                Else
                                                {
                                                    If ((Arg0 == 0x0B))
                                                    {
                                                        Return (Zero)
                                                    }

                                                    Local0 = Acquire (TA00, 0xFFFF)
                                                    If (Local0)
                                                    {
                                                        ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                    }
                                                    Else
                                                    {
                                                        If ((Arg0 == 0x0C))
                                                        {
                                                            Return (Zero)
                                                        }

                                                        Local0 = Acquire (TB00, 0xFFFF)
                                                        If (Local0)
                                                        {
                                                            ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                        }
                                                        Else
                                                        {
                                                            If ((Arg0 == 0x0D))
                                                            {
                                                                Return (Zero)
                                                            }

                                                            Local0 = Acquire (TC00, 0xFFFF)
                                                            If (Local0)
                                                            {
                                                                ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                            }
                                                            Else
                                                            {
                                                                If ((Arg0 == 0x0E))
                                                                {
                                                                    Return (Zero)
                                                                }

                                                                Local0 = Acquire (TD00, 0xFFFF)
                                                                If (Local0)
                                                                {
                                                                    ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                }
                                                                Else
                                                                {
                                                                    If ((Arg0 == 0x0F))
                                                                    {
                                                                        Return (Zero)
                                                                    }

                                                                    Local0 = Acquire (TE00, 0xFFFF)
                                                                    If (Local0)
                                                                    {
                                                                        ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                    }
                                                                    Else
                                                                    {
                                                                        If ((Arg0 == 0x10))
                                                                        {
                                                                            Return (Zero)
                                                                        }

                                                                        Local0 = Acquire (TF00, 0xFFFF)
                                                                        If (Local0)
                                                                        {
                                                                            ERR (__METHOD__, Z151, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                        }
                                                                        ElseIf ((Arg0 == 0x11))
                                                                        {
                                                                            Return (Zero)
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /*
     * Release interval of mutexes
     *
     * arg0 - number of mutexes to Release (use not less than 1)
     */
    Method (M36E, 1, NotSerialized)
    {
        If ((Arg0 >= 0x11))
        {
            Release (TF00)
        }

        If ((Arg0 >= 0x10))
        {
            Release (TE00)
        }

        If ((Arg0 >= 0x0F))
        {
            Release (TD00)
        }

        If ((Arg0 >= 0x0E))
        {
            Release (TC00)
        }

        If ((Arg0 >= 0x0D))
        {
            Release (TB00)
        }

        If ((Arg0 >= 0x0C))
        {
            Release (TA00)
        }

        If ((Arg0 >= 0x0B))
        {
            Release (T900)
        }

        If ((Arg0 >= 0x0A))
        {
            Release (T800)
        }

        If ((Arg0 >= 0x09))
        {
            Release (T700)
        }

        If ((Arg0 >= 0x08))
        {
            Release (T600)
        }

        If ((Arg0 >= 0x07))
        {
            Release (T500)
        }

        If ((Arg0 >= 0x06))
        {
            Release (T400)
        }

        If ((Arg0 >= 0x05))
        {
            Release (T300)
        }

        If ((Arg0 >= 0x04))
        {
            Release (T200)
        }

        If ((Arg0 >= 0x03))
        {
            Release (T100)
        }

        If ((Arg0 >= 0x02))
        {
            Release (\_GL)
        }

        If ((Arg0 >= 0x01))
        {
            Release (T000)
        }
    }

    /*
     * Acquire mutex
     *
     * arg0 - Level of mutex
     * arg1 - Index of mutex
     * arg2 - opcode of exception to be generated or zero
     * arg3 - opcode of TimeOutValue (see comment to ma00)
     */
    Method (M36F, 4, Serialized)
    {
        Local0 = 0x01 /* Init with FAIL */
        If (FL02)
        {
            Local1 = M21E ("Acquire mutex, ", Arg0, Arg1)
            If (IM00)
            {
                Concatenate ("IMITATION: ", Local1, Local1)
            }

            If (Arg2)
            {
                Concatenate (Local1, ", Exception expected", Local1)
            }
            Else
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x05)
                    {
                        /* TOV0 */

                        Concatenate (Local1, ", tout 0", Local1)
                    }
                    Case (0x06)
                    {
                        /* TOV1 */

                        Concatenate (Local1, ", tout 1", Local1)
                    }
                    Default
                    {
                        Concatenate (Local1, ", tout 0xffff", Local1)
                    }

                }
            }

            Debug = Local1
        }

        If (IM00)
        {
            /* Just imitation */

            Return (0x00)
        }

        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Local0 = MA00 (Arg1, Arg2, Arg3)
            }
            Case (0x01)
            {
                Local0 = MA01 (Arg1, Arg2, Arg3)
            }
            Case (0x02)
            {
                Local0 = MA02 (Arg1, Arg2, Arg3)
            }
            Case (0x03)
            {
                Local0 = MA03 (Arg1, Arg2, Arg3)
            }
            Case (0x04)
            {
                Local0 = MA04 (Arg1, Arg2, Arg3)
            }
            Case (0x05)
            {
                Local0 = MA05 (Arg1, Arg2, Arg3)
            }
            Case (0x06)
            {
                Local0 = MA06 (Arg1, Arg2, Arg3)
            }
            Case (0x07)
            {
                Local0 = MA07 (Arg1, Arg2, Arg3)
            }
            Case (0x08)
            {
                Local0 = MA08 (Arg1, Arg2, Arg3)
            }
            Case (0x09)
            {
                Local0 = MA09 (Arg1, Arg2, Arg3)
            }
            Case (0x0A)
            {
                Local0 = MA0A (Arg1, Arg2, Arg3)
            }
            Case (0x0B)
            {
                Local0 = MA0B (Arg1, Arg2, Arg3)
            }
            Case (0x0C)
            {
                Local0 = MA0C (Arg1, Arg2, Arg3)
            }
            Case (0x0D)
            {
                Local0 = MA0D (Arg1, Arg2, Arg3)
            }
            Case (0x0E)
            {
                Local0 = MA0E (Arg1, Arg2, Arg3)
            }
            Case (0x0F)
            {
                Local0 = MA0F (Arg1, Arg2, Arg3)
            }

        }

        If (!Arg2)
        {
            If (Local0)
            {
                ERR ("m36f", Z151, __LINE__, 0x00, 0x00, Local0, 0x00)
            }
        }

        Return (Local0)
    }

    /*
     * Release mutex
     *
     * arg0 - Level of mutex
     * arg1 - Index of mutex
     * arg2 - opcode of exception to be generated or zero
     */
    Method (M388, 3, Serialized)
    {
        If (FL02)
        {
            Local1 = M21E ("Release mutex, ", Arg0, Arg1)
            If (IM00)
            {
                Concatenate ("IMITATION: ", Local1, Local1)
            }

            If (Arg2)
            {
                Concatenate (Local1, ", Exception expected", Local1)
            }

            Debug = Local1
        }

        If (IM00)
        {
            Return (            /* Just imitation */

Zero)
        }

        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                MA10 (Arg1)
            }
            Case (0x01)
            {
                MA11 (Arg1)
            }
            Case (0x02)
            {
                MA12 (Arg1)
            }
            Case (0x03)
            {
                MA13 (Arg1)
            }
            Case (0x04)
            {
                MA14 (Arg1)
            }
            Case (0x05)
            {
                MA15 (Arg1)
            }
            Case (0x06)
            {
                MA16 (Arg1)
            }
            Case (0x07)
            {
                MA17 (Arg1)
            }
            Case (0x08)
            {
                MA18 (Arg1)
            }
            Case (0x09)
            {
                MA19 (Arg1)
            }
            Case (0x0A)
            {
                MA1A (Arg1)
            }
            Case (0x0B)
            {
                MA1B (Arg1)
            }
            Case (0x0C)
            {
                MA1C (Arg1)
            }
            Case (0x0D)
            {
                MA1D (Arg1)
            }
            Case (0x0E)
            {
                MA1E (Arg1)
            }
            Case (0x0F)
            {
                MA1F (Arg1)
            }

        }
    }

    /*
     * Acquire the range of mutexes from lower to upper levels (index 0)
     * arg0 - start level of mutex
     * arg1 - number of levels
     * arg2 - if non-zero - Axquire GL too
     * arg3 - non-zero means that we generate exceptional
     *        condition on each Acquire. The non-zero value
     *        means the opcode of exception.
     */
    Method (M38B, 4, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        If (Arg2)
        {
            If (Arg3)
            {
                CH03 ("m38b", Z151, __LINE__, 0x00, 0x00)
            }

            M36F (GLLL, GLIX, Arg3, 0x00) /* Acquire GL */
            If (Arg3)
            {
                CH04 ("m38b", 0x00, Arg3, Z151, __LINE__, 0x00, 0x00)
            }
        }

        LPN0 = Arg1
        LPC0 = Arg0
        While (LPN0)
        {
            If (Arg3)
            {
                CH03 ("m38b", Z151, __LINE__, 0x00, 0x00)
            }

            M36F (LPC0, 0x00, Arg3, 0x00) /* Acquire */
            If (Arg3)
            {
                CH04 ("m38b", 0x00, Arg3, Z151, __LINE__, 0x00, 0x00)
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * Release the range of mutexes from upper to lower levels (index 0)
     * arg0 - start level of mutex
     * arg1 - number of levels
     * arg2 - if non-zero - Release GL too
     * arg3 - non-zero means that we generate exceptional
     *        condition on each Acquire. The non-zero value
     *        means the opcode of exception.
     */
    Method (M38C, 4, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Local7 = 0x00
        LPN0 = Arg1
        LPC0 = Arg0
        While (LPN0)
        {
            If (Arg3)
            {
                Local7 = (CH03 ("m38b", Z151, __LINE__, 0x00, 0x00) || Local7)
            }

            M388 (LPC0, 0x00, 0x00) /* Release */
            If (Arg3)
            {
                Local7 = (CH04 ("m38b", 0x00, Arg3, Z151, __LINE__, 0x00, 0x00) || Local7)
            }

            LPN0--
            LPC0--
        }

        If (Arg2)
        {
            If (Arg3)
            {
                Local7 = (CH03 ("m38b", Z151, __LINE__, 0x00, 0x00) || Local7)
            }

            M388 (GLLL, GLIX, 0x00) /* Release GL */
            If (Arg3)
            {
                Local7 = (CH04 ("m38b", 0x00, Arg3, Z151, __LINE__, 0x00, 0x00) || Local7)
            }
        }

        Return (Local7)
    }

    /*
     * Acquire the range of mutexes
     *
     * arg0 - start level of mutex
     * arg1 - number of levels
     * arg2 - start index of mutex on level
     * arg3 - number of mutexes on the same level
     * arg4 - opcode of exception to be generated or zero
     * arg5 - repetition number
     * arg6 - opcode of TimeOutValue (see comment to ma00)
     */
    Method (M088, 7, Serialized)
    {
        Name (LPN0, 0x00) /* level */
        Name (LPC0, 0x00)
        Name (LPN1, 0x00) /* index */
        Name (LPC1, 0x00)
        Name (LPN2, 0x00) /* repetition */
        Name (LPC2, 0x00)
        Name (RPT0, 0x01)
        Name (EXC0, 0x00) /* exception is expected - opcode to pass to (m36f & CH04) */
        Name (EXC1, 0x00) /* exception is expected - run (CH03 & CH04) */
        EXC0 = Arg4
        If (IM00)
        {
            EXC1 = 0x00
        }
        ElseIf (Arg4)
        {
            EXC1 = Arg4
        }

        If (Arg5)
        {
            RPT0 = Arg5
        }

        LPN0 = Arg1
        LPC0 = Arg0
        While (LPN0)
        {
            LPN1 = Arg3
            LPC1 = Arg2
            While (LPN1)
            {
                LPN2 = RPT0 /* \M088.RPT0 */
                LPC2 = 0x00
                While (LPN2)
                {
                    If (EXC1)
                    {
                        CH03 ("m088", Z151, __LINE__, 0x00, 0x00)
                    }

                    M36F (LPC0, LPC1, EXC0, Arg6) /* Acquire */
                    If (EXC1)
                    {
                        CH04 ("m088", 0x00, EXC0, Z151, __LINE__, 0x00, 0x00)
                    }

                    LPN2--
                    LPC2++
                }

                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * Release the range of mutexes
     *
     * arg0 - start level of mutex
     * arg1 - number of levels
     * arg2 - start index of mutex on level
     * arg3 - number of mutexes on the same level
     * arg4 - opcode of exception to be generated or zero
     * arg5 - repetition number
     *
     * arg6 - order of Releasing bitmap,
     *        determinates the order of Releasing mutexes of the same level:
     *           [0] - 0 - derect order
     *                 1 - inverse order
     *           [1] - 0 - don't replace the last index
     *                 1 - replace the last index
     *        [15:8] - the index of mutex to be the last in case of non-zero [1]
     *
     * Note: the bit [1] technique was added while investigating the anomaly
     *       reflected by bug 242 "Releasing the mutex the first Acquired on
     *       the non-zero level makes Releasing the residuary mutexes of that
     *       level impossible".
     *
     * Examples:
     *
     * Acquired on the same level are mutexes of 0,1,2,3 indexes
     * Releasing for arg6 equal to:
     * 0x00 - 0123 (direct - the same order the mutexes were Acquired)
     *   01 - 3210 (inverse to Acquiring)
     *   22 - 0132 (direct + replace the last index, it becomes index 2)
     *   23 - 3102 (inverse + replace the last index, it becomes index 2)
     */
    Method (M089, 7, Serialized)
    {
        Name (LPN0, 0x00) /* level */
        Name (LPC0, 0x00)
        Name (LPN1, 0x00) /* index */
        Name (LPC1, 0x00)
        Name (LPN2, 0x00) /* repetition */
        Name (LPC2, 0x00)
        Name (RPT0, 0x01)
        Name (BG00, 0x00)
        Name (EN00, 0x00)
        Name (INV0, 0x00) /* sign of the inverse order */
        Name (RPL0, 0x00) /* to do replacing */
        Name (LIX0, 0x00) /* value to be the last index */
        Name (EXC0, 0x00) /* exception is expected - opcode to pass to (m36f & CH04) */
        Name (EXC1, 0x00) /* exception is expected - run (CH03 & CH04) */
        EXC0 = Arg4
        If (IM00)
        {
            EXC1 = 0x00
        }
        ElseIf (Arg4)
        {
            EXC1 = Arg4
        }

        If (Arg5)
        {
            RPT0 = Arg5
        }

        INV0 = (Arg6 & 0x01)
        RPL0 = (Arg6 & 0x02)
        LIX0 = (Arg6 & 0xFF00)
        LIX0 >>= 0x08
        BG00 = Arg2
        EN00 = (Arg2 + Arg3)
        EN00--
        /* Inverse order of levels */

        LPN0 = Arg1
        LPC0 = (Arg0 + Arg1)
        LPC0--
        While (LPN0)
        {
            If (INV0)
            {
                /* inverse order */

                LPN1 = Arg3
                LPC1 = (Arg2 + Arg3)
                LPC1--
                While (LPN1)
                {
                    Local0 = LPC1 /* \M089.LPC1 */
                    If (RPL0)
                    {
                        If ((LPN1 == 0x01))
                        {
                            Local0 = LIX0 /* \M089.LIX0 */
                        }
                        ElseIf ((LPC1 <= LIX0))
                        {
                            Local0 = (LPC1 - 0x01)
                        }
                    }

                    LPN2 = RPT0 /* \M089.RPT0 */
                    LPC2 = 0x00
                    While (LPN2)
                    {
                        If (EXC1)
                        {
                            CH03 ("m088", Z151, __LINE__, 0x00, 0x00)
                        }

                        M388 (LPC0, Local0, EXC0) /* Release */
                        If (EXC1)
                        {
                            CH04 ("m088", 0x00, EXC0, Z151, __LINE__, 0x00, 0x00)
                        }

                        LPN2--
                        LPC2++
                    }

                    LPN1--
                    LPC1--
                }
            }
            Else
            {
                /* direct order */

                LPN1 = Arg3
                LPC1 = Arg2
                While (LPN1)
                {
                    Local0 = LPC1 /* \M089.LPC1 */
                    If (RPL0)
                    {
                        If ((LPN1 == 0x01))
                        {
                            Local0 = LIX0 /* \M089.LIX0 */
                        }
                        ElseIf ((LPC1 >= LIX0))
                        {
                            Local0 = (LPC1 + 0x01)
                        }
                    }

                    LPN2 = RPT0 /* \M089.RPT0 */
                    LPC2 = 0x00
                    While (LPN2)
                    {
                        If (EXC1)
                        {
                            CH03 ("m088", Z151, __LINE__, 0x00, 0x00)
                        }

                        M388 (LPC0, Local0, EXC0) /* Release */
                        If (EXC1)
                        {
                            CH04 ("m088", 0x00, EXC0, Z151, __LINE__, 0x00, 0x00)
                        }

                        LPN2--
                        LPC2++
                    }

                    LPN1--
                    LPC1++
                }
            }

            LPN0--
            LPC0--
        }
    }

    /*
     * Check that all mutexes are Released (don't check T804..)
     */
    Method (M08A, 0, NotSerialized)
    {
        M089 (0x00, MAX0, 0x00, MIN0, 0x41, 0x00, 0x00) /* AE_AML_MUTEX_NOT_ACQUIRED */
    }
