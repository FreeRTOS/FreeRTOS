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
     * Check for serialized methods
     */
    Name (Z173, 0xAD)
    /*
     * Proper sequence of calls to Serialized methods with different levels, 0-15, all Serialized
     */
    Method (M3B0, 0, Serialized)
    {
        Name (I000, 0x00)
        Method (M000, 0, Serialized)
        {
            I000++
            M001 ()
        }

        Method (M001, 0, Serialized, 1)
        {
            I000++
            M002 ()
        }

        Method (M002, 0, Serialized, 2)
        {
            I000++
            M003 ()
        }

        Method (M003, 0, Serialized, 3)
        {
            I000++
            M004 ()
        }

        Method (M004, 0, Serialized, 4)
        {
            I000++
            M005 ()
        }

        Method (M005, 0, Serialized, 5)
        {
            I000++
            M006 ()
        }

        Method (M006, 0, Serialized, 6)
        {
            I000++
            M007 ()
        }

        Method (M007, 0, Serialized, 7)
        {
            I000++
            M008 ()
        }

        Method (M008, 0, Serialized, 8)
        {
            I000++
            M009 ()
        }

        Method (M009, 0, Serialized, 9)
        {
            I000++
            M010 ()
        }

        Method (M010, 0, Serialized, 10)
        {
            I000++
            M011 ()
        }

        Method (M011, 0, Serialized, 11)
        {
            I000++
            M012 ()
        }

        Method (M012, 0, Serialized, 12)
        {
            I000++
            M013 ()
        }

        Method (M013, 0, Serialized, 13)
        {
            I000++
            M014 ()
        }

        Method (M014, 0, Serialized, 14)
        {
            I000++
            M015 ()
        }

        Method (M015, 0, Serialized, 15)
        {
            I000++
            M016 ()
        }

        Method (M016, 0, Serialized, 15)
        {
            I000++
            Debug = "m016"
            If ((I000 != 0x11))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I000, 0x11)
            }
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
        M000 ()
        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
    }

    /*
     * Proper sequence of calls to Serialized methods with different levels, 0-15,
     * alternating Serialized and not-Serialized
     */
    Method (M3B1, 0, Serialized)
    {
        Name (I000, 0x00)
        Method (M000, 0, Serialized)
        {
            I000++
            M001 ()
        }

        Method (M001, 0, NotSerialized)
        {
            I000++
            M002 ()
        }

        Method (M002, 0, Serialized, 2)
        {
            I000++
            M003 ()
        }

        Method (M003, 0, NotSerialized)
        {
            I000++
            M004 ()
        }

        Method (M004, 0, NotSerialized)
        {
            I000++
            M005 ()
        }

        Method (M005, 0, Serialized, 5)
        {
            I000++
            M006 ()
        }

        Method (M006, 0, Serialized, 6)
        {
            I000++
            M007 ()
        }

        Method (M007, 0, NotSerialized)
        {
            I000++
            M008 ()
        }

        Method (M008, 0, Serialized, 8)
        {
            I000++
            M009 ()
        }

        Method (M009, 0, Serialized, 9)
        {
            I000++
            M010 ()
        }

        Method (M010, 0, NotSerialized)
        {
            I000++
            M011 ()
        }

        Method (M011, 0, NotSerialized)
        {
            I000++
            M012 ()
        }

        Method (M012, 0, Serialized, 12)
        {
            I000++
            M013 ()
        }

        Method (M013, 0, Serialized, 13)
        {
            I000++
            M014 ()
        }

        Method (M014, 0, Serialized, 14)
        {
            I000++
            M015 ()
        }

        Method (M015, 0, NotSerialized)
        {
            I000++
            M016 ()
        }

        Method (M016, 0, Serialized, 15)
        {
            I000++
            Debug = "m016"
            If ((I000 != 0x11))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I000, 0x11)
            }
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
        M000 ()
        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
    }

    /*
     * Proper sequence of calls to Serialized methods with different levels, 0-15, all Serialized,
     * 1-3 on each level
     */
    Method (M3B2, 0, Serialized)
    {
        Name (I000, 0x00)
        Name (I001, 0x00)
        Method (M000, 0, Serialized)
        {
            I000++
            M100 ()
        }

        Method (M100, 0, Serialized)
        {
            I000++
            M001 ()
        }

        Method (M001, 0, Serialized, 1)
        {
            I000++
            M002 ()
        }

        Method (M002, 0, Serialized, 2)
        {
            I000++
            M102 ()
        }

        Method (M102, 0, Serialized, 2)
        {
            I000++
            M003 ()
        }

        Method (M003, 0, Serialized, 3)
        {
            I000++
            M004 ()
        }

        Method (M004, 0, Serialized, 4)
        {
            I000++
            M104 ()
        }

        Method (M104, 0, Serialized, 4)
        {
            I000++
            M005 ()
        }

        Method (M005, 0, Serialized, 5)
        {
            I000++
            M006 ()
        }

        Method (M006, 0, Serialized, 6)
        {
            I000++
            M106 ()
        }

        Method (M106, 0, Serialized, 6)
        {
            I000++
            M007 ()
        }

        Method (M007, 0, Serialized, 7)
        {
            I000++
            M107 ()
        }

        Method (M107, 0, Serialized, 7)
        {
            I000++
            M008 ()
        }

        Method (M008, 0, Serialized, 8)
        {
            I000++
            M108 ()
        }

        Method (M108, 0, Serialized, 8)
        {
            I000++
            M009 ()
        }

        Method (M009, 0, Serialized, 9)
        {
            I000++
            M109 ()
        }

        Method (M109, 0, Serialized, 9)
        {
            I000++
            M209 ()
        }

        Method (M209, 0, Serialized, 9)
        {
            I000++
            M010 ()
        }

        Method (M010, 0, Serialized, 10)
        {
            I000++
            M110 ()
        }

        Method (M110, 0, Serialized, 10)
        {
            I000++
            M011 ()
        }

        Method (M011, 0, Serialized, 11)
        {
            I000++
            M111 ()
        }

        Method (M111, 0, Serialized, 11)
        {
            I000++
            M012 ()
        }

        Method (M012, 0, Serialized, 12)
        {
            I000++
            M112 ()
        }

        Method (M112, 0, Serialized, 12)
        {
            I000++
            M013 ()
        }

        Method (M013, 0, Serialized, 13)
        {
            I000++
            M014 ()
        }

        Method (M014, 0, Serialized, 14)
        {
            I000++
            M015 ()
        }

        Method (M015, 0, Serialized, 15)
        {
            I000++
            M115 ()
        }

        Method (M115, 0, Serialized, 15)
        {
            I000++
            Debug = "m016"
            If ((I000 != 0x1C))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I000, 0x1C)
            }

            I001 = 0xABCD0000
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
        M000 ()
        If ((I001 != 0xABCD0000))
        {
            ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I001, 0xABCD0000)
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
    }

    /*
     * Check pairs of calls to Serialized methods,
     * the second method is invoked from the first method.
     *
     * All the 256 combinations are verified (16*16):
     * - the level of the first  method in pair changes in range from 0 up to 15
     * - the level of the second method in pair changes in range from 0 up to 15
     *
     * So all the checkings are provided:
     *
     * -   proper sequence of levels (from i-th level to all possible correct levels)
     * -   proper sequence of levels (from i-th level to i-th level (in particular))
     * - improper sequence of levels (from i-th level to all possible incorrect levels)
     *
     * arg0 - level of first call
     * arg1 - level of second call
     * arg2 - how many calls to do
     */
    Method (M3B3, 3, Serialized)
    {
        Name (I000, 0x00)
        Name (I001, 0x00)
        Name (I002, 0x00)
        Name (I003, 0xABCD0003)
        Name (I004, 0xABCD0004)
        Name (I005, 0x00)
        Method (M000, 1, Serialized)
        {
            If (Arg0)
            {
                I004 = 0x00
            }
            Else
            {
                I003 = 0x00
            }

            MM00 (0x01, I000, I001)
        }

        Method (M001, 1, Serialized, 1)
        {
            If (Arg0)
            {
                I004 = 0x01
            }
            Else
            {
                I003 = 0x01
            }

            MM00 (0x01, I000, I001)
        }

        Method (M002, 1, Serialized, 2)
        {
            If (Arg0)
            {
                I004 = 0x02
            }
            Else
            {
                I003 = 0x02
            }

            MM00 (0x01, I000, I001)
        }

        Method (M003, 1, Serialized, 3)
        {
            If (Arg0)
            {
                I004 = 0x03
            }
            Else
            {
                I003 = 0x03
            }

            MM00 (0x01, I000, I001)
        }

        Method (M004, 1, Serialized, 4)
        {
            If (Arg0)
            {
                I004 = 0x04
            }
            Else
            {
                I003 = 0x04
            }

            MM00 (0x01, I000, I001)
        }

        Method (M005, 1, Serialized, 5)
        {
            If (Arg0)
            {
                I004 = 0x05
            }
            Else
            {
                I003 = 0x05
            }

            MM00 (0x01, I000, I001)
        }

        Method (M006, 1, Serialized, 6)
        {
            If (Arg0)
            {
                I004 = 0x06
            }
            Else
            {
                I003 = 0x06
            }

            MM00 (0x01, I000, I001)
        }

        Method (M007, 1, Serialized, 7)
        {
            If (Arg0)
            {
                I004 = 0x07
            }
            Else
            {
                I003 = 0x07
            }

            MM00 (0x01, I000, I001)
        }

        Method (M008, 1, Serialized, 8)
        {
            If (Arg0)
            {
                I004 = 0x08
            }
            Else
            {
                I003 = 0x08
            }

            MM00 (0x01, I000, I001)
        }

        Method (M009, 1, Serialized, 9)
        {
            If (Arg0)
            {
                I004 = 0x09
            }
            Else
            {
                I003 = 0x09
            }

            MM00 (0x01, I000, I001)
        }

        Method (M010, 1, Serialized, 10)
        {
            If (Arg0)
            {
                I004 = 0x0A
            }
            Else
            {
                I003 = 0x0A
            }

            MM00 (0x01, I000, I001)
        }

        Method (M011, 1, Serialized, 11)
        {
            If (Arg0)
            {
                I004 = 0x0B
            }
            Else
            {
                I003 = 0x0B
            }

            MM00 (0x01, I000, I001)
        }

        Method (M012, 1, Serialized, 12)
        {
            If (Arg0)
            {
                I004 = 0x0C
            }
            Else
            {
                I003 = 0x0C
            }

            MM00 (0x01, I000, I001)
        }

        Method (M013, 1, Serialized, 13)
        {
            If (Arg0)
            {
                I004 = 0x0D
            }
            Else
            {
                I003 = 0x0D
            }

            MM00 (0x01, I000, I001)
        }

        Method (M014, 1, Serialized, 14)
        {
            If (Arg0)
            {
                I004 = 0x0E
            }
            Else
            {
                I003 = 0x0E
            }

            MM00 (0x01, I000, I001)
        }

        Method (M015, 1, Serialized, 15)
        {
            If (Arg0)
            {
                I004 = 0x0F
            }
            Else
            {
                I003 = 0x0F
            }

            MM00 (0x01, I000, I001)
        }

        Method (MM00, 3, Serialized)
        {
            Name (III0, 0x00)
            Name (III1, 0x00)
            Name (III2, 0x00)
            Name (III3, 0x00)
            Local0 = I002 /* \M3B3.I002 */
            I002++
            If ((I002 > I005))
            {
                Return (Zero)
            }

            If (Arg0)
            {
                Local1 = Arg2
            }
            Else
            {
                Local1 = Arg1
            }

            Switch (ToInteger (Local1))
            {
                Case (0x00)
                {
                    M000 (Local0)
                }
                Case (0x01)
                {
                    M001 (Local0)
                }
                Case (0x02)
                {
                    M002 (Local0)
                }
                Case (0x03)
                {
                    M003 (Local0)
                }
                Case (0x04)
                {
                    M004 (Local0)
                }
                Case (0x05)
                {
                    M005 (Local0)
                }
                Case (0x06)
                {
                    M006 (Local0)
                }
                Case (0x07)
                {
                    M007 (Local0)
                }
                Case (0x08)
                {
                    M008 (Local0)
                }
                Case (0x09)
                {
                    M009 (Local0)
                }
                Case (0x0A)
                {
                    M010 (Local0)
                }
                Case (0x0B)
                {
                    M011 (Local0)
                }
                Case (0x0C)
                {
                    M012 (Local0)
                }
                Case (0x0D)
                {
                    M013 (Local0)
                }
                Case (0x0E)
                {
                    M014 (Local0)
                }
                Case (0x0F)
                {
                    M015 (Local0)
                }

            }
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
        I000 = Arg0
        I001 = Arg1
        I005 = Arg2
        MM00 (0x00, I000, I001)
        If ((Arg0 > Arg1))
        {
            CH04 (__METHOD__, 0x00, 0x40, Z173, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
        }
        Else
        {
            If ((I003 != Arg0))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I003, Arg0)
            }

            If ((I004 != Arg1))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I004, Arg1)
            }
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
    }

    Method (M3B4, 0, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        LPN0 = 0x10
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = 0x10
            LPC1 = 0x00
            While (LPN1)
            {
                M3B3 (LPC0, LPC1, 0x02)
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * The same as m3b3 but without Switch
     *
     * arg0 - level of first call
     * arg1 - level of second call
     */
    Method (M3B5, 2, Serialized)
    {
        Name (I000, 0x00)
        Name (I001, 0x00)
        Name (I002, 0x00)
        Name (I003, 0xABCD0003)
        Name (I004, 0xABCD0004)
        Method (M000, 1, Serialized)
        {
            If (Arg0)
            {
                I004 = 0x00
            }
            Else
            {
                I003 = 0x00
            }

            MM00 (0x01, I000, I001)
        }

        Method (M001, 1, Serialized, 1)
        {
            If (Arg0)
            {
                I004 = 0x01
            }
            Else
            {
                I003 = 0x01
            }

            MM00 (0x01, I000, I001)
        }

        Method (M002, 1, Serialized, 2)
        {
            If (Arg0)
            {
                I004 = 0x02
            }
            Else
            {
                I003 = 0x02
            }

            MM00 (0x01, I000, I001)
        }

        Method (M003, 1, Serialized, 3)
        {
            If (Arg0)
            {
                I004 = 0x03
            }
            Else
            {
                I003 = 0x03
            }

            MM00 (0x01, I000, I001)
        }

        Method (M004, 1, Serialized, 4)
        {
            If (Arg0)
            {
                I004 = 0x04
            }
            Else
            {
                I003 = 0x04
            }

            MM00 (0x01, I000, I001)
        }

        Method (M005, 1, Serialized, 5)
        {
            If (Arg0)
            {
                I004 = 0x05
            }
            Else
            {
                I003 = 0x05
            }

            MM00 (0x01, I000, I001)
        }

        Method (M006, 1, Serialized, 6)
        {
            If (Arg0)
            {
                I004 = 0x06
            }
            Else
            {
                I003 = 0x06
            }

            MM00 (0x01, I000, I001)
        }

        Method (M007, 1, Serialized, 7)
        {
            If (Arg0)
            {
                I004 = 0x07
            }
            Else
            {
                I003 = 0x07
            }

            MM00 (0x01, I000, I001)
        }

        Method (M008, 1, Serialized, 8)
        {
            If (Arg0)
            {
                I004 = 0x08
            }
            Else
            {
                I003 = 0x08
            }

            MM00 (0x01, I000, I001)
        }

        Method (M009, 1, Serialized, 9)
        {
            If (Arg0)
            {
                I004 = 0x09
            }
            Else
            {
                I003 = 0x09
            }

            MM00 (0x01, I000, I001)
        }

        Method (M010, 1, Serialized, 10)
        {
            If (Arg0)
            {
                I004 = 0x0A
            }
            Else
            {
                I003 = 0x0A
            }

            MM00 (0x01, I000, I001)
        }

        Method (M011, 1, Serialized, 11)
        {
            If (Arg0)
            {
                I004 = 0x0B
            }
            Else
            {
                I003 = 0x0B
            }

            MM00 (0x01, I000, I001)
        }

        Method (M012, 1, Serialized, 12)
        {
            If (Arg0)
            {
                I004 = 0x0C
            }
            Else
            {
                I003 = 0x0C
            }

            MM00 (0x01, I000, I001)
        }

        Method (M013, 1, Serialized, 13)
        {
            If (Arg0)
            {
                I004 = 0x0D
            }
            Else
            {
                I003 = 0x0D
            }

            MM00 (0x01, I000, I001)
        }

        Method (M014, 1, Serialized, 14)
        {
            If (Arg0)
            {
                I004 = 0x0E
            }
            Else
            {
                I003 = 0x0E
            }

            MM00 (0x01, I000, I001)
        }

        Method (M015, 1, Serialized, 15)
        {
            If (Arg0)
            {
                I004 = 0x0F
            }
            Else
            {
                I003 = 0x0F
            }

            MM00 (0x01, I000, I001)
        }

        Method (MM00, 3, NotSerialized)
        {
            Local0 = I002 /* \M3B5.I002 */
            I002++
            If ((I002 > 0x02))
            {
                Return (Zero)
            }

            If (Arg0)
            {
                Local1 = Arg2
            }
            Else
            {
                Local1 = Arg1
            }

            If ((Local1 == 0x00))
            {
                M000 (Local0)
            }
            ElseIf ((Local1 == 0x01))
            {
                M001 (Local0)
            }
            ElseIf ((Local1 == 0x02))
            {
                M002 (Local0)
            }
            ElseIf ((Local1 == 0x03))
            {
                M003 (Local0)
            }
            ElseIf ((Local1 == 0x04))
            {
                M004 (Local0)
            }
            ElseIf ((Local1 == 0x05))
            {
                M005 (Local0)
            }
            ElseIf ((Local1 == 0x06))
            {
                M006 (Local0)
            }
            ElseIf ((Local1 == 0x07))
            {
                M007 (Local0)
            }
            ElseIf ((Local1 == 0x08))
            {
                M008 (Local0)
            }
            ElseIf ((Local1 == 0x09))
            {
                M009 (Local0)
            }
            ElseIf ((Local1 == 0x0A))
            {
                M010 (Local0)
            }
            ElseIf ((Local1 == 0x0B))
            {
                M011 (Local0)
            }
            ElseIf ((Local1 == 0x0C))
            {
                M012 (Local0)
            }
            ElseIf ((Local1 == 0x0D))
            {
                M013 (Local0)
            }
            ElseIf ((Local1 == 0x0E))
            {
                M014 (Local0)
            }
            ElseIf ((Local1 == 0x0F))
            {
                M015 (Local0)
            }
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
        I000 = Arg0
        I001 = Arg1
        MM00 (0x00, I000, I001)
        If ((Arg0 > Arg1))
        {
            CH04 (__METHOD__, 0x00, 0x40, Z173, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
        }
        Else
        {
            If ((I003 != Arg0))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I003, Arg0)
            }

            If ((I004 != Arg1))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I004, Arg1)
            }
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
    }

    Method (M3B6, 0, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        LPN0 = 0x10
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = 0x10
            LPC1 = 0x00
            While (LPN1)
            {
                M3B5 (LPC0, LPC1)
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * The same as m3b5 but
     * between two Serialized calls non-Serialized calls are performed
     *
     * arg0 - level of first call
     * arg1 - level of second call
     * arg2 - how many calls to do
     */
    Method (M3B7, 3, Serialized)
    {
        Name (I000, 0x00)
        Name (I001, 0x00)
        Name (I002, 0x00)
        Name (I003, 0xABCD0003)
        Name (I004, 0xABCD0004)
        Name (I005, 0x00)
        Method (M000, 1, Serialized)
        {
            If (Arg0)
            {
                I004 = 0x00
            }
            Else
            {
                I003 = 0x00
            }

            MM00 (0x01, I000, I001)
        }

        Method (M001, 1, Serialized, 1)
        {
            If (Arg0)
            {
                I004 = 0x01
            }
            Else
            {
                I003 = 0x01
            }

            MM00 (0x01, I000, I001)
        }

        Method (M002, 1, Serialized, 2)
        {
            If (Arg0)
            {
                I004 = 0x02
            }
            Else
            {
                I003 = 0x02
            }

            MM00 (0x01, I000, I001)
        }

        Method (M003, 1, Serialized, 3)
        {
            If (Arg0)
            {
                I004 = 0x03
            }
            Else
            {
                I003 = 0x03
            }

            MM00 (0x01, I000, I001)
        }

        Method (M004, 1, Serialized, 4)
        {
            If (Arg0)
            {
                I004 = 0x04
            }
            Else
            {
                I003 = 0x04
            }

            MM00 (0x01, I000, I001)
        }

        Method (M005, 1, Serialized, 5)
        {
            If (Arg0)
            {
                I004 = 0x05
            }
            Else
            {
                I003 = 0x05
            }

            MM00 (0x01, I000, I001)
        }

        Method (M006, 1, Serialized, 6)
        {
            If (Arg0)
            {
                I004 = 0x06
            }
            Else
            {
                I003 = 0x06
            }

            MM00 (0x01, I000, I001)
        }

        Method (M007, 1, Serialized, 7)
        {
            If (Arg0)
            {
                I004 = 0x07
            }
            Else
            {
                I003 = 0x07
            }

            MM00 (0x01, I000, I001)
        }

        Method (M008, 1, Serialized, 8)
        {
            If (Arg0)
            {
                I004 = 0x08
            }
            Else
            {
                I003 = 0x08
            }

            MM00 (0x01, I000, I001)
        }

        Method (M009, 1, Serialized, 9)
        {
            If (Arg0)
            {
                I004 = 0x09
            }
            Else
            {
                I003 = 0x09
            }

            MM00 (0x01, I000, I001)
        }

        Method (M010, 1, Serialized, 10)
        {
            If (Arg0)
            {
                I004 = 0x0A
            }
            Else
            {
                I003 = 0x0A
            }

            MM00 (0x01, I000, I001)
        }

        Method (M011, 1, Serialized, 11)
        {
            If (Arg0)
            {
                I004 = 0x0B
            }
            Else
            {
                I003 = 0x0B
            }

            MM00 (0x01, I000, I001)
        }

        Method (M012, 1, Serialized, 12)
        {
            If (Arg0)
            {
                I004 = 0x0C
            }
            Else
            {
                I003 = 0x0C
            }

            MM00 (0x01, I000, I001)
        }

        Method (M013, 1, Serialized, 13)
        {
            If (Arg0)
            {
                I004 = 0x0D
            }
            Else
            {
                I003 = 0x0D
            }

            MM00 (0x01, I000, I001)
        }

        Method (M014, 1, Serialized, 14)
        {
            If (Arg0)
            {
                I004 = 0x0E
            }
            Else
            {
                I003 = 0x0E
            }

            MM00 (0x01, I000, I001)
        }

        Method (M015, 1, Serialized, 15)
        {
            If (Arg0)
            {
                I004 = 0x0F
            }
            Else
            {
                I003 = 0x0F
            }

            MM00 (0x01, I000, I001)
        }

        Method (MM01, 7, NotSerialized)
        {
            Local0 = 0x00
        }

        Method (MM00, 3, NotSerialized)
        {
            Local0 = I002 /* \M3B7.I002 */
            I002++
            If ((I002 > I005))
            {
                Return (Zero)
            }

            If (Arg0)
            {
                Local1 = Arg2
            }
            Else
            {
                Local1 = Arg1
            }

            If ((Local1 == 0x00))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M000 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x01))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M001 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x02))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M002 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x03))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M003 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x04))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M004 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x05))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M005 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x06))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M006 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x07))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M007 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x08))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M008 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x09))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M009 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x0A))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M010 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x0B))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M011 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x0C))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M012 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x0D))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M013 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x0E))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M014 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
            ElseIf ((Local1 == 0x0F))
            {
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
                M015 (Local0)
                MM01 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            }
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
        I000 = Arg0
        I001 = Arg1
        I005 = Arg2
        MM00 (0x00, I000, I001)
        If ((Arg0 > Arg1))
        {
            CH04 (__METHOD__, 0x00, 0x40, Z173, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
        }
        Else
        {
            If ((I003 != Arg0))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I003, Arg0)
            }

            If ((I004 != Arg1))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I004, Arg1)
            }
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
    }

    Method (M3B8, 0, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        LPN0 = 0x10
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = 0x10
            LPC1 = 0x00
            While (LPN1)
            {
                M3B7 (LPC0, LPC1, 0x02)
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * Check that Serialized method can be invoked repeatedly
     *
     * (Serialized method without internal objects (including Methods) and Switches)
     *
     * Method is invoked 2 times, then 3 times, then 4 times,...
     * Then do it for next Method.
     */
    Method (M3B9, 0, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        LPN0 = 0x10
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = 0x10
            LPC1 = 0x02
            While (LPN1)
            {
                M3B3 (LPC0, LPC0, LPC1)
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * Check that Serialized method can be invoked repeatedly
     *
     * (Serialized method without internal objects (including Methods) and Switches)
     *
     * between two Serialized calls non-Serialized calls are performed
     *
     * Method is invoked 2 times, then 3 times, then 4 times,...
     * Then do it for next Method.
     */
    Method (M3BA, 0, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        LPN0 = 0x10
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = 0x10
            LPC1 = 0x02
            While (LPN1)
            {
                M3B7 (LPC0, LPC0, LPC1)
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * The level is set up by either call to Serialized method or Acquire mutex of that level
     *
     * Check pairs of calls to methods which provide exclusive access to critical sections
     * either by 'Serialized method' technique or AML mutexes (Acquire/Release) framework.
     * The second method is invoked from the first method.
     *
     * All the 1024 combinations are verified (32*32):
     *
     * The first call to method in pair is call to:
     * - Serialized method with level in range from 0 up to 15
     * - non-Serialized method Acquiring mutex with level in range from 0 up to 15
     *
     * Identically, the second call to method in pair is call to:
     * - Serialized method with level in range from 0 up to 15
     * - non-Serialized method Acquiring mutex with level in range from 0 up to 15
     *
     * So all the checkings are provided:
     *
     * -   proper sequence of levels (from i-th level to all possible correct levels)
     * -   proper sequence of levels (from i-th level to i-th level (in particular))
     * - improper sequence of levels (from i-th level to all possible incorrect levels)
     *
     * arg0 - level of first call
     * arg1 - level of second call
     * arg2 - how many calls to do
     */
    Method (M3BB, 3, Serialized)
    {
        Name (I000, 0x00)
        Name (I001, 0x00)
        Name (I002, 0x00)
        Name (I003, 0xABCD0003)
        Name (I004, 0xABCD0004)
        Name (I005, 0x00)
        Mutex (MT00, 0x00)
        Mutex (MT10, 0x01)
        Mutex (MT20, 0x02)
        Mutex (MT30, 0x03)
        Mutex (MT40, 0x04)
        Mutex (MT50, 0x05)
        Mutex (MT60, 0x06)
        Mutex (MT70, 0x07)
        Mutex (MT80, 0x08)
        Mutex (MT90, 0x09)
        Mutex (MTA0, 0x0A)
        Mutex (MTB0, 0x0B)
        Mutex (MTC0, 0x0C)
        Mutex (MTD0, 0x0D)
        Mutex (MTE0, 0x0E)
        Mutex (MTF0, 0x0F)
        Method (M000, 1, Serialized)
        {
            If (Arg0)
            {
                I004 = 0x00
            }
            Else
            {
                I003 = 0x00
            }

            MM00 (0x01, I000, I001)
        }

        Method (M001, 1, Serialized, 1)
        {
            If (Arg0)
            {
                I004 = 0x01
            }
            Else
            {
                I003 = 0x01
            }

            MM00 (0x01, I000, I001)
        }

        Method (M002, 1, Serialized, 2)
        {
            If (Arg0)
            {
                I004 = 0x02
            }
            Else
            {
                I003 = 0x02
            }

            MM00 (0x01, I000, I001)
        }

        Method (M003, 1, Serialized, 3)
        {
            If (Arg0)
            {
                I004 = 0x03
            }
            Else
            {
                I003 = 0x03
            }

            MM00 (0x01, I000, I001)
        }

        Method (M004, 1, Serialized, 4)
        {
            If (Arg0)
            {
                I004 = 0x04
            }
            Else
            {
                I003 = 0x04
            }

            MM00 (0x01, I000, I001)
        }

        Method (M005, 1, Serialized, 5)
        {
            If (Arg0)
            {
                I004 = 0x05
            }
            Else
            {
                I003 = 0x05
            }

            MM00 (0x01, I000, I001)
        }

        Method (M006, 1, Serialized, 6)
        {
            If (Arg0)
            {
                I004 = 0x06
            }
            Else
            {
                I003 = 0x06
            }

            MM00 (0x01, I000, I001)
        }

        Method (M007, 1, Serialized, 7)
        {
            If (Arg0)
            {
                I004 = 0x07
            }
            Else
            {
                I003 = 0x07
            }

            MM00 (0x01, I000, I001)
        }

        Method (M008, 1, Serialized, 8)
        {
            If (Arg0)
            {
                I004 = 0x08
            }
            Else
            {
                I003 = 0x08
            }

            MM00 (0x01, I000, I001)
        }

        Method (M009, 1, Serialized, 9)
        {
            If (Arg0)
            {
                I004 = 0x09
            }
            Else
            {
                I003 = 0x09
            }

            MM00 (0x01, I000, I001)
        }

        Method (M010, 1, Serialized, 10)
        {
            If (Arg0)
            {
                I004 = 0x0A
            }
            Else
            {
                I003 = 0x0A
            }

            MM00 (0x01, I000, I001)
        }

        Method (M011, 1, Serialized, 11)
        {
            If (Arg0)
            {
                I004 = 0x0B
            }
            Else
            {
                I003 = 0x0B
            }

            MM00 (0x01, I000, I001)
        }

        Method (M012, 1, Serialized, 12)
        {
            If (Arg0)
            {
                I004 = 0x0C
            }
            Else
            {
                I003 = 0x0C
            }

            MM00 (0x01, I000, I001)
        }

        Method (M013, 1, Serialized, 13)
        {
            If (Arg0)
            {
                I004 = 0x0D
            }
            Else
            {
                I003 = 0x0D
            }

            MM00 (0x01, I000, I001)
        }

        Method (M014, 1, Serialized, 14)
        {
            If (Arg0)
            {
                I004 = 0x0E
            }
            Else
            {
                I003 = 0x0E
            }

            MM00 (0x01, I000, I001)
        }

        Method (M015, 1, Serialized, 15)
        {
            If (Arg0)
            {
                I004 = 0x0F
            }
            Else
            {
                I003 = 0x0F
            }

            MM00 (0x01, I000, I001)
        }

        Method (M100, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x10
            }
            Else
            {
                I003 = 0x10
            }

            Local0 = Acquire (MT00, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MT00)
            }
        }

        Method (M101, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x11
            }
            Else
            {
                I003 = 0x11
            }

            Local0 = Acquire (MT10, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MT10)
            }
        }

        Method (M102, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x12
            }
            Else
            {
                I003 = 0x12
            }

            Local0 = Acquire (MT20, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MT20)
            }
        }

        Method (M103, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x13
            }
            Else
            {
                I003 = 0x13
            }

            Local0 = Acquire (MT30, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MT30)
            }
        }

        Method (M104, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x14
            }
            Else
            {
                I003 = 0x14
            }

            Local0 = Acquire (MT40, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MT40)
            }
        }

        Method (M105, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x15
            }
            Else
            {
                I003 = 0x15
            }

            Local0 = Acquire (MT50, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MT50)
            }
        }

        Method (M106, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x16
            }
            Else
            {
                I003 = 0x16
            }

            Local0 = Acquire (MT60, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MT60)
            }
        }

        Method (M107, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x17
            }
            Else
            {
                I003 = 0x17
            }

            Local0 = Acquire (MT70, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MT70)
            }
        }

        Method (M108, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x18
            }
            Else
            {
                I003 = 0x18
            }

            Local0 = Acquire (MT80, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MT80)
            }
        }

        Method (M109, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x19
            }
            Else
            {
                I003 = 0x19
            }

            Local0 = Acquire (MT90, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MT90)
            }
        }

        Method (M110, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x1A
            }
            Else
            {
                I003 = 0x1A
            }

            Local0 = Acquire (MTA0, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MTA0)
            }
        }

        Method (M111, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x1B
            }
            Else
            {
                I003 = 0x1B
            }

            Local0 = Acquire (MTB0, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MTB0)
            }
        }

        Method (M112, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x1C
            }
            Else
            {
                I003 = 0x1C
            }

            Local0 = Acquire (MTC0, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MTC0)
            }
        }

        Method (M113, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x1D
            }
            Else
            {
                I003 = 0x1D
            }

            Local0 = Acquire (MTD0, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MTD0)
            }
        }

        Method (M114, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x1E
            }
            Else
            {
                I003 = 0x1E
            }

            Local0 = Acquire (MTE0, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MTE0)
            }
        }

        Method (M115, 2, NotSerialized)
        {
            If (Arg0)
            {
                I004 = 0x1F
            }
            Else
            {
                I003 = 0x1F
            }

            Local0 = Acquire (MTF0, 0xFFFF)
            MM00 (0x01, I000, I001)
            If (Arg1)
            {
                If (Local0)
                {
                    ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
            }

            If (!Local0)
            {
                Release (MTF0)
            }
        }

        /*
         * arg0 - 0 - first call, otherwise - non-first call
         * arg1 - level of first call
         * arg2 - level of second call
         */
        Method (MM00, 3, Serialized)
        {
            Local0 = I002 /* \M3BB.I002 */
            I002++
            If ((I002 > I005))
            {
                Return (Zero)
            }

            If (Arg0)
            {
                Local1 = Arg2
            }
            Else
            {
                Local1 = Arg1
            }

            If (Arg0)
            {
                /* non-first call */

                If ((Arg1 >= 0x10))
                {
                    Local2 = (Arg1 - 0x10)
                }
                Else
                {
                    Local2 = Arg1
                }

                If ((Arg2 >= 0x10))
                {
                    Local3 = (Arg2 - 0x10)
                }
                Else
                {
                    Local3 = Arg2
                }

                If ((Local2 > Local3))
                {
                    Local4 = 0x00
                }
                Else
                {
                    Local4 = 0x01 /* Check return of Acquire, success is expected */
                }
            }
            Else
            {
                /* first call */

                Local4 = 0x01 /* Check return of Acquire, success is expected */
            }

            Switch (ToInteger (Local1))
            {
                Case (0x00)
                {
                    M000 (Local0)
                }
                Case (0x01)
                {
                    M001 (Local0)
                }
                Case (0x02)
                {
                    M002 (Local0)
                }
                Case (0x03)
                {
                    M003 (Local0)
                }
                Case (0x04)
                {
                    M004 (Local0)
                }
                Case (0x05)
                {
                    M005 (Local0)
                }
                Case (0x06)
                {
                    M006 (Local0)
                }
                Case (0x07)
                {
                    M007 (Local0)
                }
                Case (0x08)
                {
                    M008 (Local0)
                }
                Case (0x09)
                {
                    M009 (Local0)
                }
                Case (0x0A)
                {
                    M010 (Local0)
                }
                Case (0x0B)
                {
                    M011 (Local0)
                }
                Case (0x0C)
                {
                    M012 (Local0)
                }
                Case (0x0D)
                {
                    M013 (Local0)
                }
                Case (0x0E)
                {
                    M014 (Local0)
                }
                Case (0x0F)
                {
                    M015 (Local0)
                }
                Case (0x10)
                {
                    M100 (Local0, Local4)
                }
                Case (0x11)
                {
                    M101 (Local0, Local4)
                }
                Case (0x12)
                {
                    M102 (Local0, Local4)
                }
                Case (0x13)
                {
                    M103 (Local0, Local4)
                }
                Case (0x14)
                {
                    M104 (Local0, Local4)
                }
                Case (0x15)
                {
                    M105 (Local0, Local4)
                }
                Case (0x16)
                {
                    M106 (Local0, Local4)
                }
                Case (0x17)
                {
                    M107 (Local0, Local4)
                }
                Case (0x18)
                {
                    M108 (Local0, Local4)
                }
                Case (0x19)
                {
                    M109 (Local0, Local4)
                }
                Case (0x1A)
                {
                    M110 (Local0, Local4)
                }
                Case (0x1B)
                {
                    M111 (Local0, Local4)
                }
                Case (0x1C)
                {
                    M112 (Local0, Local4)
                }
                Case (0x1D)
                {
                    M113 (Local0, Local4)
                }
                Case (0x1E)
                {
                    M114 (Local0, Local4)
                }
                Case (0x1F)
                {
                    M115 (Local0, Local4)
                }

            }
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
        I000 = Arg0
        I001 = Arg1
        I005 = Arg2
        MM00 (0x00, I000, I001)
        If ((Arg0 >= 0x10))
        {
            Local2 = (Arg0 - 0x10)
        }
        Else
        {
            Local2 = Arg0
        }

        If ((Arg1 >= 0x10))
        {
            Local3 = (Arg1 - 0x10)
        }
        Else
        {
            Local3 = Arg1
        }

        If ((Local2 > Local3))
        {
            Local4 = 0x00
        }
        Else
        {
            Local4 = 0x01 /* Success is expected, no exceptions */
        }

        If (!Local4)
        {
            CH04 (__METHOD__, 0x01, 0x40, Z173, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
        }
        Else
        {
            If ((I003 != Arg0))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I003, Arg0)
            }

            If ((I004 != Arg1))
            {
                ERR (__METHOD__, Z173, __LINE__, 0x00, 0x00, I004, Arg1)
            }
        }

        CH03 (__METHOD__, Z173, __LINE__, 0x00, 0x00)
    }

    Method (M3BC, 0, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        LPN0 = 0x20
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = 0x20
            LPC1 = 0x00
            While (LPN1)
            {
                M3BB (LPC0, LPC1, 0x02)
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    Method (M3BD, 0, NotSerialized)
    {
        SRMT ("m3b0")
        M3B0 ()
        SRMT ("m3b1")
        M3B1 ()
        SRMT ("m3b2")
        M3B2 ()
        SRMT ("m3b4")
        If (Y300)
        {
            M3B4 ()
        }
        Else
        {
            BLCK ()
        }

        SRMT ("m3b6")
        M3B6 ()
        SRMT ("m3b8")
        M3B8 ()
        SRMT ("m3b9")
        If (Y300)
        {
            M3B9 ()
        }
        Else
        {
            BLCK ()
        }

        SRMT ("m3ba")
        M3BA ()
        SRMT ("m3bc")
        If (Y300)
        {
            M3BC ()
        }
        Else
        {
            BLCK ()
        }
    }
