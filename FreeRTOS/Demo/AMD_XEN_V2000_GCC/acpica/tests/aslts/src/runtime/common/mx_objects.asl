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
     * Mutex
     *
     * declarations for common use
     */
    Name (MAX0, 0x10) /* Number of different Levels of mutexes */
    Name (HLMX, 0x0F) /* Highest Level of mutex */
    Name (MAX1, 0x12) /* Max number of mutexes of the same level */
    Name (UNIM, 0x12) /* Undefined index of mutex */
    Name (MAX2, Buffer (MAX0)
    {
        /* 0000 */  0x12, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0008 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04   // ........
    })
    /*
     * GLLL - Level of mutex for Global Lock.
     * GLIX - Index of mutex for Global Lock.
     *
     * The Global Lock in tests is represented as mutex of 0-th Level 1-th Index.
     */
    Name (GLLL, 0x00) /* Level of mutex for GL */
    Name (GLIX, 0x01) /* Index of mutex for GL */
    /*
     * Flag of Global lock.
     * If non-zero then actually the Global lock is used in tests
     * instead of the usual mutex T001 (of level 0 index 1).
     */
    Name (GL00, 0x00)
    Name (MIN0, 0x04)  /* Minimal number of mutexes of the same level in groups below */
    Name (MIN1, 0x05)  /* Minimal number of threads corresponding to min0 */
    /*
     * See TOV0 and TOV0 below,
     * all other opcodes of TimeOutValue correspond to 0xffff.
     */
    Name (TOV0, 0x05) /* opcode of TimeOutValue corresponding to 0 milliseconds */
    Name (TOV1, 0x06) /* opcode of TimeOutValue corresponding to 1 milliseconds */
    Name (TOVF, 0x00) /* opcode of TimeOutValue corresponding to 0xffff (endless) */
    /* Level 0 */

    Mutex (T000, 0x00)
    Mutex (T001, 0x00) /* used in case when the flag of the Global Lock (GL00) is zero */
    Mutex (T002, 0x00)
    Mutex (T003, 0x00)
    Mutex (T004, 0x00)
    Mutex (T005, 0x00)
    Mutex (T006, 0x00)
    Mutex (T007, 0x00)
    Mutex (T008, 0x00)
    Mutex (T009, 0x00)
    Mutex (T00A, 0x00)
    Mutex (T00B, 0x00)
    Mutex (T00C, 0x00)
    Mutex (T00D, 0x00)
    Mutex (T00E, 0x00)
    Mutex (T00F, 0x00)
    Mutex (T010, 0x00)
    Mutex (T011, 0x00)
    /* Level 1 */

    Mutex (T100, 0x01)
    Mutex (T101, 0x01)
    Mutex (T102, 0x01)
    Mutex (T103, 0x01)
    /* Level 2 */

    Mutex (T200, 0x02)
    Mutex (T201, 0x02)
    Mutex (T202, 0x02)
    Mutex (T203, 0x02)
    /* Level 3 */

    Mutex (T300, 0x03)
    Mutex (T301, 0x03)
    Mutex (T302, 0x03)
    Mutex (T303, 0x03)
    /* Level 4 */

    Mutex (T400, 0x04)
    Mutex (T401, 0x04)
    Mutex (T402, 0x04)
    Mutex (T403, 0x04)
    /* Level 5 */

    Mutex (T500, 0x05)
    Mutex (T501, 0x05)
    Mutex (T502, 0x05)
    Mutex (T503, 0x05)
    /* Level 6 */

    Mutex (T600, 0x06)
    Mutex (T601, 0x06)
    Mutex (T602, 0x06)
    Mutex (T603, 0x06)
    /* Level 7 */

    Mutex (T700, 0x07)
    Mutex (T701, 0x07)
    Mutex (T702, 0x07)
    Mutex (T703, 0x07)
    /* Level 8 */

    Mutex (T800, 0x08)
    Mutex (T801, 0x08)
    Mutex (T802, 0x08)
    Mutex (T803, 0x08)
    Mutex (T804, 0x08) /* used in functional/synchronization */
    Mutex (T805, 0x08) /* used in functional/synchronization */
    /* Level 9 */

    Mutex (T900, 0x09)
    Mutex (T901, 0x09)
    Mutex (T902, 0x09)
    Mutex (T903, 0x09)
    /* Level 10 */

    Mutex (TA00, 0x0A)
    Mutex (TA01, 0x0A)
    Mutex (TA02, 0x0A)
    Mutex (TA03, 0x0A)
    /* Level 11 */

    Mutex (TB00, 0x0B)
    Mutex (TB01, 0x0B)
    Mutex (TB02, 0x0B)
    Mutex (TB03, 0x0B)
    /* Level 12 */

    Mutex (TC00, 0x0C)
    Mutex (TC01, 0x0C)
    Mutex (TC02, 0x0C)
    Mutex (TC03, 0x0C)
    /* Level 13 */

    Mutex (TD00, 0x0D)
    Mutex (TD01, 0x0D)
    Mutex (TD02, 0x0D)
    Mutex (TD03, 0x0D)
    /* Level 14 */

    Mutex (TE00, 0x0E)
    Mutex (TE01, 0x0E)
    Mutex (TE02, 0x0E)
    Mutex (TE03, 0x0E)
    /* Level 15 */

    Mutex (TF00, 0x0F)
    Mutex (TF01, 0x0F)
    Mutex (TF02, 0x0F)
    Mutex (TF03, 0x0F)
    /*
     *
     * Methods to manage mutexes declared above
     *
     */
    /*
     * Set flag of Global lock
     *
     * arg0 - new value of flag of GL
     *
     * Return:
     *   old value of flag of GL
     */
    Method (M078, 1, NotSerialized)
    {
        Local7 = GL00 /* \GL00 */
        GL00 = Arg0
        Return (Local7)
    }

    /*
     * Acquire mutex of level 0
     *
     * arg0 - Index of mutex
     * arg1 - opcode of exception to be generated or zero
     * arg2 - opcode of TimeOutValue (unfortunately, ACPA doesn't allow TermArg there)
     *        0 - 0
     *        1 - 1
     *        otherwise - oxffff
     */
    Method (MA00, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (T000, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T000, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T000, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T000, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (GL00)
                {
                    If (Arg1)
                    {
                        Acquire (\_GL, 0xFFFF)
                    }
                    ElseIf ((Arg2 == TOV0))
                    {
                        Local0 = Acquire (\_GL, 0x0000)
                    }
                    ElseIf ((Arg2 == TOV1))
                    {
                        Local0 = Acquire (\_GL, 0x0001)
                    }
                    Else
                    {
                        Local0 = Acquire (\_GL, 0xFFFF)
                    }
                }
                ElseIf (Arg1)
                {
                    Acquire (T001, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T001, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T001, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T001, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (T002, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T002, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T002, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T002, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (T003, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T003, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T003, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T003, 0xFFFF)
                }
            }
            Case (0x04)
            {
                If (Arg1)
                {
                    Acquire (T004, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T004, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T004, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T004, 0xFFFF)
                }
            }
            Case (0x05)
            {
                If (Arg1)
                {
                    Acquire (T005, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T005, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T005, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T005, 0xFFFF)
                }
            }
            Case (0x06)
            {
                If (Arg1)
                {
                    Acquire (T006, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T006, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T006, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T006, 0xFFFF)
                }
            }
            Case (0x07)
            {
                If (Arg1)
                {
                    Acquire (T007, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T007, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T007, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T007, 0xFFFF)
                }
            }
            Case (0x08)
            {
                If (Arg1)
                {
                    Acquire (T008, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T008, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T008, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T008, 0xFFFF)
                }
            }
            Case (0x09)
            {
                If (Arg1)
                {
                    Acquire (T009, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T009, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T009, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T009, 0xFFFF)
                }
            }
            Case (0x0A)
            {
                If (Arg1)
                {
                    Acquire (T00A, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T00A, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T00A, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T00A, 0xFFFF)
                }
            }
            Case (0x0B)
            {
                If (Arg1)
                {
                    Acquire (T00B, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T00B, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T00B, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T00B, 0xFFFF)
                }
            }
            Case (0x0C)
            {
                If (Arg1)
                {
                    Acquire (T00C, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T00C, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T00C, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T00C, 0xFFFF)
                }
            }
            Case (0x0D)
            {
                If (Arg1)
                {
                    Acquire (T00D, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T00D, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T00D, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T00D, 0xFFFF)
                }
            }
            Case (0x0E)
            {
                If (Arg1)
                {
                    Acquire (T00E, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T00E, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T00E, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T00E, 0xFFFF)
                }
            }
            Case (0x0F)
            {
                If (Arg1)
                {
                    Acquire (T00F, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T00F, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T00F, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T00F, 0xFFFF)
                }
            }
            Case (0x10)
            {
                If (Arg1)
                {
                    Acquire (T010, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T010, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T010, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T010, 0xFFFF)
                }
            }
            Case (0x11)
            {
                If (Arg1)
                {
                    Acquire (T011, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T011, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T011, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T011, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 1
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA01, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (T100, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T100, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T100, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T100, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (T101, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T101, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T101, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T101, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (T102, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T102, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T102, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T102, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (T103, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T103, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T103, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T103, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 2
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA02, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (T200, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T200, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T200, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T200, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (T201, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T201, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T201, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T201, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (T202, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T202, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T202, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T202, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (T203, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T203, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T203, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T203, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 3
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA03, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (T300, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T300, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T300, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T300, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (T301, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T301, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T301, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T301, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (T302, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T302, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T302, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T302, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (T303, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T303, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T303, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T303, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 4
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA04, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (T400, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T400, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T400, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T400, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (T401, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T401, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T401, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T401, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (T402, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T402, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T402, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T402, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (T403, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T403, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T403, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T403, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 5
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA05, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (T500, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T500, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T500, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T500, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (T501, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T501, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T501, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T501, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (T502, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T502, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T502, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T502, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (T503, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T503, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T503, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T503, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 6
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA06, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (T600, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T600, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T600, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T600, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (T601, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T601, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T601, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T601, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (T602, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T602, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T602, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T602, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (T603, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T603, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T603, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T603, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 7
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA07, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (T700, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T700, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T700, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T700, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (T701, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T701, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T701, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T701, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (T702, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T702, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T702, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T702, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (T703, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T703, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T703, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T703, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 8
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA08, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (T800, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T800, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T800, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T800, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (T801, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T801, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T801, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T801, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (T802, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T802, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T802, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T802, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (T803, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T803, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T803, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T803, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 9
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA09, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (T900, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T900, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T900, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T900, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (T901, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T901, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T901, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T901, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (T902, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T902, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T902, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T902, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (T903, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (T903, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (T903, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (T903, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 10
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA0A, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (TA00, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TA00, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TA00, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TA00, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (TA01, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TA01, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TA01, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TA01, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (TA02, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TA02, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TA02, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TA02, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (TA03, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TA03, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TA03, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TA03, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 11
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA0B, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (TB00, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TB00, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TB00, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TB00, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (TB01, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TB01, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TB01, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TB01, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (TB02, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TB02, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TB02, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TB02, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (TB03, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TB03, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TB03, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TB03, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 12
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA0C, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (TC00, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TC00, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TC00, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TC00, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (TC01, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TC01, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TC01, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TC01, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (TC02, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TC02, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TC02, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TC02, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (TC03, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TC03, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TC03, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TC03, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 13
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA0D, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (TD00, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TD00, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TD00, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TD00, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (TD01, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TD01, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TD01, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TD01, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (TD02, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TD02, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TD02, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TD02, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (TD03, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TD03, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TD03, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TD03, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 14
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA0E, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (TE00, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TE00, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TE00, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TE00, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (TE01, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TE01, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TE01, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TE01, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (TE02, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TE02, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TE02, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TE02, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (TE03, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TE03, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TE03, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TE03, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Acquire mutex of level 15
     * (Index of mux, opcode of exception to be generated or zero, opcode of TimeOutValue)
     */
    Method (MA0F, 3, Serialized)
    {
        Local0 = 0x01
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                If (Arg1)
                {
                    Acquire (TF00, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TF00, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TF00, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TF00, 0xFFFF)
                }
            }
            Case (0x01)
            {
                If (Arg1)
                {
                    Acquire (TF01, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TF01, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TF01, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TF01, 0xFFFF)
                }
            }
            Case (0x02)
            {
                If (Arg1)
                {
                    Acquire (TF02, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TF02, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TF02, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TF02, 0xFFFF)
                }
            }
            Case (0x03)
            {
                If (Arg1)
                {
                    Acquire (TF03, 0xFFFF)
                }
                ElseIf ((Arg2 == TOV0))
                {
                    Local0 = Acquire (TF03, 0x0000)
                }
                ElseIf ((Arg2 == TOV1))
                {
                    Local0 = Acquire (TF03, 0x0001)
                }
                Else
                {
                    Local0 = Acquire (TF03, 0xFFFF)
                }
            }

        }

        Return (Local0)
    }

    /*
     * Release mutex of level 0
     *
     * arg0 - Index of mutex
     */
    Method (MA10, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (T000)
            }
            Case (0x01)
            {
                If (GL00)
                {
                    Release (\_GL)
                }
                Else
                {
                    Release (T001)
                }
            }
            Case (0x02)
            {
                Release (T002)
            }
            Case (0x03)
            {
                Release (T003)
            }
            Case (0x04)
            {
                Release (T004)
            }
            Case (0x05)
            {
                Release (T005)
            }
            Case (0x06)
            {
                Release (T006)
            }
            Case (0x07)
            {
                Release (T007)
            }
            Case (0x08)
            {
                Release (T008)
            }
            Case (0x09)
            {
                Release (T009)
            }
            Case (0x0A)
            {
                Release (T00A)
            }
            Case (0x0B)
            {
                Release (T00B)
            }
            Case (0x0C)
            {
                Release (T00C)
            }
            Case (0x0D)
            {
                Release (T00D)
            }
            Case (0x0E)
            {
                Release (T00E)
            }
            Case (0x0F)
            {
                Release (T00F)
            }
            Case (0x10)
            {
                Release (T010)
            }
            Case (0x11)
            {
                Release (T011)
            }

        }
    }

    /*
     * Release mutex of level 1 (Index of mux)
     */
    Method (MA11, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (T100)
            }
            Case (0x01)
            {
                Release (T101)
            }
            Case (0x02)
            {
                Release (T102)
            }
            Case (0x03)
            {
                Release (T103)
            }

        }
    }

    /*
     * Release mutex of level 2 (Index of mux)
     */
    Method (MA12, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (T200)
            }
            Case (0x01)
            {
                Release (T201)
            }
            Case (0x02)
            {
                Release (T202)
            }
            Case (0x03)
            {
                Release (T203)
            }

        }
    }

    /*
     * Release mutex of level 3 (Index of mux)
     */
    Method (MA13, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (T300)
            }
            Case (0x01)
            {
                Release (T301)
            }
            Case (0x02)
            {
                Release (T302)
            }
            Case (0x03)
            {
                Release (T303)
            }

        }
    }

    /*
     * Release mutex of level 4 (Index of mux)
     */
    Method (MA14, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (T400)
            }
            Case (0x01)
            {
                Release (T401)
            }
            Case (0x02)
            {
                Release (T402)
            }
            Case (0x03)
            {
                Release (T403)
            }

        }
    }

    /*
     * Release mutex of level 5 (Index of mux)
     */
    Method (MA15, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (T500)
            }
            Case (0x01)
            {
                Release (T501)
            }
            Case (0x02)
            {
                Release (T502)
            }
            Case (0x03)
            {
                Release (T503)
            }

        }
    }

    /*
     * Release mutex of level 6 (Index of mux)
     */
    Method (MA16, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (T600)
            }
            Case (0x01)
            {
                Release (T601)
            }
            Case (0x02)
            {
                Release (T602)
            }
            Case (0x03)
            {
                Release (T603)
            }

        }
    }

    /*
     * Release mutex of level 7 (Index of mux)
     */
    Method (MA17, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (T700)
            }
            Case (0x01)
            {
                Release (T701)
            }
            Case (0x02)
            {
                Release (T702)
            }
            Case (0x03)
            {
                Release (T703)
            }

        }
    }

    /*
     * Release mutex of level 8 (Index of mux)
     */
    Method (MA18, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (T800)
            }
            Case (0x01)
            {
                Release (T801)
            }
            Case (0x02)
            {
                Release (T802)
            }
            Case (0x03)
            {
                Release (T803)
            }

        }
    }

    /*
     * Release mutex of level 9 (Index of mux)
     */
    Method (MA19, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (T900)
            }
            Case (0x01)
            {
                Release (T901)
            }
            Case (0x02)
            {
                Release (T902)
            }
            Case (0x03)
            {
                Release (T903)
            }

        }
    }

    /*
     * Release mutex of level 10 (Index of mux)
     */
    Method (MA1A, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (TA00)
            }
            Case (0x01)
            {
                Release (TA01)
            }
            Case (0x02)
            {
                Release (TA02)
            }
            Case (0x03)
            {
                Release (TA03)
            }

        }
    }

    /*
     * Release mutex of level 11 (Index of mux)
     */
    Method (MA1B, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (TB00)
            }
            Case (0x01)
            {
                Release (TB01)
            }
            Case (0x02)
            {
                Release (TB02)
            }
            Case (0x03)
            {
                Release (TB03)
            }

        }
    }

    /*
     * Release mutex of level 12 (Index of mux)
     */
    Method (MA1C, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (TC00)
            }
            Case (0x01)
            {
                Release (TC01)
            }
            Case (0x02)
            {
                Release (TC02)
            }
            Case (0x03)
            {
                Release (TC03)
            }

        }
    }

    /*
     * Release mutex of level 13 (Index of mux)
     */
    Method (MA1D, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (TD00)
            }
            Case (0x01)
            {
                Release (TD01)
            }
            Case (0x02)
            {
                Release (TD02)
            }
            Case (0x03)
            {
                Release (TD03)
            }

        }
    }

    /*
     * Release mutex of level 14 (Index of mux)
     */
    Method (MA1E, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (TE00)
            }
            Case (0x01)
            {
                Release (TE01)
            }
            Case (0x02)
            {
                Release (TE02)
            }
            Case (0x03)
            {
                Release (TE03)
            }

        }
    }

    /*
     * Release mutex of level 15 (Index of mux)
     */
    Method (MA1F, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Release (TF00)
            }
            Case (0x01)
            {
                Release (TF01)
            }
            Case (0x02)
            {
                Release (TF02)
            }
            Case (0x03)
            {
                Release (TF03)
            }

        }
    }

    /*
     * Get name of mutex
     *
     * arg0 - string
     * arg1 - Level of mutex
     * arg2 - Index of mutex
     */
    Method (M21E, 3, NotSerialized)
    {
        Concatenate (Arg0, "Level ", Local0)
        Concatenate (Local0, Arg1, Local1)
        Concatenate (Local1, ", Index ", Local0)
        Concatenate (Local0, Arg2, Local1)
        If ((Arg1 == GLLL))
        {
            If ((Arg2 == GLIX))
            {
                If (GL00)
                {
                    Concatenate (Local1, " (Global lock)", Local1)
                }
            }
        }

        Return (Local1)
    }
