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
    /*  ///////////////////////////////////////////////////////////////////////// */
    /*  0 - Acquire                (arg0, arg1)                         => Local7 */
    /*  1 - Add                    (arg0, arg1, RES)                    => Local7 */
    /*  2 - And                    (arg0, arg1, RES)                    => Local7 */
    /*  3 - Concatenate            (arg0, arg1, RES)                    => Local7 */
    /*  4 - ConcatenateResTemplate (arg0, arg1, RES)                    => Local7 */
    /*  5 - CondRefOf              (arg0, RES)                          => Local7 */
    /*  6 - CopyObject             (arg0, RES)                          => Local7 */
    /*  7 - Decrement              (arg0 --> RES)                       => Local7 */
    /*  8 - DerefOf                (arg0)                               => Local7 */
    /*  9 - Divide                 (arg0, arg1, RES, RES)               => Local7 */
    /* 10 - Fatal                  (arg0, arg1, arg2) */
    /* 11 - FindSetLeftBit         (arg0, RES)                          => Local7 */
    /* 12 - FindSetRightBit        (arg0, RES)                          => Local7 */
    /* 13 - FromBCD                (arg0, RES)                          => Local7 */
    /* 14 - Increment              (arg0 --> RES)                       => Local7 */
    /* 15 - Index                  (arg0, arg1, RES)                    => Local7 */
    /* 16 - LAnd                   (arg0, arg1)                         => Local7 */
    /* 17 - LEqual                 (arg0, arg1)                         => Local7 */
    /* 18 - LGreater               (arg0, arg1)                         => Local7 */
    /* 19 - LGreaterEqual          (arg0, arg1)                         => Local7 */
    /* 20 - LLess                  (arg0, arg1)                         => Local7 */
    /* 21 - LLessEqual             (arg0, arg1)                         => Local7 */
    /* 22 - LNot                   (arg0)                               => Local7 */
    /* 23 - LNotEqual              (arg0, arg1)                         => Local7 */
    /* 24 - LOr                    (arg0, arg1)                         => Local7 */
    /* 25 - Match    <arg1-O1,O2>  (arg0, <O1>, arg2, <O2>, arg3, arg4) => Local7 */
    /* 26 - Mid                    (arg0, arg1, arg2, RES)              => Local7 */
    /* 27 - Mod                    (arg0, arg1, RES)                    => Local7 */
    /* 28 - Multiply               (arg0, arg1, RES)                    => Local7 */
    /* 29 - NAnd                   (arg0, arg1, RES)                    => Local7 */
    /* 30 - NOr                    (arg0, arg1, RES)                    => Local7 */
    /* 31 - Not                    (arg0, RES)                          => Local7 */
    /* 32 - ObjectType             (arg0)                               => Local7 */
    /* 33 - Or                     (arg0, arg1, RES)                    => Local7 */
    /* 34 - RefOf                  (arg0)                               => Local7 */
    /* 35 - Release                (arg0) */
    /* 36 - Reset                  (arg0) */
    /* 37 - Return                 (arg0) */
    /* 38 - ShiftLeft              (arg0, arg1, RES)                    => Local7 */
    /* 39 - ShiftRight             (arg0, arg1, RES)                    => Local7 */
    /* 40 - Signal                 (arg0) */
    /* 41 - SizeOf                 (arg0)                               => Local7 */
    /* 42 - Sleep                  (arg0) */
    /* 43 - Stall                  (arg0) */
    /* 44 - Store                  (arg0, RES)                          => Local7 */
    /* 45 - Subtract               (arg0, arg1, RES)                    => Local7 */
    /* 46 - ToBCD                  (arg0, RES)                          => Local7 */
    /* 47 - ToBuffer               (arg0, RES)                          => Local7 */
    /* 48 - ToDecimalString        (arg0, RES)                          => Local7 */
    /* 49 - ToHexString            (arg0, RES)                          => Local7 */
    /* 50 - ToInteger              (arg0, RES)                          => Local7 */
    /* 51 - ToString               (arg0, arg1, RES)                    => Local7 */
    /* 52 - Wait                   (arg0, arg1)                         => Local7 */
    /* 53 - XOr                    (arg0, arg1, RES)                    => Local7 */
    /* ////////////////////////////////////////////////////////////////////////// */
    Name (Z082, 0x52)
    /* Flag - verify result with the contents of Package */

    Name (FLG2, 0x3859A0D4)
    /* Flag - it is expected that operation will cause exception */

    Name (FLG3, 0x00)
    /* Flag - don't do further checkings */

    Name (FLG4, 0x00)
    /* Collect calls to all operators */
    /* */
    /* arg0-arg4 - parameters of operators */
    /* arg5      - miscellaneous */
    /* arg6      - opcode of operation */
    Method (M480, 7, Serialized)
    {
        Name (TS, "m480")
        Name (PR00, 0x00)
        Name (PR01, 0x00)
        Name (CHK0, 0x01)
        Name (RES0, 0x00)
        Name (RES1, 0x00)
        Name (RES2, 0x00)
        If ((Arg5 == FLG2))
        {
            CHK0 = 0x00
        }

        If (CHK0)
        {
            Name (TMP0, 0x00)
            Name (TMP1, 0x00)
            Name (OT00, 0x00)
            Name (OT01, 0x00)
            Name (OT02, 0x00)
            Name (OT03, 0x00)
            Name (OT04, 0x00)
            Name (OT05, 0x00)
            Name (OT06, 0x00)
            OT00 = ObjectType (Arg0)
            OT01 = ObjectType (Arg1)
            OT02 = ObjectType (Arg2)
            OT03 = ObjectType (Arg3)
            OT04 = ObjectType (Arg4)
            OT05 = ObjectType (Arg5)
            OT06 = ObjectType (Arg6)
            Local0 = Arg0
            Local1 = Arg1
            Local2 = Arg2
            Local3 = Arg3
            Local4 = Arg4
            Local5 = Arg5
            Local6 = Arg6
            Name (OT10, 0x00)
            Name (OT11, 0x00)
            Name (OT12, 0x00)
            Name (OT13, 0x00)
            Name (OT14, 0x00)
            Name (OT15, 0x00)
            Name (OT16, 0x00)
            OT10 = ObjectType (Local0)
            OT11 = ObjectType (Local1)
            OT12 = ObjectType (Local2)
            OT13 = ObjectType (Local3)
            OT14 = ObjectType (Local4)
            OT15 = ObjectType (Local5)
            OT16 = ObjectType (Local6)
        } /* if(chk0) */

        Local7 = 0x00
        If (PR00)
        {
            Debug = "===================== m480, Start:"
            Debug = Arg0
            Debug = Arg1
            Debug = Arg2
            Debug = Arg3
            Debug = Arg4
            Debug = Arg5
            Debug = Arg6
            If (CHK0)
            {
                Debug = "--------"
                Debug = Local0
                Debug = Local1
                Debug = Local2
                Debug = Local3
                Debug = Local4
                Debug = Local5
                Debug = Local6
                Debug = Local7
            }

            Debug = "=====================."
        }

        Switch (ToInteger (Arg6))
        {
            Case (0x00)
            {
                Local7 = Acquire (Arg0, 0x0064)
            }
            Case (0x01)
            {
                RES0 = 0x01
                Local7 = Arg5 = (Arg0 + Arg1)
            }
            Case (0x02)
            {
                RES0 = 0x01
                Local7 = Arg5 = (Arg0 & Arg1)
            }
            Case (0x03)
            {
                RES0 = 0x01
                Local7 = Concatenate (Arg0, Arg1, Arg5)
            }
            Case (0x04)
            {
                RES0 = 0x01
                Local7 = ConcatenateResTemplate (Arg0, Arg1, Arg5)
            }
            Case (0x05)
            {
                RES2 = 0x01
                Local7 = CondRefOf (Arg0, Arg5)
            }
            Case (0x06)
            {
                RES0 = 0x01
                Local7 = CopyObject (Arg0, Arg5)
            }
            Case (0x07)
            {
                RES0 = 0x01
                Arg5 = Arg0
                Local7 = Arg5--
            }
            Case (0x08)
            {
                Local7 = DerefOf (Arg0)
            }
            Case (0x09)
            {
                RES0 = 0x01
                RES1 = 0x01
                Local7 = Divide (Arg0, Arg1, Arg2, Arg5)
            }
            Case (0x0A)
            {
                Fatal (0xFF, 0xFFFFFFFF, Arg0)
            }
            Case (0x0B)
            {
                RES0 = 0x01
                Local7 = FindSetLeftBit (Arg0, Arg5)
            }
            Case (0x0C)
            {
                RES0 = 0x01
                Local7 = FindSetRightBit (Arg0, Arg5)
            }
            Case (0x0D)
            {
                RES0 = 0x01
                Local7 = FromBCD (Arg0, Arg5)
            }
            Case (0x0E)
            {
                RES0 = 0x01
                Arg5 = Arg0
                Local7 = Arg5++
            }
            Case (0x0F)
            {
                RES0 = 0x01
                Local7 = Arg5 = Arg0 [Arg1]
            }
            Case (0x10)
            {
                Local7 = (Arg0 && Arg1)
            }
            Case (0x11)
            {
                Local7 = (Arg0 == Arg1)
            }
            Case (0x12)
            {
                Local7 = (Arg0 > Arg1)
            }
            Case (0x13)
            {
                Local7 = (Arg0 >= Arg1)
            }
            Case (0x14)
            {
                Local7 = (Arg0 < Arg1)
            }
            Case (0x15)
            {
                Local7 = (Arg0 <= Arg1)
            }
            Case (0x16)
            {
                Local7 = !Arg0
            }
            Case (0x17)
            {
                Local7 = (Arg0 != Arg1)
            }
            Case (0x18)
            {
                Local7 = (Arg0 || Arg1)
            }
            Case (0x19)
            {
                /* arg1 - determine OP1 and OP2 */

                Local7 = Match (Arg0, MTR, Arg2, MTR, Arg3, Arg4)
            }
            Case (0x1A)
            {
                RES0 = 0x01
                Local7 = Mid (Arg0, Arg1, Arg2, Arg5)
            }
            Case (0x1B)
            {
                RES0 = 0x01
                Local7 = Arg5 = (Arg0 % Arg1)
            }
            Case (0x1C)
            {
                RES0 = 0x01
                Local7 = Arg5 = (Arg0 * Arg1)
            }
            Case (0x1D)
            {
                RES0 = 0x01
                Local7 = NAnd (Arg0, Arg1, Arg5)
            }
            Case (0x1E)
            {
                RES0 = 0x01
                Local7 = NOr (Arg0, Arg1, Arg5)
            }
            Case (0x1F)
            {
                RES0 = 0x01
                Local7 = Arg5 = ~Arg0
            }
            Case (0x20)
            {
                Local7 = ObjectType (Arg0)
            }
            Case (0x21)
            {
                RES0 = 0x01
                Local7 = Arg5 = (Arg0 | Arg1)
            }
            Case (0x22)
            {
                Local7 = RefOf (Arg0)
            }
            Case (0x23)
            {
                Release (Arg0)
            }
            Case (0x24)
            {
                Reset (Arg0)
            }
            Case (0x25)
            {
                Return (Arg0)
            }
            Case (0x26)
            {
                RES0 = 0x01
                Local7 = Arg5 = (Arg0 << Arg1)
            }
            Case (0x27)
            {
                RES0 = 0x01
                Local7 = Arg5 = (Arg0 >> Arg1)
            }
            Case (0x28)
            {
                Signal (Arg0)
            }
            Case (0x29)
            {
                Local7 = SizeOf (Arg0)
            }
            Case (0x2A)
            {
                Sleep (Arg0)
            }
            Case (0x2B)
            {
                Stall (Arg0)
            }
            Case (0x2C)
            {
                RES0 = 0x01
                Local7 = Arg5 = Arg0
            }
            Case (0x2D)
            {
                RES0 = 0x01
                Local7 = Arg5 = (Arg0 - Arg1)
            }
            Case (0x2E)
            {
                RES0 = 0x01
                Local7 = ToBCD (Arg0, Arg5)
            }
            Case (0x2F)
            {
                RES0 = 0x01
                Local7 = ToBuffer (Arg0, Arg5)
            }
            Case (0x30)
            {
                RES0 = 0x01
                Local7 = ToDecimalString (Arg0, Arg5)
            }
            Case (0x31)
            {
                RES0 = 0x01
                Local7 = ToHexString (Arg0, Arg5)
            }
            Case (0x32)
            {
                RES0 = 0x01
                Local7 = ToInteger (Arg0, Arg5)
            }
            Case (0x33)
            {
                RES0 = 0x01
                Local7 = ToString (Arg0, Arg1, Arg5)
            }
            Case (0x34)
            {
                Local7 = Wait (Arg0, Arg1)
            }
            Case (0x35)
            {
                RES0 = 0x01
                Local7 = Arg5 = (Arg0 ^ Arg1)
            }
            Default
            {
                Debug = "Param error 0"
                Local0 = 0x01
                Local1 = 0x00
                Divide (Local0, Local1, Local2, Local3)
            }

        }

        If (FLG3)
        {
            /* It was expected that operation will cause exception. */
            /* We verify only the presence of exception. */
            /* Nothing to do more. */
            Return (0x01)
        }

        If (FLG4)
        {
            /* Don't do further checkings. */

            Return (0x01)
        }

        If (CHK0)
        {
            /* Types of ArgX are save */

            TMP0 = ObjectType (Arg0)
            If ((TMP0 != OT00))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT00)
            }

            TMP0 = ObjectType (Arg1)
            If ((TMP0 != OT01))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT01)
            }

            TMP0 = ObjectType (Arg2)
            If ((TMP0 != OT02))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT02)
            }

            TMP0 = ObjectType (Arg3)
            If ((TMP0 != OT03))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT03)
            }

            TMP0 = ObjectType (Arg4)
            If ((TMP0 != OT04))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT04)
            }

            If (RES0)
            {
                TMP0 = ObjectType (Arg5)
                If ((TMP0 != OT05))
                {
                    ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT05)
                }
            }

            TMP0 = ObjectType (Arg6)
            If ((TMP0 != OT06))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT06)
            }

            /* Types of LocalX are save, and data of LocalX and ArgX are identical */

            TMP0 = ObjectType (Local0)
            If ((TMP0 != OT10))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT10)
            }
            Else
            {
                M481 (TS, 0x08, TMP0, Local0, Arg0)
            }

            TMP0 = ObjectType (Local1)
            If ((TMP0 != OT11))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT11)
            }
            Else
            {
                M481 (TS, 0x0A, TMP0, Local1, Arg1)
            }

            If (RES1)
            {
                TMP0 = ObjectType (Local2)
                If ((TMP0 != OT12))
                {
                    ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT12)
                }
                Else
                {
                    M481 (TS, 0x0C, TMP0, Local2, Arg2)
                }
            }

            TMP0 = ObjectType (Local3)
            If ((TMP0 != OT13))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT13)
            }
            Else
            {
                M481 (TS, 0x0E, TMP0, Local3, Arg3)
            }

            TMP0 = ObjectType (Local4)
            If ((TMP0 != OT14))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT14)
            }
            Else
            {
                M481 (TS, 0x10, TMP0, Local4, Arg4)
            }

            TMP0 = ObjectType (Local5)
            If ((TMP0 != OT15))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT15)
            }
            ElseIf (RES0)
            {
                M481 (TS, 0x12, TMP0, Local5, Arg5)
            }

            TMP0 = ObjectType (Local6)
            If ((TMP0 != OT16))
            {
                ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT16)
            }
            Else
            {
                M481 (TS, 0x14, TMP0, Local6, Arg6)
            }

            If (RES2)
            {
                If ((Local7 != Ones))
                {
                    ERR (TS, Z082, __LINE__, 0x00, 0x00, Local7, Ones)
                }
            }
            ElseIf (RES0)
            {
                TMP0 = ObjectType (Local7)
                TMP1 = ObjectType (Arg5)
                If ((TMP0 != TMP1))
                {
                    ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, TMP1)
                }
                Else
                {
                    M481 (TS, 0x17, TMP0, Local7, Arg5)
                }
            }
        } /* if(chk0) */

        If (PR01)
        {
            Debug = "===================== m480, Finish:"
            Debug = Arg0
            Debug = Arg1
            Debug = Arg2
            Debug = Arg3
            Debug = Arg4
            Debug = Arg5
            Debug = Arg6
            If (CHK0)
            {
                Debug = "--------"
                Debug = Local0
                Debug = Local1
                Debug = Local2
                Debug = Local3
                Debug = Local4
                Debug = Local5
                Debug = Local6
                Debug = Local7
            }

            Debug = "=====================."
        }

        Return (Local7)
    }

    /* Compare the contents of arg3 and arg4, arg2 - the type of objects */

    Method (M481, 5, Serialized)
    {
        Local0 = 0x00
        Switch (ToInteger (Arg2))
        {
            Case (0x01)
            {
                If ((Arg3 != Arg4))
                {
                    ERR (Arg0, Z082, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Local0 = 0x01
                }
            }
            Case (0x02)
            {
                If ((Arg3 != Arg4))
                {
                    ERR (Arg0, Z082, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Local0 = 0x01
                }
            }
            Case (0x03)
            {
                If ((Arg3 != Arg4))
                {
                    ERR (Arg0, Z082, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Local0 = 0x01
                }
            }

        }

        If (Local0)
        {
            Debug = Arg3
            Debug = Arg4
        }
    }

    /* Layer for checking referencies */
    /* */
    /* arg0-arg4 - parameters of operators */
    /* arg5      - miscellaneous */
    /* arg6      - opcode of operation */
    Method (M482, 7, Serialized)
    {
        /*///////////////// */
        /* */
        /* !!!!!!!!!!!!!!  ?????????????????????????????????????? */
        /* */
        /* Looks like a bug - why this construction is impossible: */
        /* */
        /*	Name(OT11, ObjectType(arg0)) */
        /*	Name(a000, arg0) */
        /*///////////////// */
        Name (TS, "m482")
        Name (PK06, 0x00)
        Name (TMP0, 0x00)
        Name (OT00, 0x00)
        Name (OT01, 0x00)
        Name (OT02, 0x00)
        Name (OT03, 0x00)
        Name (OT04, 0x00)
        Name (OT05, 0x00)
        Name (OT06, 0x00)
        OT00 = ObjectType (Arg0)
        OT01 = ObjectType (Arg1)
        OT02 = ObjectType (Arg2)
        OT03 = ObjectType (Arg3)
        OT04 = ObjectType (Arg4)
        OT05 = ObjectType (Arg5)
        OT06 = ObjectType (Arg6)
        /* Operation */

        OT06 = ObjectType (Arg6)
        If ((OT06 == 0x04))
        {
            Local6 = DerefOf (Arg6 [0x00])
            PK06 = 0x01
        }
        Else
        {
            Local6 = Arg6
        }

        Local0 = Arg0
        Local1 = Arg1
        Local2 = Arg2
        Local3 = Arg3
        Local4 = Arg4
        Local5 = Arg5
        /*	Store(arg6, Local6) */

        Local7 = Arg6
        Name (OT10, 0x00)
        Name (OT11, 0x00)
        Name (OT12, 0x00)
        Name (OT13, 0x00)
        Name (OT14, 0x00)
        Name (OT15, 0x00)
        Name (OT16, 0x00)
        OT10 = ObjectType (Local0)
        OT11 = ObjectType (Local1)
        OT12 = ObjectType (Local2)
        OT13 = ObjectType (Local3)
        OT14 = ObjectType (Local4)
        OT15 = ObjectType (Local5)
        OT16 = ObjectType (Local6)
        Local7 = M480 (Local0, Local1, Local2, Local3, Local4, Local5, Local6)
        /* Types of ArgX are save */

        TMP0 = ObjectType (Arg0)
        If ((TMP0 != OT00))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT00)
        }

        TMP0 = ObjectType (Arg1)
        If ((TMP0 != OT01))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT01)
        }

        TMP0 = ObjectType (Arg2)
        If ((TMP0 != OT02))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT02)
        }

        TMP0 = ObjectType (Arg3)
        If ((TMP0 != OT03))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT03)
        }

        TMP0 = ObjectType (Arg4)
        If ((TMP0 != OT04))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT04)
        }

        TMP0 = ObjectType (Arg5)
        If ((TMP0 != OT05))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT05)
        }

        TMP0 = ObjectType (Arg6)
        If ((TMP0 != OT06))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT06)
        }

        /* Types of LocalX are save, and data of LocalX and ArgX are identical */

        TMP0 = ObjectType (Local0)
        If ((TMP0 != OT10))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT10)
        }
        Else
        {
            M481 (TS, 0x23, TMP0, Local0, Arg0)
        }

        TMP0 = ObjectType (Local1)
        If ((TMP0 != OT11))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT11)
        }
        Else
        {
            M481 (TS, 0x25, TMP0, Local1, Arg1)
        }

        TMP0 = ObjectType (Local2)
        If ((TMP0 != OT12))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT12)
        }
        Else
        {
            M481 (TS, 0x27, TMP0, Local2, Arg2)
        }

        TMP0 = ObjectType (Local3)
        If ((TMP0 != OT13))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT13)
        }
        Else
        {
            M481 (TS, 0x29, TMP0, Local3, Arg3)
        }

        TMP0 = ObjectType (Local4)
        If ((TMP0 != OT14))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT14)
        }
        Else
        {
            M481 (TS, 0x2B, TMP0, Local4, Arg4)
        }

        TMP0 = ObjectType (Local5)
        If ((TMP0 != OT15))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT15)
        }
        Else
        {
            M481 (TS, 0x2D, TMP0, Local5, Arg5)
        }

        TMP0 = ObjectType (Local6)
        If ((TMP0 != OT16))
        {
            ERR (TS, Z082, __LINE__, 0x00, 0x00, TMP0, OT16)
        }
        /* Package is passed by arg6 */
        /* m481(ts, 47, tmp0, Local6, arg6) */
        Else
        {
        }

        If (PK06)
        {
            /* SEE: either to remove this ability??????????????????? */
            /* Presence of result */
            Local0 = DerefOf (Arg6 [0x01])
            If (Local0)
            {
                /* Type of result */

                Local0 = DerefOf (Arg6 [0x02])
                /* Result */

                Local1 = DerefOf (Arg6 [0x03])
                Local2 = ObjectType (Local7)
                Local3 = 0x00
                If ((Local2 != Local0))
                {
                    ERR (TS, Z082, __LINE__, 0x00, 0x00, 0x00, 0x00)
                    Debug = "Expected type of result:"
                    Debug = Local0
                    Debug = "The type of obtained result:"
                    Debug = Local2
                    Local3 = 0x01
                }
                ElseIf ((Local7 != Local1))
                {
                    ERR (TS, Z082, __LINE__, 0x00, 0x00, 0x00, 0x00)
                    Local3 = 0x01
                }

                If (Local3)
                {
                    Debug = "Expected result:"
                    Debug = Local1
                    Debug = "Actual result:"
                    Debug = Local7
                }
            }
        }

        Return (Local7)
    }
