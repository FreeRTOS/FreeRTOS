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
     *  Thermal Zone
     *
     * (verify exceptions caused by the imprope use of Thermal Zone type objects)
     */
    Name (Z105, 0x69)
    ThermalZone (TZ00)
    {
        Name (N000, "tz00")
    }

    /* Expected exceptions: */
    /* */
    /* 47 - AE_AML_OPERAND_TYPE */
    /* */
    Method (M4BD, 0, Serialized)
    {
        ThermalZone (TZ01)
        {
            Name (N000, "tz01")
        }

        Event (E000)
        Name (I000, 0x00)
        /* Local Named Object */

        Method (M000, 1, Serialized)
        {
                /* These are now caught by the compiler - Aug 2015
         ThermalZone (tz02) {Name(n000, "tz02")}
         Store (DerefOf(tz02), Local1)
         CH06(arg0, 0, 47)
         */
        }

        /* Global Named Object */

        Method (M001, 1, NotSerialized)
        {
                /* These are now caught by the compiler - Aug 2015
         if (y083) {
         Store (DerefOf(tz00), Local1)
         CH06(arg0, 1, 47)
         }
         */
        }

        /* Local */

        Method (M002, 1, Serialized)
        {
            ThermalZone (TZ02)
            {
                Name (N000, "tz02")
            }

            Event (E000)
            CopyObject (TZ02, Local0)
            /* CondRefOf */

            CondRefOf (Local0, Local1)
            CH03 (__METHOD__, Z105, __LINE__, 0x00, 0x00)
            /* CopyObject */

            CopyObject (Local0, Local1)
            CH03 (__METHOD__, Z105, __LINE__, 0x00, 0x00)
            /* Decrement */

            Local0--
            CH06 (Arg0, 0x01, 0x2F)
            /* DerefOf */

            Local1 = DerefOf (Local0)
            CH06 (Arg0, 0x02, 0x2F)
            /* FindSetLeftBit */

            FindSetLeftBit (Local0, Local1)
            CH06 (Arg0, 0x04, 0x2F)
            /* FindSetRightBit */

            FindSetRightBit (Local0, Local1)
            CH06 (Arg0, 0x06, 0x2F)
            /* FromBCD */

            FromBCD (Local0, Local1)
            CH06 (Arg0, 0x08, 0x2F)
            /* Increment */

            Local0++
            CH06 (Arg0, 0x09, 0x2F)
            /* LNot */

            Local1 = !Local0
            CH06 (Arg0, 0x0A, 0x2F)
            /* Not */

            Local1 = ~Local0
            CH06 (Arg0, 0x0C, 0x2F)
            /* ObjectType */

            Local1 = ObjectType (Local0)
            CH03 (__METHOD__, Z105, __LINE__, 0x00, 0x00)
            /* RefOf */

            Local1 = RefOf (Local0)
            CH03 (__METHOD__, Z105, __LINE__, 0x00, 0x00)
            /* Release */

            Release (Local0)
            CH06 (Arg0, 0x0D, 0x2F)
            /* Reset */

            Reset (Local0)
            CH06 (Arg0, 0x0E, 0x2F)
            /* Signal */

            Signal (Local0)
            CH06 (Arg0, 0x0F, 0x2F)
            /* SizeOf */

            Local1 = SizeOf (Local0)
            CH06 (Arg0, 0x10, 0x2F)
            /* Sleep */

            Sleep (Local0)
            CH06 (Arg0, 0x11, 0x2F)
            /* Stall */

            Stall (Local0)
            CH06 (Arg0, 0x12, 0x2F)
            /* Store */

            Local1 = Local0
            CH06 (Arg0, 0x13, 0x2F)
            /* ToBCD */

            ToBCD (Local0, Local1)
            CH06 (Arg0, 0x15, 0x2F)
            /* ToBuffer */

            ToBuffer (Local0, Local1)
            CH06 (Arg0, 0x17, 0x2F)
            /* ToDecimalString */

            ToDecimalString (Local0, Local1)
            CH06 (Arg0, 0x19, 0x2F)
            /* ToHexString */

            ToHexString (Local0, Local1)
            CH06 (Arg0, 0x1B, 0x2F)
            /* ToInteger */

            ToInteger (Local0, Local1)
            CH06 (Arg0, 0x1D, 0x2F)
            /* Acquire */

            Local1 = Acquire (Local0, 0x0064)
            CH06 (Arg0, 0x1E, 0x2F)
            /* Add */

            Local1 = (Local0 + I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x21, 0x2F)
            Local1 = (I000 + Local0)
            CH06 (Arg0, 0x22, 0x2F)
            /* And */

            Local1 = (Local0 & I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x25, 0x2F)
            Local1 = (I000 & Local0)
            CH06 (Arg0, 0x26, 0x2F)
            /* Concatenate */

            Concatenate (Local0, I000, Local1)
            CH06 (Arg0, 0x29, 0x2F)
            Concatenate (I000, Local0, Local1)
            CH06 (Arg0, 0x2A, 0x2F)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (Local0, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x2D, 0x2F)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local0, Local1)
            CH06 (Arg0, 0x2E, 0x2F)
            /* Divide */

            Divide (Local0, I000, Local2)
            CH06 (Arg0, 0x31, 0x2F)
            Divide (I000, Local0, Local2)
            CH06 (Arg0, 0x32, 0x2F)
            Divide (Local0, I000, Local2, Local1)
            CH06 (Arg0, 0x33, 0x2F)
            Divide (I000, Local0, Local2, Local1)
            CH06 (Arg0, 0x34, 0x2F)
            /* Fatal */

            Fatal (0xFF, 0xFFFFFFFF, Local0)
            CH06 (Arg0, 0x35, 0x2F)
            /* Index */

            Local1 = Local0 [0x00]
            CH06 (Arg0, 0x38, 0x2F)
            Index ("0", Local0, Local1)
            CH06 (Arg0, 0x39, 0x2F)
            /* LEqual */

            Local1 = (Local0 == I000)
            CH06 (Arg0, 0x3A, 0x2F)
            Local1 = (I000 == Local0)
            CH06 (Arg0, 0x3B, 0x2F)
            /* LGreater */

            Local1 = (Local0 > I000)
            CH06 (Arg0, 0x3C, 0x2F)
            Local1 = (I000 > Local0)
            CH06 (Arg0, 0x3D, 0x2F)
            /* LGreaterEqual */

            Local1 = (Local0 >= I000)
            CH06 (Arg0, 0x3E, 0xFF)
            Local1 = (I000 >= Local0)
            CH06 (Arg0, 0x3F, 0xFF)
            /* LLess */

            Local1 = (Local0 < I000)
            CH06 (Arg0, 0x40, 0x2F)
            Local1 = (I000 < Local0)
            CH06 (Arg0, 0x41, 0x2F)
            /* LLessEqual */

            Local1 = (Local0 <= I000)
            CH06 (Arg0, 0x42, 0xFF)
            Local1 = (I000 <= Local0)
            CH06 (Arg0, 0x43, 0xFF)
            /* LNotEqual */

            Local1 = (Local0 != I000)
            CH06 (Arg0, 0x44, 0xFF)
            Local1 = (I000 != Local0)
            CH06 (Arg0, 0x45, 0xFF)
            /* LOr */

            Local1 = (Local0 || I000)
            CH06 (Arg0, 0x46, 0x2F)
            Local1 = (I000 || Local0)
            CH06 (Arg0, 0x47, 0x2F)
            /* Mod */

            Local1 = (Local0 % I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x4A, 0x2F)
            Local1 = (I000 % Local0)
            CH06 (Arg0, 0x4B, 0x2F)
            /* Multiply */

            Local1 = (Local0 * I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x4E, 0x2F)
            Local1 = (I000 * Local0)
            CH06 (Arg0, 0x4F, 0x2F)
            /* NAnd */

            NAnd (Local0, I000, Local1)
            CH06 (Arg0, 0x52, 0x2F)
            NAnd (I000, Local0, Local1)
            CH06 (Arg0, 0x53, 0x2F)
            /* NOr */

            NOr (Local0, I000, Local1)
            CH06 (Arg0, 0x56, 0x2F)
            NOr (I000, Local0, Local1)
            CH06 (Arg0, 0x57, 0x2F)
            /* Or */

            Local1 = (Local0 | I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x5A, 0x2F)
            Local1 = (I000 | Local0)
            CH06 (Arg0, 0x5B, 0x2F)
            /* ShiftLeft */

            Local1 = (Local0 << I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x5E, 0x2F)
            Local1 = (I000 << Local0)
            CH06 (Arg0, 0x5F, 0x2F)
            /* ShiftRight */

            Local1 = (Local0 >> I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x62, 0x2F)
            Local1 = (I000 >> Local0)
            CH06 (Arg0, 0x63, 0x2F)
            /* Subtract */

            Local1 = (Local0 - I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x66, 0x2F)
            Local1 = (I000 - Local0)
            CH06 (Arg0, 0x67, 0x2F)
            /* ToString */

            ToString (Local0, 0x01, Local1)
            CH06 (Arg0, 0x6A, 0x2F)
            ToString (I000, Local0, Local1)
            CH06 (Arg0, 0x6B, 0x2F)
            /* Wait */

            Local1 = Wait (Local0, I000)
            CH06 (Arg0, 0x6C, 0x2F)
            Local1 = Wait (E000, Local0)
            CH06 (Arg0, 0x6D, 0x2F)
            /* XOr */

            Local1 = (Local0 ^ I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x70, 0x2F)
            Local1 = (I000 ^ Local0)
            CH06 (Arg0, 0x71, 0x2F)
            /* Mid */

            Mid (Local0, 0x01, 0x01, Local1)
            CH06 (Arg0, 0x75, 0x2F)
            Mid ("123", Local0, 0x01, Local1)
            CH06 (Arg0, 0x76, 0x2F)
            Mid ("123", 0x01, Local0, Local1)
            CH06 (Arg0, 0x77, 0x2F)
            /* Match */

            Local1 = Match (Local0, MTR, 0x00, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x78, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, Local0, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x79, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, Local0, 0x00)
            CH06 (Arg0, 0x7A, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, 0x00, Local0)
            CH06 (Arg0, 0x7B, 0x2F)
        }

        /* Reference to Object */

        Method (M003, 3, Serialized)
        {
            Name (EXC0, 0x2F)  /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (Arg1)
            If ((Local0 != 0x0D))
            {
                ERR (Arg0, Z105, __LINE__, 0x00, 0x00, Local0, 0x0D)
                Return (0x01)
            }

            If (Arg2)
            {
                If (!Y503)
                {
                    EXC0 = 0x3E /* AE_AML_NO_RETURN_VALUE */
                }
            }

            Local1 = DerefOf (Arg1)
            CH03 (__METHOD__, Z105, __LINE__, 0x00, 0x00)
            /* CondRefOf */

            CondRefOf (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x01, EXC0)
            /* CopyObject */

            CopyObject (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x02, EXC0)
            /* Decrement */

            DerefOf (Arg1)--
            CH06 (Arg0, 0x03, EXC0)
            /* DerefOf */

            Local1 = DerefOf (DerefOf (Arg1))
            CH06 (Arg0, 0x04, EXC0)
            /* FindSetLeftBit */

            FindSetLeftBit (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x06, EXC0)
            /* FindSetRightBit */

            FindSetRightBit (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x08, EXC0)
            /* FromBCD */

            FromBCD (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x0A, EXC0)
            /* Increment */

            DerefOf (Arg1)++
            CH06 (Arg0, 0x0B, EXC0)
            /* LNot */

            Local1 = !DerefOf (Arg1)
            CH06 (Arg0, 0x0C, EXC0)
            /* Not */

            Local1 = ~DerefOf (Arg1)
            CH06 (Arg0, 0x0E, EXC0)
            /* ObjectType */

            Local1 = ObjectType (DerefOf (Arg1))
            CH03 (__METHOD__, Z105, __LINE__, 0x00, 0x00)
            /* RefOf */

            Local1 = RefOf (DerefOf (Arg1))
            CH06 (Arg0, 0x0F, EXC0)
            /* Release */
            /* Reset */
            /* Signal */
            /* SizeOf */
            Local1 = SizeOf (DerefOf (Arg1))
            CH06 (Arg0, 0x10, EXC0)
            /* Sleep */

            Sleep (DerefOf (Arg1))
            CH06 (Arg0, 0x11, EXC0)
            /* Stall */

            Stall (DerefOf (Arg1))
            CH06 (Arg0, 0x12, EXC0)
            /* Store */

            Local1 = DerefOf (Arg1)
            CH06 (Arg0, 0x13, EXC0)
            /* ToBCD */

            ToBCD (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x15, EXC0)
            /* ToBuffer */

            ToBuffer (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x17, EXC0)
            /* ToDecimalString */

            ToDecimalString (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x19, EXC0)
            /* ToHexString */

            ToHexString (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x1B, EXC0)
            /* ToInteger */

            ToInteger (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x1D, EXC0)
            /* Acquire */
            /* Add */
            Local1 = (DerefOf (Arg1) + I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x21, EXC0)
            Local1 = (I000 + DerefOf (Arg1))
            CH06 (Arg0, 0x22, EXC0)
            /* And */

            Local1 = (DerefOf (Arg1) & I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x25, EXC0)
            Local1 = (I000 & DerefOf (Arg1))
            CH06 (Arg0, 0x26, EXC0)
            /* Concatenate */

            Concatenate (DerefOf (Arg1), I000, Local1)
            CH06 (Arg0, 0x29, EXC0)
            Concatenate (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x2A, EXC0)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (DerefOf (Arg1), Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x2D, EXC0)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x2E, EXC0)
            /* Divide */

            Divide (DerefOf (Arg1), I000, Local2)
            CH06 (Arg0, 0x31, EXC0)
            Divide (I000, DerefOf (Arg1), Local2)
            CH06 (Arg0, 0x32, EXC0)
            Divide (DerefOf (Arg1), I000, Local2, Local1)
            CH06 (Arg0, 0x33, EXC0)
            Divide (I000, DerefOf (Arg1), Local2, Local1)
            CH06 (Arg0, 0x34, EXC0)
            /* Fatal */

            Fatal (0xFF, 0xFFFFFFFF, DerefOf (Arg1))
            CH06 (Arg0, 0x35, EXC0)
            /* Index */

            Local1 = DerefOf (Arg1) [0x00]
            CH06 (Arg0, 0x38, EXC0)
            Index ("0", DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x39, EXC0)
            /* LEqual */

            Local1 = (DerefOf (Arg1) == I000)
            CH06 (Arg0, 0x3A, EXC0)
            Local1 = (I000 == DerefOf (Arg1))
            CH06 (Arg0, 0x3B, EXC0)
            /* LGreater */

            Local1 = (DerefOf (Arg1) > I000)
            CH06 (Arg0, 0x3C, EXC0)
            Local1 = (I000 > DerefOf (Arg1))
            CH06 (Arg0, 0x3D, EXC0)
            /* LGreaterEqual */

            Local1 = (DerefOf (Arg1) >= I000)
            CH06 (Arg0, 0x3E, 0xFF)
            Local1 = (I000 >= DerefOf (Arg1))
            CH06 (Arg0, 0x3F, 0xFF)
            /* LLess */

            Local1 = (DerefOf (Arg1) < I000)
            CH06 (Arg0, 0x40, EXC0)
            Local1 = (I000 < DerefOf (Arg1))
            CH06 (Arg0, 0x41, EXC0)
            /* LLessEqual */

            Local1 = (DerefOf (Arg1) <= I000)
            CH06 (Arg0, 0x42, 0xFF)
            Local1 = (I000 <= DerefOf (Arg1))
            CH06 (Arg0, 0x43, 0xFF)
            /* LNotEqual */

            Local1 = (DerefOf (Arg1) != I000)
            CH06 (Arg0, 0x44, 0xFF)
            Local1 = (I000 != DerefOf (Arg1))
            CH06 (Arg0, 0x45, 0xFF)
            /* LOr */

            Local1 = (DerefOf (Arg1) || I000)
            CH06 (Arg0, 0x46, EXC0)
            Local1 = (I000 || DerefOf (Arg1))
            CH06 (Arg0, 0x47, EXC0)
            /* Mod */

            Local1 = (DerefOf (Arg1) % I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x4A, EXC0)
            Local1 = (I000 % DerefOf (Arg1))
            CH06 (Arg0, 0x4B, EXC0)
            /* Multiply */

            Local1 = (DerefOf (Arg1) * I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x4E, EXC0)
            Local1 = (I000 * DerefOf (Arg1))
            CH06 (Arg0, 0x4F, EXC0)
            /* NAnd */

            NAnd (DerefOf (Arg1), I000, Local1)
            CH06 (Arg0, 0x52, EXC0)
            NAnd (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x53, EXC0)
            /* NOr */

            NOr (DerefOf (Arg1), I000, Local1)
            CH06 (Arg0, 0x56, EXC0)
            NOr (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x57, EXC0)
            /* Or */

            Local1 = (DerefOf (Arg1) | I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x5A, EXC0)
            Local1 = (I000 | DerefOf (Arg1))
            CH06 (Arg0, 0x5B, EXC0)
            /* ShiftLeft */

            Local1 = (DerefOf (Arg1) << I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x5E, EXC0)
            Local1 = (I000 << DerefOf (Arg1))
            CH06 (Arg0, 0x5F, EXC0)
            /* ShiftRight */

            Local1 = (DerefOf (Arg1) >> I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x62, EXC0)
            Local1 = (I000 >> DerefOf (Arg1))
            CH06 (Arg0, 0x63, EXC0)
            /* Subtract */

            Local1 = (DerefOf (Arg1) - I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x66, EXC0)
            Local1 = (I000 - DerefOf (Arg1))
            CH06 (Arg0, 0x67, EXC0)
            /* ToString */

            ToString (DerefOf (Arg1), 0x01, Local1)
            CH06 (Arg0, 0x6A, EXC0)
            ToString (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x6B, EXC0)
            /* Wait */

            Local1 = Wait (E000, DerefOf (Arg1))
            CH06 (Arg0, 0x6D, EXC0)
            /* XOr */

            Local1 = (DerefOf (Arg1) ^ I000) /* \M4BD.I000 */
            CH06 (Arg0, 0x70, EXC0)
            Local1 = (I000 ^ DerefOf (Arg1))
            CH06 (Arg0, 0x71, EXC0)
            /* Mid */

            Mid (DerefOf (Arg1), 0x01, 0x01, Local1)
            CH06 (Arg0, 0x75, EXC0)
            Mid ("123", DerefOf (Arg1), 0x01, Local1)
            CH06 (Arg0, 0x76, EXC0)
            Mid ("123", 0x01, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x77, EXC0)
            /* Match */

            Local1 = Match (DerefOf (Arg1), MTR, 0x00, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x78, EXC0)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, DerefOf (Arg1), MTR, 0x00, 0x00)
            CH06 (Arg0, 0x79, EXC0)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, DerefOf (Arg1), 0x00)
            CH06 (Arg0, 0x7A, EXC0)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, 0x00, DerefOf (Arg1))
            CH06 (Arg0, 0x7B, EXC0)
            Return (0x00)
        }

        /* Result of Method invocation */

        Method (M004, 1, Serialized)
        {
            Name (I000, 0x00) /* Label to check m000 invocations */
            Method (M000, 0, NotSerialized)
            {
                CopyObject (TZ00, Local0)
                Return (Local0)
            }

            /* CondRefOf */
            /* **** 10/2016 changed method invocation to just a namestring */
            /* CondRefOf no longer invokes the method */
            CondRefOf (M000, Local1)
            CH06 (Arg0, 0x01, 0x2F)
            /* CopyObject */

            CopyObject (M000 (), Local1)
            CH03 (__METHOD__, Z105, __LINE__, 0x00, 0x00)
            /* Decrement */

            M000 ()--
            CH06 (Arg0, 0x02, 0x2F)
            /* DerefOf */

            Local1 = DerefOf (M000 ())
            CH06 (Arg0, 0x03, 0x2F)
            /* FindSetLeftBit */

            FindSetLeftBit (M000 (), Local1)
            CH06 (Arg0, 0x05, 0x2F)
            /* FindSetRightBit */

            FindSetRightBit (M000 (), Local1)
            CH06 (Arg0, 0x07, 0x2F)
            /* FromBCD */

            FromBCD (M000 (), Local1)
            CH06 (Arg0, 0x09, 0x2F)
            /* Increment */

            M000 ()++
            CH06 (Arg0, 0x0A, 0x2F)
            /* LNot */

            Local1 = !M000 ()
            CH06 (Arg0, 0x0B, 0x2F)
            /* Not */

            Local1 = ~M000 ()
            CH06 (Arg0, 0x0D, 0x2F)
            /* ObjectType */
            /* **** Nov. 2016: Method invocation as arg to ObjectType is now illegal */
            Local0 = ObjectType (M000)
            CH03 (__METHOD__, Z105, __LINE__, 0x00, 0x00)
            /* RefOf */
            /* **** Oct. 2016: Method invocation as arg to RefOf is now illegal */
            /*		Store (RefOf(m000()), Local1) */
            /*		CH06(arg0, 14, 47) */
            /* Release */
            Release (M000 ())
            CH06 (Arg0, 0x0D, 0x2F)
            /* Reset */

            Reset (M000 ())
            CH06 (Arg0, 0x0E, 0x2F)
            /* Signal */

            Signal (M000 ())
            CH06 (Arg0, 0x0F, 0x2F)
            /* SizeOf */

            Local1 = SizeOf (M000 ())
            CH06 (Arg0, 0x10, 0x2F)
            /* Sleep */

            Sleep (M000 ())
            CH06 (Arg0, 0x11, 0x2F)
            /* Stall */

            Stall (M000 ())
            CH06 (Arg0, 0x12, 0x2F)
            /* Store */

            Local1 = M000 ()
            CH06 (Arg0, 0x13, 0x2F)
            /* ToBCD */

            ToBCD (M000 (), Local1)
            CH06 (Arg0, 0x15, 0x2F)
            /* ToBuffer */

            ToBuffer (M000 (), Local1)
            CH06 (Arg0, 0x17, 0x2F)
            /* ToDecimalString */

            ToDecimalString (M000 (), Local1)
            CH06 (Arg0, 0x19, 0x2F)
            /* ToHexString */

            ToHexString (M000 (), Local1)
            CH06 (Arg0, 0x1B, 0x2F)
            /* ToInteger */

            ToInteger (M000 (), Local1)
            CH06 (Arg0, 0x1D, 0x2F)
            /* Acquire */

            Local1 = Acquire (M000 (), 0x0064)
            CH06 (Arg0, 0x1E, 0x2F)
            /* Add */

            Local1 = (M000 () + I000) /* \M4BD.M004.I000 */
            CH06 (Arg0, 0x21, 0x2F)
            Local1 = (I000 + M000 ())
            CH06 (Arg0, 0x22, 0x2F)
            /* And */

            Local1 = (M000 () & I000) /* \M4BD.M004.I000 */
            CH06 (Arg0, 0x25, 0x2F)
            Local1 = (I000 & M000 ())
            CH06 (Arg0, 0x26, 0x2F)
            /* Concatenate */

            Concatenate (M000 (), I000, Local1)
            CH06 (Arg0, 0x29, 0x2F)
            Concatenate (I000, M000 (), Local1)
            CH06 (Arg0, 0x2A, 0x2F)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (M000 (), Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x2D, 0x2F)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, M000 (), Local1)
            CH06 (Arg0, 0x2E, 0x2F)
            /* Divide */

            Divide (M000 (), I000, Local2)
            CH06 (Arg0, 0x31, 0x2F)
            Divide (I000, M000 (), Local2)
            CH06 (Arg0, 0x32, 0x2F)
            Divide (M000 (), I000, Local2, Local1)
            CH06 (Arg0, 0x33, 0x2F)
            Divide (I000, M000 (), Local2, Local1)
            CH06 (Arg0, 0x34, 0x2F)
            /* Fatal */

            Fatal (0xFF, 0xFFFFFFFF, M000 ())
            CH06 (Arg0, 0x35, 0x2F)
            /* Index */

            Local1 = M000 () [0x00]
            CH06 (Arg0, 0x38, 0x2F)
            Index ("0", M000 (), Local1)
            CH06 (Arg0, 0x39, 0x2F)
            /* LEqual */

            Local1 = (M000 () == I000)
            CH06 (Arg0, 0x3A, 0x2F)
            Local1 = (I000 == M000 ())
            CH06 (Arg0, 0x3B, 0x2F)
            /* LGreater */

            Local1 = (M000 () > I000)
            CH06 (Arg0, 0x3C, 0x2F)
            Local1 = (I000 > M000 ())
            CH06 (Arg0, 0x3D, 0x2F)
            /* LGreaterEqual */

            Local1 = (M000 () >= I000)
            CH06 (Arg0, 0x3E, 0xFF)
            Local1 = (I000 >= M000 ())
            CH06 (Arg0, 0x3F, 0xFF)
            /* LLess */

            Local1 = (M000 () < I000)
            CH06 (Arg0, 0x40, 0x2F)
            Local1 = (I000 < M000 ())
            CH06 (Arg0, 0x41, 0x2F)
            /* LLessEqual */

            Local1 = (M000 () <= I000)
            CH06 (Arg0, 0x42, 0xFF)
            Local1 = (I000 <= M000 ())
            CH06 (Arg0, 0x43, 0xFF)
            /* LNotEqual */

            Local1 = (M000 () != I000)
            CH06 (Arg0, 0x44, 0xFF)
            Local1 = (I000 != M000 ())
            CH06 (Arg0, 0x45, 0xFF)
            /* LOr */

            Local1 = (M000 () || I000)
            CH06 (Arg0, 0x46, 0x2F)
            Local1 = (I000 || M000 ())
            CH06 (Arg0, 0x47, 0x2F)
            /* Mod */

            Local1 = (M000 () % I000) /* \M4BD.M004.I000 */
            CH06 (Arg0, 0x4A, 0x2F)
            Local1 = (I000 % M000 ())
            CH06 (Arg0, 0x4B, 0x2F)
            /* Multiply */

            Local1 = (M000 () * I000) /* \M4BD.M004.I000 */
            CH06 (Arg0, 0x4E, 0x2F)
            Local1 = (I000 * M000 ())
            CH06 (Arg0, 0x4F, 0x2F)
            /* NAnd */

            NAnd (M000 (), I000, Local1)
            CH06 (Arg0, 0x52, 0x2F)
            NAnd (I000, M000 (), Local1)
            CH06 (Arg0, 0x53, 0x2F)
            /* NOr */

            NOr (M000 (), I000, Local1)
            CH06 (Arg0, 0x56, 0x2F)
            NOr (I000, M000 (), Local1)
            CH06 (Arg0, 0x57, 0x2F)
            /* Or */

            Local1 = (M000 () | I000) /* \M4BD.M004.I000 */
            CH06 (Arg0, 0x5A, 0x2F)
            Local1 = (I000 | M000 ())
            CH06 (Arg0, 0x5B, 0x2F)
            /* ShiftLeft */

            Local1 = (M000 () << I000) /* \M4BD.M004.I000 */
            CH06 (Arg0, 0x5E, 0x2F)
            Local1 = (I000 << M000 ())
            CH06 (Arg0, 0x5F, 0x2F)
            /* ShiftRight */

            Local1 = (M000 () >> I000) /* \M4BD.M004.I000 */
            CH06 (Arg0, 0x62, 0x2F)
            Local1 = (I000 >> M000 ())
            CH06 (Arg0, 0x63, 0x2F)
            /* Subtract */

            Local1 = (M000 () - I000) /* \M4BD.M004.I000 */
            CH06 (Arg0, 0x66, 0x2F)
            Local1 = (I000 - M000 ())
            CH06 (Arg0, 0x67, 0x2F)
            /* ToString */

            ToString (M000 (), 0x01, Local1)
            CH06 (Arg0, 0x6A, 0x2F)
            ToString (I000, M000 (), Local1)
            CH06 (Arg0, 0x6B, 0x2F)
            /* Wait */

            Local1 = Wait (M000 (), I000)
            CH06 (Arg0, 0x6C, 0x2F)
            Local1 = Wait (E000, M000 ())
            CH06 (Arg0, 0x6D, 0x2F)
            /* XOr */

            Local1 = (M000 () ^ I000) /* \M4BD.M004.I000 */
            CH06 (Arg0, 0x70, 0x2F)
            Local1 = (I000 ^ M000 ())
            CH06 (Arg0, 0x71, 0x2F)
            /* Mid */

            Mid (M000 (), 0x01, 0x01, Local1)
            CH06 (Arg0, 0x75, 0x2F)
            Mid ("123", M000 (), 0x01, Local1)
            CH06 (Arg0, 0x76, 0x2F)
            Mid ("123", 0x01, M000 (), Local1)
            CH06 (Arg0, 0x77, 0x2F)
            /* Match */

            Local1 = Match (M000 (), MTR, 0x00, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x78, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, M000 (), MTR, 0x00, 0x00)
            CH06 (Arg0, 0x79, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, M000 (), 0x00)
            CH06 (Arg0, 0x7A, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, 0x00, M000 ())
            CH06 (Arg0, 0x7B, 0x2F)
        }

        /* Reference to Object as Result of Method invocation */

        Method (M005, 1, Serialized)
        {
            ThermalZone (TZ02)
            {
                Name (N000, "tz02")
            }

            Name (I000, 0x00) /* Label to check m000 invocations */
            Method (M000, 2, NotSerialized)
            {
                I000 = Arg0
                If ((Arg1 == 0x00))
                {
                    Local0 = RefOf (TZ00)
                }
                ElseIf ((Arg1 == 0x01))
                {
                    Local0 = RefOf (TZ02)
                }

                Return (Local0)
            }

            Method (CH00, 2, NotSerialized)
            {
                If ((I000 != Arg1))
                {
                    ERR (Arg0, Z105, __LINE__, 0x00, 0x00, I000, Arg1)
                }
            }

            Name (LPN0, 0x02)
            Name (LPC0, 0x00)
            While (LPN0)
            {
                Local0 = (0x03 * LPC0) /* \M4BD.M005.LPC0 */
                I000 = 0x00
                Local1 = DerefOf (M000 (0x01, LPC0))
                CH03 (__METHOD__, Z105, __LINE__, 0x00, 0x00)
                CH00 (Arg0, 0x01)
                Local1 = DerefOf (DerefOf (M000 (0x02, LPC0)))
                CH06 (Arg0, (0x01 + Local0), 0x2F)
                CH00 (Arg0, 0x02)
                Store (DerefOf (M000 (0x03, LPC0)) [0x00], Local1)
                CH06 (Arg0, (0x02 + Local0), 0x2F)
                CH00 (Arg0, 0x03)
                Local1 = Match (DerefOf (M000 (0x04, LPC0)), MTR, 0x00, MTR, 0x00, 0x00)
                CH06 (Arg0, (0x03 + Local0), 0x2F)
                CH00 (Arg0, 0x04)
                LPN0--
                LPC0++
            }
        }

        CH03 (__METHOD__, Z105, __LINE__, 0x00, 0x00)
        /* Local Named Object */

        M000 (__METHOD__)
        /* Global Named Object */

        M001 (__METHOD__)
        /* Local */

        If (Y504)
        {
            M002 (Concatenate (__METHOD__, "-m002"))
        }

        /* Reference to Local Named Object */

        M003 (Concatenate (__METHOD__, "-m003-RefLocName"), RefOf (TZ01), 0x01)
        Local0 = RefOf (TZ01)
        M003 (Concatenate (__METHOD__, "-m003-RefLocName2"), Local0, 0x01)
        CondRefOf (TZ01, Local0)
        M003 (Concatenate (__METHOD__, "-m003-CondRefLocName"), Local0, 0x01)
        M003 (Concatenate (__METHOD__, "-m003-RefGlobName"), RefOf (TZ00), 0x01)
        Local0 = RefOf (TZ00)
        M003 (Concatenate (__METHOD__, "-m003-RefGlobName2"), Local0, 0x01)
        CondRefOf (TZ00, Local0)
        M003 (Concatenate (__METHOD__, "-m003-CondRefGlobName"), Local0, 0x01)
        /* Reference to Object as element of Package */

        Name (PP00, Package (0x01)
        {
            TZ00
        })
        If (Y113)
        {
            M003 (Concatenate (__METHOD__, "-m003-Index"), PP00 [0x00], 0x00)
        }

        Store (PP00 [0x00], Local1)
        M003 (Concatenate (__METHOD__, "-m003-Index2"), Local1, 0x00)
        If (Y113)
        {
            M003 (Concatenate (__METHOD__, "-m003-Index3"), Local2 = PP00 [0x00], 0x00)
        }

        Local3 = PP00 [0x00]
        M003 (Concatenate (__METHOD__, "-m003-Index4"), Local3, 0x00)
        Local5 = Local4 = PP00 [0x00]
        M003 (Concatenate (__METHOD__, "-m003-Index5"), Local5, 0x00)
        /* Result of Method invocation */

        If (Y504)
        {
            M004 (Concatenate (__METHOD__, "-m004"))
        }

        /* Reference to Object as Result of Method invocation */

        M005 (Concatenate (__METHOD__, "-m005"))
    }
