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
     *  Package
     *
     * (verify exceptions caused by the imprope use of Package type objects)
     */
    Name (Z096, 0x60)
    Name (P100, Package (0x01)
    {
        0x61
    })
    /* Expected exceptions: */
    /* */
    /* 47 - AE_AML_OPERAND_TYPE */
    /* Note: Package can be used with Index */
    Method (M4B4, 1, Serialized)
    {
        Name (P000, Package (0x01)
        {
            0x62
        })
        Event (E000)
        Name (I000, 0x00)
        /* Local Named Object */
        /* ASL compiler prohibits to use Package */
        /* Named Objects in the most of operators */
        Method (M000, 1, Serialized)
        {
            Name (P000, Package (0x01)
            {
                0x63
            })
            /* CondRefOf */

            Local1 = CondRefOf (P000)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            CondRefOf (P000, Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* CopyObject */

            CopyObject (P000, Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Decrement */
            /* DerefOf */
            /* These are now caught by the compiler - Aug 2015
             if (y083) {
             Store (DerefOf(p000), Local1)
             CH06(arg0, 0, 47)
             }
             */
            /* FindSetLeftBit */
            /* FindSetRightBit */
            /* FromBCD */
            /* Increment */
            /* LNot */
            /* Not */
            /* ObjectType */
            Local1 = ObjectType (P000)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* RefOf */

            Local1 = RefOf (P000)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Release */
            /* Reset */
            /* Signal */
            /* SizeOf */
            Local1 = SizeOf (P000)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Sleep */
            /* Stall */
            /* Store */
            Local1 = P000 /* \M4B4.M000.P000 */
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* ToBCD */
            /* ToBuffer */
            /* ToDecimalString */
            /* ToHexString */
            /* ToInteger */
            /* Acquire */
            /* Add */
            /* And */
            /* Concatenate */
            /* ConcatenateResTemplate */
            /* Divide */
            /* Fatal */
            /* Index */
            Local1 = P000 [0x00]
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            Store (P000 [0x00], Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* LEqual */
            /* LGreater */
            /* LGreaterEqual */
            /* LLess */
            /* LLessEqual */
            /* LNotEqual */
            /* LOr */
            /* Mod */
            /* Multiply */
            /* NAnd */
            /* NOr */
            /* Or */
            /* ShiftLeft */
            /* ShiftRight */
            /* Subtract */
            /* ToString */
            /* Wait */
            /* XOr */
            /* Mid */
            /* Match */
            Local1 = Match (P000, MTR, 0x00, MTR, 0x00, 0x00)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
        }

        /* Global Named Object */

        Method (M001, 1, NotSerialized)
        {
            /* CondRefOf */

            CondRefOf (P100, Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* CopyObject */

            CopyObject (P100, Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Decrement */
            /* DerefOf */
            /* These are now caught by the compiler - Aug 2015
             if (y083) {
             Store (DerefOf(p100), Local1)
             CH06(arg0, 1, 47)
             }
             */
            /* FindSetLeftBit */
            /* FindSetRightBit */
            /* FromBCD */
            /* Increment */
            /* LNot */
            /* Not */
            /* ObjectType */
            Local1 = ObjectType (P100)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* RefOf */

            Local1 = RefOf (P100)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Release */
            /* Reset */
            /* Signal */
            /* SizeOf */
            Local1 = SizeOf (P100)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Sleep */
            /* Stall */
            /* Store */
            Local1 = P100 /* \P100 */
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* ToBCD */
            /* ToBuffer */
            /* ToDecimalString */
            /* ToHexString */
            /* ToInteger */
            /* Acquire */
            /* Add */
            /* And */
            /* Concatenate */
            /* ConcatenateResTemplate */
            /* Divide */
            /* Fatal */
            /* Index */
            Store (P100 [0x00], Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* LEqual */
            /* LGreater */
            /* LGreaterEqual */
            /* LLess */
            /* LLessEqual */
            /* LNotEqual */
            /* LOr */
            /* Mod */
            /* Multiply */
            /* NAnd */
            /* NOr */
            /* Or */
            /* ShiftLeft */
            /* ShiftRight */
            /* Subtract */
            /* ToString */
            /* Wait */
            /* XOr */
            /* Mid */
            /* Match */
            Local1 = Match (P100, MTR, 0x00, MTR, 0x00, 0x00)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
        }

        /* Argument */

        Method (M002, 2, Serialized)
        {
            Event (E000)
            /* CondRefOf */

            CondRefOf (Arg1, Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* CopyObject */

            CopyObject (Arg1, Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Decrement */

            Arg1--
            CH06 (Arg0, 0x02, 0x2F)
            /* DerefOf */

            Local1 = DerefOf (Arg1)
            CH06 (Arg0, 0x03, 0x2F)
            /* FindSetLeftBit */

            FindSetLeftBit (Arg1, Local1)
            CH06 (Arg0, 0x05, 0x2F)
            /* FindSetRightBit */

            FindSetRightBit (Arg1, Local1)
            CH06 (Arg0, 0x07, 0x2F)
            /* FromBCD */

            FromBCD (Arg1, Local1)
            CH06 (Arg0, 0x09, 0x2F)
            /* Increment */

            Arg1++
            CH06 (Arg0, 0x0A, 0x2F)
            /* LNot */

            Local1 = !Arg1
            CH06 (Arg0, 0x0B, 0x2F)
            /* Not */

            Local1 = ~Arg1
            CH06 (Arg0, 0x0D, 0x2F)
            /* ObjectType */

            Local1 = ObjectType (Arg1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* RefOf */

            Local1 = RefOf (Arg1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Release */

            Release (Arg1)
            CH06 (Arg0, 0x0E, 0x2F)
            /* Reset */

            Reset (Arg1)
            CH06 (Arg0, 0x0F, 0x2F)
            /* Signal */

            Signal (Arg1)
            CH06 (Arg0, 0x10, 0x2F)
            /* SizeOf */

            Local1 = SizeOf (Arg1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Sleep */

            Sleep (Arg1)
            CH06 (Arg0, 0x11, 0x2F)
            /* Stall */

            Stall (Arg1)
            CH06 (Arg0, 0x12, 0x2F)
            /* Store */

            Local1 = Arg1
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* ToBCD */

            ToBCD (Arg1, Local1)
            CH06 (Arg0, 0x15, 0x2F)
            /* ToBuffer */

            ToBuffer (Arg1, Local1)
            CH06 (Arg0, 0x17, 0x2F)
            /* ToDecimalString */

            ToDecimalString (Arg1, Local1)
            CH06 (Arg0, 0x19, 0x2F)
            /* ToHexString */

            ToHexString (Arg1, Local1)
            CH06 (Arg0, 0x1B, 0x2F)
            /* ToInteger */

            ToInteger (Arg1, Local1)
            CH06 (Arg0, 0x1D, 0x2F)
            /* Acquire */

            Local1 = Acquire (Arg1, 0x0064)
            CH06 (Arg0, 0x1E, 0x2F)
            /* Add */

            Local1 = (Arg1 + I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x21, 0x2F)
            Local1 = (I000 + Arg1)
            CH06 (Arg0, 0x22, 0x2F)
            /* And */

            Local1 = (Arg1 & I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x25, 0x2F)
            Local1 = (I000 & Arg1)
            CH06 (Arg0, 0x26, 0x2F)
            /* Concatenate */

            Concatenate (Arg1, I000, Local1)
            CH06 (Arg0, 0x29, 0x2F)
            Concatenate (I000, Arg1, Local1)
            CH06 (Arg0, 0x2A, 0x2F)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (Arg1, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x2D, 0x2F)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Arg1, Local1)
            CH06 (Arg0, 0x2E, 0x2F)
            /* Divide */

            Divide (Arg1, I000, Local2)
            CH06 (Arg0, 0x31, 0x2F)
            Divide (I000, Arg1, Local2)
            CH06 (Arg0, 0x32, 0x2F)
            Divide (Arg1, I000, Local2, Local1)
            CH06 (Arg0, 0x33, 0x2F)
            Divide (I000, Arg1, Local2, Local1)
            CH06 (Arg0, 0x34, 0x2F)
            /* Fatal */

            Fatal (0xFF, 0xFFFFFFFF, Arg1)
            CH06 (Arg0, 0x35, 0x2F)
            /* Index */

            Local1 = Arg1 [0x00]
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            Index ("0", Arg1, Local1)
            CH06 (Arg0, 0x39, 0x2F)
            /* LEqual */

            Local1 = (Arg1 == I000)
            CH06 (Arg0, 0x3A, 0x2F)
            Local1 = (I000 == Arg1)
            CH06 (Arg0, 0x3B, 0x2F)
            /* LGreater */

            Local1 = (Arg1 > I000)
            CH06 (Arg0, 0x3C, 0x2F)
            Local1 = (I000 > Arg1)
            CH06 (Arg0, 0x3D, 0x2F)
            /* LGreaterEqual */

            Local1 = (Arg1 >= I000)
            CH06 (Arg0, 0x3E, 0xFF)
            Local1 = (I000 >= Arg1)
            CH06 (Arg0, 0x3F, 0xFF)
            /* LLess */

            Local1 = (Arg1 < I000)
            CH06 (Arg0, 0x40, 0x2F)
            Local1 = (I000 < Arg1)
            CH06 (Arg0, 0x41, 0x2F)
            /* LLessEqual */

            Local1 = (Arg1 <= I000)
            CH06 (Arg0, 0x42, 0xFF)
            Local1 = (I000 <= Arg1)
            CH06 (Arg0, 0x43, 0xFF)
            /* LNotEqual */

            Local1 = (Arg1 != I000)
            CH06 (Arg0, 0x44, 0xFF)
            Local1 = (I000 != Arg1)
            CH06 (Arg0, 0x45, 0xFF)
            /* LOr */

            Local1 = (Arg1 || I000)
            CH06 (Arg0, 0x46, 0x2F)
            Local1 = (I000 || Arg1)
            CH06 (Arg0, 0x47, 0x2F)
            /* Mod */

            Local1 = (Arg1 % I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x4A, 0x2F)
            Local1 = (I000 % Arg1)
            CH06 (Arg0, 0x4B, 0x2F)
            /* Multiply */

            Local1 = (Arg1 * I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x4E, 0x2F)
            Local1 = (I000 * Arg1)
            CH06 (Arg0, 0x4F, 0x2F)
            /* NAnd */

            NAnd (Arg1, I000, Local1)
            CH06 (Arg0, 0x52, 0x2F)
            NAnd (I000, Arg1, Local1)
            CH06 (Arg0, 0x53, 0x2F)
            /* NOr */

            NOr (Arg1, I000, Local1)
            CH06 (Arg0, 0x56, 0x2F)
            NOr (I000, Arg1, Local1)
            CH06 (Arg0, 0x57, 0x2F)
            /* Or */

            Local1 = (Arg1 | I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5A, 0x2F)
            Local1 = (I000 | Arg1)
            CH06 (Arg0, 0x5B, 0x2F)
            /* ShiftLeft */

            Local1 = (Arg1 << I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5E, 0x2F)
            Local1 = (I000 << Arg1)
            CH06 (Arg0, 0x5F, 0x2F)
            /* ShiftRight */

            Local1 = (Arg1 >> I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x62, 0x2F)
            Local1 = (I000 >> Arg1)
            CH06 (Arg0, 0x63, 0x2F)
            /* Subtract */

            Local1 = (Arg1 - I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x66, 0x2F)
            Local1 = (I000 - Arg1)
            CH06 (Arg0, 0x67, 0x2F)
            /* ToString */

            ToString (Arg1, 0x01, Local1)
            CH06 (Arg0, 0x6A, 0x2F)
            ToString (I000, Arg1, Local1)
            CH06 (Arg0, 0x6B, 0x2F)
            /* Wait */

            Local1 = Wait (Arg1, I000)
            CH06 (Arg0, 0x6C, 0x2F)
            Local1 = Wait (E000, Arg1)
            CH06 (Arg0, 0x6D, 0x2F)
            /* XOr */

            Local1 = (Arg1 ^ I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x70, 0x2F)
            Local1 = (I000 ^ Arg1)
            CH06 (Arg0, 0x71, 0x2F)
            /* Mid */

            Mid (Arg1, 0x01, 0x01, Local1)
            CH06 (Arg0, 0x75, 0x2F)
            Mid ("123", Arg1, 0x01, Local1)
            CH06 (Arg0, 0x76, 0x2F)
            Mid ("123", 0x01, Arg1, Local1)
            CH06 (Arg0, 0x77, 0x2F)
            /* Match */

            Local1 = Match (Arg1, MTR, 0x00, MTR, 0x00, 0x00)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, Arg1, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x79, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, Arg1, 0x00)
            CH06 (Arg0, 0x7A, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, 0x00, Arg1)
            CH06 (Arg0, 0x7B, 0x2F)
        }

        /* Local */

        Method (M003, 1, NotSerialized)
        {
            Local0 = Package (0x01)
                {
                    0x63
                }
            /* CondRefOf */

            CondRefOf (Local0, Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* CopyObject */

            CopyObject (Local0, Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
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
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* RefOf */

            Local1 = RefOf (Local0)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
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
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Sleep */

            Sleep (Local0)
            CH06 (Arg0, 0x11, 0x2F)
            /* Stall */

            Stall (Local0)
            CH06 (Arg0, 0x12, 0x2F)
            /* Store */

            Local1 = Local0
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
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

            Local1 = (I000 + Local0)
            CH06 (Arg0, 0x22, 0x2F)
            /* And */

            Local1 = (Local0 & I000) /* \M4B4.I000 */
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
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
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

            Local1 = (Local0 % I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x4A, 0x2F)
            Local1 = (I000 % Local0)
            CH06 (Arg0, 0x4B, 0x2F)
            /* Multiply */

            Local1 = (Local0 * I000) /* \M4B4.I000 */
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

            Local1 = (Local0 | I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5A, 0x2F)
            Local1 = (I000 | Local0)
            CH06 (Arg0, 0x5B, 0x2F)
            /* ShiftLeft */

            Local1 = (Local0 << I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5E, 0x2F)
            Local1 = (I000 << Local0)
            CH06 (Arg0, 0x5F, 0x2F)
            /* ShiftRight */

            Local1 = (Local0 >> I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x62, 0x2F)
            Local1 = (I000 >> Local0)
            CH06 (Arg0, 0x63, 0x2F)
            /* Subtract */

            Local1 = (Local0 - I000) /* \M4B4.I000 */
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

            Local1 = (Local0 ^ I000) /* \M4B4.I000 */
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
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
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

        /* An element of Package */

        Method (M004, 1, Serialized)
        {
            Name (P000, Package (0x01)
            {
                Package (0x01)
                {
                    0x63
                }
            })
            /* DeRefOf(Index(Package, Ind)) */
            /* CondRefOf */
            CondRefOf (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x01, 0x2F)
            /* CopyObject */

            CopyObject (DerefOf (P000 [0x00]), Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Decrement */

            DerefOf (P000 [0x00])--
            CH06 (Arg0, 0x02, 0x2F)
            /* DerefOf */

            Local1 = DerefOf (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x03, 0x2F)
            /* FindSetLeftBit */

            FindSetLeftBit (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x05, 0x2F)
            /* FindSetRightBit */

            FindSetRightBit (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x07, 0x2F)
            /* FromBCD */

            FromBCD (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x09, 0x2F)
            /* Increment */

            DerefOf (P000 [0x00])++
            CH06 (Arg0, 0x0A, 0x2F)
            /* LNot */

            Local1 = !DerefOf (P000 [0x00])
            CH06 (Arg0, 0x0B, 0x2F)
            /* Not */

            Local1 = ~DerefOf (P000 [0x00])
            CH06 (Arg0, 0x0D, 0x2F)
            /* ObjectType */

            Local1 = ObjectType (DerefOf (P000 [0x00]))
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* RefOf */

            Local1 = RefOf (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x0E, 0x2F)
            /* Release */
            /* Reset */
            /* Signal */
            /* SizeOf */
            Local1 = SizeOf (DerefOf (P000 [0x00]))
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Sleep */

            Sleep (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x11, 0x2F)
            /* Stall */

            Stall (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x12, 0x2F)
            /* Store */

            Local1 = DerefOf (P000 [0x00])
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* ToBCD */

            ToBCD (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x15, 0x2F)
            /* ToBuffer */

            ToBuffer (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x17, 0x2F)
            /* ToDecimalString */

            ToDecimalString (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x19, 0x2F)
            /* ToHexString */

            ToHexString (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x1B, 0x2F)
            /* ToInteger */

            ToInteger (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x1D, 0x2F)
            /* Acquire */
            /* Add */
            Local1 = (DerefOf (P000 [0x00]) + I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x21, 0x2F)
            Local1 = (I000 + DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x22, 0x2F)
            /* And */

            Local1 = (DerefOf (P000 [0x00]) & I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x25, 0x2F)
            Local1 = (I000 & DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x26, 0x2F)
            /* Concatenate */

            Concatenate (DerefOf (P000 [0x00]), I000, Local1)
            CH06 (Arg0, 0x29, 0x2F)
            Concatenate (I000, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x2A, 0x2F)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (DerefOf (P000 [0x00]), Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x2D, 0x2F)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x2E, 0x2F)
            /* Divide */

            Divide (DerefOf (P000 [0x00]), I000, Local2)
            CH06 (Arg0, 0x31, 0x2F)
            Divide (I000, DerefOf (P000 [0x00]), Local2)
            CH06 (Arg0, 0x32, 0x2F)
            Divide (DerefOf (P000 [0x00]), I000, Local2, Local1)
            CH06 (Arg0, 0x33, 0x2F)
            Divide (I000, DerefOf (P000 [0x00]), Local2, Local1)
            CH06 (Arg0, 0x34, 0x2F)
            /* Fatal */

            Fatal (0xFF, 0xFFFFFFFF, DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x35, 0x2F)
            /* Index */

            Local1 = DerefOf (P000 [0x00]) [0x00]
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            Index ("0", DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x39, 0x2F)
            /* LEqual */

            Local1 = (DerefOf (P000 [0x00]) == I000)
            CH06 (Arg0, 0x3A, 0x2F)
            Local1 = (I000 == DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x3B, 0x2F)
            /* LGreater */

            Local1 = (DerefOf (P000 [0x00]) > I000)
            CH06 (Arg0, 0x3C, 0x2F)
            Local1 = (I000 > DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x3D, 0x2F)
            /* LGreaterEqual */

            Local1 = (DerefOf (P000 [0x00]) >= I000)
            CH06 (Arg0, 0x3E, 0xFF)
            Local1 = (I000 >= DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x3F, 0xFF)
            /* LLess */

            Local1 = (DerefOf (P000 [0x00]) < I000)
            CH06 (Arg0, 0x40, 0x2F)
            Local1 = (I000 < DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x41, 0x2F)
            /* LLessEqual */

            Local1 = (DerefOf (P000 [0x00]) <= I000)
            CH06 (Arg0, 0x42, 0xFF)
            Local1 = (I000 <= DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x43, 0xFF)
            /* LNotEqual */

            Local1 = (DerefOf (P000 [0x00]) != I000)
            CH06 (Arg0, 0x44, 0xFF)
            Local1 = (I000 != DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x45, 0xFF)
            /* LOr */

            Local1 = (DerefOf (P000 [0x00]) || I000)
            CH06 (Arg0, 0x46, 0x2F)
            Local1 = (I000 || DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x47, 0x2F)
            /* Mod */

            Local1 = (DerefOf (P000 [0x00]) % I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x4A, 0x2F)
            Local1 = (I000 % DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x4B, 0x2F)
            /* Multiply */

            Local1 = (DerefOf (P000 [0x00]) * I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x4E, 0x2F)
            Local1 = (I000 * DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x4F, 0x2F)
            /* NAnd */

            NAnd (DerefOf (P000 [0x00]), I000, Local1)
            CH06 (Arg0, 0x52, 0x2F)
            NAnd (I000, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x53, 0x2F)
            /* NOr */

            NOr (DerefOf (P000 [0x00]), I000, Local1)
            CH06 (Arg0, 0x56, 0x2F)
            NOr (I000, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x57, 0x2F)
            /* Or */

            Local1 = (DerefOf (P000 [0x00]) | I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5A, 0x2F)
            Local1 = (I000 | DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x5B, 0x2F)
            /* ShiftLeft */

            Local1 = (DerefOf (P000 [0x00]) << I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5E, 0x2F)
            Local1 = (I000 << DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x5F, 0x2F)
            /* ShiftRight */

            Local1 = (DerefOf (P000 [0x00]) >> I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x62, 0x2F)
            Local1 = (I000 >> DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x63, 0x2F)
            /* Subtract */

            Local1 = (DerefOf (P000 [0x00]) - I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x66, 0x2F)
            Local1 = (I000 - DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x67, 0x2F)
            /* ToString */

            ToString (DerefOf (P000 [0x00]), 0x01, Local1)
            CH06 (Arg0, 0x6A, 0x2F)
            ToString (I000, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x6B, 0x2F)
            /* Wait */

            Local1 = Wait (E000, DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x6D, 0x2F)
            /* XOr */

            Local1 = (DerefOf (P000 [0x00]) ^ I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x70, 0x2F)
            Local1 = (I000 ^ DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x71, 0x2F)
            /* Mid */

            Mid (DerefOf (P000 [0x00]), 0x01, 0x01, Local1)
            CH06 (Arg0, 0x75, 0x2F)
            Mid ("123", DerefOf (P000 [0x00]), 0x01, Local1)
            CH06 (Arg0, 0x76, 0x2F)
            Mid ("123", 0x01, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x77, 0x2F)
            /* Match */

            Local1 = Match (DerefOf (P000 [0x00]), MTR, 0x00, MTR, 0x00,
                0x00)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, DerefOf (P000 [0x00]), MTR, 0x00, 0x00)
            CH06 (Arg0, 0x79, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, DerefOf (P000 [0x00]), 0x00)
            CH06 (Arg0, 0x7A, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, 0x00, DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x7B, 0x2F)
            /* DeRefOf(Index(Package, Ind, Dest)) */
            /* CondRefOf */
            CondRefOf (DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0xCC, 0x2F)
            /* CopyObject */

            CopyObject (DerefOf (Local0 = P000 [0x00]), Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Decrement */

            DerefOf (Local0 = P000 [0x00])--
            CH06 (Arg0, 0x01, 0x2F)
            /* DerefOf */

            Local1 = DerefOf (DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x02, 0x2F)
            /* FindSetLeftBit */

            FindSetLeftBit (DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x04, 0x2F)
            /* FindSetRightBit */

            FindSetRightBit (DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x06, 0x2F)
            /* FromBCD */

            FromBCD (DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x08, 0x2F)
            /* Increment */

            DerefOf (Local0 = P000 [0x00])++
            CH06 (Arg0, 0x09, 0x2F)
            /* LNot */

            Local1 = !DerefOf (Local0 = P000 [0x00])
            CH06 (Arg0, 0x0A, 0x2F)
            /* Not */

            Local1 = ~DerefOf (Local0 = P000 [0x00])
            CH06 (Arg0, 0x0C, 0x2F)
            /* ObjectType */

            Local1 = ObjectType (DerefOf (Local0 = P000 [0x00]))
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* RefOf */

            Local1 = RefOf (DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0xCD, 0x2F)
            /* Release */
            /* Reset */
            /* Signal */
            /* SizeOf */
            Local1 = SizeOf (DerefOf (Local0 = P000 [0x00]))
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Sleep */

            Sleep (DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x11, 0x2F)
            /* Stall */

            Stall (DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x12, 0x2F)
            /* Store */

            Local1 = DerefOf (Local0 = P000 [0x00])
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* ToBCD */

            ToBCD (DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x15, 0x2F)
            /* ToBuffer */

            ToBuffer (DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x17, 0x2F)
            /* ToDecimalString */

            ToDecimalString (DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x19, 0x2F)
            /* ToHexString */

            ToHexString (DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x1B, 0x2F)
            /* ToInteger */

            ToInteger (DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x1D, 0x2F)
            /* Acquire */
            /* Add */
            Local1 = (DerefOf (Local0 = P000 [0x00]) + I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x21, 0x2F)
            Local1 = (I000 + DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x22, 0x2F)
            /* And */

            Local1 = (DerefOf (Local0 = P000 [0x00]) & I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x25, 0x2F)
            Local1 = (I000 & DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x26, 0x2F)
            /* Concatenate */

            Concatenate (DerefOf (Local0 = P000 [0x00]), I000, Local1)
            CH06 (Arg0, 0x29, 0x2F)
            Concatenate (I000, DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x2A, 0x2F)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (DerefOf (Local0 = P000 [0x00]), Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x2D, 0x2F)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x2E, 0x2F)
            /* Divide */

            Divide (DerefOf (Local0 = P000 [0x00]), I000, Local2)
            CH06 (Arg0, 0x31, 0x2F)
            Divide (I000, DerefOf (Local0 = P000 [0x00]), Local2)
            CH06 (Arg0, 0x32, 0x2F)
            Divide (DerefOf (Local0 = P000 [0x00]), I000, Local2, Local1)
            CH06 (Arg0, 0x33, 0x2F)
            Divide (I000, DerefOf (Local0 = P000 [0x00]), Local2, Local1)
            CH06 (Arg0, 0x34, 0x2F)
            /* Fatal */

            Fatal (0xFF, 0xFFFFFFFF, DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x35, 0x2F)
            /* Index */

            Local1 = DerefOf (Local0 = P000 [0x00]) [0x00]
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            Index ("0", DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x39, 0x2F)
            /* LEqual */

            Local1 = (DerefOf (Local0 = P000 [0x00]) == I000)
            CH06 (Arg0, 0x3A, 0x2F)
            Local1 = (I000 == DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x3B, 0x2F)
            /* LGreater */

            Local1 = (DerefOf (Local0 = P000 [0x00]) > I000)
            CH06 (Arg0, 0x3C, 0x2F)
            Local1 = (I000 > DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x3D, 0x2F)
            /* LGreaterEqual */

            Local1 = (DerefOf (Local0 = P000 [0x00]) >= I000)
            CH06 (Arg0, 0x3E, 0xFF)
            Local1 = (I000 >= DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x3F, 0xFF)
            /* LLess */

            Local1 = (DerefOf (Local0 = P000 [0x00]) < I000)
            CH06 (Arg0, 0x40, 0x2F)
            Local1 = (I000 < DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x41, 0x2F)
            /* LLessEqual */

            Local1 = (DerefOf (Local0 = P000 [0x00]) <= I000)
            CH06 (Arg0, 0x42, 0xFF)
            Local1 = (I000 <= DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x43, 0xFF)
            /* LNotEqual */

            Local1 = (DerefOf (Local0 = P000 [0x00]) != I000)
            CH06 (Arg0, 0x44, 0xFF)
            Local1 = (I000 != DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x45, 0xFF)
            /* LOr */

            Local1 = (DerefOf (Local0 = P000 [0x00]) || I000)
            CH06 (Arg0, 0x46, 0x2F)
            Local1 = (I000 || DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x47, 0x2F)
            /* Mod */

            Local1 = (DerefOf (Local0 = P000 [0x00]) % I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x4A, 0x2F)
            Local1 = (I000 % DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x4B, 0x2F)
            /* Multiply */

            Local1 = (DerefOf (Local0 = P000 [0x00]) * I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x4E, 0x2F)
            Local1 = (I000 * DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x4F, 0x2F)
            /* NAnd */

            NAnd (DerefOf (Local0 = P000 [0x00]), I000, Local1)
            CH06 (Arg0, 0x52, 0x2F)
            NAnd (I000, DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x53, 0x2F)
            /* NOr */

            NOr (DerefOf (Local0 = P000 [0x00]), I000, Local1)
            CH06 (Arg0, 0x56, 0x2F)
            NOr (I000, DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x57, 0x2F)
            /* Or */

            Local1 = (DerefOf (Local0 = P000 [0x00]) | I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5A, 0x2F)
            Local1 = (I000 | DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x5B, 0x2F)
            /* ShiftLeft */

            Local1 = (DerefOf (Local0 = P000 [0x00]) << I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5E, 0x2F)
            Local1 = (I000 << DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x5F, 0x2F)
            /* ShiftRight */

            Local1 = (DerefOf (Local0 = P000 [0x00]) >> I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x62, 0x2F)
            Local1 = (I000 >> DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x63, 0x2F)
            /* Subtract */

            Local1 = (DerefOf (Local0 = P000 [0x00]) - I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x66, 0x2F)
            Local1 = (I000 - DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x67, 0x2F)
            /* ToString */

            ToString (DerefOf (Local0 = P000 [0x00]), 0x01, Local1)
            CH06 (Arg0, 0x6A, 0x2F)
            ToString (I000, DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x6B, 0x2F)
            /* Wait */

            Local1 = Wait (E000, DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x6D, 0x2F)
            /* XOr */

            Local1 = (DerefOf (Local0 = P000 [0x00]) ^ I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x70, 0x2F)
            Local1 = (I000 ^ DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x71, 0x2F)
            /* Mid */

            Mid (DerefOf (Local0 = P000 [0x00]), 0x01, 0x01, Local1)
            CH06 (Arg0, 0x75, 0x2F)
            Mid ("123", DerefOf (Local0 = P000 [0x00]), 0x01, Local1)
            CH06 (Arg0, 0x76, 0x2F)
            Mid ("123", 0x01, DerefOf (Local0 = P000 [0x00]), Local1)
            CH06 (Arg0, 0x77, 0x2F)
            /* Match */

            Local1 = Match (DerefOf (Local0 = P000 [0x00]), MTR, 0x00, MTR, 0x00,
                0x00)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, DerefOf (Local0 = P000 [0x00]), MTR, 0x00, 0x00)
            CH06 (Arg0, 0x79, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, DerefOf (Local0 = P000 [0x00]), 0x00)
            CH06 (Arg0, 0x7A, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, 0x00, DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x7B, 0x2F)
        }

        /* Reference to Object */

        Method (M005, 2, NotSerialized)
        {
            Debug = Arg0
            Debug = Arg1
            Local0 = ObjectType (Arg1)
            If ((Local0 != 0x04))
            {
                ERR (Arg0, Z096, __LINE__, 0x00, 0x00, Local0, 0x04)
                Return (0x01)
            }

            Local1 = DerefOf (Arg1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* CondRefOf */

            Local1 = CondRefOf (DerefOf (Arg1))
            CH06 (Arg0, 0x01, 0x2F)
            Local1 = CondRefOf (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x02, 0x2F)
            /* CopyObject */

            CopyObject (DerefOf (Arg1), Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Decrement */

            DerefOf (Arg1)--
            CH06 (Arg0, 0x03, 0x2F)
            /* DerefOf */

            Local1 = DerefOf (DerefOf (Arg1))
            CH06 (Arg0, 0x04, 0x2F)
            /* FindSetLeftBit */

            FindSetLeftBit (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x06, 0x2F)
            /* FindSetRightBit */

            FindSetRightBit (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x08, 0x2F)
            /* FromBCD */

            FromBCD (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x0A, 0x2F)
            /* Increment */

            DerefOf (Arg1)++
            CH06 (Arg0, 0x0B, 0x2F)
            /* LNot */

            Local1 = !DerefOf (Arg1)
            CH06 (Arg0, 0x0C, 0x2F)
            /* Not */

            Local1 = ~DerefOf (Arg1)
            CH06 (Arg0, 0x0E, 0x2F)
            /* ObjectType */

            Local1 = ObjectType (DerefOf (Arg1))
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* RefOf */

            Local1 = RefOf (DerefOf (Arg1))
            CH06 (Arg0, 0x0F, 0x2F)
            /* Release */
            /* Reset */
            /* Signal */
            /* SizeOf */
            Local1 = SizeOf (DerefOf (Arg1))
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* Sleep */

            Sleep (DerefOf (Arg1))
            CH06 (Arg0, 0x11, 0x2F)
            /* Stall */

            Stall (DerefOf (Arg1))
            CH06 (Arg0, 0x12, 0x2F)
            /* Store */

            Local1 = DerefOf (Arg1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* ToBCD */

            ToBCD (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x15, 0x2F)
            /* ToBuffer */

            ToBuffer (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x17, 0x2F)
            /* ToDecimalString */

            ToDecimalString (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x19, 0x2F)
            /* ToHexString */

            ToHexString (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x1B, 0x2F)
            /* ToInteger */

            ToInteger (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x1D, 0x2F)
            /* Acquire */
            /* Add */
            Local1 = (DerefOf (Arg1) + I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x21, 0x2F)
            Local1 = (I000 + DerefOf (Arg1))
            CH06 (Arg0, 0x22, 0x2F)
            /* And */

            Local1 = (DerefOf (Arg1) & I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x25, 0x2F)
            Local1 = (I000 & DerefOf (Arg1))
            CH06 (Arg0, 0x26, 0x2F)
            /* Concatenate */

            Concatenate (DerefOf (Arg1), I000, Local1)
            CH06 (Arg0, 0x29, 0x2F)
            Concatenate (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x2A, 0x2F)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (DerefOf (Arg1), Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x2D, 0x2F)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x2E, 0x2F)
            /* Divide */

            Divide (DerefOf (Arg1), I000, Local2)
            CH06 (Arg0, 0x31, 0x2F)
            Divide (I000, DerefOf (Arg1), Local2)
            CH06 (Arg0, 0x32, 0x2F)
            Divide (DerefOf (Arg1), I000, Local2, Local1)
            CH06 (Arg0, 0x33, 0x2F)
            Divide (I000, DerefOf (Arg1), Local2, Local1)
            CH06 (Arg0, 0x34, 0x2F)
            /* Fatal */

            Fatal (0xFF, 0xFFFFFFFF, DerefOf (Arg1))
            CH06 (Arg0, 0x35, 0x2F)
            /* Index */

            Local1 = DerefOf (Arg1) [0x00]
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            Index ("0", DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x39, 0x2F)
            /* LEqual */

            Local1 = (DerefOf (Arg1) == I000)
            CH06 (Arg0, 0x3A, 0x2F)
            Local1 = (I000 == DerefOf (Arg1))
            CH06 (Arg0, 0x3B, 0x2F)
            /* LGreater */

            Local1 = (DerefOf (Arg1) > I000)
            CH06 (Arg0, 0x3C, 0x2F)
            Local1 = (I000 > DerefOf (Arg1))
            CH06 (Arg0, 0x3D, 0x2F)
            /* LGreaterEqual */

            Local1 = (DerefOf (Arg1) >= I000)
            CH06 (Arg0, 0x3E, 0xFF)
            Local1 = (I000 >= DerefOf (Arg1))
            CH06 (Arg0, 0x3F, 0xFF)
            /* LLess */

            Local1 = (DerefOf (Arg1) < I000)
            CH06 (Arg0, 0x40, 0x2F)
            Local1 = (I000 < DerefOf (Arg1))
            CH06 (Arg0, 0x41, 0x2F)
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
            CH06 (Arg0, 0x46, 0x2F)
            Local1 = (I000 || DerefOf (Arg1))
            CH06 (Arg0, 0x47, 0x2F)
            /* Mod */

            Local1 = (DerefOf (Arg1) % I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x4A, 0x2F)
            Local1 = (I000 % DerefOf (Arg1))
            CH06 (Arg0, 0x4B, 0x2F)
            /* Multiply */

            Local1 = (DerefOf (Arg1) * I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x4E, 0x2F)
            Local1 = (I000 * DerefOf (Arg1))
            CH06 (Arg0, 0x4F, 0x2F)
            /* NAnd */

            NAnd (DerefOf (Arg1), I000, Local1)
            CH06 (Arg0, 0x52, 0x2F)
            NAnd (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x53, 0x2F)
            /* NOr */

            NOr (DerefOf (Arg1), I000, Local1)
            CH06 (Arg0, 0x56, 0x2F)
            NOr (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x57, 0x2F)
            /* Or */

            Local1 = (DerefOf (Arg1) | I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5A, 0x2F)
            Local1 = (I000 | DerefOf (Arg1))
            CH06 (Arg0, 0x5B, 0x2F)
            /* ShiftLeft */

            Local1 = (DerefOf (Arg1) << I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5E, 0x2F)
            Local1 = (I000 << DerefOf (Arg1))
            CH06 (Arg0, 0x5F, 0x2F)
            /* ShiftRight */

            Local1 = (DerefOf (Arg1) >> I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x62, 0x2F)
            Local1 = (I000 >> DerefOf (Arg1))
            CH06 (Arg0, 0x63, 0x2F)
            /* Subtract */

            Local1 = (DerefOf (Arg1) - I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x66, 0x2F)
            Local1 = (I000 - DerefOf (Arg1))
            CH06 (Arg0, 0x67, 0x2F)
            /* ToString */

            ToString (DerefOf (Arg1), 0x01, Local1)
            CH06 (Arg0, 0x6A, 0x2F)
            ToString (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x6B, 0x2F)
            /* Wait */

            Local1 = Wait (E000, DerefOf (Arg1))
            CH06 (Arg0, 0x6D, 0x2F)
            /* XOr */

            Local1 = (DerefOf (Arg1) ^ I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x70, 0x2F)
            Local1 = (I000 ^ DerefOf (Arg1))
            CH06 (Arg0, 0x71, 0x2F)
            /* Mid */

            Mid (DerefOf (Arg1), 0x01, 0x01, Local1)
            CH06 (Arg0, 0x75, 0x2F)
            Mid ("123", DerefOf (Arg1), 0x01, Local1)
            CH06 (Arg0, 0x76, 0x2F)
            Mid ("123", 0x01, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x77, 0x2F)
            /* Match */

            Local1 = Match (DerefOf (Arg1), MTR, 0x00, MTR, 0x00, 0x00)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, DerefOf (Arg1), MTR, 0x00, 0x00)
            CH06 (Arg0, 0x79, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, DerefOf (Arg1), 0x00)
            CH06 (Arg0, 0x7A, 0x2F)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, 0x00, DerefOf (Arg1))
            CH06 (Arg0, 0x7B, 0x2F)
            Return (0x00)
        }

        /* Result of Method invocation */

        Method (M006, 1, Serialized)
        {
            Method (M000, 0, NotSerialized)
            {
                /* intermediate storing to force ASL compiler */
                /* not report "Invalid type (Method returns)" */
                Local0 = Package (0x01)
                    {
                        0x63
                    }
                Return (Local0)
            }

            Name (SS00, "0")
            /* CondRefOf */
            /* **** 10/2016 changed method invocation to just a namestring */
            /* CondRefOf no longer invokes the method */
            If (Y601)
            {
                Local1 = CondRefOf (M000)
                CH06 (Arg0, 0x00, 0x2F)
                CondRefOf (M000, Local1)
                CH06 (Arg0, 0x01, 0x2F)
            }

            /* CopyObject */

            CopyObject (M000 (), Local1)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
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
            /* **** ObjectType */
            /* Nov. 2012: Method invocation as arg to ObjectType is now illegal */
            Local0 = ObjectType (M000)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            /* RefOf */
            /* **** Oct. 2016: Method invocation as arg to RefOf is now illegal */
            /*		if (y601) { */
            /*			Store (RefOf(m000()), Local1) */
            /*			CH06(arg0, 14, 47) */
            /*		} */
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

            Local1 = (M000 () + I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x21, 0x2F)
            Local1 = (I000 + M000 ())
            CH06 (Arg0, 0x22, 0x2F)
            /* And */

            Local1 = (M000 () & I000) /* \M4B4.I000 */
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

            If (Y900)
            {
                Local1 = M000 () [0x00]
                CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
                Index ("0", M000 (), Local1)
                CH06 (Arg0, 0x39, 0x2F)
            }
            Else
            {
                CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
                Local1 = M000 () [0x00]
                CH04 (__METHOD__, 0x00, 0x55, Z094, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
                Index ("0", M000 (), Local1)
                CH04 (__METHOD__, 0x00, 0xFF, Z094, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
                Local1 = SS00 [M000 ()]
                CH04 (__METHOD__, 0x00, 0x2F, Z094, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }

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

            Local1 = (M000 () % I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x4A, 0x2F)
            Local1 = (I000 % M000 ())
            CH06 (Arg0, 0x4B, 0x2F)
            /* Multiply */

            Local1 = (M000 () * I000) /* \M4B4.I000 */
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

            Local1 = (M000 () | I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5A, 0x2F)
            Local1 = (I000 | M000 ())
            CH06 (Arg0, 0x5B, 0x2F)
            /* ShiftLeft */

            Local1 = (M000 () << I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x5E, 0x2F)
            Local1 = (I000 << M000 ())
            CH06 (Arg0, 0x5F, 0x2F)
            /* ShiftRight */

            Local1 = (M000 () >> I000) /* \M4B4.I000 */
            CH06 (Arg0, 0x62, 0x2F)
            Local1 = (I000 >> M000 ())
            CH06 (Arg0, 0x63, 0x2F)
            /* Subtract */

            Local1 = (M000 () - I000) /* \M4B4.I000 */
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

            Local1 = (M000 () ^ I000) /* \M4B4.I000 */
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
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
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

        Method (M007, 1, Serialized)
        {
            Name (P000, Package (0x01)
            {
                0x63
            })
            Name (I000, 0x00) /* Label to check m000 invocations */
            Method (M000, 2, NotSerialized)
            {
                I000 = Arg0
                If ((Arg1 == 0x00))
                {
                    Local0 = RefOf (P100)
                }
                ElseIf ((Arg1 == 0x01))
                {
                    Local0 = RefOf (P000)
                }

                Return (Local0)
            }

            Method (CH00, 2, NotSerialized)
            {
                If ((I000 != Arg1))
                {
                    ERR (Arg0, Z096, __LINE__, 0x00, 0x00, I000, Arg1)
                }
            }

            Name (LPN0, 0x02)
            Name (LPC0, 0x00)
            While (LPN0)
            {
                Local0 = (0x03 * LPC0) /* \M4B4.M007.LPC0 */
                I000 = 0x00
                Local1 = DerefOf (M000 (0x01, LPC0))
                CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
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

        /* Result of Method with checking of invocation */

        Method (M008, 1, Serialized)
        {
            Name (I000, 0x00) /* Label to check m000 invocations */
            Method (M000, 1, NotSerialized)
            {
                I000 = Arg0
                Local0 = Package (0x01)
                    {
                        0x63
                    }
                Return (Local0)
            }

            Method (CH00, 2, NotSerialized)
            {
                If ((I000 != Arg1))
                {
                    ERR (Arg0, Z096, __LINE__, 0x00, 0x00, I000, Arg1)
                }
            }

            /* CondRefOf */
            /* **** 10/2016 changed method invocation to just a namestring */
            /* CondRefOf no longer invokes the method */
            If (Y601)
            {
                Local1 = CondRefOf (M000)
                CH06 (Arg0, 0x01, 0x2F)
                CH00 (Arg0, 0x01)
            }

            Local1 = CondRefOf (M000)
            CH06 (Arg0, 0x02, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x02)
            }

            /* DerefOf */

            Local1 = DerefOf (M000 (0x03))
            CH06 (Arg0, 0x03, 0x2F)
            CH00 (Arg0, 0x03)
            /* RefOf */
            /* Oct. 2016: Method invocation as arg to RefOf is now illegal */
            /*		if (y601) { */
            /*			Store (RefOf(m000(4)), Local1) */
            /*			CH06(arg0, 4, 47) */
            /*			CH00(arg0, 4) */
            /*		} */
            /* Release */
            Release (M000 (0x05))
            CH06 (Arg0, 0x05, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x05)
            }

            /* Reset */

            Reset (M000 (0x06))
            CH06 (Arg0, 0x06, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x06)
            }

            /* Signal */

            Signal (M000 (0x07))
            CH06 (Arg0, 0x07, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x07)
            }

            /* Acquire */

            Local1 = Acquire (M000 (0x08), 0x0000)
            CH06 (Arg0, 0x08, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x08)
            }

            /* Index */

            CH03 (__METHOD__, Z094, __LINE__, 0x00, 0x00)
            Store (M000 (0x09) [0x00], Local1)
            If (Y900)
            {
                CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
                CH00 (Arg0, 0x09)
            }
            Else
            {
                CH04 (__METHOD__, 0x00, 0x55, Z094, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }

            /* Wait */

            Local1 = Wait (M000 (0x0A), 0x00)
            CH06 (Arg0, 0x09, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x0A)
            }

            /* Match */

            Local1 = Match (M000 (0x0B), MTR, 0x00, MTR, 0x00, 0x00)
            CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
            CH00 (Arg0, 0x0B)
        }

        SET0 (Z096, __METHOD__, 0x00)
        CH03 (__METHOD__, Z096, __LINE__, 0x00, 0x00)
        /* Local Named Object */

        M000 (__METHOD__)
        /* Global Named Object */

        M001 (__METHOD__)
        /* Argument */

        M002 (__METHOD__, Package (0x01)
            {
                0x62
            })
        /* Local */

        M003 (Concatenate (__METHOD__, "-m003"))
        /* An element of Package */

        M004 (Concatenate (__METHOD__, "-m004"))
        /* Reference to Local Named Object */

        M005 (Concatenate (__METHOD__, "-m005-RefLocName"), RefOf (P000))
        Local0 = RefOf (P000)
        M005 (Concatenate (__METHOD__, "-m005-RefLocName2"), Local0)
        CondRefOf (P000, Local0)
        M005 (Concatenate (__METHOD__, "-m005-CondRefLocName"), Local0)
        M005 (Concatenate (__METHOD__, "-m005-RefGlobName"), RefOf (P100))
        Local0 = RefOf (P100)
        M005 (Concatenate (__METHOD__, "-m005-RefGlobName2"), Local0)
        CondRefOf (P100, Local0)
        M005 (Concatenate (__METHOD__, "-m005-CondRefGlobName"), Local0)
        /* Reference to Local */

        Local0 = Package (0x01)
            {
                0x62
            }
        M005 (Concatenate (__METHOD__, "-m005-RefLocal"), RefOf (Local0))
        Local1 = RefOf (Local0)
        M005 (Concatenate (__METHOD__, "-m005-RefLocal2"), Local1)
        CondRefOf (Local0, Local1)
        M005 (Concatenate (__METHOD__, "-m005-CondRefLocal"), Local1)
        /* Reference to Arg */

        M005 (Concatenate (__METHOD__, "-m005-RefArg"), RefOf (Arg0))
        Local0 = RefOf (Arg0)
        M005 (Concatenate (__METHOD__, "-m005-RefArg2"), Local0)
        CondRefOf (Arg0, Local0)
        M005 (Concatenate (__METHOD__, "-m005-CondRefArg"), Local0)
        /* Index to Package */

        Name (PP00, Package (0x01)
        {
            Package (0x01)
            {
                0x62
            }
        })
        If (Y113)
        {
            M005 (Concatenate (__METHOD__, "-m005-Index"), PP00 [0x00])
        }

        Store (PP00 [0x00], Local0)
        M005 (Concatenate (__METHOD__, "-m005-Index2"), Local0)
        If (Y113)
        {
            M005 (Concatenate (__METHOD__, "-m005-Index3"), Local0 = PP00 [0x00])
        }

        Local0 = PP00 [0x00]
        M005 (Concatenate (__METHOD__, "-m005-Index4"), Local0)
        Local1 = Local0 = PP00 [0x00]
        M005 (Concatenate (__METHOD__, "-m005-Index5"), Local1)
        /* Result of Method invocation */

        M006 (Concatenate (__METHOD__, "-m006"))
        /* Reference to Object as Result of Method invocation */

        If (Y500)
        {
            M007 (Concatenate (__METHOD__, "-m007"))
        }

        /* Result of Method with checking of invocation */

        M008 (Concatenate (__METHOD__, "-m008"))
        RST0 ()
    }
