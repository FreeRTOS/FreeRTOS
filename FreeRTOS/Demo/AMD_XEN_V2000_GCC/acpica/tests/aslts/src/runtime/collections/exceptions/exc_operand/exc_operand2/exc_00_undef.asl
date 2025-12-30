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
     *  Uninitialized Data
     *
     * (verify exceptions caused by use of Uninitialized Data)
     */
    Name (Z092, 0x5C)
    /* Expected exceptions: */
    /* */
    /* 49 - AE_AML_UNINITIALIZED_LOCAL */
    /* 50 - AE_AML_UNINITIALIZED_ARG */
    /* 51 - AE_AML_UNINITIALIZED_ELEMENT */
    Method (M4B0, 1, Serialized)
    {
        Name (I000, 0x00)
        Event (E000)
        /* Uninitialized Local */

        Method (M000, 2, NotSerialized)
        {
            If (Arg1)
            {
                Local0 = 0x00
            }

            /* CondRefOf */

            CondRefOf (Local0, Local1)
            CH03 (__METHOD__, Z092, __LINE__, 0x00, 0x00)
            /* CopyObject */

            CopyObject (Local0, Local1)
            CH06 (Arg0, 0x00, 0x31)
            /* Decrement */

            Local0--
            CH06 (Arg0, 0x01, 0x31)
            /* DerefOf */

            Local1 = DerefOf (Local0)
            CH06 (Arg0, 0x02, 0x31)
            /* FindSetLeftBit */

            FindSetLeftBit (Local0, Local1)
            CH06 (Arg0, 0x04, 0x31)
            /* FindSetRightBit */

            FindSetRightBit (Local0, Local1)
            CH06 (Arg0, 0x06, 0x31)
            /* FromBCD */

            FromBCD (Local0, Local1)
            CH06 (Arg0, 0x08, 0x31)
            /* Increment */

            Local0++
            CH06 (Arg0, 0x09, 0x31)
            /* LNot */

            Local1 = !Local0
            CH06 (Arg0, 0x0A, 0x31)
            /* Not */

            Local1 = ~Local0
            CH06 (Arg0, 0x0C, 0x31)
            /* ObjectType */

            Local1 = ObjectType (Local0)
            CH03 (__METHOD__, Z092, __LINE__, 0x00, 0x00)
            /* RefOf */

            Local1 = RefOf (Local0)
            CH03 (__METHOD__, Z092, __LINE__, 0x00, 0x00)
            /* Release */

            Release (Local0)
            CH06 (Arg0, 0x0D, 0x31)
            /* Reset */

            Reset (Local0)
            CH06 (Arg0, 0x0E, 0x31)
            /* Signal */

            Signal (Local0)
            CH06 (Arg0, 0x0F, 0x31)
            /* SizeOf */

            Local1 = SizeOf (Local0)
            CH06 (Arg0, 0x10, 0x31)
            /* Sleep */

            Sleep (Local0)
            CH06 (Arg0, 0x11, 0x31)
            /* Stall */

            Stall (Local0)
            CH06 (Arg0, 0x12, 0x31)
            /* Store */

            Local1 = Local0
            CH06 (Arg0, 0x13, 0x31)
            /* ToBCD */

            ToBCD (Local0, Local1)
            CH06 (Arg0, 0x15, 0x31)
            /* ToBuffer */

            ToBuffer (Local0, Local1)
            CH06 (Arg0, 0x17, 0x31)
            /* ToDecimalString */

            ToDecimalString (Local0, Local1)
            CH06 (Arg0, 0x19, 0x31)
            /* ToHexString */

            ToHexString (Local0, Local1)
            CH06 (Arg0, 0x1B, 0x31)
            /* ToInteger */

            ToInteger (Local0, Local1)
            CH06 (Arg0, 0x1D, 0x31)
            /* Acquire */

            Local1 = Acquire (Local0, 0x0064)
            CH06 (Arg0, 0x1E, 0x31)
            /* Add */

            Local1 = (Local0 + I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x21, 0x31)
            Local1 = (I000 + Local0)
            CH06 (Arg0, 0x22, 0x31)
            /* And */

            Local1 = (Local0 & I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x25, 0x31)
            Local1 = (I000 & Local0)
            CH06 (Arg0, 0x26, 0x31)
            /* Concatenate */

            Concatenate (Local0, I000, Local1)
            CH06 (Arg0, 0x29, 0x31)
            Concatenate (I000, Local0, Local1)
            CH06 (Arg0, 0x2A, 0x31)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (Local0, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x2D, 0x31)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local0, Local1)
            CH06 (Arg0, 0x2E, 0x31)
            /* Divide */

            Divide (Local0, I000, Local2)
            CH06 (Arg0, 0x31, 0x31)
            Divide (I000, Local0, Local2)
            CH06 (Arg0, 0x32, 0x31)
            Divide (Local0, I000, Local2, Local1)
            CH06 (Arg0, 0x33, 0x31)
            Divide (I000, Local0, Local2, Local1)
            CH06 (Arg0, 0x34, 0x31)
            /* Fatal */

            Fatal (0xFF, 0xFFFFFFFF, Local0)
            CH06 (Arg0, 0x35, 0x31)
            /* Index */

            Local1 = Local0 [0x00]
            CH06 (Arg0, 0x38, 0x31)
            Index ("0", Local0, Local1)
            CH06 (Arg0, 0x39, 0x31)
            /* LEqual */

            Local1 = (Local0 == I000)
            CH06 (Arg0, 0x3A, 0x31)
            Local1 = (I000 == Local0)
            CH06 (Arg0, 0x3B, 0x31)
            /* LGreater */

            Local1 = (Local0 > I000)
            CH06 (Arg0, 0x3C, 0x31)
            Local1 = (I000 > Local0)
            CH06 (Arg0, 0x3D, 0x31)
            /* LGreaterEqual */

            Local1 = (Local0 >= I000)
            CH06 (Arg0, 0x3E, 0xFF)
            Local1 = (I000 >= Local0)
            CH06 (Arg0, 0x3F, 0xFF)
            /* LLess */

            Local1 = (Local0 < I000)
            CH06 (Arg0, 0x40, 0x31)
            Local1 = (I000 < Local0)
            CH06 (Arg0, 0x41, 0x31)
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
            CH06 (Arg0, 0x46, 0x31)
            Local1 = (I000 || Local0)
            CH06 (Arg0, 0x47, 0x31)
            /* Mod */

            Local1 = (Local0 % I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x4A, 0x31)
            Local1 = (I000 % Local0)
            CH06 (Arg0, 0x4B, 0x31)
            /* Multiply */

            Local1 = (Local0 * I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x4E, 0x31)
            Local1 = (I000 * Local0)
            CH06 (Arg0, 0x4F, 0x31)
            /* NAnd */

            NAnd (Local0, I000, Local1)
            CH06 (Arg0, 0x52, 0x31)
            NAnd (I000, Local0, Local1)
            CH06 (Arg0, 0x53, 0x31)
            /* NOr */

            NOr (Local0, I000, Local1)
            CH06 (Arg0, 0x56, 0x31)
            NOr (I000, Local0, Local1)
            CH06 (Arg0, 0x57, 0x31)
            /* Or */

            Local1 = (Local0 | I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x5A, 0x31)
            Local1 = (I000 | Local0)
            CH06 (Arg0, 0x5B, 0x31)
            /* ShiftLeft */

            Local1 = (Local0 << I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x5E, 0x31)
            Local1 = (I000 << Local0)
            CH06 (Arg0, 0x5F, 0x31)
            /* ShiftRight */

            Local1 = (Local0 >> I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x62, 0x31)
            Local1 = (I000 >> Local0)
            CH06 (Arg0, 0x63, 0x31)
            /* Subtract */

            Local1 = (Local0 - I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x66, 0x31)
            Local1 = (I000 - Local0)
            CH06 (Arg0, 0x67, 0x31)
            /* ToString */

            ToString (Local0, 0x01, Local1)
            CH06 (Arg0, 0x6A, 0x31)
            ToString (I000, Local0, Local1)
            CH06 (Arg0, 0x6B, 0x31)
            /* Wait */

            Local1 = Wait (Local0, I000)
            CH06 (Arg0, 0x6C, 0x31)
            Local1 = Wait (E000, Local0)
            CH06 (Arg0, 0x6D, 0x31)
            /* XOr */

            Local1 = (Local0 ^ I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x70, 0x31)
            Local1 = (I000 ^ Local0)
            CH06 (Arg0, 0x71, 0x31)
            /* Mid */

            Mid (Local0, 0x01, 0x01, Local1)
            CH06 (Arg0, 0x75, 0x31)
            Mid ("123", Local0, 0x01, Local1)
            CH06 (Arg0, 0x76, 0x31)
            Mid ("123", 0x01, Local0, Local1)
            CH06 (Arg0, 0x77, 0x31)
            /* Match */

            Local1 = Match (Local0, MTR, 0x00, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x78, 0x31)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, Local0, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x79, 0x31)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, Local0, 0x00)
            CH06 (Arg0, 0x7A, 0x31)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, 0x00, Local0)
            CH06 (Arg0, 0x7B, 0x31)
        }

        /* Uninitialized element of Package */

        Method (M001, 1, Serialized)
        {
            Name (P000, Package (0x01){})
            /* DeRefOf(Index(Package, Ind)) */

            Local1 = DerefOf (P000 [0x00])
            CH04 (__METHOD__, 0x01, 0x33, Z092, __LINE__, 0x00, 0x00)
            /* CondRefOf */

            CondRefOf (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x01, 0xFF)
            /* CopyObject */

            CopyObject (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x02, 0xFF)
            /* Decrement */

            DerefOf (P000 [0x00])--
            CH06 (Arg0, 0x03, 0xFF)
            /* DerefOf */

            Local1 = DerefOf (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x04, 0xFF)
            /* FindSetLeftBit */

            FindSetLeftBit (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x06, 0xFF)
            /* FindSetRightBit */

            FindSetRightBit (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x08, 0xFF)
            /* FromBCD */

            FromBCD (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x0A, 0xFF)
            /* Increment */

            DerefOf (P000 [0x00])++
            CH06 (Arg0, 0x0B, 0xFF)
            /* LNot */

            Local1 = !DerefOf (P000 [0x00])
            CH06 (Arg0, 0x0C, 0xFF)
            /* Not */

            Local1 = ~DerefOf (P000 [0x00])
            CH06 (Arg0, 0x0E, 0xFF)
            /* ObjectType */

            If (X104)
            {
                Local1 = ObjectType (DerefOf (P000 [0x00]))
                CH03 (__METHOD__, Z092, __LINE__, 0x00, 0x00)
            }

            /* RefOf */

            Local1 = RefOf (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x0F, 0xFF)
            /* Release */
            /* Reset */
            /* Signal */
            /* SizeOf */
            Local1 = SizeOf (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x10, 0xFF)
            /* Sleep */

            Sleep (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x11, 0xFF)
            /* Stall */

            Stall (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x12, 0xFF)
            /* Store */

            Local1 = DerefOf (P000 [0x00])
            CH06 (Arg0, 0x13, 0xFF)
            /* ToBCD */

            ToBCD (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x15, 0xFF)
            /* ToBuffer */

            ToBuffer (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x17, 0xFF)
            /* ToDecimalString */

            ToDecimalString (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x19, 0xFF)
            /* ToHexString */

            ToHexString (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x1B, 0xFF)
            /* ToInteger */

            ToInteger (DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x1D, 0xFF)
            /* Acquire */
            /* Add */
            Local1 = (DerefOf (P000 [0x00]) + I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x21, 0xFF)
            Local1 = (I000 + DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x22, 0xFF)
            /* And */

            Local1 = (DerefOf (P000 [0x00]) & I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x25, 0xFF)
            Local1 = (I000 & DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x26, 0xFF)
            /* Concatenate */

            Concatenate (DerefOf (P000 [0x00]), I000, Local1)
            CH06 (Arg0, 0x29, 0xFF)
            Concatenate (I000, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x2A, 0xFF)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (DerefOf (P000 [0x00]), Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x2D, 0xFF)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x2E, 0xFF)
            /* Divide */

            Divide (DerefOf (P000 [0x00]), I000, Local2)
            CH06 (Arg0, 0x31, 0xFF)
            Divide (I000, DerefOf (P000 [0x00]), Local2)
            CH06 (Arg0, 0x32, 0xFF)
            Divide (DerefOf (P000 [0x00]), I000, Local2, Local1)
            CH06 (Arg0, 0x33, 0xFF)
            Divide (I000, DerefOf (P000 [0x00]), Local2, Local1)
            CH06 (Arg0, 0x34, 0xFF)
            /* Fatal */

            Fatal (0xFF, 0xFFFFFFFF, DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x35, 0xFF)
            /* Index */

            Local1 = DerefOf (P000 [0x00]) [0x00]
            CH06 (Arg0, 0x38, 0xFF)
            Index ("0", DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x39, 0xFF)
            /* LEqual */

            Local1 = (DerefOf (P000 [0x00]) == I000)
            CH06 (Arg0, 0x3A, 0xFF)
            Local1 = (I000 == DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x3B, 0xFF)
            /* LGreater */

            Local1 = (DerefOf (P000 [0x00]) > I000)
            CH06 (Arg0, 0x3C, 0xFF)
            Local1 = (I000 > DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x3D, 0xFF)
            /* LGreaterEqual */

            Local1 = (DerefOf (P000 [0x00]) >= I000)
            CH06 (Arg0, 0x3E, 0xFF)
            Local1 = (I000 >= DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x3F, 0xFF)
            /* LLess */

            Local1 = (DerefOf (P000 [0x00]) < I000)
            CH06 (Arg0, 0x40, 0xFF)
            Local1 = (I000 < DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x41, 0xFF)
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
            CH06 (Arg0, 0x46, 0xFF)
            Local1 = (I000 || DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x47, 0xFF)
            /* Mod */

            Local1 = (DerefOf (P000 [0x00]) % I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x4A, 0xFF)
            Local1 = (I000 % DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x4B, 0xFF)
            /* Multiply */

            Local1 = (DerefOf (P000 [0x00]) * I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x4E, 0xFF)
            Local1 = (I000 * DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x4F, 0xFF)
            /* NAnd */

            NAnd (DerefOf (P000 [0x00]), I000, Local1)
            CH06 (Arg0, 0x52, 0xFF)
            NAnd (I000, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x53, 0xFF)
            /* NOr */

            NOr (DerefOf (P000 [0x00]), I000, Local1)
            CH06 (Arg0, 0x56, 0xFF)
            NOr (I000, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x57, 0xFF)
            /* Or */

            Local1 = (DerefOf (P000 [0x00]) | I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x5A, 0xFF)
            Local1 = (I000 | DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x5B, 0xFF)
            /* ShiftLeft */

            Local1 = (DerefOf (P000 [0x00]) << I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x5E, 0xFF)
            Local1 = (I000 << DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x5F, 0xFF)
            /* ShiftRight */

            Local1 = (DerefOf (P000 [0x00]) >> I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x62, 0xFF)
            Local1 = (I000 >> DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x63, 0xFF)
            /* Subtract */

            Local1 = (DerefOf (P000 [0x00]) - I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x66, 0xFF)
            Local1 = (I000 - DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x67, 0xFF)
            /* ToString */

            ToString (DerefOf (P000 [0x00]), 0x01, Local1)
            CH06 (Arg0, 0x6A, 0xFF)
            ToString (I000, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x6B, 0xFF)
            /* Wait */

            Local1 = Wait (E000, DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x6D, 0xFF)
            /* XOr */

            Local1 = (DerefOf (P000 [0x00]) ^ I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x70, 0xFF)
            Local1 = (I000 ^ DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x71, 0xFF)
            /* Mid */

            Mid (DerefOf (P000 [0x00]), 0x01, 0x01, Local1)
            CH06 (Arg0, 0x75, 0xFF)
            Mid ("123", DerefOf (P000 [0x00]), 0x01, Local1)
            CH06 (Arg0, 0x76, 0xFF)
            Mid ("123", 0x01, DerefOf (P000 [0x00]), Local1)
            CH06 (Arg0, 0x77, 0xFF)
            /* Match */

            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, DerefOf (P000 [0x00]), MTR, 0x00, 0x00)
            CH06 (Arg0, 0x79, 0xFF)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, DerefOf (P000 [0x00]), 0x00)
            CH06 (Arg0, 0x7A, 0xFF)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, 0x00, DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x7B, 0xFF)
            /* DeRefOf(Index(Package, Ind, Dest)) */
            /* This should cause an exception */
            /* on storing to Dest (see m001) */
            Return (0x00)
        }

        /*
         // Causes Remark on compilation
         // Uninitialized Arg
         Method(m002, 2)
         {
         if (arg1) {
         Store(0, arg2)
         }
         // CondRefOf

         CondRefOf(arg2)
         CH03(ts, z092, 6, __LINE__, 0)
         CondRefOf(arg2, Local1)
         CH03(ts, z092, 7, __LINE__, 0)
         // CopyObject
         CopyObject(arg2, Local1)
         CH06(arg0, 0, 50)
         // Decrement
         Decrement(arg2)
         CH06(arg0, 1, 50)
         // DerefOf
         DerefOf(arg2)
         CH06(arg0, 2, 50)
         // FindSetLeftBit
         FindSetLeftBit(arg2)
         CH06(arg0, 3, 50)
         FindSetLeftBit(arg2, Local1)
         CH06(arg0, 4, 50)
         // FindSetRightBit
         FindSetRightBit(arg2)
         CH06(arg0, 5, 50)
         FindSetRightBit(arg2, Local1)
         CH06(arg0, 6, 50)
         // FromBCD
         FromBCD(arg2)
         CH06(arg0, 7, 50)
         FromBCD(arg2, Local1)
         CH06(arg0, 8, 50)
         // Increment
         Increment(arg2)
         CH06(arg0, 9, 50)
         // LNot
         LNot(arg2)
         CH06(arg0, 10, 50)
         // Not
         Not(arg2)
         CH06(arg0, 11, 50)
         Not(arg2, Local1)
         CH06(arg0, 12, 50)
         // ObjectType
         ObjectType(arg2)
         CH03(ts, z092, 8, __LINE__, 0)
         // RefOf
         RefOf(arg2)
         CH03(ts, z092, 9, __LINE__, 0)
         // Release
         Release(arg2)
         CH06(arg0, 13, 50)
         // Reset
         Reset(arg2)
         CH06(arg0, 14, 50)
         // Signal
         Signal(arg2)
         CH06(arg0, 15, 50)
         // SizeOf
         SizeOf(arg2)
         CH06(arg0, 16, 50)
         // Sleep
         Sleep(arg2)
         CH06(arg0, 17, 50)
         // Stall
         Stall(arg2)
         CH06(arg0, 18, 50)
         // Store
         Store(arg2, Local1)
         CH06(arg0, 19, 50)
         // ToBCD
         ToBCD(arg2)
         CH06(arg0, 20, 50)
         ToBCD(arg2, Local1)
         CH06(arg0, 21, 50)
         // ToBuffer
         ToBuffer(arg2)
         CH06(arg0, 22, 50)
         ToBuffer(arg2, Local1)
         CH06(arg0, 23, 50)
         // ToDecimalString
         ToDecimalString(arg2)
         CH06(arg0, 24, 50)
         ToDecimalString(arg2, Local1)
         CH06(arg0, 25, 50)
         // ToHexString
         ToHexString(arg2)
         CH06(arg0, 26, 50)
         ToHexString(arg2, Local1)
         CH06(arg0, 27, 50)
         // ToInteger
         ToInteger(arg2)
         CH06(arg0, 28, 50)
         ToInteger(arg2, Local1)
         CH06(arg0, 29, 50)
         // Acquire
         Store(Acquire(arg2, 100), Local1)
         CH06(arg0, 30, 50)
         // Add
         Add(arg2, i000)
         CH06(arg0, 31, 50)
         Add(i000, arg2)
         CH06(arg0, 32, 50)
         Add(arg2, i000, Local1)
         CH06(arg0, 33, 50)
         Add(i000, arg2, Local1)
         CH06(arg0, 34, 50)
         // And
         And(arg2, i000)
         CH06(arg0, 35, 50)
         And(i000, arg2)
         CH06(arg0, 36, 50)
         And(arg2, i000, Local1)
         CH06(arg0, 37, 50)
         And(i000, arg2, Local1)
         CH06(arg0, 38, 50)
         // Concatenate
         Concatenate(arg2, i000)
         CH06(arg0, 39, 50)
         Concatenate(i000, arg2)
         CH06(arg0, 40, 50)
         Concatenate(arg2, i000, Local1)
         CH06(arg0, 41, 50)
         Concatenate(i000, arg2, Local1)
         CH06(arg0, 42, 50)
         // ConcatenateResTemplate
         ConcatenateResTemplate(arg2, ResourceTemplate(){})
         CH06(arg0, 43, 50)
         ConcatenateResTemplate(ResourceTemplate(){}, arg2)
         CH06(arg0, 44, 50)
         ConcatenateResTemplate(arg2, ResourceTemplate(){}, Local1)
         CH06(arg0, 45, 50)
         ConcatenateResTemplate(ResourceTemplate(){}, arg2, Local1)
         CH06(arg0, 46, 50)
         // Divide
         Divide(arg2, i000)
         CH06(arg0, 47, 50)
         Divide(i000, arg2)
         CH06(arg0, 48, 50)
         Divide(arg2, i000, Local2)
         CH06(arg0, 49, 50)
         Divide(i000, arg2, Local2)
         CH06(arg0, 50, 50)
         Divide(arg2, i000, Local2, Local1)
         CH06(arg0, 51, 50)
         Divide(i000, arg2, Local2, Local1)
         CH06(arg0, 52, 50)
         // Fatal
         Fatal(0xff, 0xffffffff, arg2)
         CH06(arg0, 53, 50)
         // Index
         Index(arg2, 0)
         CH06(arg0, 54, 50)
         Index("0", arg2)
         CH06(arg0, 55, 50)
         Index(arg2, 0, Local1)
         CH06(arg0, 56, 50)
         Index("0", arg2, Local1)
         CH06(arg0, 57, 50)
         // LEqual
         LEqual(arg2, i000)
         CH06(arg0, 58, 50)
         LEqual(i000, arg2)
         CH06(arg0, 59, 50)
         // LGreater
         LGreater(arg2, i000)
         CH06(arg0, 60, 50)
         LGreater(i000, arg2)
         CH06(arg0, 61, 50)
         // LGreaterEqual
         LGreaterEqual(arg2, i000)
         CH06(arg0, 62, 0xff)
         LGreaterEqual(i000, arg2)
         CH06(arg0, 63, 0xff)
         // LLess
         LLess(arg2, i000)
         CH06(arg0, 64, 50)
         LLess(i000, arg2)
         CH06(arg0, 65, 50)
         // LLessEqual
         LLessEqual(arg2, i000)
         CH06(arg0, 66, 0xff)
         LLessEqual(i000, arg2)
         CH06(arg0, 67, 0xff)
         // LNotEqual
         LNotEqual(arg2, i000)
         CH06(arg0, 68, 0xff)
         LNotEqual(i000, arg2)
         CH06(arg0, 69, 0xff)
         // LOr
         LOr(arg2, i000)
         CH06(arg0, 70, 50)
         LOr(i000, arg2)
         CH06(arg0, 71, 50)
         // Mod
         Mod(arg2, i000)
         CH06(arg0, 72, 50)
         Mod(i000, arg2)
         CH06(arg0, 73, 50)
         Mod(arg2, i000, Local1)
         CH06(arg0, 74, 50)
         Mod(i000, arg2, Local1)
         CH06(arg0, 75, 50)
         // Multiply
         Multiply(arg2, i000)
         CH06(arg0, 76, 50)
         Multiply(i000, arg2)
         CH06(arg0, 77, 50)
         Multiply(arg2, i000, Local1)
         CH06(arg0, 78, 50)
         Multiply(i000, arg2, Local1)
         CH06(arg0, 79, 50)
         // NAnd
         NAnd(arg2, i000)
         CH06(arg0, 80, 50)
         NAnd(i000, arg2)
         CH06(arg0, 81, 50)
         NAnd(arg2, i000, Local1)
         CH06(arg0, 82, 50)
         NAnd(i000, arg2, Local1)
         CH06(arg0, 83, 50)
         // NOr
         NOr(arg2, i000)
         CH06(arg0, 84, 50)
         NOr(i000, arg2)
         CH06(arg0, 85, 50)
         NOr(arg2, i000, Local1)
         CH06(arg0, 86, 50)
         NOr(i000, arg2, Local1)
         CH06(arg0, 87, 50)
         // Or
         Or(arg2, i000)
         CH06(arg0, 88, 50)
         Or(i000, arg2)
         CH06(arg0, 89, 50)
         Or(arg2, i000, Local1)
         CH06(arg0, 90, 50)
         Or(i000, arg2, Local1)
         CH06(arg0, 91, 50)
         // ShiftLeft
         ShiftLeft(arg2, i000)
         CH06(arg0, 92, 50)
         ShiftLeft(i000, arg2)
         CH06(arg0, 93, 50)
         ShiftLeft(arg2, i000, Local1)
         CH06(arg0, 94, 50)
         ShiftLeft(i000, arg2, Local1)
         CH06(arg0, 95, 50)
         // ShiftRight
         ShiftRight(arg2, i000)
         CH06(arg0, 96, 50)
         ShiftRight(i000, arg2)
         CH06(arg0, 97, 50)
         ShiftRight(arg2, i000, Local1)
         CH06(arg0, 98, 50)
         ShiftRight(i000, arg2, Local1)
         CH06(arg0, 99, 50)
         // Subtract
         Subtract(arg2, i000)
         CH06(arg0, 100, 50)
         Subtract(i000, arg2)
         CH06(arg0, 101, 50)
         Subtract(arg2, i000, Local1)
         CH06(arg0, 102, 50)
         Subtract(i000, arg2, Local1)
         CH06(arg0, 103, 50)
         // ToString
         ToString(arg2, 1)
         CH06(arg0, 104, 50)
         ToString(i000, arg2)
         CH06(arg0, 105, 50)
         ToString(arg2, 1, Local1)
         CH06(arg0, 106, 50)
         ToString(i000, arg2, Local1)
         CH06(arg0, 107, 50)
         // Wait
         Store(Wait(arg2, i000), Local1)
         CH06(arg0, 108, 50)
         Store(Wait(e000, arg2), Local1)
         CH06(arg0, 109, 50)
         // XOr
         XOr(arg2, i000)
         CH06(arg0, 110, 50)
         XOr(i000, arg2)
         CH06(arg0, 111, 50)
         XOr(arg2, i000, Local1)
         CH06(arg0, 112, 50)
         XOr(i000, arg2, Local1)
         CH06(arg0, 113, 50)
         // Mid
         Mid(arg2, 1, 1)
         CH06(arg0, 114, 50)
         Mid("123", arg2, 1)
         CH06(arg0, 115, 50)
         Mid("123", 1, arg2)
         CH06(arg0, 116, 50)
         Mid(arg2, 1, 1, Local1)
         CH06(arg0, 117, 50)
         Mid("123", arg2, 1, Local1)
         CH06(arg0, 118, 50)
         Mid("123", 1, arg2, Local1)
         CH06(arg0, 119, 50)
         // Match
         Match(arg2, MTR, 0, MTR, 0, 0)
         CH06(arg0, 120, 50)
         Match(Package(){1}, MTR, arg2, MTR, 0, 0)
         CH06(arg0, 121, 50)
         Match(Package(){1}, MTR, 0, MTR, arg2, 0)
         CH06(arg0, 122, 50)
         Match(Package(){1}, MTR, 0, MTR, 0, arg2)
         CH06(arg0, 123, 50)
         }
         */
        /* Reference to Uninitialized Object */
        Method (M003, 2, NotSerialized)
        {
            Local0 = ObjectType (Arg1)
            If ((Local0 != 0x00))
            {
                ERR (Arg0, Z092, __LINE__, 0x00, 0x00, Local0, 0x00)
                Return (0x01)
            }

            Local1 = DerefOf (Arg1)
            CH04 (__METHOD__, 0x00, 0x3E, Z092, __LINE__, 0x00, 0x00)
            /* CondRefOf */

            CondRefOf (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x01, 0xFF)
            /* CopyObject */

            CopyObject (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x02, 0xFF)
            /* Decrement */

            DerefOf (Arg1)--
            CH06 (Arg0, 0x03, 0xFF)
            /* DerefOf */

            Local1 = DerefOf (DerefOf (Arg1))
            CH06 (Arg0, 0x04, 0xFF)
            /* FindSetLeftBit */

            FindSetLeftBit (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x06, 0xFF)
            /* FindSetRightBit */

            FindSetRightBit (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x08, 0xFF)
            /* FromBCD */

            FromBCD (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x0A, 0xFF)
            /* Increment */

            DerefOf (Arg1)++
            CH06 (Arg0, 0x0B, 0xFF)
            /* LNot */

            Local1 = !DerefOf (Arg1)
            CH06 (Arg0, 0x0C, 0xFF)
            /* Not */

            Store (~DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x0E, 0xFF)
            /* ObjectType */

            If (X104)
            {
                Local1 = ObjectType (DerefOf (Arg1))
                CH03 (__METHOD__, Z092, __LINE__, 0x00, 0x00)
            }

            /* RefOf */

            Local1 = RefOf (DerefOf (Arg1))
            CH06 (Arg0, 0x0F, 0xFF)
            /* Release */
            /* Reset */
            /* Signal */
            /* SizeOf */
            Local1 = SizeOf (DerefOf (Arg1))
            CH06 (Arg0, 0x10, 0xFF)
            /* Sleep */

            Sleep (DerefOf (Arg1))
            CH06 (Arg0, 0x11, 0xFF)
            /* Stall */

            Stall (DerefOf (Arg1))
            CH06 (Arg0, 0x12, 0xFF)
            /* Store */

            Local1 = DerefOf (Arg1)
            CH06 (Arg0, 0x13, 0xFF)
            /* ToBCD */

            ToBCD (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x15, 0xFF)
            /* ToBuffer */

            ToBuffer (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x17, 0xFF)
            /* ToDecimalString */

            ToDecimalString (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x19, 0xFF)
            /* ToHexString */

            ToHexString (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x1B, 0xFF)
            /* ToInteger */

            ToInteger (DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x1D, 0xFF)
            /* Acquire */
            /* Add */
            Local1 = (DerefOf (Arg1) + I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x21, 0xFF)
            Local1 = (I000 + DerefOf (Arg1))
            CH06 (Arg0, 0x22, 0xFF)
            /* And */

            Local1 = (DerefOf (Arg1) & I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x25, 0xFF)
            Local1 = (I000 & DerefOf (Arg1))
            CH06 (Arg0, 0x26, 0xFF)
            /* Concatenate */

            Concatenate (DerefOf (Arg1), I000, Local1)
            CH06 (Arg0, 0x29, 0xFF)
            Concatenate (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x2A, 0xFF)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (DerefOf (Arg1), Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x2D, 0xFF)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x2E, 0xFF)
            /* Divide */

            Divide (DerefOf (Arg1), I000, Local2)
            CH06 (Arg0, 0x31, 0xFF)
            Divide (I000, DerefOf (Arg1), Local2)
            CH06 (Arg0, 0x32, 0xFF)
            Divide (DerefOf (Arg1), I000, Local2, Local1)
            CH06 (Arg0, 0x33, 0xFF)
            Divide (I000, DerefOf (Arg1), Local2, Local1)
            CH06 (Arg0, 0x34, 0xFF)
            /* Fatal */

            Fatal (0xFF, 0xFFFFFFFF, DerefOf (Arg1))
            CH06 (Arg0, 0x35, 0xFF)
            /* Index */

            Local1 = DerefOf (Arg1) [0x00]
            CH06 (Arg0, 0x38, 0xFF)
            Index ("0", DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x39, 0xFF)
            /* LEqual */

            Local1 = (DerefOf (Arg1) == I000)
            CH06 (Arg0, 0x3A, 0xFF)
            Local1 = (I000 == DerefOf (Arg1))
            CH06 (Arg0, 0x3B, 0xFF)
            /* LGreater */

            Local1 = (DerefOf (Arg1) > I000)
            CH06 (Arg0, 0x3C, 0xFF)
            Local1 = (I000 > DerefOf (Arg1))
            CH06 (Arg0, 0x3D, 0xFF)
            /* LGreaterEqual */

            Local1 = (DerefOf (Arg1) >= I000)
            CH06 (Arg0, 0x3E, 0xFF)
            Local1 = (I000 >= DerefOf (Arg1))
            CH06 (Arg0, 0x3F, 0xFF)
            /* LLess */

            Local1 = (DerefOf (Arg1) < I000)
            CH06 (Arg0, 0x40, 0xFF)
            Local1 = (I000 < DerefOf (Arg1))
            CH06 (Arg0, 0x41, 0xFF)
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
            CH06 (Arg0, 0x46, 0xFF)
            Local1 = (I000 || DerefOf (Arg1))
            CH06 (Arg0, 0x47, 0xFF)
            /* Mod */

            Local1 = (DerefOf (Arg1) % I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x4A, 0xFF)
            Local1 = (I000 % DerefOf (Arg1))
            CH06 (Arg0, 0x4B, 0xFF)
            /* Multiply */

            Local1 = (DerefOf (Arg1) * I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x4E, 0xFF)
            Local1 = (I000 * DerefOf (Arg1))
            CH06 (Arg0, 0x4F, 0xFF)
            /* NAnd */

            NAnd (DerefOf (Arg1), I000, Local1)
            CH06 (Arg0, 0x52, 0xFF)
            NAnd (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x53, 0xFF)
            /* NOr */

            NOr (DerefOf (Arg1), I000, Local1)
            CH06 (Arg0, 0x56, 0xFF)
            NOr (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x57, 0xFF)
            /* Or */

            Local1 = (DerefOf (Arg1) | I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x5A, 0xFF)
            Local1 = (I000 | DerefOf (Arg1))
            CH06 (Arg0, 0x5B, 0xFF)
            /* ShiftLeft */

            Local1 = (DerefOf (Arg1) << I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x5E, 0xFF)
            Local1 = (I000 << DerefOf (Arg1))
            CH06 (Arg0, 0x5F, 0xFF)
            /* ShiftRight */

            Local1 = (DerefOf (Arg1) >> I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x62, 0xFF)
            Local1 = (I000 >> DerefOf (Arg1))
            CH06 (Arg0, 0x63, 0xFF)
            /* Subtract */

            Local1 = (DerefOf (Arg1) - I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x66, 0xFF)
            Local1 = (I000 - DerefOf (Arg1))
            CH06 (Arg0, 0x67, 0xFF)
            /* ToString */

            ToString (DerefOf (Arg1), 0x01, Local1)
            CH06 (Arg0, 0x6A, 0xFF)
            ToString (I000, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x6B, 0xFF)
            /* Wait */

            Local1 = Wait (E000, DerefOf (Arg1))
            CH06 (Arg0, 0x6D, 0xFF)
            /* XOr */

            Local1 = (DerefOf (Arg1) ^ I000) /* \M4B0.I000 */
            CH06 (Arg0, 0x70, 0xFF)
            Local1 = (I000 ^ DerefOf (Arg1))
            CH06 (Arg0, 0x71, 0xFF)
            /* Mid */

            Mid (DerefOf (Arg1), 0x01, 0x01, Local1)
            CH06 (Arg0, 0x75, 0xFF)
            Mid ("123", DerefOf (Arg1), 0x01, Local1)
            CH06 (Arg0, 0x76, 0xFF)
            Mid ("123", 0x01, DerefOf (Arg1), Local1)
            CH06 (Arg0, 0x77, 0xFF)
            /* Match */

            Local1 = Match (DerefOf (Arg1), MTR, 0x00, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x78, 0xFF)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, DerefOf (Arg1), MTR, 0x00, 0x00)
            CH06 (Arg0, 0x79, 0xFF)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, DerefOf (Arg1), 0x00)
            CH06 (Arg0, 0x7A, 0xFF)
            Local1 = Match (Package (0x01)
                    {
                        0x01
                    }, MTR, 0x00, MTR, 0x00, DerefOf (Arg1))
            CH06 (Arg0, 0x7B, 0xFF)
            Return (0x00)
        }

        /* Uninitialized Local in Return */

        Method (M004, 1, NotSerialized)
        {
            If (Arg0)
            {
                Local0 = 0x00
            }

            Return (Local0)
        }

        /* Uninitialized element of Package in Return */

        Method (M005, 0, Serialized)
        {
            Name (P000, Package (0x01){})
            Return (DerefOf (P000 [0x00]))
        }

        /*
         // Causes Remark on compilation
         // Uninitialized Arg in Return
         Method(m006, 1)
         {
         if (arg0) {
         Store(0, arg1)
         }
         Return (arg1)
         }
         */
        /* Uninitialized Local in If */
        Method (M007, 1, NotSerialized)
        {
            If (Arg0)
            {
                Local0 = 0x00
            }

            Local1 = 0x00
            If (Local0)
            {
                Local1 = 0x01
            }

            Return (Local1)
        }

        /* Uninitialized element of Package in If */

        Method (M008, 0, Serialized)
        {
            Name (P000, Package (0x01){})
            Local1 = 0x00
            If (DerefOf (P000 [0x00]))
            {
                Local1 = 0x01
            }

            Return (Local1)
        }

        /*
         // Causes Remark on compilation
         // Uninitialized Arg in If
         Method(m009, 1)
         {
         if (arg0) {
         Store(0, arg1)
         }
         Store(0, Local1)
         if (arg1) {
         Store(1, Local1)
         }
         Return (Local1)
         }
         */
        /* Uninitialized Local in Elseif */
        Method (M00A, 1, NotSerialized)
        {
            If (Arg0)
            {
                Local0 = 0x00
            }

            Local1 = 0x00
            If (Arg0)
            {
                Local1 = 0x01
            }
            ElseIf (Local0)
            {
                Local1 = 0x02
            }

            Return (Local1)
        }

        /* Uninitialized element of Package in Elseif */

        Method (M00B, 1, Serialized)
        {
            Name (P000, Package (0x01){})
            Local1 = 0x00
            If (Arg0)
            {
                Local1 = 0x01
            }
            ElseIf (DerefOf (P000 [0x00]))
            {
                Local1 = 0x02
            }

            Return (Local1)
        }

        /*
         // Causes Remark on compilation
         // Uninitialized Arg in If
         Method(m00c, 1)
         {
         if (arg0) {
         Store(0, arg1)
         }
         Store(0, Local1)
         if (arg0) {
         Store(1, Local1)
         } elseif (arg1) {
         Store(2, Local1)
         }
         Return (Local1)
         }
         */
        Name (I001, 0x00)
        Method (M00D, 1, NotSerialized)
        {
            I001 = 0x01
        }

        /* Uninitialized element of Package as parameter of a method */

        Method (M00E, 1, Serialized)
        {
            Name (P000, Package (0x01){})
            I001 = 0x00
            M00D (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x00, 0x33)
            If ((I001 != 0x00))
            {
                ERR (Arg0, Z092, __LINE__, 0x00, 0x00, I001, 0x00)
            }

            I001 = 0x00
            Store (P000 [0x00], Local1)
            M00D (DerefOf (Local1))
            CH06 (Arg0, 0x02, 0x33)
            If ((I001 != 0x00))
            {
                ERR (Arg0, Z092, __LINE__, 0x00, 0x00, I001, 0x00)
            }

            I001 = 0x00
            M00D (DerefOf (Local2 = P000 [0x00]))
            CH06 (Arg0, 0x04, 0x33)
            If ((I001 != 0x00))
            {
                ERR (Arg0, Z092, __LINE__, 0x00, 0x00, I001, 0x00)
            }

            I001 = 0x00
            Local3 = P000 [0x00]
            M00D (DerefOf (Local3))
            CH06 (Arg0, 0x06, 0x33)
            If ((I001 != 0x00))
            {
                ERR (Arg0, Z092, __LINE__, 0x00, 0x00, I001, 0x00)
            }

            I001 = 0x00
            Local5 = Local4 = P000 [0x00]
            M00D (DerefOf (Local5))
            CH06 (Arg0, 0x08, 0x33)
            If ((I001 != 0x00))
            {
                ERR (Arg0, Z092, __LINE__, 0x00, 0x00, I001, 0x00)
            }
        }

        CH03 (__METHOD__, Z092, __LINE__, 0x00, 0x00)
        /* Uninitialized Local */

        M000 (Concatenate (__METHOD__, "-m000"), 0x00)
        /* Uninitialized element of Package */

        M001 (Concatenate (__METHOD__, "-m001"))
        /*
         // Causes Remark on compilation
         // Uninitialized Arg
         m002(Concatenate(ts, "-m002"), 0)
         */
        /* Reference to Uninitialized Local */
        If (Arg0)
        {
            Local0 = 0x00
        }

        M003 (Concatenate (__METHOD__, "-m003-RefLocal"), RefOf (Local0))
        /* Reference (Index) to Uninitialized element of Package */

        If (Y502)
        {
            Name (P000, Package (0x01){})
            If (Y113)
            {
                M003 (Concatenate (__METHOD__, "-m003-Index"), P000 [0x00])
            }

            Store (P000 [0x00], Local1)
            M003 (Concatenate (__METHOD__, "-m003-Index2"), Local1)
            If (Y113)
            {
                M003 (Concatenate (__METHOD__, "-m003-Index3"), Local2 = P000 [0x00])
            }

            Local3 = P000 [0x00]
            M003 (Concatenate (__METHOD__, "-m003-Index4"), Local3)
            Local5 = Local4 = P000 [0x00]
            M003 (Concatenate (__METHOD__, "-m003-Index5"), Local5)
        }

        /* Uninitialized Local in Return */

        M004 (0x00)
        CH06 (__METHOD__, 0x00, 0x31)
        /* Uninitialized element of Package in Return */

        If (Y502)
        {
            M005 ()
            CH06 (__METHOD__, 0x01, 0x33)
        }

        /*
         // Causes Remark on compilation
         // Uninitialized Arg in Return
         m006(0)
         CH06(ts, 2, 50)
         */
        /* Uninitialized Local in If */
        M007 (0x00)
        CH06 (__METHOD__, 0x03, 0x31)
        /* Uninitialized element of Package in If */

        If (Y502)
        {
            M008 ()
            CH06 (__METHOD__, 0x04, 0x33)
        }

        /*
         // Causes Remark on compilation
         // Uninitialized Arg in If
         m009(0)
         CH06(ts, 5, 50)
         */
        /* Uninitialized Local in Elseif */
        M00A (0x00)
        CH06 (__METHOD__, 0x06, 0x31)
        /* Uninitialized element of Package in Elseif */

        If (Y502)
        {
            M00B (0x00)
            CH06 (__METHOD__, 0x07, 0x33)
        }

        /*
         // Causes Remark on compilation
         // Uninitialized Arg in Elseif
         m00c(0)
         CH06(ts, 8, 50)
         */
        /* Uninitialized Local as parameter of a method */
        I001 = 0x00
        M00D (Local0)
        CH06 (__METHOD__, 0x09, 0x31)
        If ((I001 != 0x00))
        {
            ERR (__METHOD__, Z092, __LINE__, 0x00, 0x00, I001, 0x00)
        }

        /* Uninitialized element of Package as parameter of a method */

        If (Y502)
        {
            M00E (Concatenate (__METHOD__, "-m00e"))
        }
        /*
     // Causes Remark on compilation
     // Uninitialized Arg as parameter of a method
     Store(0, i001)
     m00d(Arg1)
     CH06(ts, 11, 50)
     if (LNotEqual(i001, 0)) {
     err(ts, z092, __LINE__, i001, 0)
     }
     */
    }
