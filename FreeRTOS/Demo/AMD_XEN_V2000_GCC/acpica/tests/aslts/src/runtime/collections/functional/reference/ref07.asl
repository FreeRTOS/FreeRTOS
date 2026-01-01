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
     * References
     *
     * TEST, Package total
     */
    Name (Z116, 0x74)
    /*
     * Flags and values used by m1c3
     */
    Name (FL00, 0x00) /* flag of testing of exceptions */
    Name (V000, 0x00) /* type of the Standard Data object */
    Name (V001, 0x00) /* index of element of Package */
    /*
     * Read immediate image element of Package
     *
     * Package specified by the immediate
     * images {Integer, String, Buffer, Package}.
     * Perform all the ways reading element of
     * Package passed by ArgX.
     */
    Method (M1C1, 0, Serialized)
    {
        Name (PPP0, Package (0x04)
        {
            0x77,
            "qwer0000",
            Buffer (0x04)
            {
                 0x01, 0x77, 0x03, 0x04                           // .w..
            },

            Package (0x03)
            {
                0x05,
                0x77,
                0x07
            }
        })
        FL00 = 0x00    /* flag of testing of exceptions */
        V000 = C009 /* type of the Standard Data object */ /* \C009 */
        V001 = 0x00    /* index of element of Package */
        M1C3 (PPP0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
        V000 = C00A /* type of the Standard Data object */ /* \C00A */
        V001 = 0x01    /* index of element of Package */
        M1C3 (PPP0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
        V000 = C00B /* type of the Standard Data object */ /* \C00B */
        V001 = 0x02    /* index of element of Package */
        M1C3 (PPP0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
        V000 = C00C /* type of the Standard Data object */ /* \C00C */
        V001 = 0x03    /* index of element of Package */
        M1C3 (PPP0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
    }

    /*
     * Read NamedX element of Package
     * {Integer, String, Buffer, Package}.
     */
    Method (M1C2, 0, Serialized)
    {
        Name (I000, 0x77)
        Name (S000, "qwer0000")
        Name (B000, Buffer (0x04)
        {
             0x01, 0x77, 0x03, 0x04                           // .w..
        })
        Name (P000, Package (0x03)
        {
            0x05,
            0x77,
            0x07
        })
        Name (PPP0, Package (0x04)
        {
            I000,
            S000,
            B000,
            P000
        })
        FL00 = 0x00    /* flag of testing of exceptions */
        V000 = C009 /* type of the Standard Data object */ /* \C009 */
        V001 = 0x00    /* index of element of Package */
        M1C3 (PPP0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
        V000 = C00A /* type of the Standard Data object */ /* \C00A */
        V001 = 0x01    /* index of element of Package */
        M1C3 (PPP0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
        V000 = C00B /* type of the Standard Data object */ /* \C00B */
        V001 = 0x02    /* index of element of Package */
        M1C3 (PPP0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
        V000 = C00C /* type of the Standard Data object */ /* \C00C */
        V001 = 0x03    /* index of element of Package */
        M1C3 (PPP0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
        M380 (__METHOD__, I000, 0x00, __LINE__)
        M381 (__METHOD__, S000, 0x00, __LINE__)
        M382 (__METHOD__, B000, 0x00, __LINE__)
        M383 (__METHOD__, P000, 0x00, __LINE__)
    }

    /* All the ways reading element of Package given by ArgX */
    /* arg0 - Package */
    /* arg1, */
    /* arg2, */
    /* arg3, */
    /* arg4, */
    /* arg5, */
    /* arg6 - auxiliary, for arbitrary use */
    Method (M1C3, 7, Serialized)
    {
        Name (I000, 0x00)
        Name (I001, 0x00)
        Name (I002, 0x00)
        Name (I003, 0x00)
        Name (I004, 0x00)
        Name (I005, 0x00)
        Name (I006, 0x00)
        Name (P000, Package (0x02){})
        Name (PPP0, Package (0x02){})
        /* LocalX */

        Store (Arg0 [V001], Local3)
        M390 (DerefOf (Local3), V000, 0x00, __LINE__)
        Local4 = DerefOf (Local3)
        M390 (Local4, V000, 0x00, __LINE__)
        M390 (DerefOf (Arg0 [V001]), V000, 0x00, 0x06)
        Local3 = Local2 = Arg0 [V001] /* \V001 */
        M390 (DerefOf (Local3), V000, 0x00, __LINE__)
        Local4 = DerefOf (Local3)
        M390 (Local4, V000, 0x00, __LINE__)
        M390 (DerefOf (Local2), V000, 0x00, __LINE__)
        Local4 = DerefOf (Local2)
        M390 (Local4, V000, 0x00, __LINE__)
        /* ArgX */

        Store (Arg0 [V001], Arg3)
        M390 (DerefOf (Arg3), V000, 0x00, __LINE__)
        Arg4 = DerefOf (Arg3)
        M390 (Arg4, V000, 0x00, __LINE__)
        M390 (DerefOf (Arg0 [V001]), V000, 0x00, 0x0D)
        Arg3 = Arg2 = Arg0 [V001] /* \V001 */
        M390 (DerefOf (Arg3), V000, 0x00, __LINE__)
        Arg4 = DerefOf (Arg3)
        M390 (Arg4, V000, 0x00, __LINE__)
        M390 (DerefOf (Arg2), V000, 0x00, __LINE__)
        Arg4 = DerefOf (Arg2)
        M390 (Arg4, V000, 0x00, __LINE__)
        /* NamedX */

        If (Y127)
        {
            CopyObject (PPP0 [0x00], I003) /* \M1C3.I003 */
            Store (Arg0 [V001], I003) /* \M1C3.I003 */
            M390 (DerefOf (I003), V000, 0x00, __LINE__)
            I004 = DerefOf (I003)
            M390 (I004, V000, 0x00, __LINE__)
            M390 (DerefOf (Arg0 [V001]), V000, 0x00, 0x14)
            I003 = I002 = Arg0 [V001] /* \V001 */
            M390 (DerefOf (I003), V000, 0x00, __LINE__)
            I004 = DerefOf (I003)
            M390 (I004, V000, 0x00, __LINE__)
            M390 (DerefOf (I002), V000, 0x00, __LINE__)
            I004 = DerefOf (I002)
            M390 (I004, V000, 0x00, __LINE__)
        }

        /*
         * El_of_Package
         *
         * Identical to the first checking, but only
         * store intermediately the references to element
         * of Package arg0 Index(arg0, x) into Index(p000, y)
         * but not into LocalX.
         */
        P000 [0x01] = P000 [0x00] = Arg0 [V001] /* \V001 */
        /* DerefOf(DerefOf(Index(x,Destination))) */

        M390 (DerefOf (DerefOf (P000 [0x00])), V000, 0x00, 0x19)
        /* DerefOf(DerefOf(Index(x,Result))) */

        M390 (DerefOf (DerefOf (P000 [0x01])), V000, 0x00, 0x1A)
        /* El_of_Package, Destination, LocalX */
        /*
         * After Store(Index(p000, 0), Local5)
         * Local5 below - reference to element of
         * Package p000 containing reference to the
         * 0-th element of Arg0-Package.
         *
         * Correspondingly, after Store(DerefOf(Local5), Local3)
         * Local3 - reference to the 0-th element of Arg0-Package.
         *
         * Further, DerefOf(Local3) - 0-th element of Arg0-Package.
         */
        If (FL00)
        {
            Store (P000 [0x00], Local5)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (Local5 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (DerefOf (Local5) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Local5, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Local5), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            Local5 = Local2 = P000 [0x00]
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (Local5 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (DerefOf (Local5) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Local5, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Local5), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (Local2 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (DerefOf (Local2) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Local2, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Local2), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        }

        If (Q001)
        {
            Store (P000 [0x00], Local5)
            Local3 = DerefOf (Local5)
            M390 (DerefOf (Local3), V000, 0x00, __LINE__)
            Local4 = DerefOf (Local3)
            M390 (Local4, V000, 0x00, __LINE__)
            Local5 = Local2 = P000 [0x00]
            Local3 = DerefOf (Local5)
            M390 (DerefOf (Local3), V000, 0x00, __LINE__)
            Local4 = DerefOf (Local3)
            M390 (Local4, V000, 0x00, __LINE__)
            Local3 = DerefOf (Local2)
            M390 (DerefOf (Local3), V000, 0x00, __LINE__)
            Local4 = DerefOf (Local3)
            M390 (Local4, V000, 0x00, __LINE__)
        }

        /* if(q001) */
        /* El_of_Package, Result, LocalX */
        If (FL00)
        {
            Store (P000 [0x01], Local5)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (Local5 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (DerefOf (Local5) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Local5, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Local5), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            Local5 = Local2 = P000 [0x01]
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (Local5 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (DerefOf (Local5) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Local5, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Local5), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (Local2 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Local6 = (DerefOf (Local2) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Local2, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Local2), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        }

        If (Q001)
        {
            Store (P000 [0x01], Local5)
            Local3 = DerefOf (Local5)
            M390 (DerefOf (Local3), V000, 0x00, __LINE__)
            Local4 = DerefOf (Local3)
            M390 (Local4, V000, 0x00, __LINE__)
            Local5 = Local2 = P000 [0x01]
            Local3 = DerefOf (Local5)
            M390 (DerefOf (Local3), V000, 0x00, __LINE__)
            Local4 = DerefOf (Local3)
            M390 (Local4, V000, 0x00, __LINE__)
            Local3 = DerefOf (Local2)
            M390 (DerefOf (Local3), V000, 0x00, __LINE__)
            Local4 = DerefOf (Local3)
            M390 (Local4, V000, 0x00, __LINE__)
        }

        /* if(q001) */
        /* El_of_Package, Destination, argX */
        If (FL00)
        {
            Store (P000 [0x00], Arg5)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (Arg5 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (DerefOf (Arg5) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Arg5, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Arg5), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            Arg5 = Arg2 = P000 [0x00]
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (Arg5 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (DerefOf (Arg5) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Arg5, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Arg5), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (Arg2 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (DerefOf (Arg2) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Arg2, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Arg2), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        }

        If (Q001)
        {
            Store (P000 [0x00], Arg5)
            Arg3 = DerefOf (Arg5)
            M390 (DerefOf (Arg3), V000, 0x00, __LINE__)
            Arg4 = DerefOf (Arg3)
            M390 (Arg4, V000, 0x00, __LINE__)
            Arg5 = Arg2 = P000 [0x00]
            Arg3 = DerefOf (Arg5)
            M390 (DerefOf (Arg3), V000, 0x00, __LINE__)
            Arg4 = DerefOf (Arg3)
            M390 (Arg4, V000, 0x00, __LINE__)
            Arg3 = DerefOf (Arg2)
            M390 (DerefOf (Arg3), V000, 0x00, __LINE__)
            Arg4 = DerefOf (Arg3)
            M390 (Arg4, V000, 0x00, __LINE__)
        }

        /* if(q001) */
        /* El_of_Package, Result, argX */
        If (FL00)
        {
            Store (P000 [0x01], Arg5)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (Arg5 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (DerefOf (Arg5) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Arg5, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Arg5), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            Arg5 = Arg2 = P000 [0x01]
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (Arg5 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (DerefOf (Arg5) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Arg5, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Arg5), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (Arg2 + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Arg6 = (DerefOf (Arg2) + 0x01)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (Arg2, V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            M390 (DerefOf (Arg2), V000, 0x00, __LINE__)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        }

        If (Q001)
        {
            Store (P000 [0x01], Arg5)
            Arg3 = DerefOf (Arg5)
            M390 (DerefOf (Arg3), V000, 0x00, __LINE__)
            Arg4 = DerefOf (Arg3)
            M390 (Arg4, V000, 0x00, __LINE__)
            Arg5 = Arg2 = P000 [0x01]
            Arg3 = DerefOf (Arg5)
            M390 (DerefOf (Arg3), V000, 0x00, __LINE__)
            Arg4 = DerefOf (Arg3)
            M390 (Arg4, V000, 0x00, __LINE__)
            Arg3 = DerefOf (Arg2)
            M390 (DerefOf (Arg3), V000, 0x00, __LINE__)
            Arg4 = DerefOf (Arg3)
            M390 (Arg4, V000, 0x00, __LINE__)
        }

        /* if(q001) */

        If (Y127)
        {
            /* El_of_Package, Destination, NamedX */

            If (FL00)
            {
                CopyObject (PPP0 [0x00], I005) /* \M1C3.I005 */
                Store (P000 [0x00], I005) /* \M1C3.I005 */
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (I005 + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (DerefOf (I005) + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (I005, V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (DerefOf (I005), V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                I005 = I002 = P000 [0x00]
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (I005 + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (DerefOf (I005) + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (I005, V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (DerefOf (I005), V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (I002 + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (DerefOf (I002) + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (I002, V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (DerefOf (I002), V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            }

            If (Q001)
            {
                Store (P000 [0x00], I005) /* \M1C3.I005 */
                I003 = DerefOf (I005)
                M390 (DerefOf (I003), V000, 0x00, __LINE__)
                I004 = DerefOf (I003)
                M390 (I004, V000, 0x00, __LINE__)
                I005 = I002 = P000 [0x00]
                I003 = DerefOf (I005)
                M390 (DerefOf (I003), V000, 0x00, __LINE__)
                I004 = DerefOf (I003)
                M390 (I004, V000, 0x00, __LINE__)
                I003 = DerefOf (I002)
                M390 (DerefOf (I003), V000, 0x00, __LINE__)
                I004 = DerefOf (I003)
                M390 (I004, V000, 0x00, __LINE__)
            }

            /* if(q001) */
            /* El_of_Package, Result, NamedX */
            If (FL00)
            {
                Store (P000 [0x01], I005) /* \M1C3.I005 */
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (I005 + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (DerefOf (I005) + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (I005, V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (DerefOf (I005), V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                I005 = I002 = P000 [0x01]
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (I005 + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (DerefOf (I005) + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (I005, V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (DerefOf (I005), V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (I002 + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                I006 = (DerefOf (I002) + 0x01)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (I002, V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
                CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
                M390 (DerefOf (I002), V000, 0x00, __LINE__)
                CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
            }

            If (Q001)
            {
                Store (P000 [0x01], I005) /* \M1C3.I005 */
                I003 = DerefOf (I005)
                M390 (DerefOf (I003), V000, 0x00, __LINE__)
                I004 = DerefOf (I003)
                M390 (I004, V000, 0x00, __LINE__)
                I005 = I002 = P000 [0x01]
                I003 = DerefOf (I005)
                M390 (DerefOf (I003), V000, 0x00, __LINE__)
                I004 = DerefOf (I003)
                M390 (I004, V000, 0x00, __LINE__)
                I003 = DerefOf (I002)
                M390 (DerefOf (I003), V000, 0x00, __LINE__)
                I004 = DerefOf (I003)
                M390 (I004, V000, 0x00, __LINE__)
            }
                /* if(q001) */
        }
        /* if(y127) */
    }

    /* Check Uninitialized element of Package */

    Method (M1C4, 0, Serialized)
    {
        Name (PPP0, Package (0x0A)
        {
            0x77,
            "qwer0000",
            Buffer (0x04)
            {
                 0x01, 0x77, 0x03, 0x04                           // .w..
            },

            Package (0x03)
            {
                0x05,
                0x77,
                0x07
            }
        })
        Method (M000, 2, NotSerialized)
        {
            Store (Arg0 [Arg1], Local0)
            M1A3 (Local0, C008, Z116, "m1c4", __LINE__)
        }

        M000 (PPP0, 0x04)
        M000 (PPP0, 0x05)
        M000 (PPP0, 0x06)
        M000 (PPP0, 0x07)
        M000 (PPP0, 0x08)
        M000 (PPP0, 0x09)
    }

    /* The chain of Index_References */

    Method (M1C5, 0, Serialized)
    {
        Name (PPP0, Package (0x04)
        {
            0x77,
            "qwer0000",
            Buffer (0x04)
            {
                 0x01, 0x77, 0x03, 0x04                           // .w..
            },

            Package (0x03)
            {
                0x05,
                0x77,
                0x07
            }
        })
        Name (P000, Package (0x14){})
        Store (PPP0 [0x00], P000 [0x00])
        M390 (DerefOf (DerefOf (P000 [0x00])), C009, Z116, 0x5E)
        If (Q002)
        {
            Store (P000 [0x00], P000 [0x01])
            M390 (DerefOf (DerefOf (DerefOf (P000 [0x01]))), C009, Z116, 0x5F)
            Store (P000 [0x01], P000 [0x02])
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (P000 [0x02])))), C009, Z116, 0x60)
            Store (P000 [0x02], P000 [0x03])
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (P000 [0x03]))))), C009, Z116,
                0x61)
            Store (P000 [0x03], P000 [0x04])
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (P000 [0x04])))))), C009,
                Z116, 0x62)
            Store (P000 [0x04], P000 [0x05])
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (P000 [0x05]))))))),
                C009, Z116, 0x63)
            Store (P000 [0x05], P000 [0x06])
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (P000 [0x06]
                )))))))), C009, Z116, 0x64)
            Store (P000 [0x06], P000 [0x07])
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (P000 [
                0x07]))))))))), C009, Z116, 0x65)
        }

        M390 (DerefOf (DerefOf (P000 [0x00])), C009, Z116, 0x66)
        If (Q002)
        {
            M390 (DerefOf (DerefOf (DerefOf (P000 [0x01]))), C009, Z116, 0x67)
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (P000 [0x02])))), C009, Z116, 0x68)
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (P000 [0x03]))))), C009, Z116,
                0x69)
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (P000 [0x04])))))), C009,
                Z116, 0x6A)
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (P000 [0x05]))))))),
                C009, Z116, 0x6B)
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (P000 [0x06]
                )))))))), C009, Z116, 0x6C)
            M390 (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (DerefOf (P000 [
                0x07]))))))))), C009, Z116, 0x6D)
        }
    }

    /* Access to the Method named object element of Package */
    /* Methods without parameters */
    Method (M1C7, 0, Serialized)
    {
        Name (I000, 0x77)
        Method (M000, 0, NotSerialized)
        {
            I000 = 0x00
        }

        Method (M001, 0, NotSerialized)
        {
            I000 = 0x01
            Return (0x12345678)
        }

        Method (M002, 0, NotSerialized)
        {
            I000 = 0x00
        }

        Method (M003, 0, NotSerialized)
        {
            I000 = 0x01
            Return (0x12345678)
        }

        Name (P000, Package (0x0A)
        {
            M000,
            M001,
            M002,
            M003,
            M000,
            M001,
            M002,
            M003,
            I000,
            I000
        })
        Store (P000 [0x00], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        Store (P000 [0x01], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        Store (P000 [0x02], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        Store (P000 [0x03], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        Store (P000 [0x04], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        Store (P000 [0x05], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        Store (P000 [0x06], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        Store (P000 [0x07], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        Store (P000 [0x08], Local0)
        M1A3 (Local0, C009, Z116, __METHOD__, __LINE__)
        Store (P000 [0x09], Local0)
        M1A3 (Local0, C009, Z116, __METHOD__, __LINE__)
        M380 (__METHOD__, I000, 0x00, __LINE__)
    }

    /* CURRENTLY: compiler failed, Too few arguments (M002 requires X) */
    /* Methods with parameters */
    Method (M1C8, 0, Serialized)
    {
        /*
     Name(i000, 0x77)
     Method(m000) {
     Store(0, i000)
     }
     Method(m001) {
     Store(1, i000)
     return (0x12345678)
     }
     Method(m002, 1) {
     Store(arg0, i000)
     Store(0, i000)
     }
     Method(m003, 7) {
     Store(arg0, i000)
     Store(arg1, i000)
     Store(arg2, i000)
     Store(arg3, i000)
     Store(arg4, i000)
     Store(arg5, i000)
     Store(arg6, i000)
     Store(1, i000)
     return (0x12345678)
     }
     Name(p000, Package() {m000, m001, m002, m003,
     m000, m001, m002, m003,
     i000, i000})
     Store(Index(p000, 0), Local0)
     m1a3(Local0, c010, z116, ts, `120)
     Store(Index(p000, 1), Local0)
     m1a3(Local0, c010, z116, ts, 121)
     Store(Index(p000, 2), Local0)
     m1a3(Local0, c010, z116, ts, 122)
     Store(Index(p000, 3), Local0)
     m1a3(Local0, c010, z116, ts, 123)
     Store(Index(p000, 4), Local0)
     m1a3(Local0, c010, z116, ts, 124)
     Store(Index(p000, 5), Local0)
     m1a3(Local0, c010, z116, ts, 125)
     Store(Index(p000, 6), Local0)
     m1a3(Local0, c010, z116, ts, 126)
     Store(Index(p000, 7), Local0)
     m1a3(Local0, c010, z116, ts, 127)
     Store(Index(p000, 8), Local0)
     m1a3(Local0, c009, z116, ts, 128)
     Store(Index(p000, 9), Local0)
     m1a3(Local0, c009, z116, ts, 129)
     m380 (ts, i000, 0, __LINE__)
     */
    }

    /* DerefOf of the Method named object element of Package */

    Method (M1C9, 0, Serialized)
    {
        Name (I000, 0x77)
        Method (M000, 0, NotSerialized)
        {
            I000 = 0x00
        }

        Method (M001, 0, NotSerialized)
        {
            I000 = 0x01
            Return (0x12345678)
        }

        Method (M002, 0, NotSerialized)
        {
            I000 = 0x00
        }

        Method (M003, 0, NotSerialized)
        {
            I000 = 0x01
            Return (0x12345678)
        }

        Name (P000, Package (0x0A)
        {
            M000,
            M001,
            M002,
            M003,
            M000,
            M001,
            M002,
            M003,
            I000,
            I000
        })
        Store (P000 [0x00], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local1 = DerefOf (Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Store (P000 [0x01], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local1 = DerefOf (Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Store (P000 [0x02], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local1 = DerefOf (Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Store (P000 [0x03], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local1 = DerefOf (Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Store (P000 [0x04], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local1 = DerefOf (Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Store (P000 [0x05], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local1 = DerefOf (Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Store (P000 [0x06], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local1 = DerefOf (Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Store (P000 [0x07], Local0)
        M1A3 (Local0, C010, Z116, __METHOD__, __LINE__)
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local1 = DerefOf (Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        M380 (__METHOD__, I000, 0x00, __LINE__)
    }

    /* Size of Package */

    Method (M1CA, 0, Serialized)
    {
        Method (M000, 1, Serialized)
        {
            Name (P000, Package (Arg0){})
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Store (P000 [Arg0], Local0)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        }

        Method (M001, 1, Serialized)
        {
            Name (P000, Package (Arg0){})
            Name (LPN0, 0x00)
            Name (LPC0, 0x00)
            /* Write each element of Package with its index */

            LPN0 = Arg0
            LPC0 = 0x00
            While (LPN0)
            {
                P000 [LPC0] = LPC0 /* \M1CA.M001.LPC0 */
                LPN0--
                LPC0++
            }

            /* Verify each element of Package */

            LPN0 = Arg0
            LPC0 = 0x00
            While (LPN0)
            {
                Store (P000 [LPC0], Local0)
                Local1 = DerefOf (Local0)
                If ((Local1 != LPC0))
                {
                    ERR (__METHOD__, Z116, __LINE__, Z116, 0x00, Local1, LPC0)
                    Break
                }

                LPN0--
                LPC0++
            }
        }

        Method (M003, 0, Serialized)
        {
            Name (P000, Package (0x02){})
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Store (P000 [0x02], Local0)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        }

        Method (M004, 0, Serialized)
        {
            Name (P000, Package (0xFF){})
            CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
            Store (P000 [0xFF], Local0)
            CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        }

        /* Size not greater than 255 */

        M000 (0x01)
        M000 (0x08)
        M000 (0x7F)
        M000 (0xFF)
        M003 ()
        M004 ()
        /* VarPackage: size of Package greater than 255 */
        /* (bug 129, not a bug) */
        M001 (0x0100)
    }

    /* Size of Package, see comma "6,})" */

    Method (M1CB, 0, Serialized)
    {
        Name (P000, Package (0x06)
        {
            0x01,
            0x02,
            0x03,
            0x04,
            0x05,
            0x06
        })
        Local0 = SizeOf (P000)
        If ((Local0 != 0x06))
        {
            ERR (__METHOD__, Z116, __LINE__, 0x00, 0x00, Local0, 0x06)
        }
    }

    /* Check the read automatic dereference */
    /* arg0 - name of Method initiating the checking */
    /* arg1 - Oref or IRef */
    /* arg2 - expected value */
    /* arg3 - exception is expected */
    Method (M1CC, 4, NotSerialized)
    {
        CH03 (Arg0, Z116, __LINE__, 0x00, 0x00)
        Local0 = Arg1
        Local7 = (Local0 + 0x01)
        If ((Local7 != Arg2))
        {
            ERR (Arg0, Z116, __LINE__, 0x00, 0x00, Local7, Arg2)
        }

        CH03 (Arg0, Z116, __LINE__, 0x00, 0x00)
    }

    /* Check the read automatic dereference */
    /* arg0 - name of Method initiating the checking */
    /* arg1 - Oref or IRef */
    /* arg2 - expected value */
    /* arg3 - exception is expected */
    Method (M1CD, 4, NotSerialized)
    {
        CH03 (Arg0, Z116, __LINE__, 0x00, 0x00)
        Local7 = (Arg1 + 0x01)
        If ((Local7 != Arg2))
        {
            ERR (Arg0, Z116, __LINE__, 0x00, 0x00, Local7, Arg2)
        }

        CH03 (Arg0, Z116, __LINE__, 0x00, 0x00)
    }

    /* Check the read automatic dereference */
    /* when accessing element of Package. */
    Method (M1CE, 0, Serialized)
    {
        Name (P000, Package (0x01)
        {
            0x77
        })
        M1CC (__METHOD__, Local0 = P000 [0x00], 0x78, 0x00)
        M1CD (__METHOD__, P000 [0x00], 0x78, 0x00)
    }

    Method (M1CF, 0, Serialized)
    {
        Name (P000, Package (0x01)
        {
            0x77
        })
        Local0 = P000 [0x00]
        M1CC (__METHOD__, Local0, 0x78, 0x00)
        M1CD (__METHOD__, Local0, 0x78, 0x00)
        Local1 = Local0 = P000 [0x00]
        M1CC (__METHOD__, Local0, 0x78, 0x00)
        M1CD (__METHOD__, Local0, 0x78, 0x00)
        M1CC (__METHOD__, Local1, 0x78, 0x00)
        M1CD (__METHOD__, Local1, 0x78, 0x00)
    }

    Method (M1D0, 0, Serialized)
    {
        Name (P000, Package (0x01)
        {
            0x77
        })
        CopyObject (Local0 = P000 [0x00], Local1)
        M1CC (__METHOD__, Local0, 0x78, 0x00)
        M1CD (__METHOD__, Local0, 0x78, 0x00)
        M1CC (__METHOD__, Local1, 0x78, 0x00)
        M1CD (__METHOD__, Local1, 0x78, 0x00)
    }

    /* EXCEPTIONS */
    /* ref07.asl 1093: Add(Index(p000, 0, Local0), 1, Local7) */
    /* Error 1035 -    Invalid type ^  ([Reference] found, */
    /*                   Add operator requires [Integer|String|Buffer]) */
    /*
     * Method(m1d1)
     * {
     *	Name(p000, Package(1) {0x77})
     *	CH03(ts, z116, 170, __LINE__, 0)
     *	Add(Index(p000, 0, Local0), 1, Local7)
     *	CH04(ts, 0, 0xff, z116, __LINE__, 0, 0)
     * }
     */
    /* LocalX */
    Method (M1D1, 0, Serialized)
    {
        Name (P000, Package (0x01)
        {
            0x77
        })
        Local1 = Local0 = P000 [0x00]
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local7 = (Local0 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Local7 = (Local1 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
    }

    Method (M1D2, 0, Serialized)
    {
        Name (P000, Package (0x01)
        {
            0x77
        })
        CopyObject (Local0 = P000 [0x00], Local1)
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local7 = (Local0 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Local7 = (Local1 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
    }

    /* ArgX */

    Method (M1D3, 2, Serialized)
    {
        Name (P000, Package (0x01)
        {
            0x77
        })
        Arg1 = Arg0 = P000 [0x00]
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local7 = (Arg0 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Local7 = (Arg1 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
    }

    Method (M1D4, 2, Serialized)
    {
        Name (P000, Package (0x01)
        {
            0x77
        })
        CopyObject (Arg0 = P000 [0x00], Arg1)
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local7 = (Arg0 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        /* Type of Arg1 should be IRef here, */
        /* so, exception is expected. */
        Local7 = (Arg1 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
    }

    /* NamedX */

    Method (M1D5, 0, Serialized)
    {
        Name (I001, 0x00)
        Name (P000, Package (0x02)
        {
            0x77,
            0x88
        })
        Name (SW00, 0x01)
        Name (HG00, 0x00) /* if non-zero - the test hangs */
        Name (HG01, 0x00) /* if non-zero - the test hangs */
        Name (HG02, 0x00) /* if non-zero - the test hangs */
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        CopyObject (Local0 = P000 [0x01], I001) /* \M1D5.I001 */
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        /* Type of i001 should be already IRef here, */
        /* so, don't expect exception. */
        I001 = Local0 = P000 [0x00]
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local7 = (Local0 + 0x01)
        If (Y248)
        {
            HG00 = 0x01
            HG01 = 0x01
            HG02 = 0x01
        }

        /*
         * To show visually the consequences of the anomaly
         * run one of code below. They cause hang.
         */
        If (HG00)
        {
            /* Infinite loop of printing */

            Local1 = 0x00
            Debug = Local0
        }

        If (HG01)
        {
            /* Infinite loop of printing */

            Debug = Local0
            Debug = Local0
        }

        If (HG02)
        {
            Local1 = 0x00
            Debug = "============== sit 2:"
            Local7 = ObjectType (Local0)
            Debug = Local7
        }

        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Local7 = (I001 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        /*
         * Looks identical to b248: "Incorrect ReferenceCount on Switch operation":
         *
         * Reference count of Local0 is mistakenly zeroed there too.
         *
         * [ACPI Debug]  String: [0x0F] "<-------- 0000>"
         * [ACPI Debug]  Reference: [Debug]
         * [ACPI Debug]  String: [0x0F] "<-------- 1111>"
         *
         * [ACPI Debug]  String: [0x0F] "<-------- 0000>"
         * [ACPI Debug]  [ACPI Debug]  String: [0x0F] "<-------- 1111>"
         */
        Debug = "<-------- 0000>"
        Debug = Local0
        Debug = "<-------- 1111>"
    }

    Method (M1D6, 0, Serialized)
    {
        Name (I001, 0x00)
        Name (P000, Package (0x01)
        {
            0x77
        })
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        CopyObject (Local0 = P000 [0x00], I001) /* \M1D6.I001 */
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local7 = (I001 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
    }

    /* Out of Package */

    Method (M1D7, 0, Serialized)
    {
        Name (P000, Package (0x01)
        {
            0x77
        })
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Store (P000 [0x01], Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        Local1 = Local0 = P000 [0x01]
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
    }

    Method (M1D8, 0, Serialized)
    {
        Name (P000, Package (0x01)
        {
            0x77
        })
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        CopyObject (P000 [0x01], Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
        CopyObject (Local0 = P000 [0x01], Local1)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
    }

    Method (M1DB, 0, Serialized)
    {
        Name (I001, 0x00)
        Name (P000, Package (0x02)
        {
            0x77,
            0x88
        })
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        CopyObject (P000 [0x01], I001) /* \M1DB.I001 */
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        /* Type of i001 should be already IRef here, */
        /* so, don't expect exception. Writing to i001 */
        /* is here identical to Store into it. */
        I001 = P000 [0x00]
        CH03 (__METHOD__, Z116, __LINE__, 0x00, 0x00)
        Local7 = (I001 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, Z116, __LINE__, 0x00, 0x00)
    }

    /* WRITE */

    Method (M1D9, 0, Serialized)
    {
        Name (P000, Package (0x03)
        {
            0x05,
            0x00,
            0x07
        })
        Method (M000, 1, NotSerialized)
        {
            Local0 = (0x76 + 0x01)
            Arg0 = Local0
        }

        M000 (P000 [0x01])
        M383 ("m1d9", P000, Z116, __LINE__)
    }

    Method (M1DA, 0, Serialized)
    {
        Name (P000, Package (0x03)
        {
            0x05,
            0x00,
            0x07
        })
        Method (M000, 1, NotSerialized)
        {
            Arg0 = (0x76 + 0x01)
        }

        M000 (P000 [0x01])
        M383 ("m1da", P000, Z116, __LINE__)
    }
