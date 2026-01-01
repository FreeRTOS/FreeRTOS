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
     */
    Name (Z110, 0x6E)
    /* The number of repetitions */
    /* */
    /* Minimum: 26*6=156 */
    Name (REP0, 0x03E8)
    /* Strategies of traveling the Cases of Switch */
    /* Total number of Cases */
    Name (MAXF, 0x64)
    /* Current indexes inside groups */

    Name (I200, 0x00)
    Name (I201, 0x00)
    Name (I202, 0x00)
    Name (I203, 0x00)
    Name (I204, 0x00)
    Name (I205, 0x00)
    /*
     * Mix of groups strategy
     *
     * Distribution of (6) groups:
     *
     * 0) Cases   0 - 13 (14)
     * 1) Cases  14 - 19 (6)
     * 2) Cases  20 - 33 (14)
     * 3) Cases  34 - 47 (14)
     * 4) Cases  48 - 73 (26)
     * 5) Cases  74 - 99 (26)
     *
     * arg0 - index of iteration
     */
    Method (M1E1, 1, Serialized)
    {
        Local7 = (Arg0 % 0x06)
        /* Groups */

        Switch (ToInteger (Local7))
        {
            Case (0x00)
            {
                Local1 = (I200 % 0x0E)
                I200++
            }
            Case (0x01)
            {
                Local0 = (I201 % 0x06)
                Local1 = (0x0E + Local0)
                I201++
            }
            Case (0x02)
            {
                Local0 = (I202 % 0x0E)
                Local1 = (0x14 + Local0)
                I202++
            }
            Case (0x03)
            {
                Local0 = (I203 % 0x0E)
                Local1 = (0x22 + Local0)
                I203++
            }
            Case (0x04)
            {
                Local0 = (I204 % 0x1A)
                Local1 = (0x30 + Local0)
                I204++
            }
            Case (0x05)
            {
                Local0 = (I205 % 0x1A)
                Local1 = (0x4A + Local0)
                I205++
            }
            Default
            {
                ERR ("m1e2", Z110, __LINE__, 0x00, 0x00, Local7, 0x00)
            }

        }

        Return (Local1)
    }

    /* Mod-6 strategy */
    /* */
    /* Observed, it causes many "Outstanding allocations" */
    /* */
    /* arg0 - index of iteration */
    Method (M1E2, 1, NotSerialized)
    {
        Local7 = (Arg0 % 0x06)
        Return (Local7)
    }

    /* Linear strategy */
    /* */
    /* arg0 - index of iteration */
    Method (M1E3, 1, NotSerialized)
    {
        Local7 = (Arg0 % MAXF) /* \MAXF */
        Return (Local7)
    }

    /* arg0 - strategy of traveling the Cases of Switch */

    Method (M1E0, 1, Serialized)
    {
        /*
         // ################################## Check all the test:
         // Packages for _TCI statistics
         Name(LLL0, Package(1) {})
         Name(LLL1, Package(1) {})
         Name(LLL2, Package(1) {})
         // Create and initialize the Memory Consumption Statistics Packages
         Store(m3a0(c200), LLL0)	// _TCI-end statistics
         Store(m3a0(c201), LLL1)	// _TCI-begin statistics
         Store(m3a0(0), LLL2)	// difference
         _TCI(c200, LLL0)
         // ################################## Check all the test.
         */
        Name (PR, 0x00)
        Name (IND0, 0x00)
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        C081 = Z110 /* absolute index of file initiating the checking */ /* \Z110 */
        LPN0 = REP0 /* \REP0 */
        LPC0 = 0x00
        If ((Arg0 == 0x01))
        {
            Debug = "Mix of groups strategy"
        }
        ElseIf ((Arg0 == 0x02))
        {
            Debug = "Mod-6 strategy"
        }
        Else
        {
            Debug = "Linear strategy"
        }

        While (LPN0)
        {
            If (PR)
            {
                Debug = LPC0 /* \M1E0.LPC0 */
            }

            If ((Arg0 == 0x01))
            {
                IND0 = M1E1 (LPC0)
            }
            ElseIf ((Arg0 == 0x02))
            {
                IND0 = M1E2 (LPC0)
            }
            Else
            {
                IND0 = M1E3 (LPC0)
            }

            Switch (ToInteger (IND0))
            {
                /* ========================= Group 0: */
                /* All types */
                /* (from m1b1: CopyObject of Object to LocalX) */
                Case (0x00)
                {
                    CopyObject (I900, Local0)
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x01)
                {
                    CopyObject (S900, Local0)
                    M1A3 (Local0, C00A, Z110, __METHOD__, __LINE__)
                }
                Case (0x02)
                {
                    CopyObject (B900, Local0)
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                }
                Case (0x03)
                {
                    CopyObject (P900, Local0)
                    M1A3 (Local0, C00C, Z110, __METHOD__, __LINE__)
                }
                Case (0x04)
                {
                    CopyObject (F900, Local0)
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x05)
                {
                    CopyObject (RefOf (D900), Local0)
                    M1A3 (Local0, C00E, Z110, __METHOD__, __LINE__)
                }
                Case (0x06)
                {
                    CopyObject (RefOf (E900), Local0)
                    M1A3 (Local0, C00F, Z110, __METHOD__, __LINE__)
                }
                Case (0x07)
                {
                    If (RN06)
                    {
                        CopyObject (RefOf (M901), Local0)
                    }
                    Else
                    {
                        CopyObject (RefOf (M901), Local0)
                    }

                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                }
                Case (0x08)
                {
                    CopyObject (RefOf (MX90), Local0)
                    M1A3 (Local0, C011, Z110, __METHOD__, __LINE__)
                }
                Case (0x09)
                {
                    If (Y510)
                    {
                        CopyObject (RefOf (R900), Local0)
                        M1A3 (Local0, C012, Z110, __METHOD__, __LINE__)
                    }
                }
                Case (0x0A)
                {
                    CopyObject (RefOf (PW90), Local0)
                    M1A3 (Local0, C013, Z110, __METHOD__, __LINE__)
                }
                Case (0x0B)
                {
                    CopyObject (RefOf (PR90), Local0)
                    M1A3 (Local0, C014, Z110, __METHOD__, __LINE__)
                }
                Case (0x0C)
                {
                    If (Y508)
                    {
                        CopyObject (RefOf (TZ90), Local0)
                        M1A3 (Local0, C015, Z110, __METHOD__, __LINE__)
                    }
                }
                Case (0x0D)
                {
                    CopyObject (BF90, Local0)
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                }
                Case                /* ========================= Group 1: */
                /* All available for Store types */
                /* (from m1b2: Store of Object to LocalX) */
 (0x0E)
                {
                    Local0 = I900 /* \I900 */
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x0F)
                {
                    Local0 = S900 /* \S900 */
                    M1A3 (Local0, C00A, Z110, __METHOD__, __LINE__)
                }
                Case (0x10)
                {
                    Local0 = B900 /* \B900 */
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                }
                Case (0x11)
                {
                    Local0 = P900 /* \P900 */
                    M1A3 (Local0, C00C, Z110, __METHOD__, __LINE__)
                }
                Case (0x12)
                {
                    Local0 = F900 /* \F900 */
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x13)
                {
                    Local0 = BF90 /* \BF90 */
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                }
                Case                /* ========================= Group 2: */
                /* All types */
                /* (from m1b4: CopyObject the result of RefOf/CondRefOf to LocalX) */
 (0x14)
                {
                    CopyObject (RefOf (I900), Local0)
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x15)
                {
                    CopyObject (RefOf (S900), Local0)
                    M1A3 (Local0, C00A, Z110, __METHOD__, __LINE__)
                }
                Case (0x16)
                {
                    CopyObject (RefOf (B900), Local0)
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                }
                Case (0x17)
                {
                    CopyObject (RefOf (P900), Local0)
                    M1A3 (Local0, C00C, Z110, __METHOD__, __LINE__)
                }
                Case (0x18)
                {
                    CopyObject (RefOf (F900), Local0)
                    M1A3 (Local0, C00D, Z110, __METHOD__, __LINE__)
                }
                Case (0x19)
                {
                    CopyObject (RefOf (D900), Local0)
                    M1A3 (Local0, C00E, Z110, __METHOD__, __LINE__)
                }
                Case (0x1A)
                {
                    CopyObject (RefOf (E900), Local0)
                    M1A3 (Local0, C00F, Z110, __METHOD__, __LINE__)
                }
                Case (0x1B)
                {
                    CopyObject (RefOf (M901), Local0)
                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                }
                Case (0x1C)
                {
                    CopyObject (RefOf (MX90), Local0)
                    M1A3 (Local0, C011, Z110, __METHOD__, __LINE__)
                }
                Case (0x1D)
                {
                    CopyObject (RefOf (R900), Local0)
                    M1A3 (Local0, C012, Z110, __METHOD__, __LINE__)
                }
                Case (0x1E)
                {
                    CopyObject (RefOf (PW90), Local0)
                    M1A3 (Local0, C013, Z110, __METHOD__, __LINE__)
                }
                Case (0x1F)
                {
                    CopyObject (RefOf (PR90), Local0)
                    M1A3 (Local0, C014, Z110, __METHOD__, __LINE__)
                }
                Case (0x20)
                {
                    CopyObject (RefOf (TZ90), Local0)
                    M1A3 (Local0, C015, Z110, __METHOD__, __LINE__)
                }
                Case (0x21)
                {
                    CopyObject (RefOf (BF90), Local0)
                    M1A3 (Local0, C016, Z110, __METHOD__, __LINE__)
                }
                Case                /* ========================= Group 3: */
                /* All types */
                /* (from m1b5: Store the result of RefOf/CondRefOf to LocalX) */
 (0x22)
                {
                    Local0 = RefOf (I900)
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x23)
                {
                    Local0 = RefOf (S900)
                    M1A3 (Local0, C00A, Z110, __METHOD__, __LINE__)
                }
                Case (0x24)
                {
                    Local0 = RefOf (B900)
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                }
                Case (0x25)
                {
                    Local0 = RefOf (P900)
                    M1A3 (Local0, C00C, Z110, __METHOD__, __LINE__)
                }
                Case (0x26)
                {
                    Local0 = RefOf (F900)
                    M1A3 (Local0, C00D, Z110, __METHOD__, __LINE__)
                }
                Case (0x27)
                {
                    Local0 = RefOf (D900)
                    M1A3 (Local0, C00E, Z110, __METHOD__, __LINE__)
                }
                Case (0x28)
                {
                    Local0 = RefOf (E900)
                    M1A3 (Local0, C00F, Z110, __METHOD__, __LINE__)
                }
                Case (0x29)
                {
                    Local0 = RefOf (M901)
                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                }
                Case (0x2A)
                {
                    Local0 = RefOf (MX90)
                    M1A3 (Local0, C011, Z110, __METHOD__, __LINE__)
                }
                Case (0x2B)
                {
                    Local0 = RefOf (R900)
                    M1A3 (Local0, C012, Z110, __METHOD__, __LINE__)
                }
                Case (0x2C)
                {
                    Local0 = RefOf (PW90)
                    M1A3 (Local0, C013, Z110, __METHOD__, __LINE__)
                }
                Case (0x2D)
                {
                    Local0 = RefOf (PR90)
                    M1A3 (Local0, C014, Z110, __METHOD__, __LINE__)
                }
                Case (0x2E)
                {
                    Local0 = RefOf (TZ90)
                    M1A3 (Local0, C015, Z110, __METHOD__, __LINE__)
                }
                Case (0x2F)
                {
                    Local0 = RefOf (BF90)
                    M1A3 (Local0, C016, Z110, __METHOD__, __LINE__)
                }
                Case                /* ========================= Group 4: */
                /* From m1b6: CopyObject the result of Index to LocalX */
                /* Computational Data */
 (0x30)
                {
                    CopyObject (Local0 = S900 [0x01], Local1)
                    M1A3 (Local0, C016, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C016, Z110, __METHOD__, __LINE__)
                }
                Case (0x31)
                {
                    CopyObject (Local0 = B900 [0x01], Local1)
                    M1A3 (Local0, C016, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C016, Z110, __METHOD__, __LINE__)
                }
                Case                /* Elements of Package are Uninitialized */

 (0x32)
                {
                    If (Y127)
                    {
                        CopyObject (Local0 = P900 [0x00], Local1)
                        M1A3 (Local0, C008, Z110, __METHOD__, __LINE__)
                        M1A3 (Local1, C008, Z110, __METHOD__, __LINE__)
                    }
                }
                Case                /* Elements of Package are Computational Data */

 (0x33)
                {
                    CopyObject (Local0 = P901 [0x01], Local1)
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x34)
                {
                    CopyObject (Local0 = P904 [0x01], Local1)
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00B, Z110, __METHOD__, __LINE__)
                }
                Case (0x35)
                {
                    CopyObject (Local0 = P905 [0x00], Local1)
                    M1A3 (Local0, C00C, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00C, Z110, __METHOD__, __LINE__)
                }
                Case (0x36)
                {
                    CopyObject (Local0 = P90D [0x00], Local1)
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x37)
                {
                    CopyObject (Local0 = P90E [0x00], Local1)
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x38)
                {
                    CopyObject (Local0 = P90F [0x00], Local1)
                    M1A3 (Local0, C00A, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00A, Z110, __METHOD__, __LINE__)
                }
                Case (0x39)
                {
                    CopyObject (Local0 = P910 [0x00], Local1)
                    M1A3 (Local0, C00A, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00A, Z110, __METHOD__, __LINE__)
                }
                Case (0x3A)
                {
                    CopyObject (Local0 = P911 [0x00], Local1)
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00B, Z110, __METHOD__, __LINE__)
                }
                Case (0x3B)
                {
                    CopyObject (Local0 = P912 [0x00], Local1)
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x3C)
                {
                    CopyObject (Local0 = P913 [0x00], Local1)
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x3D)
                {
                    CopyObject (Local0 = P914 [0x00], Local1)
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x3E)
                {
                    CopyObject (Local0 = P915 [0x00], Local1)
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00B, Z110, __METHOD__, __LINE__)
                }
                Case                /* Elements of Package are NOT Computational Data */

 (0x3F)
                {
                    CopyObject (Local0 = P916 [0x00], Local1)
                    M1A3 (Local0, C00E, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00E, Z110, __METHOD__, __LINE__)
                }
                Case (0x40)
                {
                    CopyObject (Local0 = P917 [0x00], Local1)
                    M1A3 (Local0, C00F, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00F, Z110, __METHOD__, __LINE__)
                }
                Case (0x41)
                {
                    CopyObject (Local0 = P918 [0x00], Local1)
                    M1A3 (Local0, C011, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C011, Z110, __METHOD__, __LINE__)
                }
                Case (0x42)
                {
                    CopyObject (Local0 = P919 [0x00], Local1)
                    M1A3 (Local0, C012, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C012, Z110, __METHOD__, __LINE__)
                }
                Case (0x43)
                {
                    CopyObject (Local0 = P91A [0x00], Local1)
                    M1A3 (Local0, C013, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C013, Z110, __METHOD__, __LINE__)
                }
                Case (0x44)
                {
                    CopyObject (Local0 = P91B [0x00], Local1)
                    M1A3 (Local0, C014, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C014, Z110, __METHOD__, __LINE__)
                }
                Case (0x45)
                {
                    CopyObject (Local0 = P91C [0x00], Local1)
                    M1A3 (Local0, C015, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C015, Z110, __METHOD__, __LINE__)
                }
                Case                /* Elements of Package are Methods */

 (0x46)
                {
                    CopyObject (Local0 = P91D [0x00], Local1)
                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C010, Z110, __METHOD__, __LINE__)
                }
                Case (0x47)
                {
                    CopyObject (Local0 = P91E [0x00], Local1)
                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C010, Z110, __METHOD__, __LINE__)
                }
                Case (0x48)
                {
                    CopyObject (Local0 = P91F [0x00], Local1)
                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C010, Z110, __METHOD__, __LINE__)
                }
                Case (0x49)
                {
                    CopyObject (Local0 = P920 [0x00], Local1)
                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C010, Z110, __METHOD__, __LINE__)
                }
                Case                /* ========================= Group 5: */
                /* From m1b7: Store the result of Index to LocalX */
                /* Computational Data */
 (0x4A)
                {
                    Local1 = Local0 = S900 [0x01]
                    M1A3 (Local0, C016, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C016, Z110, __METHOD__, __LINE__)
                }
                Case (0x4B)
                {
                    Local1 = Local0 = B900 [0x01]
                    M1A3 (Local0, C016, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C016, Z110, __METHOD__, __LINE__)
                }
                Case                /* Elements of Package are Uninitialized */

 (0x4C)
                {
                    Local1 = Local0 = P900 [0x00]
                    M1A3 (Local0, C008, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C008, Z110, __METHOD__, __LINE__)
                }
                Case                /* Elements of Package are Computational Data */

 (0x4D)
                {
                    Local1 = Local0 = P901 [0x01]
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x4E)
                {
                    Local1 = Local0 = P904 [0x01]
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00B, Z110, __METHOD__, __LINE__)
                }
                Case (0x4F)
                {
                    Local1 = Local0 = P905 [0x00]
                    M1A3 (Local0, C00C, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00C, Z110, __METHOD__, __LINE__)
                }
                Case (0x50)
                {
                    Local1 = Local0 = P90D [0x00]
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x51)
                {
                    Local1 = Local0 = P90E [0x00]
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x52)
                {
                    Local1 = Local0 = P90F [0x00]
                    M1A3 (Local0, C00A, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00A, Z110, __METHOD__, __LINE__)
                }
                Case (0x53)
                {
                    Local1 = Local0 = P910 [0x00]
                    M1A3 (Local0, C00A, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00A, Z110, __METHOD__, __LINE__)
                }
                Case (0x54)
                {
                    Local1 = Local0 = P911 [0x00]
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00B, Z110, __METHOD__, __LINE__)
                }
                Case (0x55)
                {
                    Local1 = Local0 = P912 [0x00]
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x56)
                {
                    Local1 = Local0 = P913 [0x00]
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x57)
                {
                    Local1 = Local0 = P914 [0x00]
                    M1A3 (Local0, C009, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C009, Z110, __METHOD__, __LINE__)
                }
                Case (0x58)
                {
                    Local1 = Local0 = P915 [0x00]
                    M1A3 (Local0, C00B, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00B, Z110, __METHOD__, __LINE__)
                }
                Case                /* Elements of Package are NOT Computational Data */

 (0x59)
                {
                    Local1 = Local0 = P916 [0x00]
                    M1A3 (Local0, C00E, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00E, Z110, __METHOD__, __LINE__)
                }
                Case (0x5A)
                {
                    Local1 = Local0 = P917 [0x00]
                    M1A3 (Local0, C00F, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C00F, Z110, __METHOD__, __LINE__)
                }
                Case (0x5B)
                {
                    Local1 = Local0 = P918 [0x00]
                    M1A3 (Local0, C011, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C011, Z110, __METHOD__, __LINE__)
                }
                Case (0x5C)
                {
                    Local1 = Local0 = P919 [0x00]
                    M1A3 (Local0, C012, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C012, Z110, __METHOD__, __LINE__)
                }
                Case (0x5D)
                {
                    Local1 = Local0 = P91A [0x00]
                    M1A3 (Local0, C013, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C013, Z110, __METHOD__, __LINE__)
                }
                Case (0x5E)
                {
                    Local1 = Local0 = P91B [0x00]
                    M1A3 (Local0, C014, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C014, Z110, __METHOD__, __LINE__)
                }
                Case (0x5F)
                {
                    Local1 = Local0 = P91C [0x00]
                    M1A3 (Local0, C015, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C015, Z110, __METHOD__, __LINE__)
                }
                Case                /* Elements of Package are Methods */

 (0x60)
                {
                    Local1 = Local0 = P91D [0x00]
                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C010, Z110, __METHOD__, __LINE__)
                }
                Case (0x61)
                {
                    Local1 = Local0 = P91E [0x00]
                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C010, Z110, __METHOD__, __LINE__)
                }
                Case (0x62)
                {
                    Local1 = Local0 = P91F [0x00]
                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C010, Z110, __METHOD__, __LINE__)
                }
                Case (0x63)
                {
                    Local1 = Local0 = P920 [0x00]
                    M1A3 (Local0, C010, Z110, __METHOD__, __LINE__)
                    M1A3 (Local1, C010, Z110, __METHOD__, __LINE__)
                }
                Default
                {
                    ERR (__METHOD__, Z110, __LINE__, 0x00, 0x00, IND0, 0x00)
                }

            }

            /* Switch */

            LPN0--
            LPC0++
        }
        /* While */
    /*
     // ################################## Check all the test:
     _TCI(c201, LLL1)
     m3a3(LLL0, LLL1, LLL2)
     m3a4(LLL0, LLL1, LLL2, 0, 0, 0, 0x12345678)
     // ################################## Check all the test.
     */
    /*	m1a6() */
    }
