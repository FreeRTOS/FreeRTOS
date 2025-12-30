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
     * Bug 304:
     *
     * SUMMARY: No exception AE_AML_METHOD_LIMIT for the number of method invocations exceeding 255
     */
    Method (M1ED, 0, NotSerialized)
    {
        Method (M18A, 1, Serialized, 3)
        {
            Name (RPT0, 0x00)
            Name (I000, 0x00)
            /*
             * Total number of calls of the same Recursively Called method (RCM),
             * the first call is counted there too.
             */
            Name (N000, 0x03)
            Name (CNT0, 0x00) /* how many methods are in progress simultaneously */
            Name (MAX0, 0x00) /* maximal number of methods being in progress simultaneously */
            Name (CNT1, 0x00) /* summary of total indexes */
            Name (IX00, 0x00) /* total index of current call */
            Name (IND1, 0x00) /* index of call to m100 */
            Name (IND2, 0x00) /* index of call to m200 */
            Name (IND3, 0x00) /* index of call to m300 */
            Name (IND4, 0x00) /* index of call to m400 */
            Name (N100, 0x03) /* number of calls to m100 */
            Name (N200, 0x06) /* number of calls to m200 */
            Name (N300, 0x0C) /* number of calls to m300 */
            Name (N400, 0x18) /* number of calls to m400 */
            Name (P100, Package (N100){}) /* Package to keep total indexes of call to m100 */
            Name (P200, Package (N200){}) /* Package to keep total indexes of call to m200 */
            Name (P300, Package (N300){}) /* Package to keep total indexes of call to m300 */
            Name (P400, Package (0x0100){}) /* Package to keep total indexes of call to m400 */
            /* Benchmarks of indexes */

            Name (B1B0, Buffer (N100)
            {
                 0x00, 0x16, 0x2C                                 // ..,
            })
            Name (B2B0, Buffer (N200)
            {
                 0x01, 0x0B, 0x15, 0x17, 0x21, 0x2B               // ....!+
            })
            Name (B3B0, Buffer (N300)
            {
                /* 0000 */  0x02, 0x06, 0x0A, 0x0C, 0x10, 0x14, 0x18, 0x1C,  // ........
                /* 0008 */  0x20, 0x22, 0x26, 0x2A                           //  "&*
            })
            Name (B4B0, Buffer (0x0100)
            {
                /* 0000 */  0x03, 0x04, 0x05, 0x07, 0x08, 0x09, 0x0D, 0x0E,  // ........
                /* 0008 */  0x0F, 0x11, 0x12, 0x13, 0x19, 0x1A, 0x1B, 0x1D,  // ........
                /* 0010 */  0x1E, 0x1F, 0x23, 0x24, 0x25, 0x27, 0x28, 0x29   // ..#$%'()
            })
            /*
             * Open method execution
             *
             * arg0 - ID of method (1,2,3...)
             * arg1 - the message to be reported
             */
            Method (M800, 2, Serialized)
            {
                If (RPT0)
                {
                    Debug = Arg1
                }

                CNT0++
                If ((CNT0 > MAX0))
                {
                    MAX0 = CNT0 /* \M1ED.M18A.CNT0 */
                }

                Switch (ToInteger (Arg0))
                {
                    Case (0x01)
                    {
                        P100 [IND1] = IX00 /* \M1ED.M18A.IX00 */
                        IND1++
                    }
                    Case (0x02)
                    {
                        P200 [IND2] = IX00 /* \M1ED.M18A.IX00 */
                        IND2++
                    }
                    Case (0x03)
                    {
                        P300 [IND3] = IX00 /* \M1ED.M18A.IX00 */
                        IND3++
                    }
                    Case (0x04)
                    {
                        P400 [IND4] = IX00 /* \M1ED.M18A.IX00 */
                        IND4++
                    }

                }

                IX00++ /* total index */
            }

            /*
             * Close method execution
             *
             * arg0 - ID of method (1,2,3...)
             */
            Method (M801, 1, NotSerialized)
            {
                CNT0--
            }

            /*
             * arg0 - ID of method (1,2,3...)
             * arg1 - number of elements to be compared
             * arg2 - Package
             * arg3 - Package with the benchmark values
             */
            Method (M802, 4, Serialized)
            {
                Name (LPN0, 0x00)
                Name (LPC0, 0x00)
                LPN0 = Arg1
                LPC0 = 0x00
                While (LPN0)
                {
                    Local0 = DerefOf (Arg2 [LPC0])
                    Local1 = DerefOf (Arg3 [LPC0])
                    If ((Local0 != Local1))
                    {
                        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Local1)
                        Debug = Arg0
                        Debug = LPC0 /* \M1ED.M18A.M802.LPC0 */
                    }

                    LPN0--
                    LPC0++
                }

                Switch (ToInteger (Arg0))
                {
                    Case (0x01)
                    {
                        If ((IND1 != N100))
                        {
                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, IND1, N100)
                        }
                    }
                    Case (0x02)
                    {
                        If ((IND2 != N200))
                        {
                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, IND2, N200)
                        }
                    }
                    Case (0x03)
                    {
                        If ((IND3 != N300))
                        {
                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, IND3, N300)
                        }
                    }
                    Case (0x04)
                    {
                        If ((IND4 != N400))
                        {
                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, IND4, N400)
                        }
                    }

                }
            }

            /*
             * Arguments of methods:
             * arg0 - 0 - the first call, otherwise - recursive calls
             */
            Name (C000, 0x03)
            Name (C100, 0x03)
            Name (C200, 0x03)
            Name (C300, 0x03)
            /*
             * None internal objects (including Methods) or Switches in Serialized methods below
             *
             * Note: if Serialized method has internal objects (including Methods and Switches)
             *       it could not be invoked recursively by the same thread.
             */
            Method (M100, 0, Serialized)
            {
                C100 = 0x03
                Local1 = IND1 /* \M1ED.M18A.IND1 */
                Local0 = IX00 /* \M1ED.M18A.IX00 */
                M800 (0x01, "m100")
                C000--
                If ((C000 == 0x00)){                /* m000() */
                }
                Else
                {
                    M200 ()
                }

                M801 (0x01)
                CNT1 += Local0
                Local1 = DerefOf (P100 [Local1])
                If ((Local1 != Local0))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
                }
            }

            Method (M200, 0, Serialized)
            {
                C200 = 0x03
                Local1 = IND2 /* \M1ED.M18A.IND2 */
                Local0 = IX00 /* \M1ED.M18A.IX00 */
                M800 (0x02, "m200")
                C100--
                If ((C100 == 0x00))
                {
                    M100 ()
                }
                Else
                {
                    M300 ()
                }

                M801 (0x02)
                CNT1 += Local0
                Local1 = DerefOf (P200 [Local1])
                If ((Local1 != Local0))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
                }
            }

            Method (M300, 0, Serialized)
            {
                If (I000)
                {
                    C300 = 0x1F
                                /* Store(32, c300) // AE_AML_METHOD_LIMIT occurs for this number (0x111 == 273) */
                }
                Else
                {
                    C300 = 0x03
                }

                Local1 = IND3 /* \M1ED.M18A.IND3 */
                Local0 = IX00 /* \M1ED.M18A.IX00 */
                M800 (0x03, "m300")
                C200--
                If ((C200 == 0x00))
                {
                    M200 ()
                }
                Else
                {
                    M400 ()
                }

                M801 (0x03)
                CNT1 += Local0
                Local1 = DerefOf (P300 [Local1])
                If ((Local1 != Local0))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
                }
            }

            Method (M400, 0, Serialized)
            {
                Local1 = IND4 /* \M1ED.M18A.IND4 */
                Local0 = IX00 /* \M1ED.M18A.IX00 */
                M800 (0x04, "m400")
                C300--
                If ((C300 == 0x00))
                {
                    M300 ()
                }
                Else
                {
                    M400 ()
                }

                M801 (0x04)
                CNT1 += Local0
                Local1 = DerefOf (P400 [Local1])
                If ((Local1 != Local0))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
                }
            }

            I000 = Arg0
            M100 ()
            Concatenate ("Maximal number of methods being in progress simultaneously ", MAX0, Debug)
            /* Check if exception takes place (AE_AML_METHOD_LIMIT) */

            If (Arg0)
            {
                CH04 (__METHOD__, 0x00, 0x54, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_METHOD_LIMIT */
            }
            Else
            {
                CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            }
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("m18a-0")
        M18A (0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("m18a-1")
        M18A (0x01)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
