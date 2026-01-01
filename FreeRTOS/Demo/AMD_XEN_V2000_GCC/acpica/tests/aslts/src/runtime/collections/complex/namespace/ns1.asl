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
    Name (Z155, 0x9B)
    /*
     * Three tests below are here
     * as specific type arguments passing -
     * arguments though passed directly to method, not as references,
     * nevertheless allow access to the elements of original objects.
     */
    Method (M100, 0, Serialized)
    {
        Name (P000, Package (0x03)
        {
            0xABCD0000,
            0xABCD0001,
            0xABCD0002
        })
        Method (M001, 2, NotSerialized)
        {
            Arg0 [0x00] = 0x11112222
        }

        M001 (P000, RefOf (P000))
        Local0 = DerefOf (P000 [0x00])
        If ((Local0 != 0x11112222))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x11112222)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    Method (M101, 0, Serialized)
    {
        Name (B000, Buffer (0x03)
        {
             0x10, 0x11, 0x12                                 // ...
        })
        Method (M001, 2, NotSerialized)
        {
            Arg0 [0x00] = 0x67
        }

        M001 (B000, RefOf (B000))
        Local0 = DerefOf (B000 [0x00])
        If ((Local0 != 0x67))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x67)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    Method (M102, 0, Serialized)
    {
        Name (S000, "qqqqqqqqqqqqqq")
        Method (M001, 2, NotSerialized)
        {
            Arg0 [0x00] = 0x38
        }

        M001 (S000, RefOf (S000))
        Local0 = DerefOf (S000 [0x00])
        If ((Local0 != 0x38))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x38)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    /*
     * Element of Package instead of i000 (in m001)
     */
    Method (M103, 1, Serialized)
    {
        Name (I001, 0x00)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        Name (PP00, Package (0x03)
        {
            0x11111111,
            0x01,
            0x22223333
        })
        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
        I001 = Arg0
        Method (M001, 0, NotSerialized)
        {
            Method (M002, 0, NotSerialized)
            {
                Method (M003, 0, NotSerialized)
                {
                    Method (M004, 0, NotSerialized)
                    {
                        Method (M005, 0, NotSerialized)
                        {
                            Method (M006, 0, NotSerialized)
                            {
                                Method (M007, 0, NotSerialized)
                                {
                                    Method (M008, 0, NotSerialized)
                                    {
                                        If (I001)
                                        {
                                            PP00 [0x01] = P000 /* \M103.P000 */
                                        }

                                        Return (0x00)
                                    }

                                    PP00 [0x01] = 0x80000000
                                    Return ((DerefOf (PP00 [0x01]) + M008 ()))
                                }

                                PP00 [0x01] = 0x07000000
                                Return ((DerefOf (PP00 [0x01]) + M007 ()))
                            }

                            PP00 [0x01] = 0x00600000
                            Return ((DerefOf (PP00 [0x01]) + M006 ()))
                        }

                        PP00 [0x01] = 0x00050000
                        Return ((DerefOf (PP00 [0x01]) + M005 ()))
                    }

                    PP00 [0x01] = 0x4000
                    Return ((DerefOf (PP00 [0x01]) + M004 ()))
                }

                PP00 [0x01] = 0x0300
                Return ((DerefOf (PP00 [0x01]) + M003 ()))
            }

            PP00 [0x01] = 0x20
            Return ((DerefOf (PP00 [0x01]) + M002 ()))
        }

        Store ((DerefOf (PP00 [0x01]) + M001 ()), Local0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        Local0 = DerefOf (PP00 [0x01])
        If ((Local0 != 0x80000000))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x80000000)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    /*
     * Element of Package instead of i000 (in m002)
     */
    Method (M104, 0, Serialized)
    {
        Name (I001, 0x00)
        Name (PP00, Package (0x03)
        {
            0x11111111,
            0x00100000,
            0x22223333
        })
        Method (M001, 0, NotSerialized)
        {
            If ((I001 < 0x64))
            {
                Local0 = DerefOf (PP00 [0x01])
                Local0++
                PP00 [0x01] = Local0
                I001++
                Local0 = (DerefOf (PP00 [0x01]) + M001 ())
                Return (Local0)
            }

            Return (0x00)
        }

        Store ((DerefOf (PP00 [0x01]) + M001 ()), Local0)
        If ((Local0 != 0x065013BA))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x065013BA)
        }

        Local0 = DerefOf (PP00 [0x01])
        If ((Local0 != 0x00100064))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x00100064)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    /*
     * Buffer Field instead of i000 (in m001)
     */
    Method (M105, 1, Serialized)
    {
        Name (I001, 0x00)
        Name (B000, Buffer (0x10){})
        CreateField (B000, 0x05, 0x20, BF00)
        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
        I001 = Arg0
        Method (M001, 0, NotSerialized)
        {
            Method (M002, 0, NotSerialized)
            {
                Method (M003, 0, NotSerialized)
                {
                    Method (M004, 0, NotSerialized)
                    {
                        Method (M005, 0, NotSerialized)
                        {
                            Method (M006, 0, NotSerialized)
                            {
                                Method (M007, 0, NotSerialized)
                                {
                                    Method (M008, 0, NotSerialized)
                                    {
                                        If (I001)
                                        {
                                            BF00 = 0x11223344
                                        }

                                        Return (0x00)
                                    }

                                    BF00 = 0x80000000
                                    Return ((BF00 + M008 ()))
                                }

                                BF00 = 0x07000000
                                Return ((BF00 + M007 ()))
                            }

                            BF00 = 0x00600000
                            Return ((BF00 + M006 ()))
                        }

                        BF00 = 0x00050000
                        Return ((BF00 + M005 ()))
                    }

                    BF00 = 0x4000
                    Return ((BF00 + M004 ()))
                }

                BF00 = 0x0300
                Return ((BF00 + M003 ()))
            }

            BF00 = 0x20
            Return ((BF00 + M002 ()))
        }

        BF00 = 0x01
        Store ((BF00 + M001 ()), Local0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        If (Arg0)
        {
            Local1 = Buffer() {0x44, 0x33, 0x22, 0x11}
        }
        Else
        {
            Local1 = Buffer() {0x00, 0x00, 0x00, 0x80}
        }

        If ((BF00 != Local1))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, BF00, Local1)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    /*
     * Field instead of i000 (in m001)
     */
    Method (M106, 1, Serialized)
    {
        Name (I001, 0x00)
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   32,
            F001,   32
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
        I001 = Arg0
        Method (M001, 0, NotSerialized)
        {
            Method (M002, 0, NotSerialized)
            {
                Method (M003, 0, NotSerialized)
                {
                    Method (M004, 0, NotSerialized)
                    {
                        Method (M005, 0, NotSerialized)
                        {
                            Method (M006, 0, NotSerialized)
                            {
                                Method (M007, 0, NotSerialized)
                                {
                                    Method (M008, 0, NotSerialized)
                                    {
                                        If (I001)
                                        {
                                            F001 = 0x11223344
                                        }

                                        Return (0x00)
                                    }

                                    F001 = 0x80000000
                                    Return ((F001 + M008 ()))
                                }

                                F001 = 0x07000000
                                Return ((F001 + M007 ()))
                            }

                            F001 = 0x00600000
                            Return ((F001 + M006 ()))
                        }

                        F001 = 0x00050000
                        Return ((F001 + M005 ()))
                    }

                    F001 = 0x4000
                    Return ((F001 + M004 ()))
                }

                F001 = 0x0300
                Return ((F001 + M003 ()))
            }

            F001 = 0x20
            Return ((F001 + M002 ()))
        }

        F001 = 0x01
        Store ((F001 + M001 ()), Local0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        If (Arg0)
        {
            Local1 = 0x11223344
        }
        Else
        {
            Local1 = 0x80000000
        }

        If ((F001 != Local1))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, F001, Local1)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    /*
     * Bank Field instead of i000 (in m001)
     *
     * (is this test correct?)
     */
    Method (M107, 1, Serialized)
    {
        Name (I001, 0x00)
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   32,
            F001,   32
        }

        BankField (R000, F001, 0x00, ByteAcc, NoLock, Preserve)
        {
            BNK0,   32
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
        I001 = Arg0
        Method (M001, 0, NotSerialized)
        {
            Method (M002, 0, NotSerialized)
            {
                Method (M003, 0, NotSerialized)
                {
                    Method (M004, 0, NotSerialized)
                    {
                        Method (M005, 0, NotSerialized)
                        {
                            Method (M006, 0, NotSerialized)
                            {
                                Method (M007, 0, NotSerialized)
                                {
                                    Method (M008, 0, NotSerialized)
                                    {
                                        If (I001)
                                        {
                                            BNK0 = 0x11223344
                                        }

                                        Return (0x00)
                                    }

                                    BNK0 = 0x80000000
                                    Return ((BNK0 + M008 ()))
                                }

                                BNK0 = 0x07000000
                                Return ((BNK0 + M007 ()))
                            }

                            BNK0 = 0x00600000
                            Return ((BNK0 + M006 ()))
                        }

                        BNK0 = 0x00050000
                        Return ((BNK0 + M005 ()))
                    }

                    BNK0 = 0x4000
                    Return ((BNK0 + M004 ()))
                }

                BNK0 = 0x0300
                Return ((BNK0 + M003 ()))
            }

            BNK0 = 0x20
            Return ((BNK0 + M002 ()))
        }

        BNK0 = 0x01
        Store ((BNK0 + M001 ()), Local0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        If (Arg0)
        {
            Local1 = 0x11223344
        }
        Else
        {
            Local1 = 0x80000000
        }

        If ((BNK0 != Local1))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, BNK0, Local1)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    /*
     * Index Field instead of i000 (in m001)
     *
     * (is this test correct?)
     */
    Method (M108, 1, Serialized)
    {
        Name (I001, 0x00)
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   32,
            F001,   32
        }

        IndexField (F000, F001, ByteAcc, NoLock, Preserve)
        {
            IF00,   32
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
        I001 = Arg0
        Method (M001, 0, NotSerialized)
        {
            Method (M002, 0, NotSerialized)
            {
                Method (M003, 0, NotSerialized)
                {
                    Method (M004, 0, NotSerialized)
                    {
                        Method (M005, 0, NotSerialized)
                        {
                            Method (M006, 0, NotSerialized)
                            {
                                Method (M007, 0, NotSerialized)
                                {
                                    Method (M008, 0, NotSerialized)
                                    {
                                        If (I001)
                                        {
                                            IF00 = 0x11223344
                                        }

                                        Return (0x00)
                                    }

                                    IF00 = 0x80000000
                                    Return ((IF00 + M008 ()))
                                }

                                IF00 = 0x07000000
                                Return ((IF00 + M007 ()))
                            }

                            IF00 = 0x00600000
                            Return ((IF00 + M006 ()))
                        }

                        IF00 = 0x00050000
                        Return ((IF00 + M005 ()))
                    }

                    IF00 = 0x4000
                    Return ((IF00 + M004 ()))
                }

                IF00 = 0x0300
                Return ((IF00 + M003 ()))
            }

            IF00 = 0x20
            Return ((IF00 + M002 ()))
        }

        IF00 = 0x01
        Store ((IF00 + M001 ()), Local0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        If (Arg0)
        {
            Local1 = 0x11223344
        }
        Else
        {
            Local1 = 0x80000000
        }

        If ((IF00 != Local1))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, IF00, Local1)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    /*
     * Element of Buffer instead of i000 (in m001)
     */
    Method (M109, 1, Serialized)
    {
        Name (I001, 0x00)
        Name (B000, Buffer (0x03)
        {
             0x11, 0x01, 0x22                                 // .."
        })
        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
        I001 = Arg0
        Method (M001, 0, NotSerialized)
        {
            Method (M002, 0, NotSerialized)
            {
                Method (M003, 0, NotSerialized)
                {
                    Method (M004, 0, NotSerialized)
                    {
                        Method (M005, 0, NotSerialized)
                        {
                            Method (M006, 0, NotSerialized)
                            {
                                Method (M007, 0, NotSerialized)
                                {
                                    Method (M008, 0, NotSerialized)
                                    {
                                        If (I001)
                                        {
                                            B000 [0x01] = 0xFF
                                        }

                                        Return (0x00)
                                    }

                                    B000 [0x01] = 0x08
                                    Return ((DerefOf (B000 [0x01]) + M008 ()))
                                }

                                B000 [0x01] = 0x07
                                Return ((DerefOf (B000 [0x01]) + M007 ()))
                            }

                            B000 [0x01] = 0x06
                            Return ((DerefOf (B000 [0x01]) + M006 ()))
                        }

                        B000 [0x01] = 0x05
                        Return ((DerefOf (B000 [0x01]) + M005 ()))
                    }

                    B000 [0x01] = 0x04
                    Return ((DerefOf (B000 [0x01]) + M004 ()))
                }

                B000 [0x01] = 0x03
                Return ((DerefOf (B000 [0x01]) + M003 ()))
            }

            B000 [0x01] = 0x02
            Return ((DerefOf (B000 [0x01]) + M002 ()))
        }

        Store ((DerefOf (B000 [0x01]) + M001 ()), Local0)
        If ((Local0 != 0x24))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x24)
        }

        Local0 = DerefOf (B000 [0x01])
        If (Arg0)
        {
            Local1 = 0xFF
        }
        Else
        {
            Local1 = 0x08
        }

        If ((Local0 != Local1))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, Local1)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    /*
     * Element of String instead of i000 (in m001)
     */
    Method (M10A, 1, Serialized)
    {
        Name (I001, 0x00)
        Name (S000, "q\x01ertyuiop")
        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
        I001 = Arg0
        Method (M001, 0, NotSerialized)
        {
            Method (M002, 0, NotSerialized)
            {
                Method (M003, 0, NotSerialized)
                {
                    Method (M004, 0, NotSerialized)
                    {
                        Method (M005, 0, NotSerialized)
                        {
                            Method (M006, 0, NotSerialized)
                            {
                                Method (M007, 0, NotSerialized)
                                {
                                    Method (M008, 0, NotSerialized)
                                    {
                                        If (I001)
                                        {
                                            S000 [0x01] = 0xFF
                                        }

                                        Return (0x00)
                                    }

                                    S000 [0x01] = 0x08
                                    Return ((DerefOf (S000 [0x01]) + M008 ()))
                                }

                                S000 [0x01] = 0x07
                                Return ((DerefOf (S000 [0x01]) + M007 ()))
                            }

                            S000 [0x01] = 0x06
                            Return ((DerefOf (S000 [0x01]) + M006 ()))
                        }

                        S000 [0x01] = 0x05
                        Return ((DerefOf (S000 [0x01]) + M005 ()))
                    }

                    S000 [0x01] = 0x04
                    Return ((DerefOf (S000 [0x01]) + M004 ()))
                }

                S000 [0x01] = 0x03
                Return ((DerefOf (S000 [0x01]) + M003 ()))
            }

            S000 [0x01] = 0x02
            Return ((DerefOf (S000 [0x01]) + M002 ()))
        }

        Store ((DerefOf (S000 [0x01]) + M001 ()), Local0)
        If ((Local0 != 0x24))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, 0x24)
        }

        Local0 = DerefOf (S000 [0x01])
        If (Arg0)
        {
            Local1 = 0xFF
        }
        Else
        {
            Local1 = 0x08
        }

        If ((Local0 != Local1))
        {
            ERR (__METHOD__, Z155, __LINE__, 0x00, 0x00, Local0, Local1)
        }

        CH03 (__METHOD__, Z155, __LINE__, 0x00, 0x00)
    }

    Method (N001, 0, NotSerialized)
    {
        If (0x01)
        {
            SRMT ("m100")
            M100 ()
            SRMT ("m101")
            M101 ()
            SRMT ("m102")
            M102 ()
            SRMT ("m103-0")
            M103 (0x00)
            SRMT ("m103-1")
            If (Y200)
            {
                M103 (0x01)
            }
            Else
            {
                BLCK ()
            }

            SRMT ("m104")
            M104 ()
            SRMT ("m105-0")
            M105 (0x00)
            SRMT ("m105-1")
            M105 (0x01)
            SRMT ("m106-0")
            M106 (0x00)
            SRMT ("m106-1")
            M106 (0x01)
            SRMT ("m107-0")
            M107 (0x00)
            SRMT ("m107-1")
            M107 (0x01)
            SRMT ("m108-0")
            M108 (0x00)
            SRMT ("m108-1")
            M108 (0x01)
            SRMT ("m109-0")
            M109 (0x00)
            SRMT ("m109-1")
            M109 (0x01)
            SRMT ("m10a-0")
            M10A (0x00)
            SRMT ("m10a-1")
            M10A (0x01)
            SRMT ("m10a-0-2") /* Run it twice: see bug 265 */
            M10A (0x00)
            M10A (0x00)
        }
        Else
        {
            SRMT ("m10a-0")
            M10A (0x00)
            SRMT ("m10a-1")
            M10A (0x00)
        }
    }
