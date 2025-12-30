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
     * The tests differ those from ns1.asl by that the parent object is
     * passed to methods as argument (Arg) but not directly by name.
     */
    Name (Z157, 0x9D)
    Method (M300, 0, Serialized)
    {
        Name (P000, Package (0x03)
        {
            0xABCD0000,
            0xABCD0001,
            0xABCD0002
        })
        Method (M000, 1, NotSerialized)
        {
            Method (M001, 2, NotSerialized)
            {
                Arg0 [0x00] = 0x11112222
            }

            M001 (Arg0, RefOf (Arg0))
            Local0 = DerefOf (Arg0 [0x00])
            If ((Local0 != 0x11112222))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x11112222)
            }
        }

        M000 (P000)
        Local0 = DerefOf (P000 [0x00])
        If ((Local0 != 0x11112222))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x11112222)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    Method (M301, 0, Serialized)
    {
        Name (B000, Buffer (0x03)
        {
             0x10, 0x11, 0x12                                 // ...
        })
        Method (M000, 1, NotSerialized)
        {
            Method (M001, 2, NotSerialized)
            {
                Arg0 [0x00] = 0x67
            }

            M001 (Arg0, RefOf (Arg0))
            Local0 = DerefOf (Arg0 [0x00])
            If ((Local0 != 0x67))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x67)
            }
        }

        M000 (B000)
        Local0 = DerefOf (B000 [0x00])
        If ((Local0 != 0x67))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x67)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    Method (M302, 0, Serialized)
    {
        Name (S000, "qqqqqqqqqqqqqq")
        Method (M000, 1, NotSerialized)
        {
            Method (M001, 2, NotSerialized)
            {
                Arg0 [0x00] = 0x38
            }

            M001 (Arg0, RefOf (Arg0))
            Local0 = DerefOf (Arg0 [0x00])
            If ((Local0 != 0x38))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x38)
            }
        }

        M000 (S000)
        Local0 = DerefOf (S000 [0x00])
        If ((Local0 != 0x38))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x38)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    /*
     * Element of Package instead of i000 (in m001)
     */
    Method (M303, 1, Serialized)
    {
        Name (PP00, Package (0x03)
        {
            0x11111111,
            0x01,
            0x22223333
        })
        Method (M000, 2, Serialized)
        {
            Name (I001, 0x00)
            Name (P000, Package (0x04)
            {
                0x01,
                0x02,
                0x03,
                0x04
            })
            CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
            I001 = Arg1
            Method (M001, 1, NotSerialized)
            {
                Method (M002, 1, NotSerialized)
                {
                    Method (M003, 1, NotSerialized)
                    {
                        Method (M004, 1, NotSerialized)
                        {
                            Method (M005, 1, NotSerialized)
                            {
                                Method (M006, 1, NotSerialized)
                                {
                                    Method (M007, 1, NotSerialized)
                                    {
                                        Method (M008, 1, NotSerialized)
                                        {
                                            If (I001)
                                            {
                                                Arg0 [0x01] = P000 /* \M303.M000.P000 */
                                            }

                                            Return (0x00)
                                        }

                                        Arg0 [0x01] = 0x80000000
                                        Return ((DerefOf (Arg0 [0x01]) + M008 (Arg0)))
                                    }

                                    Arg0 [0x01] = 0x07000000
                                    Return ((DerefOf (Arg0 [0x01]) + M007 (Arg0)))
                                }

                                Arg0 [0x01] = 0x00600000
                                Return ((DerefOf (Arg0 [0x01]) + M006 (Arg0)))
                            }

                            Arg0 [0x01] = 0x00050000
                            Return ((DerefOf (Arg0 [0x01]) + M005 (Arg0)))
                        }

                        Arg0 [0x01] = 0x4000
                        Return ((DerefOf (Arg0 [0x01]) + M004 (Arg0)))
                    }

                    Arg0 [0x01] = 0x0300
                    Return ((DerefOf (Arg0 [0x01]) + M003 (Arg0)))
                }

                Arg0 [0x01] = 0x20
                Return ((DerefOf (Arg0 [0x01]) + M002 (Arg0)))
            }

            Store ((DerefOf (Arg0 [0x01]) + M001 (Arg0)), Local0)
            If ((Local0 != 0x87654321))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            Local1 = DerefOf (Arg0 [0x01])
            If ((Local1 != 0x80000000))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local1, 0x80000000)
            }

            CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
            Return (Local0)
        }

        Local0 = M000 (PP00, Arg0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        Local0 = DerefOf (PP00 [0x01])
        If ((Local0 != 0x80000000))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x80000000)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    /*
     * Element of Package instead of i000 (in m002)
     */
    Method (M304, 0, Serialized)
    {
        Name (I001, 0x00)
        Name (PP00, Package (0x03)
        {
            0x11111111,
            0x00100000,
            0x22223333
        })
        Method (M000, 1, NotSerialized)
        {
            Method (M001, 1, NotSerialized)
            {
                If ((I001 < 0x64))
                {
                    Local0 = DerefOf (Arg0 [0x01])
                    Local0++
                    Arg0 [0x01] = Local0
                    I001++
                    Local0 = (DerefOf (Arg0 [0x01]) + M001 (Arg0))
                    Return (Local0)
                }

                Return (0x00)
            }

            Store ((DerefOf (Arg0 [0x01]) + M001 (Arg0)), Local0)
            If ((Local0 != 0x065013BA))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x065013BA)
            }

            Local1 = DerefOf (Arg0 [0x01])
            If ((Local1 != 0x00100064))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local1, 0x00100064)
            }

            Return (Local0)
        }

        Local0 = M000 (PP00)
        If ((Local0 != 0x065013BA))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x065013BA)
        }

        Local1 = DerefOf (PP00 [0x01])
        If ((Local1 != 0x00100064))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local1, 0x00100064)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    /*
     * Buffer Field instead of i000 (in m001)
     */
    Method (M305, 0, Serialized)
    {
        Name (B000, Buffer (0x10){})
        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x05, 0x20, BF00)
        BF00 = 0xABCDEF70
        Method (M000, 1, NotSerialized)
        {
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
                                            Return (0x00)
                                        }

                                        Arg0 = 0x80000000
                                        Return ((Arg0 + M008 ()))
                                    }

                                    Arg0 = 0x07000000
                                    Return ((Arg0 + M007 ()))
                                }

                                Arg0 = 0x00600000
                                Return ((Arg0 + M006 ()))
                            }

                            Arg0 = 0x00050000
                            Return ((Arg0 + M005 ()))
                        }

                        Arg0 = 0x4000
                        Return ((Arg0 + M004 ()))
                    }

                    Arg0 = 0x0300
                    Return ((Arg0 + M003 ()))
                }

                Arg0 = 0x20
                Return ((Arg0 + M002 ()))
            }

            Arg0 = 0x01
            Store ((Arg0 + M001 ()), Local0)
            If ((Local0 != 0x87654321))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            Local1 = 0x01
            If ((Arg0 != Local1))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Arg0, Local1)
            }

            CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
            Return (Local0)
        }

        Local0 = M000 (BF00)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        Local1 = Buffer () {0x70, 0xEF, 0xCD, 0xAB}
        If ((BF00 != Local1))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, BF00, Local1)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    /*
     * Field instead of i000 (in m001)
     */
    Method (M306, 0, Serialized)
    {
        Name (I001, 0x00)
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   32,
            F001,   32
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
        F000 = 0xABCDEF70
        Method (M000, 1, NotSerialized)
        {
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
                                            Return (0x00)
                                        }

                                        Arg0 = 0x80000000
                                        Return ((Arg0 + M008 ()))
                                    }

                                    Arg0 = 0x07000000
                                    Return ((Arg0 + M007 ()))
                                }

                                Arg0 = 0x00600000
                                Return ((Arg0 + M006 ()))
                            }

                            Arg0 = 0x00050000
                            Return ((Arg0 + M005 ()))
                        }

                        Arg0 = 0x4000
                        Return ((Arg0 + M004 ()))
                    }

                    Arg0 = 0x0300
                    Return ((Arg0 + M003 ()))
                }

                Arg0 = 0x20
                Return ((Arg0 + M002 ()))
            }

            Arg0 = 0x01
            Store ((Arg0 + M001 ()), Local0)
            If ((Local0 != 0x87654321))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            Local1 = 0x01
            If ((Arg0 != Local1))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Arg0, Local1)
            }

            CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
            Return (Local0)
        }

        Local0 = M000 (F000)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        Local1 = 0xABCDEF70
        If ((F000 != Local1))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, F000, Local1)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    /*
     * Bank Field instead of i000 (in m001)
     */
    Method (M307, 0, Serialized)
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

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
        BNK0 = 0xABCDEF70
        Method (M000, 1, NotSerialized)
        {
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
                                            Return (0x00)
                                        }

                                        Arg0 = 0x80000000
                                        Return ((Arg0 + M008 ()))
                                    }

                                    Arg0 = 0x07000000
                                    Return ((Arg0 + M007 ()))
                                }

                                Arg0 = 0x00600000
                                Return ((Arg0 + M006 ()))
                            }

                            Arg0 = 0x00050000
                            Return ((Arg0 + M005 ()))
                        }

                        Arg0 = 0x4000
                        Return ((Arg0 + M004 ()))
                    }

                    Arg0 = 0x0300
                    Return ((Arg0 + M003 ()))
                }

                Arg0 = 0x20
                Return ((Arg0 + M002 ()))
            }

            Arg0 = 0x01
            Store ((Arg0 + M001 ()), Local0)
            If ((Local0 != 0x87654321))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            Local1 = 0x01
            If ((Arg0 != Local1))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Arg0, Local1)
            }

            CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
            Return (Local0)
        }

        Local0 = M000 (BNK0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        Local1 = 0xABCDEF70
        If ((BNK0 != Local1))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, BNK0, Local1)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    /*
     * Index Field instead of i000 (in m001)
     */
    Method (M308, 0, Serialized)
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

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
        IF00 = 0xABCDEF70
        Method (M000, 1, NotSerialized)
        {
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
                                            Return (0x00)
                                        }

                                        Arg0 = 0x80000000
                                        Return ((Arg0 + M008 ()))
                                    }

                                    Arg0 = 0x07000000
                                    Return ((Arg0 + M007 ()))
                                }

                                Arg0 = 0x00600000
                                Return ((Arg0 + M006 ()))
                            }

                            Arg0 = 0x00050000
                            Return ((Arg0 + M005 ()))
                        }

                        Arg0 = 0x4000
                        Return ((Arg0 + M004 ()))
                    }

                    Arg0 = 0x0300
                    Return ((Arg0 + M003 ()))
                }

                Arg0 = 0x20
                Return ((Arg0 + M002 ()))
            }

            Arg0 = 0x01
            Store ((Arg0 + M001 ()), Local0)
            If ((Local0 != 0x87654321))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            Local1 = 0x01
            If ((Arg0 != Local1))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Arg0, Local1)
            }

            CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
            Return (Local0)
        }

        Local0 = M000 (IF00)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        Local1 = 0xABCDEF70
        If ((IF00 != Local1))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, IF00, Local1)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    /*
     * Element of Buffer instead of i000 (in m001)
     */
    Method (M309, 1, Serialized)
    {
        Name (I001, 0x00)
        Name (B000, Buffer (0x03)
        {
             0x11, 0x01, 0x22                                 // .."
        })
        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
        I001 = Arg0
        Method (M000, 2, NotSerialized)
        {
            Method (M001, 1, NotSerialized)
            {
                Method (M002, 1, NotSerialized)
                {
                    Method (M003, 1, NotSerialized)
                    {
                        Method (M004, 1, NotSerialized)
                        {
                            Method (M005, 1, NotSerialized)
                            {
                                Method (M006, 1, NotSerialized)
                                {
                                    Method (M007, 1, NotSerialized)
                                    {
                                        Method (M008, 1, NotSerialized)
                                        {
                                            If (I001)
                                            {
                                                Arg0 [0x01] = 0xFF
                                            }

                                            Return (0x00)
                                        }

                                        Arg0 [0x01] = 0x08
                                        Return ((DerefOf (Arg0 [0x01]) + M008 (Arg0)))
                                    }

                                    Arg0 [0x01] = 0x07
                                    Return ((DerefOf (Arg0 [0x01]) + M007 (Arg0)))
                                }

                                Arg0 [0x01] = 0x06
                                Return ((DerefOf (Arg0 [0x01]) + M006 (Arg0)))
                            }

                            Arg0 [0x01] = 0x05
                            Return ((DerefOf (Arg0 [0x01]) + M005 (Arg0)))
                        }

                        Arg0 [0x01] = 0x04
                        Return ((DerefOf (Arg0 [0x01]) + M004 (Arg0)))
                    }

                    Arg0 [0x01] = 0x03
                    Return ((DerefOf (Arg0 [0x01]) + M003 (Arg0)))
                }

                Arg0 [0x01] = 0x02
                Return ((DerefOf (Arg0 [0x01]) + M002 (Arg0)))
            }

            Store ((DerefOf (Arg0 [0x01]) + M001 (Arg0)), Local0)
            If ((Local0 != 0x24))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x24)
            }

            Local1 = DerefOf (Arg0 [0x01])
            If (Arg1)
            {
                Local2 = 0xFF
            }
            Else
            {
                Local2 = 0x08
            }

            If ((Local1 != Local2))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local1, Local2)
            }

            CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
            Return (Local0)
        }

        Local0 = M000 (B000, Arg0)
        If ((Local0 != 0x24))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x24)
        }

        Local1 = DerefOf (B000 [0x01])
        If (Arg0)
        {
            Local2 = 0xFF
        }
        Else
        {
            Local2 = 0x08
        }

        If ((Local1 != Local2))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local1, Local2)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    /*
     * Element of String instead of i000 (in m001)
     */
    Method (M30A, 1, Serialized)
    {
        Name (I001, 0x00)
        Name (S000, "q\x01ertyuiop")
        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
        I001 = Arg0
        Method (M000, 2, NotSerialized)
        {
            Method (M001, 1, NotSerialized)
            {
                Method (M002, 1, NotSerialized)
                {
                    Method (M003, 1, NotSerialized)
                    {
                        Method (M004, 1, NotSerialized)
                        {
                            Method (M005, 1, NotSerialized)
                            {
                                Method (M006, 1, NotSerialized)
                                {
                                    Method (M007, 1, NotSerialized)
                                    {
                                        Method (M008, 1, NotSerialized)
                                        {
                                            If (I001)
                                            {
                                                Arg0 [0x01] = 0xFF
                                            }

                                            Return (0x00)
                                        }

                                        Arg0 [0x01] = 0x08
                                        Return ((DerefOf (Arg0 [0x01]) + M008 (Arg0)))
                                    }

                                    Arg0 [0x01] = 0x07
                                    Return ((DerefOf (Arg0 [0x01]) + M007 (Arg0)))
                                }

                                Arg0 [0x01] = 0x06
                                Return ((DerefOf (Arg0 [0x01]) + M006 (Arg0)))
                            }

                            Arg0 [0x01] = 0x05
                            Return ((DerefOf (Arg0 [0x01]) + M005 (Arg0)))
                        }

                        Arg0 [0x01] = 0x04
                        Return ((DerefOf (Arg0 [0x01]) + M004 (Arg0)))
                    }

                    Arg0 [0x01] = 0x03
                    Return ((DerefOf (Arg0 [0x01]) + M003 (Arg0)))
                }

                Arg0 [0x01] = 0x02
                Return ((DerefOf (Arg0 [0x01]) + M002 (Arg0)))
            }

            Store ((DerefOf (Arg0 [0x01]) + M001 (Arg0)), Local0)
            If ((Local0 != 0x24))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x24)
            }

            Local1 = DerefOf (Arg0 [0x01])
            If (Arg1)
            {
                Local2 = 0xFF
            }
            Else
            {
                Local2 = 0x08
            }

            If ((Local1 != Local2))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local1, Local2)
            }

            CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
            Return (Local0)
        }

        Local0 = M000 (S000, Arg0)
        If ((Local0 != 0x24))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x24)
        }

        Local1 = DerefOf (S000 [0x01])
        If (Arg0)
        {
            Local2 = 0xFF
        }
        Else
        {
            Local2 = 0x08
        }

        If ((Local1 != Local2))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local1, Local2)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    /*
     * Buffer Field instead of i000 (in m001)
     *
     * CreateField deeper than parent
     */
    Method (M30B, 1, Serialized)
    {
        Name (I001, 0x00)
        Name (B000, Buffer (0x10){})
        I001 = Arg0
        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
        Method (M000, 2, NotSerialized)
        {
            CreateField (B000, 0x05, 0x20, BF00)
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
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            If (Arg1)
            {
                Local1 = Buffer() {0x44, 0x33, 0x22, 0x11}
            }
            Else
            {
                Local1 = Buffer() {0x00, 0x00, 0x00, 0x80}
            }

            If ((BF00 != Local1))
            {
                ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, BF00, Local1)
            }

            CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
            Return (Local0)
        }

        Local0 = M000 (0x00, Arg0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z157, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        CH03 (__METHOD__, Z157, __LINE__, 0x00, 0x00)
    }

    Method (N003, 0, NotSerialized)
    {
        If (0x01)
        {
            SRMT ("m300")
            M300 ()
            SRMT ("m301")
            M301 ()
            SRMT ("m302")
            M302 ()
            SRMT ("m303-0")
            M303 (0x00)
            SRMT ("m303-1")
            If (Y200)
            {
                M303 (0x01)
            }
            Else
            {
                BLCK ()
            }

            SRMT ("m304")
            M304 ()
            SRMT ("m305")
            M305 ()
            SRMT ("m306")
            M306 ()
            SRMT ("m307")
            M307 ()
            SRMT ("m308")
            M308 ()
            SRMT ("m309-0")
            M309 (0x00)
            SRMT ("m309-1")
            M309 (0x01)
            SRMT ("m30a-0")
            M30A (0x00)
            SRMT ("m30a-1")
            M30A (0x01)
            SRMT ("m30b-0")
            M30B (0x00)
            SRMT ("m30b-1")
            M30B (0x01)
        }
        Else
        {
            SRMT ("m300")
            M300 ()
        }
    }
