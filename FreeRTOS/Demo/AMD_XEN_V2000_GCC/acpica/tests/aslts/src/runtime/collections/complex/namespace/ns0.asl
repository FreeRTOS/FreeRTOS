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
     * Trying to get the chain of calls of methods such that
     * sections of operative stack corresponding to different
     * methods contain the internal object (itself, not a RefOf
     * reference to it) of the same Name Space node.
     *
     * Then force (by Store/CopyObject):
     *   1) changing the value of that internal object
     *   2) replacing the internal object itself by some another one
     *
     * Check that the changing/replacing has no effect on the
     * values evaluated on the lowest stages of calculation.
     */
    Name (Z154, 0x9A)
    /*
     * Named Integer i000
     */
    Method (M000, 1, Serialized)
    {
        Name (I000, 0x01)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        Name (I001, 0x00)
        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
        I001 = Arg0
        Method (M001, 0, NotSerialized)
        {
            Method (M002, 0, NotSerialized)
            {
                Method (M003, 0, NotSerialized)
                {
                    If (I001)
                    {
                        CopyObject (P000, I000) /* \M000.I000 */
                    }

                    Return (0xABCD0000)
                }

                Return ((I000 + M003 ()))
            }

            Return ((I000 + M002 ()))
        }

        Store ((I000 + M001 ()), Local0)
        If ((Local0 != 0xABCD0003))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local0, 0xABCD0003)
        }

        Debug = Local0
        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
    }

    Method (M001, 1, Serialized)
    {
        Name (I000, 0x01)
        Name (I001, 0x00)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
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
                                            CopyObject (P000, I000) /* \M001.I000 */
                                        }

                                        Return (0x00)
                                    }

                                    I000 = 0x80000000
                                    Return ((I000 + M008 ()))
                                }

                                I000 = 0x07000000
                                Return ((I000 + M007 ()))
                            }

                            I000 = 0x00600000
                            Return ((I000 + M006 ()))
                        }

                        I000 = 0x00050000
                        Return ((I000 + M005 ()))
                    }

                    I000 = 0x4000
                    Return ((I000 + M004 ()))
                }

                I000 = 0x0300
                Return ((I000 + M003 ()))
            }

            I000 = 0x20
            Return ((I000 + M002 ()))
        }

        Store ((I000 + M001 ()), Local0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        If ((I000 != 0x80000000))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, I000, 0x80000000)
        }

        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
    }

    Method (M002, 0, Serialized)
    {
        Name (I000, 0x00100000)
        Name (I001, 0x00)
        Method (M001, 0, NotSerialized)
        {
            If ((I001 < 0x64))
            {
                I000++
                I001++
                Local0 = (I000 + M001 ())
                Return (Local0)
            }

            Return (0x00)
        }

        Store ((I000 + M001 ()), Local0)
        If ((Local0 != 0x065013BA))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local0, 0x065013BA)
        }

        If ((I000 != 0x00100064))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, I000, 0x00100064)
        }

        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
    }

    Method (M003, 0, Serialized)
    {
        Name (I000, 0x00100000)
        Name (I001, 0x00)
        Method (M001, 0, NotSerialized)
        {
            If ((I001 < 0x64))
            {
                I000++
                I001++
                Return (Local0 = (I000 + M001 ()))
            }

            Return (0x00)
        }

        Store ((I000 + M001 ()), Local0)
        If ((Local0 != 0x065013BA))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local0, 0x065013BA)
        }

        If ((I000 != 0x00100064))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, I000, 0x00100064)
        }

        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
    }

    /*
     * Local instead of i000 (in m001)
     */
    Method (M004, 1, Serialized)
    {
        Name (I001, 0x00)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        I001 = Arg0
        Local7 = 0x01
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
                                            CopyObject (P000, Local7)
                                        }

                                        Return (0x00)
                                    }

                                    Local7 = 0x80000000
                                    Return ((Local7 + M008 ()))
                                }

                                Local7 = 0x07000000
                                Return ((Local7 + M007 ()))
                            }

                            Local7 = 0x00600000
                            Return ((Local7 + M006 ()))
                        }

                        Local7 = 0x00050000
                        Return ((Local7 + M005 ()))
                    }

                    Local7 = 0x4000
                    Return ((Local7 + M004 ()))
                }

                Local7 = 0x0300
                Return ((Local7 + M003 ()))
            }

            Local7 = 0x20
            Return ((Local7 + M002 ()))
        }

        Store ((Local7 + M001 ()), Local0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        If ((Local7 != 0x01))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local7, 0x01)
        }

        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
    }

    /*
     * Arg instead of i000 (in m001)
     */
    Method (M005, 2, Serialized)
    {
        Name (I001, 0x00)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        I001 = Arg0
        Arg1 = 0x01
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
                                            CopyObject (P000, Arg1)
                                        }

                                        Return (0x00)
                                    }

                                    Arg1 = 0x80000000
                                    Return ((Arg1 + M008 ()))
                                }

                                Arg1 = 0x07000000
                                Return ((Arg1 + M007 ()))
                            }

                            Arg1 = 0x00600000
                            Return ((Arg1 + M006 ()))
                        }

                        Arg1 = 0x00050000
                        Return ((Arg1 + M005 ()))
                    }

                    Arg1 = 0x4000
                    Return ((Arg1 + M004 ()))
                }

                Arg1 = 0x0300
                Return ((Arg1 + M003 ()))
            }

            Arg1 = 0x20
            Return ((Arg1 + M002 ()))
        }

        Store ((Arg1 + M001 ()), Local0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        If ((Arg1 != 0x01))
        {
            ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Arg1, 0x01)
        }

        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
    }

    Method (N000, 0, NotSerialized)
    {
        If (0x01)
        {
            SRMT ("m000-0")
            M000 (0x00)
            SRMT ("m000-1")
            M000 (0x01)
            SRMT ("m001-0")
            M001 (0x00)
            SRMT ("m001-1")
            If (Y200)
            {
                M001 (0x01)
            }
            Else
            {
                BLCK ()
            }

            SRMT ("m002")
            M002 ()
            SRMT ("m003")
            M003 ()
            SRMT ("m004-0")
            M004 (0x00)
            SRMT ("m004-1")
            M004 (0x01)
            SRMT ("m005-0")
            M005 (0x00, 0x00)
            SRMT ("m005-1")
            M005 (0x01, 0x00)
        }
        Else
        {
            SRMT ("m000-0")
            M000 (0x00)
            SRMT ("m000-1")
            M000 (0x01)
        }
    }
