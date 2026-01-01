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
     * ns0 originated but has names from root
     */
    /*
     * Internal Integer of Device instead of i000 (in m001)
     */
    Method (M006, 1, Serialized)
    {
        Device (D000)
        {
            Name (I000, 0x01)
        }

        Name (I001, 0x00)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        I001 = Arg0
        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
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
                                            CopyObject (P000, \M006.D000.I000)
                                        }

                                        Return (0x00)
                                    }

                                    \M006.D000.I000 = 0x80000000
                                    Return ((\M006.D000.I000 + M008 ()))
                                }

                                \M006.D000.I000 = 0x07000000
                                Return ((\M006.D000.I000 + M007 ()))
                            }

                            \M006.D000.I000 = 0x00600000
                            Return ((\M006.D000.I000 + M006 ()))
                        }

                        \M006.D000.I000 = 0x00050000
                        Return ((\M006.D000.I000 + M005 ()))
                    }

                    \M006.D000.I000 = 0x4000
                    Return ((\M006.D000.I000 + M004 ()))
                }

                \M006.D000.I000 = 0x0300
                Return ((\M006.D000.I000 + M003 ()))
            }

            ^D000.I000 = 0x20
            Return ((^D000.I000 + M002 ()))
        }

        Store ((D000.I000 + M001 ()), Local0)
        If (FLG9)
        {
            CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
            If ((Local0 != 0x87654321))
            {
                ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            If ((D000.I000 != 0x80000000))
            {
                ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, D000.I000, 0x80000000)
            }
        }
        Else
        {
            CH04 (__METHOD__, 0x01, 0x05, Z154, __LINE__, 0x00, 0x00)    /* AE_NOT_FOUND */
        }
    }

    /*
     * Internal Integer of ThermalZone instead of i000 (in m001)
     */
    Method (M007, 1, Serialized)
    {
        ThermalZone (TZ00)
        {
            Name (I000, 0x01)
        }

        Name (I001, 0x00)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        I001 = Arg0
        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
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
                                            CopyObject (P000, \M007.TZ00.I000)
                                        }

                                        Return (0x00)
                                    }

                                    \M007.TZ00.I000 = 0x80000000
                                    Return ((\M007.TZ00.I000 + M008 ()))
                                }

                                \M007.TZ00.I000 = 0x07000000
                                Return ((\M007.TZ00.I000 + M007 ()))
                            }

                            \M007.TZ00.I000 = 0x00600000
                            Return ((\M007.TZ00.I000 + M006 ()))
                        }

                        \M007.TZ00.I000 = 0x00050000
                        Return ((\M007.TZ00.I000 + M005 ()))
                    }

                    \M007.TZ00.I000 = 0x4000
                    Return ((\M007.TZ00.I000 + M004 ()))
                }

                \M007.TZ00.I000 = 0x0300
                Return ((\M007.TZ00.I000 + M003 ()))
            }

            ^TZ00.I000 = 0x20
            Return ((^TZ00.I000 + M002 ()))
        }

        Store ((TZ00.I000 + M001 ()), Local0)
        If (FLG9)
        {
            CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
            If ((Local0 != 0x87654321))
            {
                ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            If ((TZ00.I000 != 0x80000000))
            {
                ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, TZ00.I000, 0x80000000)
            }
        }
        Else
        {
            CH04 (__METHOD__, 0x01, 0x05, Z154, __LINE__, 0x00, 0x00)    /* AE_NOT_FOUND */
        }
    }

    /*
     * Internal Integer of Processor instead of i000 (in m001)
     */
    Method (M008, 1, Serialized)
    {
        Processor (PR00, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (I000, 0x01)
        }

        Name (I001, 0x00)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        I001 = Arg0
        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
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
                                            CopyObject (P000, \M008.PR00.I000)
                                        }

                                        Return (0x00)
                                    }

                                    \M008.PR00.I000 = 0x80000000
                                    Return ((\M008.PR00.I000 + M008 ()))
                                }

                                \M008.PR00.I000 = 0x07000000
                                Return ((\M008.PR00.I000 + M007 ()))
                            }

                            \M008.PR00.I000 = 0x00600000
                            Return ((\M008.PR00.I000 + M006 ()))
                        }

                        \M008.PR00.I000 = 0x00050000
                        Return ((\M008.PR00.I000 + M005 ()))
                    }

                    \M008.PR00.I000 = 0x4000
                    Return ((\M008.PR00.I000 + M004 ()))
                }

                \M008.PR00.I000 = 0x0300
                Return ((\M008.PR00.I000 + M003 ()))
            }

            ^PR00.I000 = 0x20
            Return ((^PR00.I000 + M002 ()))
        }

        Store ((PR00.I000 + M001 ()), Local0)
        If (FLG9)
        {
            CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
            If ((Local0 != 0x87654321))
            {
                ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            If ((PR00.I000 != 0x80000000))
            {
                ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, PR00.I000, 0x80000000)
            }
        }
        Else
        {
            CH04 (__METHOD__, 0x01, 0x05, Z154, __LINE__, 0x00, 0x00)    /* AE_NOT_FOUND */
        }
    }

    /*
     * Internal Integer of PowerResource instead of i000 (in m001)
     */
    Method (M009, 1, Serialized)
    {
        PowerResource (PW00, 0x01, 0x0000)
        {
            Name (I000, 0x01)
        }

        Name (I001, 0x00)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        I001 = Arg0
        CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
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
                                            CopyObject (P000, \M009.PW00.I000)
                                        }

                                        Return (0x00)
                                    }

                                    \M009.PW00.I000 = 0x80000000
                                    Return ((\M009.PW00.I000 + M008 ()))
                                }

                                \M009.PW00.I000 = 0x07000000
                                Return ((\M009.PW00.I000 + M007 ()))
                            }

                            \M009.PW00.I000 = 0x00600000
                            Return ((\M009.PW00.I000 + M006 ()))
                        }

                        \M009.PW00.I000 = 0x00050000
                        Return ((\M009.PW00.I000 + M005 ()))
                    }

                    \M009.PW00.I000 = 0x4000
                    Return ((\M009.PW00.I000 + M004 ()))
                }

                \M009.PW00.I000 = 0x0300
                Return ((\M009.PW00.I000 + M003 ()))
            }

            ^PW00.I000 = 0x20
            Return ((^PW00.I000 + M002 ()))
        }

        Store ((PW00.I000 + M001 ()), Local0)
        If (FLG9)
        {
            CH03 (__METHOD__, Z154, __LINE__, 0x00, 0x00)
            If ((Local0 != 0x87654321))
            {
                ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            If ((PW00.I000 != 0x80000000))
            {
                ERR (__METHOD__, Z154, __LINE__, 0x00, 0x00, PW00.I000, 0x80000000)
            }
        }
        Else
        {
            CH04 (__METHOD__, 0x01, 0x05, Z154, __LINE__, 0x00, 0x00)    /* AE_NOT_FOUND */
        }
    }

    Method (N100, 0, NotSerialized)
    {
        If (0x01)
        {
            SRMT ("m006-0")
            M006 (0x00)
            SRMT ("m006-1")
            If (Y200)
            {
                M006 (0x01)
            }
            Else
            {
                BLCK ()
            }

            SRMT ("m007-0")
            M007 (0x00)
            SRMT ("m007-1")
            If (Y200)
            {
                M007 (0x01)
            }
            Else
            {
                BLCK ()
            }

            SRMT ("m008-0")
            M008 (0x00)
            SRMT ("m008-1")
            If (Y200)
            {
                M008 (0x01)
            }
            Else
            {
                BLCK ()
            }

            SRMT ("m009-0")
            M009 (0x00)
            SRMT ("m009-1")
            If (Y200)
            {
                M009 (0x01)
            }
            Else
            {
                BLCK ()
            }
        }
        Else
        {
        }
    }
