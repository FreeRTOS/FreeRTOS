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
     * ns2 originated but has names from root
     */
    /*
     * Element of Package instead of i000 (in m001)
     */
    Method (M203, 1, Serialized)
    {
        Name (I001, 0x00)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        Device (D000)
        {
            Name (PP00, Package (0x03)
            {
                0x11111111,
                0x01,
                0x22223333
            })
        }

        CH03 (__METHOD__, Z156, __LINE__, 0x00, 0x00)
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
                                            \M203.D000.PP00 [0x01] = P000 /* \M203.P000 */
                                        }

                                        Return (0x00)
                                    }

                                    \M203.D000.PP00 [0x01] = 0x80000000
                                    Return ((DerefOf (\M203.D000.PP00 [0x01]) + M008 ()))
                                }

                                \M203.D000.PP00 [0x01] = 0x07000000
                                Return ((DerefOf (\M203.D000.PP00 [0x01]) + M007 ()))
                            }

                            \M203.D000.PP00 [0x01] = 0x00600000
                            Return ((DerefOf (\M203.D000.PP00 [0x01]) + M006 ()))
                        }

                        \M203.D000.PP00 [0x01] = 0x00050000
                        Return ((DerefOf (\M203.D000.PP00 [0x01]) + M005 ()))
                    }

                    \M203.D000.PP00 [0x01] = 0x4000
                    Return ((DerefOf (\M203.D000.PP00 [0x01]) + M004 ()))
                }

                \M203.D000.PP00 [0x01] = 0x0300
                Return ((DerefOf (\M203.D000.PP00 [0x01]) + M003 ()))
            }

            ^D000.PP00 [0x01] = 0x20
            Return ((DerefOf (^D000.PP00 [0x01]) + M002 ()))
        }

        Store ((DerefOf (D000.PP00 [0x01]) + M001 ()), Local0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z156, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        Local0 = DerefOf (D000.PP00 [0x01])
        If ((Local0 != 0x80000000))
        {
            ERR (__METHOD__, Z156, __LINE__, 0x00, 0x00, Local0, 0x80000000)
        }

        CH03 (__METHOD__, Z156, __LINE__, 0x00, 0x00)
    }

    /*
     * Buffer Field instead of i000 (in m001)
     */
    Method (M205, 1, Serialized)
    {
        Name (I001, 0x00)
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        CH03 (__METHOD__, Z156, __LINE__, 0x00, 0x00)
        Device (D000)
        {
            Name (B000, Buffer (0x10){})
            CreateField (B000, 0x05, 0x20, BF00)
        }

        CH03 (__METHOD__, Z156, __LINE__, 0x00, 0x00)
        If (0x00)
        {
            CreateField (D000.B000, 0x05, 0x20, BF00)
        }

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
                                            \M205.D000.BF00 [0x01] = P000 /* \M205.P000 */
                                        }

                                        Return (0x00)
                                    }

                                    \M205.D000.BF00 [0x01] = 0x80000000
                                    Return ((DerefOf (\M205.D000.BF00 [0x01]) + M008 ()))
                                }

                                \M205.D000.BF00 [0x01] = 0x07000000
                                Return ((DerefOf (\M205.D000.BF00 [0x01]) + M007 ()))
                            }

                            \M205.D000.BF00 [0x01] = 0x00600000
                            Return ((DerefOf (\M205.D000.BF00 [0x01]) + M006 ()))
                        }

                        \M205.D000.BF00 [0x01] = 0x00050000
                        Return ((DerefOf (\M205.D000.BF00 [0x01]) + M005 ()))
                    }

                    \M205.D000.BF00 [0x01] = 0x4000
                    Return ((DerefOf (\M205.D000.BF00 [0x01]) + M004 ()))
                }

                \M205.D000.BF00 [0x01] = 0x0300
                Return ((DerefOf (\M205.D000.BF00 [0x01]) + M003 ()))
            }

            ^D000.BF00 [0x01] = 0x20
            Return ((DerefOf (^D000.BF00 [0x01]) + M002 ()))
        }

        Store ((DerefOf (D000.BF00 [0x01]) + M001 ()), Local0)
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, Z156, __LINE__, 0x00, 0x00, Local0, 0x87654321)
        }

        Local0 = DerefOf (D000.BF00 [0x01])
        If ((Local0 != 0x80000000))
        {
            ERR (__METHOD__, Z156, __LINE__, 0x00, 0x00, Local0, 0x80000000)
        }

        CH03 (__METHOD__, Z156, __LINE__, 0x00, 0x00)
    }

    Method (N102, 0, NotSerialized)
    {
        If (0x01)
        {
            SRMT ("m203-0")
            M203 (0x00)
            SRMT ("m203-1")
            If (Y200)
            {
                M203 (0x01)
            }
            Else
            {
                BLCK ()
            }

            SRMT ("m205-0")
            If (Y216)
            {
                M205 (0x00)
            }
            Else
            {
                BLCK ()
            }

            SRMT ("m205-1")
            If ((Y200 && Y216))
            {
                M205 (0x01)
            }
            Else
            {
                BLCK ()
            }
        }
        Else
        {
            SRMT ("m205-0")
            M205 (0x00)
        }
    }
