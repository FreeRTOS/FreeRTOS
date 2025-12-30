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
     * Bug 263:
     *
     * SUMMARY: The sequence of evaluating operands of expression with the named objects is violated
     */
    Method (M026, 0, NotSerialized)
    {
        Method (MM00, 0, Serialized)
        {
            Name (I000, 0x01)
            Method (M001, 0, NotSerialized)
            {
                I000 = 0x50000000
                Return (I000) /* \M026.MM00.I000 */
            }

            Store ((I000 + M001 ()), Local0)
            Debug = Local0
            Debug = I000 /* \M026.MM00.I000 */
            If ((Local0 != 0x50000001))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x50000001)
            }

            If ((I000 != 0x50000000))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0x50000000)
            }
        }

        Method (MM01, 1, Serialized)
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
                                                CopyObject (P000, I000) /* \M026.MM01.I000 */
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
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x87654321)
            }

            If ((I000 != 0x80000000))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0x80000000)
            }
        }

        MM00 ()
        MM01 (0x00)
    }
