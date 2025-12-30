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
     * Bug 269:
     *
     * SUMMARY: The sequence of evaluating Named object operands passed to method is violated
     */
    Method (M022, 0, Serialized)
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
        I001 = 0x00
        Method (MADD, 2, NotSerialized)
        {
            Local0 = (Arg0 + Arg1)
            Return (Local0)
        }

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
                                            CopyObject (P000, I000) /* \M022.I000 */
                                        }

                                        Return (0x00)
                                    }

                                    I000 = 0x80000000
                                    Return (MADD (I000, M008 ()))
                                }

                                I000 = 0x07000000
                                Return (MADD (I000, M007 ()))
                            }

                            I000 = 0x00600000
                            Return (MADD (I000, M006 ()))
                        }

                        I000 = 0x00050000
                        Return (MADD (I000, M005 ()))
                    }

                    I000 = 0x4000
                    Return (MADD (I000, M004 ()))
                }

                I000 = 0x0300
                Return (MADD (I000, M003 ()))
            }

            I000 = 0x20
            Return (MADD (I000, M002 ()))
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = MADD (I000, M001 ())
        If ((Local0 != 0x87654321))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, C00E)
        }

        If ((I000 != 0x80000000))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, C00E)
        }

        Debug = "Result:"
        Debug = Local0
        Debug = "i000:"
        Debug = I000 /* \M022.I000 */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
