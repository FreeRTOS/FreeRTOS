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
     * Bug 265:
     *
     * SUMMARY: The second run to method calculating the IRef-to-String expression is evaluated incorrectly
     */
    Method (M024, 0, NotSerialized)
    {
        Method (MM00, 0, Serialized)
        {
            Name (I001, 0x00)
            Name (S000, "q\x01ertyuiop")
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
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x24)
            }

            Local0 = DerefOf (S000 [0x01])
            Local1 = 0x08
            If ((Local0 != Local1))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Local1)
            }
        }

        Method (MM01, 0, NotSerialized)
        {
            Debug = "The first run to mm00:"
            MM00 ()
            Debug = "The second run to mm00:"
            MM00 ()
            Debug = "The third run to mm00:"
            MM00 ()
        }

        MM01 ()
    }
