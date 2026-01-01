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
     * Bug 166:
     *
     * SUMMARY: Releasing memory of the inside Method scopes surrounding Return operation is needed
     *
     * Only, to initiate Return operation from the inside
     * Method scopes surrounding that Return operation (If,
     * While, Switch, etc..)
     */
    Method (MF4F, 0, NotSerialized)
    {
    }

    Method (MF50, 0, NotSerialized)
    {
        If (0xABCD0001)
        {
            Return (0xABCD0010)
        }
    }

    Method (MF51, 0, NotSerialized)
    {
        If (0xABCD0000)
        {
            If (0xABCD0001)
            {
                Return (0xABCD0010)
            }
        }
    }

    Method (MF52, 0, NotSerialized)
    {
        While (0xABCD0000)
        {
            Return (0xABCD0020)
        }
    }

    Method (MF53, 0, NotSerialized)
    {
        MF4F ()
        MF50 ()
        MF51 ()
        MF52 ()
        While (0xABCD0000)
        {
            MF4F ()
            MF50 ()
            MF51 ()
            MF52 ()
            If (0xABCD0001)
            {
                While (0xABCD0002)
                {
                    If (0xABCD0003)
                    {
                        While (0xABCD0004)
                        {
                            If (0xABCD0005)
                            {
                                While (0xABCD0006)
                                {
                                    If (0xABCD0007)
                                    {
                                        MF4F ()
                                        MF50 ()
                                        MF51 ()
                                        MF52 ()
                                        While (0xABCD0008)
                                        {
                                            If (0xABCD0009)
                                            {
                                                While (0xABCD000A)
                                                {
                                                    If (0xABCD000B)
                                                    {
                                                        While (0xABCD000C)
                                                        {
                                                            If (0xABCD000D)
                                                            {
                                                                While (0xABCD000E)
                                                                {
                                                                    If (0xABCD000F)
                                                                    {
                                                                        If (0x00)
                                                                        {
                                                                            Debug = "Impossible 0"
                                                                        }
                                                                        ElseIf (0xABCD0010)
                                                                        {
                                                                            Return (0xABCD0030)
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }

                                                        MF4F ()
                                                        MF50 ()
                                                        MF51 ()
                                                        MF52 ()
                                                    }
                                                }
                                            }
                                        }

                                        MF4F ()
                                        MF50 ()
                                        MF51 ()
                                        MF52 ()
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
