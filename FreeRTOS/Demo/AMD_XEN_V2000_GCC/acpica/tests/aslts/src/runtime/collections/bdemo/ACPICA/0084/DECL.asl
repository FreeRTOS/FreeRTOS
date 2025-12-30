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
     * Bug 0084:
     *
     * SUMMARY: Failed to interpret AML code alternated with Method declarations
     */
    Method (ME35, 1, NotSerialized)
    {
        Method (M001, 0, NotSerialized)
        {
            Return (0x00)
        }

        Debug = "Before m001 run"
        If (Arg0)
        {
            Debug = "m001 started"
            M001 ()
            Debug = "m001 finished"
        }

        Debug = "After m001 run"
        Method (M002, 0, NotSerialized)
        {
            Return (0x00)
        }

        Method (M003, 0, NotSerialized)
        {
            Return (0x00)
        }

        Debug = "Before return from me35"
        Return (0x00)
    }

    Method (ME36, 0, NotSerialized)
    {
        Debug = "Before me35(0) run"
        ME35 (0x00)
        Debug = "After me35(0) completion"
        Debug = "Before me35(1) run"
        ME35 (0x01)
        Debug = "After me35(1) completion"
    }

    Method (M803, 0, Serialized)
    {
        Name (I000, 0xABCD0000)
        Method (M000, 0, NotSerialized)
        {
            If ((I000 != 0xABCD0000))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0000)
            }

            I000 = 0xABCD0001
            Return (0xABCD0002)
        }

        M000 ()
        Method (M001, 0, NotSerialized)
        {
            If ((I000 != 0xABCD0001))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0001)
            }

            I000 = 0xABCD0003
            Return (0xABCD0004)
        }

        M001 ()
        Method (M002, 0, NotSerialized)
        {
            If ((I000 != 0xABCD0003))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0003)
            }

            I000 = 0xABCD0005
            Return (0xABCD0006)
        }

        M002 ()
        Method (M003, 0, NotSerialized)
        {
            If ((I000 != 0xABCD0005))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0005)
            }

            I000 = 0xABCD0007
            Return (0xABCD0008)
        }

        M003 ()
    }

    Method (M804, 0, Serialized)
    {
        Name (I000, 0xABCD0000)
        Method (M000, 0, NotSerialized)
        {
            Method (M000, 0, NotSerialized)
            {
                If ((I000 != 0xABCD0000))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0000)
                }

                I000 = 0xABCD0001
                Return (0xABCD0002)
            }

            M000 ()
            Method (M001, 0, NotSerialized)
            {
                If ((I000 != 0xABCD0001))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0001)
                }

                I000 = 0xABCD0003
                Return (0xABCD0004)
            }

            M001 ()
            Method (M002, 0, NotSerialized)
            {
                If ((I000 != 0xABCD0003))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0003)
                }

                I000 = 0xABCD0005
                Return (0xABCD0006)
            }

            M002 ()
            Method (M003, 0, NotSerialized)
            {
                If ((I000 != 0xABCD0005))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0005)
                }

                I000 = 0xABCD0007
                Return (0xABCD0008)
            }

            M003 ()
        }

        M000 ()
        Method (M001, 0, NotSerialized)
        {
            Method (M000, 0, NotSerialized)
            {
                If ((I000 != 0xABCD0007))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0007)
                }

                I000 = 0xABCD0008
                Return (0xABCD0009)
            }

            M000 ()
            Method (M001, 0, NotSerialized)
            {
                If ((I000 != 0xABCD0008))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0008)
                }

                I000 = 0xABCD000A
                Return (0xABCD000B)
            }

            M001 ()
            Method (M002, 0, NotSerialized)
            {
                If ((I000 != 0xABCD000A))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD000A)
                }

                I000 = 0xABCD000C
                Return (0xABCD000D)
            }

            M002 ()
            Method (M003, 0, NotSerialized)
            {
                If ((I000 != 0xABCD000C))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD000C)
                }

                I000 = 0xABCD000E
                Return (0xABCD000F)
            }

            M003 ()
        }

        M001 ()
        Method (M002, 0, NotSerialized)
        {
            Method (M000, 0, NotSerialized)
            {
                If ((I000 != 0xABCD000E))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD000E)
                }

                I000 = 0xABCD0010
                Return (0xABCD0011)
            }

            M000 ()
            Method (M001, 0, NotSerialized)
            {
                If ((I000 != 0xABCD0010))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0010)
                }

                I000 = 0xABCD0012
                Return (0xABCD0013)
            }

            M001 ()
            Method (M002, 0, NotSerialized)
            {
                If ((I000 != 0xABCD0012))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0012)
                }

                I000 = 0xABCD0014
                Return (0xABCD0015)
            }

            M002 ()
            Method (M003, 0, NotSerialized)
            {
                If ((I000 != 0xABCD0014))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0014)
                }

                I000 = 0xABCD0016
                Return (0xABCD0017)
            }

            M003 ()
        }

        M002 ()
        If ((I000 != 0xABCD0016))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xABCD0016)
        }
    }
