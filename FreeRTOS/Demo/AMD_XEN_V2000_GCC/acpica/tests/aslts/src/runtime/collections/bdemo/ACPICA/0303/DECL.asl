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
     * Bug 303:
     *
     * SUMMARY: Name operation performed from inside the If operation doesn't work for the full-path ObjectName
     */
    Method (M1EC, 0, NotSerialized)
    {
        /* The usual case, it works */

        Method (M000, 0, NotSerialized)
        {
            Method (M100, 1, Serialized, 3)
            {
                Name (\I4Z0, 0xABCD0000)
                If ((I4Z0 != 0xABCD0000))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I4Z0, 0xABCD0000)
                }

                If ((\I4Z0 != 0xABCD0000))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, \I4Z0, 0xABCD0000)
                }

                M101 ()
            }

            Method (M101, 0, NotSerialized)
            {
                If ((I4Z0 != 0xABCD0000))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I4Z0, 0xABCD0000)
                }

                If ((\I4Z0 != 0xABCD0000))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, \I4Z0, 0xABCD0000)
                }
            }

            Debug = "---------------- The case 1 started:"
            M100 (0x00)
            Debug = "---------------- Completed."
        }

        /* The case where Name(\i4z1, 0xabcd0000) is performed from If, it doesn't work. */

        Method (M001, 0, NotSerialized)
        {
            Method (M100, 1, Serialized)
            {
                If (!Arg0)
                {
                    Name (\I4Z1, 0xABCD0000)
                }

                If ((I4Z1 != 0xABCD0000))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I4Z1, 0xABCD0000)
                }

                If ((\I4Z1 != 0xABCD0000))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, \I4Z1, 0xABCD0000)
                }

                M101 ()
            }

            Method (M101, 0, NotSerialized)
            {
                If ((I4Z1 != 0xABCD0000))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I4Z1, 0xABCD0000)
                }

                If ((\I4Z1 != 0xABCD0000))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, \I4Z1, 0xABCD0000)
                }
            }

            Debug = "---------------- The case 2 started:"
            M100 (0x00)
            Debug = "---------------- Completed"
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("m1ec-m000")
        M000 ()
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("m1ec-m001")
        M001 ()
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
