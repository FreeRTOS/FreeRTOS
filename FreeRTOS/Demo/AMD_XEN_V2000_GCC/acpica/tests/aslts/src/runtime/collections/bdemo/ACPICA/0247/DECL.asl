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
     * Bug 247:
     *
     * SUMMARY: ASL compiler incorrectly implements Break within Switch
     */
    Method (M17C, 0, Serialized)
    {
        Name (ERRN, 0x00)
        Method (M000, 3, Serialized)
        {
            Name (CH10, 0x00)
            Name (CH11, 0x00)
            Name (CH20, 0x00)
            Name (CH21, 0x00)
            Debug = Arg0
            Local0 = 0x02
            While (Local0)
            {
                If (CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00))
                {
                    Return (Zero)
                }

                ERRN++
                Switch (Local0)
                {
                    Case (0x01)
                    {
                        If (Arg1)
                        {
                            CH10 = 0x01
                            Break
                        }

                        CH11 = 0x01
                    }
                    Case (0x02)
                    {
                        If (Arg2)
                        {
                            CH20 = 0x01
                            Break
                        }

                        CH21 = 0x01
                    }

                }

                If (CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00))
                {
                    Return (Zero)
                }

                ERRN++
                Local0--
            }

            If ((CH10 != Arg1))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, CH10, Arg1)
            }

            ERRN++
            If ((CH11 == Arg1))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, CH11, Arg1)
            }

            ERRN++
            If ((CH20 != Arg2))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, CH20, Arg2)
            }

            ERRN++
            If ((CH21 == Arg2))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, CH21, Arg2)
            }

            ERRN++
        }

        M000 ("No Breaks", 0x00, 0x00)
        M000 ("Break 2", 0x00, 0x01)
        M000 ("Break 1", 0x01, 0x00)
        M000 ("2 Breaks", 0x01, 0x01)
    }
