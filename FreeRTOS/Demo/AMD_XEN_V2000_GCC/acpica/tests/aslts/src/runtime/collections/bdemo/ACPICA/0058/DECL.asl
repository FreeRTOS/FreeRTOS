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
     * Bug 0058:
     *
     * SUMMARY: Concatenate of two Integers may operates in 32-bit mode as in 64-bit mode
     *
     * These are three appearances probably
     * of one the same differently looking bug.
     * Concatenate Operator seems to have
     * indirect effect in all those cases.
     */
    Method (MDF5, 1, NotSerialized)
    {
        Debug = "Run mdf5:"
        If (Arg0)
        {
            Debug = "===================== 0:"
            Local0 = Concatenate (0x01, 0x02)
            If (F64)
            {
                If ((Local0 != Buffer (0x10)
                            {
                                /* 0000 */  0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                                /* 0008 */  0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
                            }))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x10)
                        {
                            /* 0000 */  0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                            /* 0008 */  0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
                        })
                }
            }
            ElseIf ((Local0 != Buffer (0x08)
                        {
                             0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00   // ........
                        }))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x08)
                    {
                         0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00   // ........
                    })
            }
        }
        Else
        {
            Debug = "===================== 1:"
        }
    }

    Method (MDF6, 1, NotSerialized)
    {
        Debug = "Run mdf6:"
        If (Arg0)
        {
            Debug = "===================== 2:"
            Local0 = Concatenate (0x1234, 0x7890)
            If (F64)
            {
                If ((Local0 != Buffer (0x10)
                            {
                                /* 0000 */  0x34, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // 4.......
                                /* 0008 */  0x90, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // .x......
                            }))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x10)
                        {
                            /* 0000 */  0x34, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // 4.......
                            /* 0008 */  0x90, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // .x......
                        })
                }
            }
            ElseIf ((Local0 != Buffer (0x08)
                        {
                             0x34, 0x12, 0x00, 0x00, 0x90, 0x78, 0x00, 0x00   // 4....x..
                        }))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x08)
                    {
                         0x34, 0x12, 0x00, 0x00, 0x90, 0x78, 0x00, 0x00   // 4....x..
                    })
            }
        }
        Else
        {
            Debug = "===================== 3:"
        }
    }

    Method (MDF7, 0, NotSerialized)
    {
        Debug = "Run mdf7:"
        Local0 = Concatenate (0x01, 0x02)
        If (F64)
        {
            If ((Local0 != Buffer (0x10)
                        {
                            /* 0000 */  0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                            /* 0008 */  0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
                        }))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x10)
                    {
                        /* 0000 */  0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                        /* 0008 */  0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
                    })
            }
        }
        ElseIf ((Local0 != Buffer (0x08)
                    {
                         0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00   // ........
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x08)
                {
                     0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00   // ........
                })
        }

        Debug = Local0
    }

    Method (MDF8, 0, NotSerialized)
    {
        MDF5 (0x00)
        MDF6 (0x00)
        MDF7 ()
        MDF5 (0x01)
        MDF6 (0x01)
    }
