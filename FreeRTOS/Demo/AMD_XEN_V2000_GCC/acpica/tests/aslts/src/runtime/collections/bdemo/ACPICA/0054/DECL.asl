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
     * Bug 0054:
     *
     * SUMMARY: All ASL Operators causes exceptions on two immediately passed Buffers
     *
     * All the ASL Operators which deal with
     * at least two Buffer type objects cause
     * unexpected exceptions in cases when both
     * Buffer type objects are passed immediately.
     */
    Method (MDDF, 0, Serialized)
    {
        Name (B000, Buffer (0x02)
        {
             0x79, 0x00                                       // y.
        })
        Name (B001, Buffer (0x02)
        {
             0x79, 0x00                                       // y.
        })
        Local0 = ConcatenateResTemplate (B000, B001)
        If ((Local0 != Buffer (0x02)
                    {
                         0x79, 0x00                                       // y.
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                })
        }
    }

    /* ConcatenateResTemplate */

    Method (MDE0, 0, Serialized)
    {
        Name (B000, Buffer (0x02)
        {
             0x79, 0x00                                       // y.
        })
        Local0 = ConcatenateResTemplate (B000, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                })
        If ((Local0 != Buffer (0x02)
                    {
                         0x79, 0x00                                       // y.
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                })
        }

        Local0 = ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, B000)
        If ((Local0 != Buffer (0x02)
                    {
                         0x79, 0x00                                       // y.
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                })
        }
    }

    Method (MDE1, 0, NotSerialized)
    {
        Local0 = ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                })
        If ((Local0 != Buffer (0x02)
                    {
                         0x79, 0x00                                       // y.
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                })
        }
    }

    /* LEqual */

    Method (MDE2, 0, Serialized)
    {
        Name (B000, Buffer (0x01)
        {
             0x79                                             // y
        })
        Local0 = (B000 == Buffer (0x01)
                {
                     0x79                                             // y
                })
        If ((Local0 != Ones))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Ones)
        }

        Local0 = (Buffer (0x01)
                {
                     0x79                                             // y
                } == B000)
        If ((Local0 != Ones))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Ones)
        }
    }

    Method (MDE3, 0, NotSerialized)
    {
        Local0 = (Buffer (0x01)
                {
                     0x79                                             // y
                } == Buffer (0x01)
                {
                     0x79                                             // y
                })
        If ((Local0 != Ones))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Ones)
        }
    }

    /* LGreater */

    Method (MDE4, 0, Serialized)
    {
        Name (B000, Buffer (0x01)
        {
             0x79                                             // y
        })
        Local0 = (B000 > Buffer (0x01)
                {
                     0x79                                             // y
                })
        If ((Local0 != Zero))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Zero)
        }

        Local0 = (Buffer (0x01)
                {
                     0x79                                             // y
                } > B000)
        If ((Local0 != Zero))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Zero)
        }
    }

    Method (MDE5, 0, NotSerialized)
    {
        Local0 = (Buffer (0x01)
                {
                     0x79                                             // y
                } > Buffer (0x01)
                {
                     0x79                                             // y
                })
        If ((Local0 != Zero))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Zero)
        }
    }

    /* .......... */
    /* Concatenate */
    Method (MDE6, 0, Serialized)
    {
        Name (B000, Buffer (0x01)
        {
             0x79                                             // y
        })
        Local0 = Concatenate (B000, Buffer (0x01)
                {
                     0x79                                             // y
                })
        If ((Local0 != Buffer (0x02)
                    {
                         0x79, 0x79                                       // yy
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x02)
                {
                     0x79, 0x79                                       // yy
                })
        }

        Local0 = Concatenate (Buffer (0x01)
                {
                     0x79                                             // y
                }, B000)
        If ((Local0 != Buffer (0x02)
                    {
                         0x79, 0x79                                       // yy
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x02)
                {
                     0x79, 0x79                                       // yy
                })
        }
    }

    Method (MDE7, 0, NotSerialized)
    {
        Local0 = Concatenate (Buffer (0x01)
                {
                     0x79                                             // y
                }, Buffer (0x01)
                {
                     0x79                                             // y
                })
        If ((Local0 != Buffer (0x02)
                    {
                         0x79, 0x79                                       // yy
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Buffer (0x02)
                {
                     0x79, 0x79                                       // yy
                })
        }
    }

    /* Add */

    Method (MDE8, 0, Serialized)
    {
        Name (B000, Buffer (0x01)
        {
             0x79                                             // y
        })
        Local0 = (B000 + Buffer (0x01)
            {
                 0x79                                             // y
            })
        If ((Local0 != 0xF2))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xF2)
        }

        Local0 = (Buffer (0x01)
            {
                 0x79                                             // y
            } + B000) /* \MDE8.B000 */
        If ((Local0 != 0xF2))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xF2)
        }
    }

    Method (MDE9, 0, NotSerialized)
    {
        Local0 = (Buffer (0x01)
            {
                 0x79                                             // y
            } + Buffer (0x01)
            {
                 0x79                                             // y
            })
        If ((Local0 != 0xF2))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xF2)
        }
    }

    /* .......... */

    Method (MDEA, 0, NotSerialized)
    {
        MDDF ()
        /* ConcatenateResTemplate */

        MDE0 ()
        MDE1 ()
        /* LEqual */

        MDE2 ()
        MDE3 ()
        /* LGreater */

        MDE4 ()
        MDE5 ()
        /* Concatenate */

        MDE6 ()
        MDE7 ()
        /* Add */

        MDE8 ()
        MDE9 ()
    }
