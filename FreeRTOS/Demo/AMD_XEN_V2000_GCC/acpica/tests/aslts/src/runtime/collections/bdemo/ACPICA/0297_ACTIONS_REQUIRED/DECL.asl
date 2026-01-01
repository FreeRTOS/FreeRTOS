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
     * Bug 297:
     *
     * SUMMARY: After AE_LIMIT the further work of ACPICA mutex framework looks unstable
     */
    /*
     * It is m369 od Synchronization test
     */
    Method (M1E4, 1, Serialized)
    {
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Mutex (MT00, 0x00)
        Mutex (MT10, 0x01)
        Mutex (MT20, 0x02)
        Mutex (MT30, 0x03)
        Mutex (MT40, 0x04)
        Mutex (MT50, 0x05)
        Mutex (MT60, 0x06)
        Mutex (MT70, 0x07)
        Mutex (MT80, 0x08)
        Mutex (MT90, 0x09)
        Mutex (MTA0, 0x0A)
        Mutex (MTB0, 0x0B)
        Mutex (MTC0, 0x0C)
        Mutex (MTD0, 0x0D)
        Mutex (MTE0, 0x0E)
        Mutex (MTF0, 0x0F)
        Mutex (MT01, 0x00)
        Mutex (MT11, 0x01)
        Mutex (MT21, 0x02)
        Mutex (MT31, 0x03)
        Mutex (MT41, 0x04)
        Mutex (MT51, 0x05)
        Mutex (MT61, 0x06)
        Mutex (MT71, 0x07)
        Mutex (MT81, 0x08)
        Mutex (MT91, 0x09)
        Mutex (MTA1, 0x0A)
        Mutex (MTB1, 0x0B)
        Mutex (MTC1, 0x0C)
        Mutex (MTD1, 0x0D)
        Mutex (MTE1, 0x0E)
        If (Arg0)
        {
            /* Should be enough to exceed the maximal available number of mutexes */

            Mutex (M000, 0x0A)
            Mutex (M001, 0x0A)
            Mutex (M002, 0x0A)
            Mutex (M003, 0x0A)
            Mutex (M004, 0x0A)
            Mutex (M005, 0x0A)
            Mutex (M006, 0x0A)
            Mutex (M007, 0x0A)
            Mutex (M008, 0x0A)
            Mutex (M009, 0x0A)
            Mutex (M010, 0x0A)
            Mutex (M011, 0x0A)
            Mutex (M012, 0x0A)
            Mutex (M013, 0x0A)
            Mutex (M014, 0x0A)
            Mutex (M015, 0x0A)
            Mutex (M016, 0x0A)
            Mutex (M017, 0x0A)
            Mutex (M018, 0x0A)
            Mutex (M019, 0x0A)
            Mutex (M020, 0x0A)
            Mutex (M021, 0x0A)
            Mutex (M022, 0x0A)
            Mutex (M023, 0x0A)
            Mutex (M024, 0x0A)
            Mutex (M025, 0x0A)
            Mutex (M026, 0x0A)
            Mutex (M027, 0x0A)
            Mutex (M028, 0x0A)
            Mutex (M029, 0x0A)
            Mutex (M030, 0x0A)
            Mutex (M031, 0x0A)
            Mutex (M032, 0x0A)
            Mutex (M033, 0x0A)
            Mutex (M034, 0x0A)
            Mutex (M035, 0x0A)
            Mutex (M036, 0x0A)
            Mutex (M037, 0x0A)
            Mutex (M038, 0x0A)
            Mutex (M039, 0x0A)
            Mutex (MTB2, 0x0B)
            Mutex (MTB3, 0x0B)
            Mutex (MTB4, 0x0B)
            Mutex (MTB5, 0x0B)
            Mutex (MTB6, 0x0B)
            Mutex (MTB7, 0x0B)
            Mutex (MTB8, 0x0B)
            Mutex (MTB9, 0x0B)
            Mutex (MTBA, 0x0B)
            Mutex (MTBB, 0x0B)
            Mutex (MTBC, 0x0B)
            Mutex (MTBD, 0x0B)
            Mutex (MTBE, 0x0B)
            Mutex (MTBF, 0x0B)
            Mutex (MTC2, 0x0C)
            Mutex (MTC3, 0x0C)
            Mutex (MTC4, 0x0C)
            Mutex (MTC5, 0x0C)
            Mutex (MTC6, 0x0C)
            Mutex (MTC7, 0x0C)
            Mutex (MTC8, 0x0C)
            Mutex (MTC9, 0x0C)
            Mutex (MTCA, 0x0C)
            Mutex (MTCB, 0x0C)
            Mutex (MTCC, 0x0C)
            Mutex (MTCD, 0x0C)
            Mutex (MTCE, 0x0C)
            Mutex (MTCF, 0x0C)
            Mutex (MTD2, 0x0D)
            Mutex (MTD3, 0x0D)
            Mutex (MTD4, 0x0D)
            Mutex (MTD5, 0x0D)
            Mutex (MTD6, 0x0D)
            Mutex (MTD7, 0x0D)
            Mutex (MTD8, 0x0D)
            Mutex (MTD9, 0x0D)
            Mutex (MTDA, 0x0D)
            Mutex (MTDB, 0x0D)
            Mutex (MTDC, 0x0D)
            Mutex (MTDD, 0x0D)
            Mutex (MTDE, 0x0D)
            Mutex (MTDF, 0x0D)
            Mutex (MTE2, 0x0E)
            Mutex (MTE3, 0x0E)
            Mutex (MTE4, 0x0E)
            Mutex (MTE5, 0x0E)
            Mutex (MTE6, 0x0E)
            Mutex (MTE7, 0x0E)
            Mutex (MTE8, 0x0E)
            Mutex (MTE9, 0x0E)
            Mutex (MTEA, 0x0E)
            Mutex (MTEB, 0x0E)
            Mutex (MTEC, 0x0E)
            Mutex (MTED, 0x0E)
            Mutex (MTEE, 0x0E)
            Mutex (MTEF, 0x0E)
            Mutex (MTF1, 0x0F)
            Mutex (MTF2, 0x0F)
            Mutex (MTF3, 0x0F)
            Mutex (MTF4, 0x0F)
            Mutex (MTF5, 0x0F)
            Mutex (MTF6, 0x0F)
            Mutex (MTF7, 0x0F)
            Mutex (MTF8, 0x0F)
            Mutex (MTF9, 0x0F)
            Mutex (MTFA, 0x0F)
            Mutex (MTFB, 0x0F)
            Mutex (MTFC, 0x0F)
            Mutex (MTFD, 0x0F)
            Mutex (MTFE, 0x0F)
            Mutex (MTFF, 0x0F)
        }

        Local0 = Acquire (MT00, 0xFFFF)
        If (Local0)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
        }
        Else
        {
            Local0 = Acquire (MT01, 0xFFFF)
            /* the same level */

            If (Local0)
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
            }
            Else
            {
                Local0 = Acquire (\_GL, 0xFFFF)
                /* GL */

                If (Local0)
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                }
                Else
                {
                    Local0 = Acquire (MT10, 0xFFFF)
                    If (Local0)
                    {
                        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                    }
                    Else
                    {
                        Local0 = Acquire (MT11, 0xFFFF)
                        If (Local0)
                        {
                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                        }
                        Else
                        {
                            Local0 = Acquire (MT20, 0xFFFF)
                            If (Local0)
                            {
                                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                            }
                            Else
                            {
                                Local0 = Acquire (MT21, 0xFFFF)
                                If (Local0)
                                {
                                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                }
                                Else
                                {
                                    Local0 = Acquire (MT30, 0xFFFF)
                                    If (Local0)
                                    {
                                        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                    }
                                    Else
                                    {
                                        Local0 = Acquire (MT31, 0xFFFF)
                                        If (Local0)
                                        {
                                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                        }
                                        Else
                                        {
                                            Local0 = Acquire (MT40, 0xFFFF)
                                            If (Local0)
                                            {
                                                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                            }
                                            Else
                                            {
                                                Local0 = Acquire (MT41, 0xFFFF)
                                                If (Local0)
                                                {
                                                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                }
                                                Else
                                                {
                                                    Local0 = Acquire (MT50, 0xFFFF)
                                                    If (Local0)
                                                    {
                                                        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                    }
                                                    Else
                                                    {
                                                        Local0 = Acquire (MT51, 0xFFFF)
                                                        If (Local0)
                                                        {
                                                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                        }
                                                        Else
                                                        {
                                                            Local0 = Acquire (MT60, 0xFFFF)
                                                            If (Local0)
                                                            {
                                                                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                            }
                                                            Else
                                                            {
                                                                Local0 = Acquire (MT61, 0xFFFF)
                                                                If (Local0)
                                                                {
                                                                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                }
                                                                Else
                                                                {
                                                                    Local0 = Acquire (MT70, 0xFFFF)
                                                                    If (Local0)
                                                                    {
                                                                        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                    }
                                                                    Else
                                                                    {
                                                                        Local0 = Acquire (MT71, 0xFFFF)
                                                                        If (Local0)
                                                                        {
                                                                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                        }
                                                                        Else
                                                                        {
                                                                            Local0 = Acquire (MT80, 0xFFFF)
                                                                            If (Local0)
                                                                            {
                                                                                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                            }
                                                                            Else
                                                                            {
                                                                                Local0 = Acquire (MT81, 0xFFFF)
                                                                                If (Local0)
                                                                                {
                                                                                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                }
                                                                                Else
                                                                                {
                                                                                    Local0 = Acquire (MT90, 0xFFFF)
                                                                                    If (Local0)
                                                                                    {
                                                                                        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                    }
                                                                                    Else
                                                                                    {
                                                                                        Local0 = Acquire (MT91, 0xFFFF)
                                                                                        If (Local0)
                                                                                        {
                                                                                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                        }
                                                                                        Else
                                                                                        {
                                                                                            Local0 = Acquire (MTA0, 0xFFFF)
                                                                                            If (Local0)
                                                                                            {
                                                                                                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                            }
                                                                                            Else
                                                                                            {
                                                                                                Local0 = Acquire (MTA1, 0xFFFF)
                                                                                                If (Local0)
                                                                                                {
                                                                                                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                }
                                                                                                Else
                                                                                                {
                                                                                                    Local0 = Acquire (MTB0, 0xFFFF)
                                                                                                    If (Local0)
                                                                                                    {
                                                                                                        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                    }
                                                                                                    Else
                                                                                                    {
                                                                                                        Local0 = Acquire (MTB1, 0xFFFF)
                                                                                                        If (Local0)
                                                                                                        {
                                                                                                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                        }
                                                                                                        Else
                                                                                                        {
                                                                                                            Local0 = Acquire (MTC0, 0xFFFF)
                                                                                                            If (Local0)
                                                                                                            {
                                                                                                                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                            }
                                                                                                            Else
                                                                                                            {
                                                                                                                Local0 = Acquire (MTC1, 0xFFFF)
                                                                                                                If (Local0)
                                                                                                                {
                                                                                                                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                                }
                                                                                                                Else
                                                                                                                {
                                                                                                                    Local0 = Acquire (MTD0, 0xFFFF)
                                                                                                                    If (Local0)
                                                                                                                    {
                                                                                                                        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                                    }
                                                                                                                    Else
                                                                                                                    {
                                                                                                                        Local0 = Acquire (MTD1, 0xFFFF)
                                                                                                                        If (Local0)
                                                                                                                        {
                                                                                                                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                                        }
                                                                                                                        Else
                                                                                                                        {
                                                                                                                            Local0 = Acquire (MTE0, 0xFFFF)
                                                                                                                            If (Local0)
                                                                                                                            {
                                                                                                                                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                                            }
                                                                                                                            Else
                                                                                                                            {
                                                                                                                                Local0 = Acquire (MTE1, 0xFFFF)
                                                                                                                                If (Local0)
                                                                                                                                {
                                                                                                                                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                                                }
                                                                                                                                Else
                                                                                                                                {
                                                                                                                                    Local0 = Acquire (MTF0, 0xFFFF)
                                                                                                                                    If (Local0)
                                                                                                                                    {
                                                                                                                                        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                                                    }
                                                                                                                                    Else
                                                                                                                                    {
                                                                                                                                        If (Arg0)
                                                                                                                                        {
                                                                                                                                            Local0 = Acquire (MTF1, 0xFFFF)
                                                                                                                                        }
                                                                                                                                        Else
                                                                                                                                        {
                                                                                                                                            Local0 = 0x00
                                                                                                                                        }

                                                                                                                                        If (Local0)
                                                                                                                                        {
                                                                                                                                            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, Local0)
                                                                                                                                        }
                                                                                                                                        Else
                                                                                                                                        {
                                                                                                                                            If (Arg0)
                                                                                                                                            {
                                                                                                                                                Release (MTF1)
                                                                                                                                            }

                                                                                                                                            Release (MTF0)
                                                                                                                                            Release (MTE1)
                                                                                                                                            Release (MTE0)
                                                                                                                                            Release (MTD1)
                                                                                                                                            Release (MTD0)
                                                                                                                                            Release (MTC1)
                                                                                                                                            Release (MTC0)
                                                                                                                                            Release (MTB1)
                                                                                                                                            Release (MTB0)
                                                                                                                                            Release (MTA1)
                                                                                                                                            Release (MTA0)
                                                                                                                                            Release (MT91)
                                                                                                                                            Release (MT90)
                                                                                                                                            Release (MT81)
                                                                                                                                            Release (MT80)
                                                                                                                                            Release (MT71)
                                                                                                                                            Release (MT70)
                                                                                                                                            Release (MT61)
                                                                                                                                            Release (MT60)
                                                                                                                                            Release (MT51)
                                                                                                                                            Release (MT50)
                                                                                                                                            Release (MT41)
                                                                                                                                            Release (MT40)
                                                                                                                                            Release (MT31)
                                                                                                                                            Release (MT30)
                                                                                                                                            Release (MT21)
                                                                                                                                            Release (MT20)
                                                                                                                                            Release (MT11)
                                                                                                                                            Release (MT10)
                                                                                                                                            Release (\_GL)
                                                                                                                                            Release (MT01)
                                                                                                                                            Release (MT00)
                                                                                                                                        }
                                                                                                                                    }
                                                                                                                                }
                                                                                                                            }
                                                                                                                        }
                                                                                                                    }
                                                                                                                }
                                                                                                            }
                                                                                                        }
                                                                                                    }
                                                                                                }
                                                                                            }
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        If (Arg0)
        {
            CH04 (__METHOD__, 0x01, 0x12, 0x00, __LINE__, 0x00, 0x00) /* AE_LIMIT */
        }
        Else
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }
    }

    Method (M1E5, 0, NotSerialized)
    {
        /*
         * This DECLARATION causes hang forever
         *
         * Event(E000)
         */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /*
         * This causes messages (but no exceptions):
         *
         * ACPI Error (utmutex-0421): Mutex [0] is not acquired, cannot release [20061215]
         * ACPI Error (exutils-0250): Could not release AML Interpreter mutex [20061215]
         * ACPI Exception (utmutex-0376): AE_BAD_PARAMETER, Thread B45 could not acquire Mutex [0] [20061215]
         * ACPI Error (exutils-0180): Could not acquire AML Interpreter mutex [20061215]
         */
        Sleep (0x64)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    Method (M1E6, 0, NotSerialized)
    {
        SRMT ("m1e4-1")
        M1E4 (0x01)
        SRMT ("m1e4-0")
        M1E4 (0x00)
        SRMT ("m1e5")
        M1E5 ()
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /*
         * m1e5 shows appearance of bug but doesn't cause exceptions
         * (so it is not detected automatically), so actions are required
         * for to see result of this bug until it is actually fixed. Then
         * (when fixed) uncomment Event(E000) in m1e5 and remove this error
         * report below (or try to find how to detect this situation
         * automatically now (for not fixed yet)):
         */
        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
    }
