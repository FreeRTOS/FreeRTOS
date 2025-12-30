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
     * Bug 301:
     *
     * SUMMARY: Recursive calls to methods with the internal declarations (and Switches) causes AE_AML_INTERNAL and crash
     */
    Method (M1EA, 0, NotSerialized)
    {
        Method (M19C, 0, Serialized)
        {
            Name (RPT0, 0x00)
            /*
             * Total number of calls of the same Recursively Called method (RCM),
             * the first call is counted there too.
             */
            Name (N000, 0x03)
            Name (CNT0, 0x00) /* how many methods are in progress simultaneously */
            Name (MAX0, 0x00) /* maximal number of methods being in progress simultaneously */
            /*
             * Open method execution
             *
             * arg0 - ID of method (1,2,3...)
             * arg1 - the message to be reported
             */
            Method (M800, 2, NotSerialized)
            {
                If (RPT0)
                {
                    Debug = Arg1
                }

                CNT0++
                If ((CNT0 > MAX0))
                {
                    MAX0 = CNT0 /* \M1EA.M19C.CNT0 */
                }
            }

            /*
             * Close method execution
             *
             * arg0 - ID of method (1,2,3...)
             */
            Method (M801, 1, NotSerialized)
            {
                CNT0--
            }

            /*
             * Arguments of methods:
             * arg0 - 0 - the first call, otherwise - recursive calls
             */
            Name (C000, 0x03)
            Method (M100, 0, Serialized)
            {
                Name (C100, 0x03)
                Method (M200, 0, Serialized)
                {
                    Name (C200, 0x03)
                    Method (M300, 0, Serialized)
                    {
                        Name (C300, 0x03)
                        Method (M400, 0, NotSerialized)
                        {
                            M800 (0x04, "m400")
                            C300--
                            If ((C300 == 0x00))
                            {
                                M300 ()
                            }
                            Else
                            {
                                M400 ()
                            }

                            M801 (0x04)
                        }

                        M800 (0x03, "m300")
                        C200--
                        If ((C200 == 0x00))
                        {
                            M200 ()
                        }
                        Else
                        {
                            M400 ()
                        }

                        M801 (0x03)
                    }

                    M800 (0x02, "m200")
                    C100--
                    If ((C100 == 0x00))
                    {
                        M100 ()
                    }
                    Else
                    {
                        M300 ()
                    }

                    M801 (0x02)
                }

                M800 (0x01, "m100")
                C000--
                If ((C000 == 0x00)){                /* m000() */
                }
                Else
                {
                    M200 ()
                }

                M801 (0x01)
            }

            M100 ()
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        M19C ()
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
