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
     * Bug 300:
     *
     * SUMMARY: Recursive calls to methods with the internal declarations (and Switches) should be provided
     */
    Method (M1E9, 0, NotSerialized)
    {
        Method (M000, 0, Serialized)
        {
            Name (I000, 0x00)
            Name (MAX0, 0x0A)
            I000 = MAX0 /* \M1E9.M000.MAX0 */
            Method (M100, 1, Serialized)
            {
                /*
                 * Method m100 contains internal declarations and Switch and
                 * is invoked recursively but no exceptions should be there,
                 * and the proper execution provided.
                 */
                Name (II00, 0x00)
                Name (II01, 0x00)
                Name (II02, 0x00)
                Name (II03, 0x00)
                II00 = Arg0
                II01 = 0x00
                II02 = 0x00
                II03 = 0x00
                Local5 = Arg0
                Concatenate ("================== i000: ", I000, Debug)
                I000--
                Switch (I000)
                {
                    Case (0x00)
                    {
                        Debug = "No more recursive calls"
                    }
                    Default
                    {
                        M100 (I000)
                    }

                }

                If ((Arg0 != II00))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, II00)
                }

                If ((Arg0 != Local5))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, Local5)
                }
            }

            M100 (0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        M000 ()
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
