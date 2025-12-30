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
     * Bug 186:
     *
     * SUMMARY: The predicate value of If/While operations is implicitly returned in slack mode
     */
    Method (MF6D, 0, Serialized)
    {
        Name (FL00, 0x00)
        Name (I000, 0xABCD0000)
        Name (I001, 0xABCD0001)
        Method (M000, 0, Serialized)
        {
            Switch (ToInteger (I001 = 0xABCD0000))
            {
                Case (0x00)
                {
                    If (FL00)
                    {
                        Return (0x00)
                    }
                }

            }
        }

        Method (M001, 0, NotSerialized)
        {
            If (I001 = 0xABCD0001)
            {
                If (FL00)
                {
                    Return (0x00)
                }
            }
        }

        Method (M002, 0, NotSerialized)
        {
            While (I001 = 0xABCD0002)
            {
                If (FL00)
                {
                    Return (0x00)
                }

                Break
            }
        }

        /* m000 */

        I000 = 0xDDDD0000
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        I000 = M000 ()
        If (SLCK)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            /*y901: Predicate generates Implicit Return since ACPICA release 20080926	 */

            If (Y901)
            {
                Local0 = 0x00
            }
            Else
            {
                Local0 = 0xABCD0000
            }

            If ((I000 != Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, Local0)
            }
        }
        Else
        {
            CH07 ("", 0x00, 0xFF, 0x00, 0x03, 0x00, 0x00)
        }

        /* m001 */

        I000 = 0xDDDD0001
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        I000 = M001 ()
        If (SLCK)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            /*y901: Predicate generates Implicit Return since ACPICA release 20080926	 */

            If (Y901)
            {
                Local0 = 0x00
            }
            Else
            {
                Local0 = 0xABCD0001
            }

            If ((I000 != Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, Local0)
            }
        }
        Else
        {
            CH07 ("", 0x00, 0xFF, 0x00, 0x07, 0x00, 0x00)
        }

        /* m002 */

        I000 = 0xDDDD0002
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        I000 = M001 ()
        If (SLCK)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            /*y901: Predicate generates Implicit Return since ACPICA release 20080926	 */

            If (Y901)
            {
                Local0 = 0x00
            }
            Else
            {
                Local0 = 0xABCD0002
            }

            If ((I000 != Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, Local0)
            }
        }
        Else
        {
            CH07 ("", 0x00, 0xFF, 0x00, 0x0B, 0x00, 0x00)
        }
    }
