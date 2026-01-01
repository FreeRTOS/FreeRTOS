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
     * Bug 0038:
     *
     * SUMMARY: LGreater passed with Integer and String works incorrectly in 32-bit mode
     */
    Method (MDCE, 0, Serialized)
    {
        Local7 = 0x00
        /* Show that (in 32-bit mode) "FdeAcb0132547698" passed to Name */
        /* operator is correctly implicitly converted to Integer 0xfdeacb01 */
        Name (N000, 0x00)
        N000 = "FdeAcb0132547698"
        Debug = N000 /* \MDCE.N000 */
        If ((N000 != 0xFDEACB01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, N000, 0xFDEACB01)
        }

        /* Show that LGreater operator indicates correctly */
        /* that 0x42345678 is greater than 0x32547698 */
        If ((0x42345678 > 0x32547698))
        {
            Local7 = 0x01
        }
        Else
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x42345678, 0x32547698)
        }

        /* Show that (in 32-bit mode) "FdeAcb0132547698" passed to Name operator */
        /* is implicitly converted to some Integer (0xfdeacb01) which is actually */
        /* treated by LGreater as being greater than 0x42345678 */
        If ((N000 > 0x42345678))
        {
            Local7 = 0x01
        }
        Else
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, N000, 0x42345678)
        }

        /* Show that, nevertheless, (in 32-bit mode) "FdeAcb01Fdeacb03" passed */
        /* to LGreater operator is implicitly converted to some unexpected value */
        /* which is NOT equal to the expected correct 0xfdeacb01 value. */
        If ((0xFDEACB02 > "FdeAcb01Fdeacb03"))
        {
            Local7 = 0x01
        }
        Else
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0xFDEACB02, "FdeAcb01Fdeacb03")
        }

        Return (Local7)
    }
