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
     * Bug 268:
     *
     * SUMMARY: The manner parameters are passed to method in ACPICA contradicts to MS
     */
    Method (M023, 0, Serialized)
    {
        Name (I000, 0xABCD0000)
        Method (MM00, 1, NotSerialized)
        {
            Debug = "The view from inside method MM00:"
            Debug = "--------- i000 before re-writing i000:"
            Debug = I000 /* \M023.I000 */
            Debug = "--------- Arg0 before re-writing i000:"
            Debug = Arg0
            I000 = 0x11223344
            Debug = "--------- Arg0 after re-writing i000:"
            Debug = Arg0
            Debug = "--------- i000 after re-writing i000:"
            Debug = I000 /* \M023.I000 */
            If ((Arg0 != 0xABCD0000))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, 0xABCD0000)
            }
        }

        Debug = "m000: test 0 (Integer passed to method)"
        Debug = "========= i000 from m000 before re-writing i000:"
        Debug = I000 /* \M023.I000 */
        MM00 (I000)
        Debug = "========= i000 from m000 after re-writing i000:"
        Debug = I000 /* \M023.I000 */
        If ((I000 != 0x11223344))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0x11223344)
        }
    }
