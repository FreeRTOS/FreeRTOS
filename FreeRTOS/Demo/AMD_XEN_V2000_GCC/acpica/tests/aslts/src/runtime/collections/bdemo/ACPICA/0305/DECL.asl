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
     * Bug 305:
     *
     * SUMMARY: Not owner recursive method call releases global object created by method
     */
    Method (MFF2, 0, NotSerialized)
    {
        Method (M000, 1, Serialized, 3)
        {
            If (!Arg0)
            {
                Scope (\_SB)
                {
                    Name (I2Z6, 0xABCD0000)
                }
            }

            If (!Arg0)
            {
                M000 (0x01)
            }

            Debug = "==================== 0"
            Debug = Arg0
            Local0 = (\_SB.I2Z6 + 0x03)
            Debug = "==================== 1"
            If ((Local0 != 0xABCD0003))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCD0003)
            }
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        M000 (0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
