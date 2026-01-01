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
    Name (Z179, 0xB3)
    /*
     !!!!!!!!!!!!!!!!    It is in progress, just started !!!!!!!!!!!!!!!!
     */
    /*
     * Check full path Name declarations performed from inside Methods
     */
    Method (FP00, 0, Serialized)
    {
        Method (M000, 0, Serialized)
        {
            Name (\I4Z0, 0xABCD0000)
            If ((I4Z0 != 0xABCD0000))
            {
                ERR (__METHOD__, Z179, __LINE__, 0x00, 0x00, I4Z0, 0xABCD0000)
            }

            If ((\I4Z0 != 0xABCD0000))
            {
                ERR (__METHOD__, Z179, __LINE__, 0x00, 0x00, \I4Z0, 0xABCD0000)
            }

            M001 ()
        }

        Method (M001, 0, NotSerialized)
        {
            If ((I4Z0 != 0xABCD0000))
            {
                ERR (__METHOD__, Z179, __LINE__, 0x00, 0x00, I4Z0, 0xABCD0000)
            }

            If ((\I4Z0 != 0xABCD0000))
            {
                ERR (__METHOD__, Z179, __LINE__, 0x00, 0x00, \I4Z0, 0xABCD0000)
            }
        }

        CH03 (__METHOD__, Z179, __LINE__, 0x00, 0x00)
        M000 ()
        CH03 (__METHOD__, Z179, __LINE__, 0x00, 0x00)
    }

    Method (FP01, 0, Serialized)
    {
        Method (M000, 1, Serialized)
        {
            If (!Arg0)
            {
                Name (\I4Z1, 0xABCD0000)
            }

            If ((I4Z1 != 0xABCD0000))
            {
                ERR (__METHOD__, Z179, __LINE__, 0x00, 0x00, I4Z1, 0xABCD0000)
            }

            If ((\I4Z1 != 0xABCD0000))
            {
                ERR (__METHOD__, Z179, __LINE__, 0x00, 0x00, \I4Z1, 0xABCD0000)
            }

            M001 ()
        }

        Method (M001, 0, NotSerialized)
        {
            If ((I4Z1 != 0xABCD0000))
            {
                ERR (__METHOD__, Z179, __LINE__, 0x00, 0x00, I4Z1, 0xABCD0000)
            }

            If ((\I4Z1 != 0xABCD0000))
            {
                ERR (__METHOD__, Z179, __LINE__, 0x00, 0x00, \I4Z1, 0xABCD0000)
            }
        }

        CH03 (__METHOD__, Z179, __LINE__, 0x00, 0x00)
        M000 (0x00)
        CH03 (__METHOD__, Z179, __LINE__, 0x00, 0x00)
    }

    Method (FPD0, 0, NotSerialized)
    {
        SRMT ("fp00")
        FP00 ()
        SRMT ("fp01")
        FP01 ()
    }
