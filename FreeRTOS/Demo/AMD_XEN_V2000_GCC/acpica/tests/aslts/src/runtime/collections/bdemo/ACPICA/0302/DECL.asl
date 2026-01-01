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
     * Bug 302:
     *
     * SUMMARY: Scope operation doesn't work for the root node Location
     */
    Method (M1EB, 0, NotSerialized)
    {
        Method (M100, 0, NotSerialized)
        {
            Method (M200, 0, Serialized)
            {
                Debug = "---------------- Before <Scope(\\_SB)>"
                Scope (\_SB)
                {
                    Name (I2Z7, 0xABCD0007)
                }

                Debug = "---------------- After Scope(\\_SB)"
                M201 ()
                Debug = "---------------- Completed."
            }

            Method (M201, 0, NotSerialized)
            {
                If ((\_SB.I2Z7 != 0xABCD0007))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, \_SB.I2Z7, 0xABCD0007)
                }
            }

            M200 ()
        }

        Method (M101, 0, NotSerialized)
        {
            Method (M202, 0, Serialized)
            {
                Debug = "---------------- Before <Scope(\\)>"
                Scope (\)
                {
                    Name (I2Z4, 0xABCD0004)
                }

                Debug = "---------------- After Scope(\\)"
                M203 ()
                Debug = "---------------- Completed."
            }

            Method (M203, 0, NotSerialized)
            {
                If ((\I2Z4 != 0xABCD0004))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, \I2Z4, 0xABCD0004)
                }
            }

            M202 ()
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("m1eb-m100")
        M100 ()
        SRMT ("m1eb-m101")
        If (Y302)
        {
            M101 ()
        }
        Else
        {
            BLCK ()
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
