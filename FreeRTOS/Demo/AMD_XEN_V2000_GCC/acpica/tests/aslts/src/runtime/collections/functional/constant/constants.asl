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
     * Constants
     */
    Name (Z002, 0x02)
    /* Run-method */

    Method (CST1, 0, Serialized)
    {
        If ((Zero != 0x00))
        {
            ERR (__METHOD__, Z002, __LINE__, 0x00, 0x00, Zero, 0x00)
        }

        If ((One != 0x01))
        {
            ERR (__METHOD__, Z002, __LINE__, 0x00, 0x00, One, 0x01)
        }

        If ((F64 == 0x01))
        {
            If ((Ones != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (__METHOD__, Z002, __LINE__, 0x00, 0x00, Ones, 0xFFFFFFFFFFFFFFFF)
            }
        }
        ElseIf ((Ones != 0xFFFFFFFF))
        {
            ERR (__METHOD__, Z002, __LINE__, 0x00, 0x00, Ones, 0xFFFFFFFF)
        }

        If ((Revision < 0x20140114))
        {
            ERR (__METHOD__, Z002, __LINE__, 0x00, 0x00, Revision, 0x20050114)
        }

        If ((Revision > 0x20500000))
        {
            ERR (__METHOD__, Z002, __LINE__, 0x00, 0x00, Revision, 0x20500000)
        }

        /*
         * June, 2015:
         * The _REV object is in the process of being deprecated, because
         * other ACPI implementations permanently return 2. Thus, it
         * has little or no value. Return 2 for compatibility with
         * other ACPI implementations.
         */
        If ((\_REV != 0x02))
        {
            ERR (__METHOD__, Z002, __LINE__, 0x00, 0x00, \_REV, 0x02)
        }
    }
