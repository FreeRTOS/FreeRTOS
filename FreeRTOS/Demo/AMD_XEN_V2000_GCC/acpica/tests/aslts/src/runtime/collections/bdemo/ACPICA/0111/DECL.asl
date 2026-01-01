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
     * Bug 111:
     *
     * SUMMARY: No String to Integer and Buffer to Integer conversions of the Predicate Value in If, ElseIf and While operators
     */
    Method (ME73, 1, NotSerialized)
    {
        If (Arg0)
        {
            Debug = "If done"
            ID0F = 0x01
        }
    }

    Method (ME74, 2, NotSerialized)
    {
        If (Arg1)
        {
            ID0F = 0x01
        }
        ElseIf (Arg0)
        {
            ID0F = 0x02
        }
    }

    Method (ME75, 1, NotSerialized)
    {
        While (Arg0)
        {
            ID0F = 0x01
            Break
        }
    }

    Method (ME76, 0, NotSerialized)
    {
        /* ////////// */

        ID0F = 0x00
        ME73 ("1")
        If (!ID0F)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME73 (Buffer (0x01)
            {
                 0x01                                             // .
            })
        If (!ID0F)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME73 ("0")
        If (ID0F)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME73 (Buffer (0x01)
            {
                 0x00                                             // .
            })
        If (ID0F)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* ////////// */

        ID0F = 0x00
        ME74 ("1", 0x00)
        If ((ID0F != 0x02))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME74 (Buffer (0x04)
            {
                 0x00, 0x00, 0x01, 0x00                           // ....
            }, 0x00)
        If ((ID0F != 0x02))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME74 ("0", 0x00)
        If (ID0F)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME74 (Buffer (0x04)
            {
                 0x00, 0x00, 0x00, 0x00                           // ....
            }, 0x00)
        If (ID0F)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME74 ("1", 0x01)
        If ((ID0F != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME74 (Buffer (0x04)
            {
                 0x00, 0x00, 0x01, 0x00                           // ....
            }, 0x01)
        If ((ID0F != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME75 ("0")
        If (ID0F)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME75 (Buffer (0x01)
            {
                 0x00                                             // .
            })
        If (ID0F)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME75 ("01")
        If (!ID0F)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ID0F = 0x00
        ME75 (Buffer (0x04)
            {
                 0x00, 0x00, 0x01, 0x00                           // ....
            })
        If (!ID0F)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }
    }
