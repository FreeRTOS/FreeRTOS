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
     * Bug 0057:
     *
     * SUMMARY: The standalone Return is processed incorrectly
     */
    Method (MDEF, 0, NotSerialized)
    {
        Debug = "mdef"
    }

    Method (MDF0, 0, NotSerialized)
    {
        Debug = "mdf0"
    }

    Method (MDF1, 0, NotSerialized)
    {
        Debug = "mdf1"
    }

    Method (MDF2, 1, NotSerialized)
    {
        Debug = "mdf2"
        MDEF ()
        If (Arg0)
        {
            Debug = "mdf2: before Return"
            Return (0x1234)
                /* ASL-compiler report Warning in this case */
        /* Store("ERROR 0: mdf2, after Return !!!", Debug) */
        }

        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        MDF0 ()
        MDF1 ()
        Return (0x5678)
    }

    Method (MDF3, 1, NotSerialized)
    {
        Debug = "mdf3"
        MDEF ()
        If (Arg0)
        {
            Debug = "mdf3: before Return"
            Return (            /* ASL-compiler DOESN'T report Warning in this case!!! */
            /* And the Store operator below is actually processed!!! */
Zero)
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        MDF0 ()
        MDF1 ()
        Return (Zero)
    }

    Method (MDF4, 0, NotSerialized)
    {
        Local7 = MDF2 (0x01)
        Debug = Local7
        MDF3 (0x01)
    }
