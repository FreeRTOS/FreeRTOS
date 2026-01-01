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
     * Bug 200 (local-bugzilla-352):
     *
     * SUMMARY: the code path taken after exception is incorrect
     *
     * AcpiPsParseLoop --> AcpiDsGetPredicateValue --> FAILURE -->>
     * doesn't fall into AcpiDsMethodError routine after FAILURE (exception)
     * (the ASLTS-testing stops after these FAILUREs).
     */
    Method (MFB4, 0, NotSerialized)
    {
        Debug = "Message from mfb4 -------------------------------!!!"
    }

    Method (MFB5, 0, NotSerialized)
    {
        Local7 = 0x00
        Divide (0x01, Local7, Local2)
        If ((Local2 != 0x00))
        {
            MFB4 ()
        }
    }

    Method (MFB6, 0, NotSerialized)
    {
        Local7 = 0x00
        Divide (0x01, Local7, Local2)
        If ((Local2 != 0x00))
        {
            Debug = "Message 0 !!!!!!!!!!!!!!!!!!!!!!"
            MFB4 ()
        }
    }

    Method (MFB7, 0, NotSerialized)
    {
        Local7 = 0x00
        Divide (0x01, Local7, Local2)
    }

    Method (MFB8, 0, NotSerialized)
    {
        Local7 = 0x00
        Divide (0x01, Local7, Local2)
        While ((Local2 != 0x00))
        {
            MFB4 ()
            Break
        }
    }

    Method (MFB9, 0, NotSerialized)
    {
        Local7 = 0x00
        Divide (0x01, Local7, Local2)
        While ((Local2 != 0x00))
        {
            Debug = "Message 1 !!!!!!!!!!!!!!!!!!!!!!"
            MFB4 ()
            Break
        }
    }

    Method (MFBA, 0, Serialized)
    {
        Local7 = 0x00
        Divide (0x01, Local7, Local2)
        Switch ((Local2 != 0x00))
            {
            Case (0x00)
            {
                MFB4 ()
            }

        }
    }

    Method (MFBB, 0, Serialized)
    {
        Local7 = 0x00
        Divide (0x01, Local7, Local2)
        Switch ((Local2 != 0x00))
            {
            Case (0x00)
            {
                Debug = "Message 2 !!!!!!!!!!!!!!!!!!!!!!"
                MFB4 ()
            }

        }
    }

    Method (MFBC, 0, NotSerialized)
    {
        Local7 = 0x00
        Divide (0x01, Local7, Local2)
        Return (Local2)
    }

    Method (MFBD, 0, NotSerialized)
    {
        If (MFBC ())
        {
            Debug = "Message 3 !!!!!!!!!!!!!!!!!!!!!!"
        }
    }

    Method (MFBE, 0, NotSerialized)
    {
        While (MFBC ())
        {
            Break
        }
    }

    Method (MFBF, 0, Serialized)
    {
        Switch (ToInteger (MFBC ()))
        {
            Case (0x00)
            {
                Debug = "Message 4 !!!!!!!!!!!!!!!!!!!!!!"
            }

        }
    }

    Method (MFC0, 0, NotSerialized)
    {
        /*
         * The code path taken after the exception here
         * is not correct for each of these Method calls:
         */
        SRMT ("mfb5")
        If (Y200)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            MFB5 ()
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        }
        Else
        {
            BLCK ()
        }

        SRMT ("mfbd")
        If (Y200)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            MFBD ()
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        }
        Else
        {
            BLCK ()
        }

        SRMT ("mfbe")
        If (Y200)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            MFBE ()
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        }
        Else
        {
            BLCK ()
        }

        /*
         * These work Ok:
         */
        SRMT ("mfb6")
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        MFB6 ()
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("mfb7")
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        MFB7 ()
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("mfb8")
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        MFB8 ()
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("mfb9")
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        MFB9 ()
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("mfba")
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        MFBA ()
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("mfbb")
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        MFBB ()
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("mfbf")
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        MFBF ()
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        Debug = "mfc0 ==== successfully returned to mfc0; finished !!!!!"
    }
