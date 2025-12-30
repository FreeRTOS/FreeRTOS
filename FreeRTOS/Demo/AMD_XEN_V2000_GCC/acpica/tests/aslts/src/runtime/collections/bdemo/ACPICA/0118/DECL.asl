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
     * Bug 118:
     *
     * SUMMARY: Access to FieldObject element of Package causes exception
     *
     * EXAMPLES:
     *
     * ROOT CAUSE:
     *
     * SEE ALSO:     bugs 65,66,67,68,118
     */
    /* Access to the named Integer object as an element of Package */
    Method (MF80, 0, Serialized)
    {
        Name (I000, 0xAAAA0000)
        Name (P000, Package (0x01)
        {
            I000
        })
        I000 = 0xAAAA0100
        Store (P000 [0x00], Local0)
        I000 = 0xAAAA0200
        Local1 = DerefOf (Local0)
        I000 = 0xAAAA0300
        Local2 = ObjectType (I000)
        Local3 = ObjectType (Local0)
        Local4 = ObjectType (Local1)
        Local5 = (Local1 + 0x79)
        If ((Local4 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local4, C009)
        }
        ElseIf ((Local5 != 0xAAAA0279))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local5, 0xAAAA0279)
        }

        If ((I000 != 0xAAAA0300))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xAAAA0300)
        }

        If ((Local2 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local2, C009)
        }

        If ((Local3 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local3, C009)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local5 = (Local0 + 0x79)
        CH04 (__METHOD__, 0x00, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
    }

    Method (MF81, 0, Serialized)
    {
        Name (II00, 0x00)
        Name (II01, 0x00)
        Name (II02, 0x00)
        Name (II03, 0x00)
        Name (II04, 0x00)
        Name (II05, 0x00)
        Name (I000, 0xAAAA0000)
        Name (P000, Package (0x01)
        {
            I000
        })
        I000 = 0xAAAA0100
        /*	Store(Index(p000, 0), ii00) */
        /*	CopyObject(Index(p000, 0), ii00) */
        Store (P000 [0x00], Local0)
        I000 = 0xAAAA0200
        II01 = DerefOf (Local0)
        I000 = 0xAAAA0300
        II02 = ObjectType (I000)
        II03 = ObjectType (Local0)
        II04 = ObjectType (II01)
        II05 = (II01 + 0x79)
        If ((II04 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, II04, C009)
        }
        ElseIf ((II05 != 0xAAAA0279))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, II05, 0xAAAA0279)
        }

        If ((I000 != 0xAAAA0300))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xAAAA0300)
        }

        If ((II02 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, II02, C009)
        }

        If ((II03 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, II03, C009)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        II05 = (Local0 + 0x79)
        CH04 (__METHOD__, 0x00, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
    }

    Method (MF82, 0, Serialized)
    {
        Name (II00, 0x00)
        Name (II01, 0x00)
        Name (II02, 0x00)
        Name (II03, 0x00)
        Name (II04, 0x00)
        Name (II05, 0x00)
        Name (I000, 0xAAAA0000)
        Name (P000, Package (0x01)
        {
            I000
        })
        I000 = 0xAAAA0100
        CopyObject (P000 [0x00], II00) /* \MF82.II00 */
        I000 = 0xAAAA0200
        II01 = DerefOf (II00)
        I000 = 0xAAAA0300
        II02 = ObjectType (I000)
        II03 = ObjectType (II00)
        II04 = ObjectType (II01)
        II05 = (II01 + 0x79)
        If ((II04 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, II04, C009)
        }
        ElseIf ((II05 != 0xAAAA0279))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, II05, 0xAAAA0279)
        }

        If ((I000 != 0xAAAA0300))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I000, 0xAAAA0300)
        }

        If ((II02 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, II02, C009)
        }

        If ((II03 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, II03, C009)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        II05 = (II00 + 0x79)
        CH04 (__METHOD__, 0x00, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
    }

    Method (MD79, 0, NotSerialized)
    {
        Store (PD0A [0x00], Local0)
        Local1 = DerefOf (Local0)
        Local0 = ObjectType (Local1)
        If ((Local0 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, C009)
        }
        ElseIf ((Local1 != 0xFE7CB391D650A284))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0xFE7CB391D650A284)
        }
    }

    /* Access to the Buffer Field object as an element of Package */

    Method (MD7A, 0, NotSerialized)
    {
        Store (PD0B [0x00], Local0)
        Local1 = DerefOf (Local0)
        Local0 = ObjectType (Local1)
        If ((Local0 != C016))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, C016)
        }
        Else
        {
            Debug = "======================================="
            Debug = Local1
            Debug = BFD1 /* \BFD1 */
            Local0 = Local1
            Debug = Local0
            Debug = "======================================="
            If (0x01)
            {
                If ((Local1 != 0x59))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0x59)
                }
            }
        }
    }

    /* Access to the Field Unit object as an element of Package */

    Method (MD7B, 0, NotSerialized)
    {
        Store (PD0C [0x00], Local0)
        Local1 = DerefOf (Local0)
        Local0 = ObjectType (Local1)
        If ((Local0 != C00D))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, C00D)
        }
        Else
        {
            Debug = "======================================="
            Debug = Local1
            Debug = FD03 /* \FD03 */
            Local0 = Local1
            Debug = Local0
            Debug = "======================================="
            If (0x01)
            {
                If ((Local1 != 0x00))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0x00)
                }
            }
        }
    }

    Method (MD7C, 0, NotSerialized)
    {
        /* Named Integer object as an element of Package */
        /*
         SRMT("mf80")
         mf80()
         SRMT("mf81")
         mf81()
         SRMT("mf82")
         if (y127) {
         mf82()
         } else {
         BLCK()
         }
         SRMT("md79")
         md79()
         */
        SRMT ("md7a")
        MD7A ()
        SRMT ("md7b")
        MD7B ()
    }
