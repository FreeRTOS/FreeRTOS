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
     * DynObj: executable ASL operators
     */
    Name (Z129, 0x81)
    /* The sample test */

    Method (M370, 0, Serialized)
    {
        /* Flag of printing */

        Name (PR, 0x00)
        /* Check that _TCI is supported */

        If (!M3A5 ())
        {
            Debug = "The Test Command interface with the ACPICA (_TCI) is not supported"
            Debug = "Test m370 skipped"
            Return (0x01)
        }

        /* The benchmark Package */

        Name (PP00, Package (0x20)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00
        })
        /* Package for _TCI-begin statistics */
        /* (use NamedX, don't use ArgX/LocalX). */
        Name (PP0A, Package (0x01){})
        /* Auxiliary objects for ASL-construction */
        /* being investigated: */
        Name (NUM, 0x05)
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        /* Create and initialize the Memory Consumption Statistics Packages */

        Local0 = M3A0 (C200)   /* _TCI-end statistics */
        PP0A = M3A0 (C201)     /* _TCI-begin statistics */
        Local1 = M3A0 (0x00)      /* difference */
        /* Available free locals */

        Local2 = 0x00
        Local3 = 0x00
        Local4 = 0x00
        Local5 = 0x00
        Local6 = 0x00
        Local7 = 0x00
        /* ======================== While */

        If (RN00)
        {
            Debug = "While"
            LPN0 = NUM /* \M370.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            /* ASL-construction being investigated */

            While (LPN0)
            {
                LPN0--
                LPC0++
            }

            /* Use NamedX for _TCI-begin statistics Package */
            /* not to touch the LOCAL_REFERENCE entry. */
            _TCI (C201, PP0A)
            /* Print out the _TCI-end statistics */
            /* and _TCI-begin statistics Packages */
            If (PR)
            {
                M3A2 (Local0, 0x00)
                M3A2 (PP0A, 0x01)
            }

            /* Calculate difference of Packages */

            M3A3 (Local0, PP0A, Local1)
            /* Print out the difference between the two */
            /* Memory Consumption Statistics Packages. */
            If (PR)
            {
                M3A2 (Local1, 0x02)
            }

            /* Verify result */

            Local4 = M3A8 ()
            Local5 = (0x02 * NUM) /* \M370.NUM_ */
            Local4 [C009] = Local5
            M3A4 (Local0, PP0A, Local1, Local4, 0x00, 0x00, 0x00)
        }

        Return (0x00)
    }

    /* Check simple particular operations */

    Method (M371, 0, Serialized)
    {
        /* Because Local0-7 all have been taken, we declare a new variable here. */

        Name (TEMP, 0x00)
        /* The Created Objects benchmark Package */

        Name (PP00, Package (0x01){})
        /* The Deleted Objects benchmark Package */

        Name (PP01, Package (0x01){})
        /* The per-memory type benchmark Package */

        Name (PP02, Package (0x01){})
        /* Package for _TCI-begin statistics */
        /* (use NamedX, don't use ArgX/LocalX). */
        Name (PP0A, Package (0x01){})
        /* Objects for verified operators */

        Mutex (MT00, 0x00)
        Event (EV00)
        Name (I000, 0x00)
        Name (I001, 0x00)
        Name (I002, 0x00)
        Name (I003, 0x00)
        Name (NUM, 0x05)
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (B000, Buffer (0x08){})
        Name (B001, Buffer (0x08){})
        Name (B002, Buffer (0x08){})
        Name (B003, Buffer (0x01){})
        Name (B004, Buffer (0x08){})
        Name (RTP0, ResourceTemplate ()
        {
            IRQNoFlags ()
                {1}
        })
        Name (RTP1, ResourceTemplate ()
        {
            IRQNoFlags ()
                {1}
        })
        Name (P001, Package (0x08)
        {
            0x01,
            0x02,
            0x03,
            0x04,
            0x05,
            0x06,
            0x07,
            0x08
        })
        Name (P002, Package (0x08)
        {
            0x01,
            0x02,
            0x03,
            0x04,
            0x05,
            0x06,
            0x07,
            0x08
        })
        Name (S000, "s")
        Name (S001, "x")
        Name (S002, "swqrtyuiopnm")
        /* Optional Results, writing into uninitialized LocalX */
        /* Add */
        Method (M000, 0, Serialized)
        {
            Name (PP00, Package (0x01){})
            Name (PP01, Package (0x01){})
            Name (PP02, Package (0x01){})
            Name (PP0A, Package (0x01){})
            Local0 = M3A0 (C200)   /* _TCI-end statistics */
            PP0A = M3A0 (C201)     /* _TCI-begin statistics */
            Local1 = M3A0 (0x00)      /* difference */
            _TCI (C200, Local0)
            /*		Store(Add(3, 4, Local2), i000) */

            Local2 = (0x03 + 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            /* Since Local2 was uninitialized, */
            /* acq0 is greater than rel0 by 1. */
            PP02 = M3A9 ()
            PP02 [C228] = 0x01 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x01)
        }

        /* And */

        Method (M001, 0, Serialized)
        {
            Name (PP00, Package (0x01){})
            Name (PP01, Package (0x01){})
            Name (PP02, Package (0x01){})
            Name (PP0A, Package (0x01){})
            Local0 = M3A0 (C200)   /* _TCI-end statistics */
            PP0A = M3A0 (C201)     /* _TCI-begin statistics */
            Local1 = M3A0 (0x00)      /* difference */
            _TCI (C200, Local0)
            /*		Store(And(3, 4, Local2), i000) */

            Local2 = (0x03 & 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            /* Since Local2 was uninitialized, */
            /* acq0 is greater than rel0 by 1. */
            PP02 = M3A9 ()
            PP02 [C228] = 0x01 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x02)
        }

        /* Store */

        Method (M002, 0, Serialized)
        {
            Name (PP00, Package (0x01){})
            Name (PP01, Package (0x01){})
            Name (PP02, Package (0x01){})
            Name (PP0A, Package (0x01){})
            Local0 = M3A0 (C200)   /* _TCI-end statistics */
            PP0A = M3A0 (C201)     /* _TCI-begin statistics */
            Local1 = M3A0 (0x00)      /* difference */
            _TCI (C200, Local0)
            Local2 = "ssss"
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x02 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            /* Since Local2 was uninitialized, */
            /* acq0 is greater than rel0 by 1. */
            PP02 = M3A9 ()
            PP02 [C228] = 0x01 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x03)
        }

        /*
         *	// Apply the same technique to the entire test.
         *
         *	// ################################## Check all the test:
         *
         *	// Packages for _TCI statistics
         *	Name(LLL0, Package(1) {})
         *	Name(LLL1, Package(1) {})
         *	Name(LLL2, Package(1) {})
         *
         *	// Create and initialize the Memory Consumption Statistics Packages
         *
         *	Store(m3a0(c200), LLL0)	// _TCI-end statistics
         *	Store(m3a0(c201), LLL1)	// _TCI-begin statistics
         *	Store(m3a0(0), LLL2)	// difference
         *
         *	_TCI(c200, LLL0)
         *	// ################################## Check all the test.
         */
        /* Create and initialize the Memory Consumption Statistics Packages */
        Local0 = M3A0 (C200)   /* _TCI-end statistics */
        PP0A = M3A0 (C201)     /* _TCI-begin statistics */
        Local1 = M3A0 (0x00)      /* difference */
        /* Available free locals */

        Local2 = 0x00
        Local3 = 0x00
        Local4 = 0x00
        Local5 = 0x00
        Local6 = 0x00
        Local7 = 0x00
        SET0 (Z129, "m371", 0x00)
        /* ======================== Acquire */

        If (RN00)
        {
            Debug = "Acquire"
            _TCI (C200, Local0)
            /* ASL-construction being investigated */

            Acquire (MT00, 0x0064)
            /* Use NamedX for _TCI-begin statistics Package */
            /* not to touch the LOCAL_REFERENCE entry. */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1) /* calculate difference */
            /* Verify result */

            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x04)
        }

        /* ======================== Add */

        If (RN00)
        {
            Debug = "Add"
            /* Writing into uninitialized LocalX test */

            M000 ()
            _TCI (C200, Local0)
            Store ((0x03 + 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x05)
            _TCI (C200, Local0)
            Store ((0x03 + 0x04), TEMP) /* \M371.TEMP */
            Store ((0x03 + 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x08 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x06)
            LPN0 = NUM /* \M371.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                Store ((0x03 + 0x04), TEMP) /* \M371.TEMP */
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x06 * NUM) /* \M371.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x07)
            I000 = 0x03
            I001 = 0x04
            _TCI (C200, Local0)
            Store ((I000 + I001), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x08)
            Local4 = 0x00
            _TCI (C200, Local0)
            Local4 = (I000 + I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x09)
            Local4 = 0x00
            Local4 = "ssss"
            _TCI (C200, Local0)
            Local4 = (I000 + I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x0A)
            _TCI (C200, Local0)
            Local4 = (I000 + I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x0B)
            Local4 = "ssss"
            _TCI (C200, Local0)
            Local4 = (I000 + I001) /* \M371.I001 */
            Local4 = (I000 + I001) /* \M371.I001 */
            Local4 = (I000 + I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x03 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x03 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x0C)
            Local4 = 0x00
            Local5 = 0x00
            Local6 = 0x00
            _TCI (C200, Local0)
            Local6 = (Local4 + Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x03 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x0D)
            Local6 = 0x00
            _TCI (C200, Local0)
            I000 = (0x03 + Local6)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x0E)
            /* Initialized Package example */

            Local4 = Package (0x09)
                {
                    0x01,
                    "",
                    "1",
                    0x02,
                    0x03,
                    Buffer (0x07)
                    {
                         0x08                                             // .
                    },

                    Package (0x14)
                    {
                        0x08,
                        0x09,
                        "q",
                        0x0A,
                        0x0B,
                        Buffer (0x03)
                        {
                             0x06                                             // .
                        }
                    }
                }
            _TCI (C200, Local0)
            Local4 = (I000 + I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00C] = 0x02 /* Package */
            PP01 [C009] = 0x07 /* Integer */
            PP01 [C00A] = 0x03 /* String */
            PP01 [C00B] = 0x02 /* Buffer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            /* These 13 objects of "Store(Package(9) {1,..." */
            /* being deleted inside _TCI brackets were created */
            /* outside it before that: */
            PP02 = M3A9 ()
            Local4 = (0x02 - 0x0F)
            PP02 [C228] = Local4 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x0F)
        }

        /* ======================== And */

        If (RN00)
        {
            Debug = "And"
            /* Writing into uninitialized LocalX test */

            M001 ()
            _TCI (C200, Local0)
            Store ((0x03 & 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x10)
            Local4 = Package (0x09){}
            _TCI (C200, Local0)
            Local4 = (0x03 & 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x11)
            _TCI (C200, Local0)
            I000 = (0x03 & 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x12)
        }

        /* ======================== Concatenate */

        If (RN00)
        {
            Debug = "Concatenate"
            _TCI (C200, Local0)
            TEMP = Concatenate (0x03, 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C00B] = 0x01 /* Buffer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x13)
            _TCI (C200, Local0)
            Concatenate (0x03, 0x04, B000) /* \M371.B000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00B] = 0x01 /* Buffer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x14)
            _TCI (C200, Local0)
            Concatenate (0x03, 0x04, B003) /* \M371.B003 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00B] = 0x01 /* Buffer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x15)
            _TCI (C200, Local0)
            TEMP = Concatenate ("3", "4")
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C00A] = 0x03 /* String */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x16)
            _TCI (C200, Local0)
            Concatenate ("3", "4", S000) /* \M371.S000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x03 /* String */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x17)
            I000 = 0x02
            I001 = 0x03
            _TCI (C200, Local0)
            TEMP = Concatenate (Buffer (I000)
                    {
                         0x03, 0x04                                       // ..
                    }, Buffer (I001)
                    {
                         0x06, 0x07, 0x08                                 // ...
                    })
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C00B] = 0x03 /* Buffer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x18)
            _TCI (C200, Local0)
            Concatenate (Buffer (I000)
                {
                     0x03, 0x04                                       // ..
                }, Buffer (I001)
                {
                     0x06, 0x07, 0x08                                 // ...
                }, B002) /* \M371.B002 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00B] = 0x03 /* Buffer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x19)
            _TCI (C200, Local0)
            Concatenate (Buffer (I000)
                {
                     0x03, 0x04                                       // ..
                }, Buffer (I001)
                {
                     0x06, 0x07, 0x08                                 // ...
                }, S000) /* \M371.S000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C00B] = 0x03 /* Buffer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x1A)
            CopyObject ("", S000) /* \M371.S000 */
            _TCI (C200, Local0)
            Concatenate ("3", "4", B001) /* \M371.B001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C00A] = 0x03 /* String */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x1B)
            Local4 = Package (0x09){}
            _TCI (C200, Local0)
            Concatenate (0x03, 0x04, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x1C)
            Local4 = "sss"
            _TCI (C200, Local0)
            Concatenate ("3", "4", Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x03 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x1D)
            Local4 = 0x00
            _TCI (C200, Local0)
            Concatenate ("3", "4", Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x03 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00A] = 0x02 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x1E)
            Local4 = Package (0x09){}
            _TCI (C200, Local0)
            Concatenate (Buffer (0x03){}, Buffer (0x04){}, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00B] = 0x03 /* Buffer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C00B] = 0x02 /* Buffer */
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x1F)
        }

        /* ======================== ConcatenateResTemplate */

        If (RN00)
        {
            Debug = "ConcatenateResTemplate"
            Local4 = 0x00
            _TCI (C200, Local0)
            ConcatenateResTemplate (RTP0, RTP1, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x20)
        }

        /* ======================== CondRefOf */

        If (RN01)
        {
            Debug = "CondRefOf"
            /* Investigate: why 3 objects, but not 2 */

            _TCI (C200, Local0)
            TEMP = CondRefOf (I003)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x21)
            CopyObject ("sssss", S000) /* \M371.S000 */
            _TCI (C200, Local0)
            TEMP = CondRefOf (S000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x22)
            _TCI (C200, Local0)
            TEMP = CondRefOf (I003)
            TEMP = CondRefOf (I003)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x23)
        }

        If (RN00)
        {
            Local4 = Package (0x09){}
            _TCI (C200, Local0)
            CondRefOf (S001, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x24)
            Local4 = Buffer (0x09){}
            Local5 = Package (0x09){}
            _TCI (C200, Local0)
            CondRefOf (Local4, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x03 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x25)
        }

        /* ======================== CopyObject */

        If (RN00)
        {
            Debug = "CopyObject"
            _TCI (C200, Local0)
            CopyObject (I000, I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x26)
            Local4 = Buffer (0x09){}
            I000 = 0x02
            _TCI (C200, Local0)
            CopyObject (I000, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x27)
            CondRefOf (Local4, Local5)
            _TCI (C200, Local0)
            CopyObject (Local4, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C01C] = 0x03 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x28)
            _TCI (C200, Local0)
            CopyObject (Local4, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x29)
        }

        /* ======================== Decrement */

        If (RN00)
        {
            Debug = "Decrement"
            _TCI (C200, Local0)
            I000--
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2A)
            _TCI (C200, Local0)
            Local4--
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2B)
        }

        /* ======================== DerefOf */

        If (RN00)
        {
            Debug = "DerefOf"
            CopyObject (0x00, I000) /* \M371.I000 */
            CopyObject (0x00, I001) /* \M371.I001 */
            Local4 = RefOf (I000)
            _TCI (C200, Local0)
            TEMP = DerefOf (Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2C)
            Local4 = RefOf (I000)
            _TCI (C200, Local0)
            I001 = DerefOf (Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2D)
        }

        /* ======================== Divide */

        If (RN01)
        {
            Debug = "Divide"
            /* Investigate: why 6 objects, but not 5 */

            _TCI (C200, Local0)
            Store ((0x01 / 0x02), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x06 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2E)
            _TCI (C200, Local0)
            Divide (0x01, 0x02, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x05 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2F)
            _TCI (C200, Local0)
            Divide (0x01, 0x02, I000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x05 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x30)
            _TCI (C200, Local0)
            Divide (0x01, 0x02, I000, I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x31)
            _TCI (C200, Local0)
            Divide (0x01, 0x02, Local4, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x32)
            Local4 = 0x1111111111111111
            Local5 = 0x12345678
            Local6 = "sssssssss"
            Local7 = Buffer (0x11){}
            _TCI (C200, Local0)
            Divide (Local4, Local5, Local6, Local7)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x04 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00A] = 0x01 /* String */
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x04 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x33)
        }

        /* ======================== Fatal */

        If (RN00)
        {
            Debug = "Fatal"
            _TCI (C200, Local0)
            Fatal (0x01, 0x00000002, 0x03)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x34)
        }

        I000 = 0x01
        I001 = 0x01
        /* ======================== FindSetLeftBit */

        If (RN00)
        {
            Debug = "FindSetLeftBit"
            _TCI (C200, Local0)
            TEMP = FindSetLeftBit (0x05)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x35)
            _TCI (C200, Local0)
            TEMP = FindSetLeftBit (I000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x36)
            _TCI (C200, Local0)
            FindSetLeftBit (I000, I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x37)
            _TCI (C200, Local0)
            FindSetLeftBit (I000, I000) /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x38)
            Local4 = 0x01
            Local5 = 0x01
            _TCI (C200, Local0)
            FindSetLeftBit (Local4, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x39)
            _TCI (C200, Local0)
            FindSetLeftBit (I000, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3A)
        }

        /* ======================== FindSetRightBit */

        If (RN00)
        {
            Debug = "FindSetRightBit"
            _TCI (C200, Local0)
            TEMP = FindSetRightBit (0x05)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3B)
            _TCI (C200, Local0)
            TEMP = FindSetRightBit (I000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3C)
            _TCI (C200, Local0)
            FindSetRightBit (I000, I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3D)
            _TCI (C200, Local0)
            FindSetRightBit (I000, I000) /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3E)
            Local4 = 0x01
            Local5 = 0x01
            _TCI (C200, Local0)
            FindSetRightBit (Local4, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3F)
            _TCI (C200, Local0)
            FindSetRightBit (I000, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x40)
            Local5 = Package (0x09){}
            _TCI (C200, Local0)
            FindSetRightBit (I000, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x41)
        }

        /* ======================== FromBCD */

        If (RN00)
        {
            Debug = "FromBCD"
            _TCI (C200, Local0)
            TEMP = FromBCD (0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x42)
            I000 = 0x01
            I001 = 0x01
            _TCI (C200, Local0)
            TEMP = FromBCD (I000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x43)
            _TCI (C200, Local0)
            FromBCD (I000, I000) /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x44)
            _TCI (C200, Local0)
            FromBCD (I000, I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x45)
            Local4 = 0x01
            Local5 = Buffer (0x09){}
            _TCI (C200, Local0)
            FromBCD (Local4, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x46)
        }

        /* ======================== Increment */

        If (RN00)
        {
            Debug = "Increment"
            I000 = 0x01
            _TCI (C200, Local0)
            I000++
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x47)
            Local4 = 0x01
            _TCI (C200, Local0)
            Local4++
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x48)
        }

        /* ======================== Index */

        If (RN00)
        {
            Debug = "Index"
            /* Package */

            _TCI (C200, Local0)
            Store (P001 [0x01], TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x49)
            _TCI (C200, Local0)
            Store (Index (Package (0x10)
                    {
                        0x01,
                        0x02,
                        0x03,
                        0x04,
                        0x05,
                        0x06,
                        0x07,
                        0x08
                    }, 0x01), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x0B /* Integer */
            PP00 [C00C] = 0x01  /* Package */
            PP00 [C01C] = 0x01  /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x4A)
            Local4 = Buffer (0x01){}
            _TCI (C200, Local0)
            Local4 = P001 [0x01]
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x4B)
            I000 = 0x01
            Local4 = "ssssss"
            _TCI (C200, Local0)
            Local4 = P001 [I000] /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x4C)
            /* Buffer */

            _TCI (C200, Local0)
            Store (B004 [0x01], TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x4D)
            _TCI (C200, Local0)
            Store (Index (Buffer (0x10)
                    {
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
                    }, 0x01), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C00B] = 0x01  /* Buffer */
            PP00 [C01C] = 0x01  /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x4E)
            Local4 = "ssssssssss"
            _TCI (C200, Local0)
            Local4 = B004 [0x01]
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x4F)
            I000 = 0x01
            Local4 = "ssssss"
            _TCI (C200, Local0)
            Local4 = B004 [I000] /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x50)
            Local4 = Buffer (0x09){}
            _TCI (C200, Local0)
            Local4 = B004 [0x01]
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x51)
            /* String */

            _TCI (C200, Local0)
            Store (S002 [0x01], TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x52)
            _TCI (C200, Local0)
            Store (Index ("sdrtghjkiopuiy", 0x01), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x53)
            Local4 = Buffer (0x01){}
            _TCI (C200, Local0)
            Local4 = S002 [0x01]
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x54)
            I000 = 0x01
            Local4 = "ssssss"
            _TCI (C200, Local0)
            Local4 = S002 [I000] /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x55)
        }

        /* ======================== LAnd */

        If (RN00)
        {
            Debug = "LAnd"
            I000 = 0x01
            I001 = 0x01
            _TCI (C200, Local0)
            TEMP = (0x03 && 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x56)
            _TCI (C200, Local0)
            TEMP = (I000 && I001)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x57)
            Local4 = 0x01
            Local5 = 0x01
            _TCI (C200, Local0)
            TEMP = (Local4 && Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x58)
            Local5 = 0x01
            _TCI (C200, Local0)
            TEMP = (I000 && Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x59)
        }

        /* ======================== LEqual */

        If (RN00)
        {
            Debug = "LEqual"
            Local4 = 0x01
            Local5 = 0x01
            I000 = 0x01
            I001 = 0x01
            _TCI (C200, Local0)
            TEMP = (0x03 == 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x5A)
            _TCI (C200, Local0)
            TEMP = (I000 == I001)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x5B)
            _TCI (C200, Local0)
            TEMP = (Local4 == Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x5C)
            _TCI (C200, Local0)
            TEMP = (I000 == Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x5D)
        }

        /* ======================== LGreater */

        If (RN00)
        {
            Debug = "LGreater"
            _TCI (C200, Local0)
            TEMP = (0x03 > 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x5E)
            _TCI (C200, Local0)
            TEMP = (I000 > I001)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x5F)
            _TCI (C200, Local0)
            TEMP = (Local4 > Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x60)
            _TCI (C200, Local0)
            TEMP = (I000 > Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x61)
        }

        /* ======================== LGreaterEqual */

        If (RN01)
        {
            Debug = "LGreaterEqual"
            /* Investigate: why the numbers differ */
            /* those of LGreater (+1 Integer). */
            _TCI (C200, Local0)
            TEMP = (0x03 >= 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x62)
            _TCI (C200, Local0)
            TEMP = (I000 >= I001)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x63)
            _TCI (C200, Local0)
            TEMP = (Local4 >= Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x64)
            _TCI (C200, Local0)
            TEMP = (I000 >= Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x65)
        }

        /* ======================== LLess */

        If (RN00)
        {
            Debug = "LLess"
            _TCI (C200, Local0)
            TEMP = (0x03 < 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x66)
            _TCI (C200, Local0)
            TEMP = (I000 < I001)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x67)
            _TCI (C200, Local0)
            TEMP = (Local4 < Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x68)
            _TCI (C200, Local0)
            TEMP = (I000 < Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x69)
        }

        /* ======================== LLessEqual */

        If (RN01)
        {
            Debug = "LLessEqual"
            /* Investigate: why the numbers differ */
            /* those of LGreater (+1 Integer) (but */
            /* identical to LGreaterEqual). */
            _TCI (C200, Local0)
            TEMP = (0x03 <= 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x6A)
            _TCI (C200, Local0)
            TEMP = (I000 <= I001)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x6B)
            _TCI (C200, Local0)
            TEMP = (Local4 <= Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x6C)
            _TCI (C200, Local0)
            TEMP = (I000 <= Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x6D)
        }

        /* ======================== LNot */

        If (RN00)
        {
            Debug = "LNot"
            _TCI (C200, Local0)
            TEMP = !0x03
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x6E)
            _TCI (C200, Local0)
            TEMP = !I000
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x6F)
            _TCI (C200, Local0)
            TEMP = !Local4
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x70)
        }

        /* ======================== LNotEqual */

        If (RN01)
        {
            Debug = "LNotEqual"
            /* Investigate: why the numbers differ */
            /* those of LGreater (+1 Integer) (but */
            /* identical to LGreaterEqual). */
            _TCI (C200, Local0)
            TEMP = (0x03 != 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x71)
            _TCI (C200, Local0)
            TEMP = (I000 != I001)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x72)
            _TCI (C200, Local0)
            TEMP = (Local4 != Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x73)
            _TCI (C200, Local0)
            TEMP = (I000 != Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x74)
        }

        /* ======================== LOr */

        If (RN00)
        {
            Debug = "LOr"
            _TCI (C200, Local0)
            TEMP = (0x03 || 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x75)
            _TCI (C200, Local0)
            TEMP = (I000 || I001)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x76)
            _TCI (C200, Local0)
            TEMP = (Local4 || Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x77)
            _TCI (C200, Local0)
            TEMP = (I000 || Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x78)
        }

        /* ======================== Match */

        If (RN00)
        {
            Debug = "Match"
            Local4 = 0x01
            Local5 = 0x01
            I000 = 0x01
            I001 = 0x01
            _TCI (C200, Local0)
            TEMP = Match (Package (0x08)
                    {
                        0x01,
                        0x02,
                        0x03,
                        0x04,
                        0x05,
                        0x06,
                        0x07,
                        0x08
                    }, MTR, 0x02, MTR, 0x03, 0x00)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x0F /* Integer */
            PP00 [C00C] = 0x01  /* Package */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x79)
            _TCI (C200, Local0)
            TEMP = Match (Package (I001)
                    {
                        0x01,
                        0x02,
                        0x03,
                        0x04,
                        0x05,
                        0x06,
                        0x07,
                        0x08
                    }, MTR, I000, MTR, Local4, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x0B /* Integer */
            PP00 [C00C] = 0x01  /* Package */
            PP00 [C01C] = 0x02  /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x7A)
            _TCI (C200, Local0)
            TEMP = Match (P002, MTR, I000, MTR, Local4, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x02  /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x7B)
        }

        /* ======================== Mid */

        If (RN00)
        {
            Debug = "Mid"
            _TCI (C200, Local0)
            TEMP = Mid ("asdfghjk", 0x00, 0x01)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C00A] = 0x02 /* String */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x7C)
            Local4 = Package (0x09){}
            _TCI (C200, Local0)
            Mid ("gsqrtsghjkmnh", 0x00, 0x09, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00A] = 0x02 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C00A] = 0x01 /* String */
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x7D)
            Local4 = Package (0x09){}
            _TCI (C200, Local0)
            Mid (S000, 0x00, 0x01, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x7E)
            Local4 = Buffer (0x09){}
            _TCI (C200, Local0)
            Mid (B000, 0x00, 0x01, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x7F)
        }

        /* ======================== Mod */

        If (RN00)
        {
            Debug = "Mod"
            _TCI (C200, Local0)
            Store ((0x03 % 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x80)
            Local4 = Buffer (0x09){}
            _TCI (C200, Local0)
            Local4 = (0x03 % 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x81)
            Local4 = 0x01
            _TCI (C200, Local0)
            I001 = (I000 % Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x82)
        }

        /* ======================== Multiply */

        If (RN00)
        {
            Debug = "Multiply"
            _TCI (C200, Local0)
            Store ((0x03 * 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x83)
            _TCI (C200, Local0)
            I000 = (0x03 * 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x84)
            Local4 = 0x01
            _TCI (C200, Local0)
            Local4 *= Local4
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x03 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x85)
        }

        /* ======================== NAnd */

        If (RN00)
        {
            Debug = "NAnd"
            _TCI (C200, Local0)
            TEMP = NAnd (0x03, 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x86)
            _TCI (C200, Local0)
            NAnd (I000, 0x04, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x87)
            _TCI (C200, Local0)
            NAnd (I000, I001, I002) /* \M371.I002 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x88)
        }

        /* ======================== NOr */

        If (RN00)
        {
            Debug = "NOr"
            _TCI (C200, Local0)
            TEMP = NOr (0x03, 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x89)
            _TCI (C200, Local0)
            NOr (I000, 0x04, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x8A)
            _TCI (C200, Local0)
            NOr (I000, I001, I002) /* \M371.I002 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x8B)
        }

        /* ======================== Not */

        If (RN00)
        {
            Debug = "Not"
            _TCI (C200, Local0)
            Store (~0x03, TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x8C)
            _TCI (C200, Local0)
            I001 = ~0x03
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x8D)
            _TCI (C200, Local0)
            I001 = ~I000 /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x8E)
            Local4 = 0x01
            _TCI (C200, Local0)
            Local4 = ~Local4
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x8F)
            Local5 = "sssssssssss"
            _TCI (C200, Local0)
            Local5 = ~I000 /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x90)
        }

        /* ======================== ObjectType */

        If (RN00)
        {
            Debug = "ObjectType"
            _TCI (C200, Local0)
            TEMP = ObjectType (I000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x91)
            Local4 = Package (0x01){}
            _TCI (C200, Local0)
            TEMP = ObjectType (Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x92)
        }

        /* ======================== Or */

        If (RN00)
        {
            Debug = "Or"
            _TCI (C200, Local0)
            Store ((0x03 | 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x93)
            Local4 = Package (0x09){}
            _TCI (C200, Local0)
            Local4 = (I000 | 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x94)
            _TCI (C200, Local0)
            I002 = (I000 | I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x95)
        }

        /* ======================== RefOf */

        If (RN00)
        {
            Debug = "RefOf"
            _TCI (C200, Local0)
            TEMP = RefOf (I000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x96)
            Local4 = 0x01
            _TCI (C200, Local0)
            TEMP = RefOf (Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x97)
        }

        /* ======================== Release */

        If (RN00)
        {
            Debug = "Release"
            Acquire (MT00, 0x0064)
            _TCI (C200, Local0)
            Release (MT00)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x98)
        }

        /* ======================== Reset */

        If (RN00)
        {
            Debug = "Reset"
            _TCI (C200, Local0)
            Reset (EV00)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x99)
        }

        /* ======================== ShiftLeft */

        If (RN00)
        {
            Debug = "ShiftLeft"
            _TCI (C200, Local0)
            Store ((0x03 << 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x9A)
            Local4 = "qqqqqqqqqqqqq"
            _TCI (C200, Local0)
            Local4 = (0x03 << 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x9B)
            _TCI (C200, Local0)
            I001 = (I000 << Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x9C)
        }

        /* ======================== ShiftRight */

        If (RN00)
        {
            Debug = "ShiftRight"
            _TCI (C200, Local0)
            Store ((0x03 >> 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x9D)
            Local4 = "qqqqqqqqqqqqq"
            _TCI (C200, Local0)
            Local4 = (0x03 >> 0x04)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0x9E)
            _TCI (C200, Local0)
            I001 = (I000 >> Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x9F)
        }

        /* ======================== Signal */

        If (RN00)
        {
            Debug = "Signal"
            Reset (EV00)
            _TCI (C200, Local0)
            Signal (EV00)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xA0)
        }

        /* ======================== SizeOf */

        If (RN00)
        {
            Debug = "SizeOf"
            Local4 = Package (0x09){}
            _TCI (C200, Local0)
            TEMP = SizeOf (Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xA1)
            _TCI (C200, Local0)
            TEMP = SizeOf (B000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xA2)
        }

        /* ======================== Sleep */

        If (RN00)
        {
            Debug = "Sleep"
            _TCI (C200, Local0)
            Sleep (0x01)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xA3)
            I000 = 0x01
            _TCI (C200, Local0)
            Sleep (I000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xA4)
            Local4 = 0x01
            _TCI (C200, Local0)
            Sleep (Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xA5)
        }

        /* ======================== Stall */

        If (RN00)
        {
            Debug = "Stall"
            _TCI (C200, Local0)
            Stall (0x01)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xA6)
            _TCI (C200, Local0)
            Stall (I000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xA7)
            _TCI (C200, Local0)
            Stall (Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xA8)
        }

        /* ======================== Store */

        If (RN01)
        {
            /* Investigate and analyze the logic of */
            /* crreating/deleting objects while processing */
            /* the Store operator (the number of objects in */
            /* different cases applying the Store operator). */
            Debug = "Store"
            /* Writing into uninitialized LocalX */

            M002 ()
            Local4 = "ssssssssss"
            _TCI (C200, Local0)
            Local4 = 0x05
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xA9)
            I000 = 0x01
            I001 = 0x01
            _TCI (C200, Local0)
            I001 = I000 /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xAA)
            /* But why this example contains three objects, */
            /* just as expected. */
            Local4 = "sssssssss"
            Local5 = Package (0x09){}
            _TCI (C200, Local0)
            Local5 = Local4
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xAB)
            Local4 = Package (0x08)
                {
                    0x01,
                    0x02,
                    0x03,
                    0x04,
                    0x05,
                    0x06,
                    0x07,
                    0x08
                }
            Local5 = 0x01
            _TCI (C200, Local0)
            Local5 = Local4
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x08 /* Integer */
            PP00 [C00C] = 0x01 /* Package */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C01C] = 0x02 /* LOCAL_REFERENCE */
            /* Package is not being removed, */
            /* its elements created outide are */
            /* not removed as well. */
            PP02 = M3A9 ()
            PP02 [C228] = 0x08 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0xAC)
            Local4 = Buffer (0x08)
                {
                     0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
                }
            Local5 = "q"
            _TCI (C200, Local0)
            Local5 = Local4
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00A] = 0x01 /* String */
            PP01 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xAD)
            Local4 = "sghjklopiuytrwq"
            Local5 = Buffer (0x08)
                {
                     0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
                }
            _TCI (C200, Local0)
            Local5 = Local4
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xAE)
            Local4 = "a"
            _TCI (C200, Local0)
            Local4 = "ssss"
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xAF)
            Local4 = Buffer (0x03){}
            _TCI (C200, Local0)
            Local4 = Buffer (0x03){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xB0)
            /* Why there is no one new Integer? */

            I000 = 0x00
            I001 = 0x00
            _TCI (C200, Local0)
            I001 = I000 /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xB1)
        }

        /* ======================== Subtract */

        If (RN00)
        {
            Debug = "Subtract"
            _TCI (C200, Local0)
            Store ((0x03 - 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xB2)
            _TCI (C200, Local0)
            Store ((0x03 - 0x04), TEMP) /* \M371.TEMP */
            Store ((0x03 - 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x08 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xB3)
            NUM = 0x05
            LPN0 = NUM /* \M371.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                Store ((0x03 - 0x04), TEMP) /* \M371.TEMP */
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x06 * NUM) /* \M371.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xB4)
            I000 = 0x03
            I001 = 0x04
            _TCI (C200, Local0)
            Store ((I000 - I001), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xB5)
            Local4 = 0x00
            _TCI (C200, Local0)
            Local4 = (I000 - I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xB6)
            Local4 = 0x02
            Local5 = 0x01
            Local6 = 0x00
            _TCI (C200, Local0)
            Local6 = (Local4 - Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x03 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xB7)
            _TCI (C200, Local0)
            I000 = (0x03 - Local6)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xB8)
        }

        /* ======================== ToBCD */

        If (RN00)
        {
            Debug = "ToBCD"
            _TCI (C200, Local0)
            TEMP = ToBCD (0x03)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xB9)
            _TCI (C200, Local0)
            ToBCD (0x03, I000) /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xBA)
            _TCI (C200, Local0)
            ToBCD (0x03, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xBB)
            _TCI (C200, Local0)
            ToBCD (I000, I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xBC)
            _TCI (C200, Local0)
            ToBCD (Local4, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xBD)
        }

        /* ======================== ToBuffer */

        If (RN00)
        {
            Debug = "ToBuffer"
            _TCI (C200, Local0)
            TEMP = ToBuffer (0x03)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00B] = 0x01 /* Buffer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xBE)
            Local4 = 0x01
            _TCI (C200, Local0)
            ToBuffer (0x03, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xBF)
            Local4 = 0x01
            _TCI (C200, Local0)
            ToBuffer (Local4, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xC0)
            Local4 = 0x01
            _TCI (C200, Local0)
            ToBuffer (Buffer (0x03){}, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C00B] = 0x02 /* Buffer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xC1)
        }

        If (RN01)
        {
            /* Investigate, why only two objects */

            Local4 = Buffer (0x03){}
            _TCI (C200, Local0)
            ToBuffer (Local4, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xC2)
        }

        If (RN00)
        {
            Local4 = Buffer (0x03){}
            Local5 = Buffer (0x03){}
            _TCI (C200, Local0)
            ToBuffer (Local4, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xC3)
        }

        /* ======================== ToDecimalString */

        If (RN00)
        {
            Debug = "ToDecimalString"
            _TCI (C200, Local0)
            TEMP = ToDecimalString (0x03)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xC4)
            Local4 = Buffer (0x03){}
            _TCI (C200, Local0)
            ToDecimalString (0x03, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xC5)
            Local4 = "aaa"
            _TCI (C200, Local0)
            ToDecimalString (I000, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xC6)
            Local4 = 0x01
            Local5 = Package (0x09){}
            _TCI (C200, Local0)
            ToDecimalString (Local4, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xC7)
            Local4 = 0x01
            _TCI (C200, Local0)
            ToDecimalString (Local4, S000) /* \M371.S000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xC8)
        }

        /* ======================== ToHexString */

        If (RN00)
        {
            Debug = "ToHexString"
            _TCI (C200, Local0)
            TEMP = ToHexString (0x03)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xC9)
            Local4 = Buffer (0x03){}
            _TCI (C200, Local0)
            ToHexString (0x03, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00B] = 0x01 /* Buffer */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xCA)
            Local4 = "aaa"
            _TCI (C200, Local0)
            ToHexString (I000, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xCB)
            Local4 = 0x01
            Local5 = Package (0x09){}
            _TCI (C200, Local0)
            ToHexString (Local4, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xCC)
            Local4 = 0x01
            _TCI (C200, Local0)
            ToHexString (Local4, S000) /* \M371.S000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xCD)
        }

        /* ======================== ToInteger */

        If (RN01)
        {
            Debug = "ToInteger"
            /* Investigate: why only 2 objects, but not 3 */

            _TCI (C200, Local0)
            TEMP = ToInteger (0x03)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xCE)
            _TCI (C200, Local0)
            ToInteger (0x03, I000) /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xCF)
            /* Inv: why only one object, no Integer */

            Local4 = 0x01
            _TCI (C200, Local0)
            ToInteger (Local4, I000) /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xD0)
            Local4 = Package (0x09){}
            _TCI (C200, Local0)
            ToInteger (I000, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xD1)
            /* See: there are created all the expected 3 objects */

            _TCI (C200, Local0)
            TEMP = ToInteger ("0xaaaa")
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xD2)
            _TCI (C200, Local0)
            ToInteger ("0xaaaa", I000) /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xD3)
            Local4 = "0xaaaa"
            _TCI (C200, Local0)
            ToInteger (Local4, I000) /* \M371.I000 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xD4)
            S000 = "0xaaaa"
            Local4 = Package (0x09){}
            _TCI (C200, Local0)
            ToInteger (S000, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xD5)
            _TCI (C200, Local0)
            TEMP = ToInteger (Buffer (0x09)
                    {
                        /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                        /* 0008 */  0x09                                             // .
                    })
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C00B] = 0x01 /* Buffer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xD6)
        }

        /* ======================== ToString */

        If (RN02)
        {
            Debug = "ToString"
            /* Integer */
            /* Inv: Buffer is result of conversion of Integer 2? */
            /* Error: 1 Integer is not deleted */
            _TCI (C200, Local0)
            TEMP = ToString (0x02, Ones)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            PP00 [C00B] = 0x01 /* Buffer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xD7)
        }

        If (RN00)
        {
            Local5 = "sssss"
            _TCI (C200, Local0)
            Local5 = ToString (0x02, Ones)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xD8)
            I000 = 0x02
            Local5 = "sssss"
            _TCI (C200, Local0)
            Local5 = ToString (I000, Ones)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xD9)
        }

        If (RN02)
        {
            /* Error: 1 Integer is not deleted */

            Local5 = "sssss"
            _TCI (C200, Local0)
            ToString (0x02, 0x00, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xDA)
        }

        /* Buffer */

        If (RN00)
        {
            Local5 = "sssss"
            B000 = Buffer (0x09)
                {
                    /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                    /* 0008 */  0x09                                             // .
                }
            _TCI (C200, Local0)
            Local5 = ToString (B000, Ones)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xDB)
            Local5 = "sssss"
            _TCI (C200, Local0)
            ToString (Buffer (0x09)
                {
                    /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                    /* 0008 */  0x09                                             // .
                }, 0x00, Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C00A] = 0x01 /* String */
            PP00 [C00B] = 0x01 /* Buffer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xDC)
            Local4 = Buffer (0x09)
                {
                    /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                    /* 0008 */  0x09                                             // .
                }
            Local5 = 0x01
            Local6 = "sssssss"
            _TCI (C200, Local0)
            ToString (Local4, Local5, Local6)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP00 [C01C] = 0x03 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xDD)
        }

        /* ======================== Wait */

        If (RN00)
        {
            Debug = "Wait"
            _TCI (C200, Local0)
            Wait (EV00, 0x01)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xDE)
            Local4 = 0x01
            _TCI (C200, Local0)
            Wait (EV00, Local4)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xDF)
            I000 = 0x01
            _TCI (C200, Local0)
            Wait (EV00, I000)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xE0)
        }

        /* ======================== XOr */

        If (RN00)
        {
            Debug = "XOr"
            _TCI (C200, Local0)
            Store ((0x03 ^ 0x04), TEMP) /* \M371.TEMP */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xE1)
            Local4 = 0x01
            Local5 = 0x01
            Local6 = 0x01
            _TCI (C200, Local0)
            Local6 = (Local4 ^ Local5)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x03 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xE2)
            I000 = 0x01
            I001 = 0x01
            I002 = 0x01
            _TCI (C200, Local0)
            I002 = (I000 ^ I001) /* \M371.I001 */
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0xE3)
            Local6 = Package (0x09){}
            _TCI (C200, Local0)
            Local6 = (I000 ^ 0x03)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP01 [C00C] = 0x01 /* Package */
            PP01 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, 0x00, 0xE4)
        }

        RST0 ()
        /*
     *	// ################################## Check all the test:
     *	_TCI(c201, LLL1)
     *	m3a3(LLL0, LLL1, LLL2)
     *	m3a4(LLL0, LLL1, LLL2, 0, 0, 0, 0xff0)
     *	// ################################## Check all the test.
     */
    }
