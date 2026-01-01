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
     * DynObj: Method execution control operators
     */
    Name (Z131, 0x83)
    /* Check the Method Execution Control operators */

    Method (M372, 0, Serialized)
    {
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

        Name (NUM, 0x00)
        Name (NUM2, 0x00)
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (I000, 0x00)
        Name (I001, 0x00)
        Name (I002, 0x00)
        /* Methods verified */

        Method (M000, 0, NotSerialized)
        {
        }

        Method (M001, 0, NotSerialized)
        {
            Return (0x03E8)
        }

        Method (M002, 6, NotSerialized)
        {
        }

        Method (M003, 7, NotSerialized)
        {
            Return (0x03E8)
        }

        Method (M004, 7, NotSerialized)
        {
            Local0 = 0x00
            Local1 = 0x00
            Local2 = 0x00
            Local3 = 0x00
            Local4 = 0x00
            Local5 = 0x00
            Local6 = 0x00
            Local7 = 0x00
            Local7 = (Local0 + Local1)
            Return (Local7)
        }

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
        SET0 (Z131, "m372", 0x00)
        /* ======================== While */

        If (RN00)
        {
            Debug = "While, Continue, Break"
            NUM = 0x49
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x00)
            /* Inv: why (3*num)+1, why +1? */

            NUM = 0x25
            Local4 = NUM /* \M372.NUM_ */
            Local5 = 0x00
            _TCI (C200, Local0)
            While (Local4)
            {
                Local4--
                Local5++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local6 = (0x02 * NUM) /* \M372.NUM_ */
            Local7 = (0x03 * NUM) /* \M372.NUM_ */
            Local7++
            PP00 [C009] = Local6 /* Integer */
            PP00 [C01C] = Local7 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x01)
        }

        If (RN02)
        {
            /* Error: memory is lost */

            NUM2 = 0xC8
            I000 = NUM2 /* \M372.NUM2 */
            NUM = 0xC8
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                If (I000)
                {
                    I000--
                    Continue
                }

                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            Local4 = (Local5 + NUM2) /* \M372.NUM2 */
            PP00 [C009] = Local4 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x02)
        }

        If (RN02)
        {
            /* Error: memory is lost */

            NUM2 = 0x64
            Local4 = NUM2 /* \M372.NUM2 */
            NUM = 0xC8
            Local5 = NUM /* \M372.NUM_ */
            Local6 = 0x00
            _TCI (C200, Local0)
            While (Local5)
            {
                If (Local4)
                {
                    Local4--
                    Continue
                }

                Local5--
                Local6++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            Local4 = (Local5 + NUM2) /* \M372.NUM2 */
            PP00 [C009] = Local4 /* Integer */
            Local7 = (0x04 * NUM) /* \M372.NUM_ */
            Local7++
            Local6 = (0x03 * NUM2) /* \M372.NUM2 */
            Local5 = (Local7 + Local6)
            PP00 [C01C] = Local5 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x03)
        }

        If (RN02)
        {
            NUM = 0x64
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                Break
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x04)
        }

        /* ======================== If */

        If (RN00)
        {
            Debug = "If, ElseIf, Else"
            _TCI (C200, Local0)
            If (0x00){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x05)
            _TCI (C200, Local0)
            If (0x01){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x06)
            I000 = 0x00
            _TCI (C200, Local0)
            If (I000){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x07)
            I000 = 0x01
            _TCI (C200, Local0)
            If (I000){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x08)
            Local4 = 0x00
            _TCI (C200, Local0)
            If (Local4){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x09)
            Local4 = 0x01
            _TCI (C200, Local0)
            If (Local4){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x0A)
            I000 = 0x00
            NUM = 0x13
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                If (I000){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x0B)
            I000 = 0x01
            NUM = 0x13
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                If (I000){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x0C)
            Local4 = 0x00
            NUM = 0x13
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                If (Local4){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            PP00 [C01C] = NUM /* LOCAL_REFERENCE */ /* \M372.NUM_ */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x0D)
            Local4 = 0x01
            NUM = 0x13
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                If (Local4){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            PP00 [C01C] = NUM /* LOCAL_REFERENCE */ /* \M372.NUM_ */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x0E)
            /* LEqual */

            NUM = 0x64
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            Local4 = 0x01
            Local5 = 0x01
            _TCI (C200, Local0)
            While (LPN0)
            {
                If ((Local4 == Local5)){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x03 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            PP00 [C01C] = Local5 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x0F)
            NUM = 0x64
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            Local4 = 0x00
            Local5 = 0x01
            _TCI (C200, Local0)
            While (LPN0)
            {
                If ((Local4 == Local5)){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x03 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            PP00 [C01C] = Local5 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x10)
        }

        /* ======================== If, Else */

        If (RN02)
        {
            /* Error: 1 ACPI_MEM_LIST_STATE is not deleted */

            Local4 = 0x01
            Local5 = 0x01
            _TCI (C200, Local0)
            If ((Local4 == Local5)){}
            Else
            {
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x11)
            Local4 = 0x00
            Local5 = 0x00
            _TCI (C200, Local0)
            If ((Local4 == Local5)){}
            Else
            {
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x12)
            I000 = 0x01
            I001 = 0x01
            _TCI (C200, Local0)
            If ((I000 == I001)){}
            Else
            {
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x13)
            I000 = 0x00
            I001 = 0x00
            _TCI (C200, Local0)
            If ((I000 == I001)){}
            Else
            {
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x14)
        }

        If (RN00)
        {
            Local4 = 0x00
            Local5 = 0x01
            _TCI (C200, Local0)
            If ((Local4 == Local5)){}
            Else
            {
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x15)
            I000 = 0x00
            I001 = 0x01
            _TCI (C200, Local0)
            If ((I000 == I001)){}
            Else
            {
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x16)
        }

        /* ======================== If, ElseIf */

        If (RN02)
        {
            /* Error: 1 ACPI_MEM_LIST_STATE is not deleted */

            Local4 = 0x01
            _TCI (C200, Local0)
            If (Local4){}
            ElseIf (Local4){}
            ElseIf (Local4){}
            ElseIf (Local4){}
            ElseIf (Local4){}
            ElseIf (Local4){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x17)
            /* Error: 1 ACPI_MEM_LIST_STATE is not deleted */

            I000 = 0x01
            _TCI (C200, Local0)
            If (I000){}
            ElseIf (I000){}
            ElseIf (I000){}
            ElseIf (I000){}
            ElseIf (I000){}
            ElseIf (I000){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x18)
            /* Error: (1*num) ACPI_MEM_LIST_STATE are not deleted */

            NUM = 0x64
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            Local4 = 0x01
            _TCI (C200, Local0)
            While (LPN0)
            {
                If (Local4){}
                ElseIf (Local4){}
                ElseIf (Local4){}
                ElseIf (Local4){}
                ElseIf (Local4){}
                ElseIf (Local4){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            PP00 [C01C] = NUM /* LOCAL_REFERENCE */ /* \M372.NUM_ */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x19)
        }

        If (RN00)
        {
            Local4 = 0x00
            _TCI (C200, Local0)
            If (Local4){}
            ElseIf (Local4){}
            ElseIf (Local4){}
            ElseIf (Local4){}
            ElseIf (Local4){}
            ElseIf (Local4){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01C] = 0x06 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x1A)
            I000 = 0x00
            _TCI (C200, Local0)
            If (I000){}
            ElseIf (I000){}
            ElseIf (I000){}
            ElseIf (I000){}
            ElseIf (I000){}
            ElseIf (I000){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x1B)
        }

        If (RN02)
        {
            /* Error: 1 ACPI_MEM_LIST_STATE is not deleted */

            Local4 = 0x01
            Local5 = 0x01
            _TCI (C200, Local0)
            If ((Local4 == Local5)){}
            ElseIf ((Local4 == Local5)){}
            ElseIf ((Local4 == Local5)){}
            ElseIf ((Local4 == Local5)){}
            ElseIf ((Local4 == Local5)){}
            ElseIf ((Local4 == Local5)){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C01C] = 0x02 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x1C)
            /* Error: (1*num) ACPI_MEM_LIST_STATE are not deleted */

            NUM = 0x64
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            Local4 = 0x01
            Local5 = 0x01
            _TCI (C200, Local0)
            While (LPN0)
            {
                If ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x03 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            PP00 [C01C] = Local5 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x1D)
            /* Error: (1*num) ACPI_MEM_LIST_STATE are not deleted */

            NUM = 0x64
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            I000 = 0x01
            I001 = 0x01
            _TCI (C200, Local0)
            While (LPN0)
            {
                If ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x03 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x1E)
            /* Error: (1*num) ACPI_MEM_LIST_STATE are not deleted */

            NUM = 0x64
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            I000 = 0x00
            I001 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                If ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x03 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x1F)
        }

        If (RN00)
        {
            NUM = 0x11
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            Local4 = 0x00
            Local5 = 0x01
            _TCI (C200, Local0)
            While (LPN0)
            {
                If ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x08 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            Local5 = (0x0C * NUM) /* \M372.NUM_ */
            PP00 [C01C] = Local5 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x20)
            NUM = 0x11
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            I000 = 0x00
            I001 = 0x01
            _TCI (C200, Local0)
            While (LPN0)
            {
                If ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                ElseIf ((I000 == I001)){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x08 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x21)
        }

        If (RN02)
        {
            /* Error: (1*num) ACPI_MEM_LIST_STATE are not deleted */

            NUM = 0x64
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            Local4 = 0x00
            Local5 = 0x01
            _TCI (C200, Local0)
            While (LPN0)
            {
                If ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == 0x00)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x06 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            Local5 = (0x05 * NUM) /* \M372.NUM_ */
            PP00 [C01C] = Local5 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x22)
        }

        /* ======================== If, ElseIf, Else */

        If (RN02)
        {
            /* Error: (1*num) ACPI_MEM_LIST_STATE are not deleted */

            NUM = 0x64
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            Local4 = 0x01
            Local5 = 0x01
            _TCI (C200, Local0)
            While (LPN0)
            {
                If ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                ElseIf ((Local4 == Local5)){}
                Else
                {
                }

                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x03 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            Local5 = (0x02 * NUM) /* \M372.NUM_ */
            PP00 [C01C] = Local5 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x23)
        }

        /* ======================== Switch, Case, Default */
        /* CAUTION: these tests should be a few updated after fixing interpreter */
        If (RN02)
        {
            Debug = "Switch, Case, Default"
            /* Inv: why so many Integers, 4 */
            /* Error: why is one Integer not deleted */
            _TCI (C200, Local0)
            Switch (0x00)
            {
                Case (0x01)
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x24)
            _TCI (C200, Local0)
            Switch (0x01)
            {
                Case (0x01)
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x25)
        }

        If (RN02)
        {
            /* Inv: why so many Integers, 4 */
            /* Error: why is one Integer not deleted */
            /* Error: 1 ACPI_MEM_LIST_STATE is not deleted */
            _TCI (C200, Local0)
            Switch (0x00)
            {
                Case (0x01)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x26)
            _TCI (C200, Local0)
            Switch (0x01)
            {
                Case (0x01)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x04 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x27)
        }

        If (RN02)
        {
            /* Inv: what is the number of Integers */
            /* Error: why is one Integer not deleted */
            /* Error: (1*num) ACPI_MEM_LIST_STATE are not deleted */
            NUM = 0x0A
            LPN0 = NUM /* \M372.NUM_ */
            LPC0 = 0x00
            _TCI (C200, Local0)
            While (LPN0)
            {
                Switch (0x01)
                {
                    Case (0x01)
                    {
                    }
                    Default
                    {
                    }

                }

                LPN0--
                LPC0++
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            Local5 = (0x06 * NUM) /* \M372.NUM_ */
            PP00 [C009] = Local5 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x28)
        }

        /* ///////////////////// NamedX & LocalX */

        If (RN02)
        {
            /* NamedX */
            /* Error: why is one Integer not deleted */
            I000 = 0x00
            _TCI (C200, Local0)
            Switch (ToInteger (I000))
            {
                Case (0x00)
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x29)
            I000 = 0x01
            _TCI (C200, Local0)
            Switch (ToInteger (I000))
            {
                Case (0x01)
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2A)
            I000 = 0x00
            _TCI (C200, Local0)
            Switch (ToInteger (I000))
            {
                Case (0x01)
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2B)
            /* LocalX */

            Local4 = 0x00
            _TCI (C200, Local0)
            Switch (ToInteger (Local4))
            {
                Case (0x00)
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2C)
            Local4 = 0x01
            _TCI (C200, Local0)
            Switch (ToInteger (Local4))
            {
                Case (0x01)
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2D)
            Local4 = 0x00
            _TCI (C200, Local0)
            Switch (ToInteger (Local4))
            {
                Case (0x01)
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2E)
        }

        If (RN02)
        {
            /* NamedX */
            /* Error: why is one Integer not deleted */
            I000 = 0x00
            _TCI (C200, Local0)
            Switch (ToInteger (I000))
            {
                Case (0x00)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x2F)
            I000 = 0x01
            _TCI (C200, Local0)
            Switch (ToInteger (I000))
            {
                Case (0x01)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x30)
            I000 = 0x00
            _TCI (C200, Local0)
            Switch (ToInteger (I000))
            {
                Case (0x01)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x31)
            /* LocalX */

            Local4 = 0x00
            _TCI (C200, Local0)
            Switch (ToInteger (Local4))
            {
                Case (0x00)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x32)
            Local4 = 0x01
            _TCI (C200, Local0)
            Switch (ToInteger (Local4))
            {
                Case (0x01)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x33)
            Local4 = 0x00
            _TCI (C200, Local0)
            Switch (ToInteger (Local4))
            {
                Case (0x01)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x34)
        }

        If (RN02)
        {
            I000 = 0x01
            _TCI (C200, Local0)
            Switch (ToInteger (I000))
            {
                Case (0x01)
                {
                }
                Case (0x02)
                {
                }
                Case (0x03)
                {
                }
                Case (0x04)
                {
                }
                Case (0x05)
                {
                }
                Case (0x06)
                {
                }
                Case (0x07)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x35)
            I000 = 0x07
            _TCI (C200, Local0)
            Switch (ToInteger (I000))
            {
                Case (0x01)
                {
                }
                Case (0x02)
                {
                }
                Case (0x03)
                {
                }
                Case (0x04)
                {
                }
                Case (0x05)
                {
                }
                Case (0x06)
                {
                }
                Case (0x07)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x11 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x36)
            I000 = 0x2710
            _TCI (C200, Local0)
            Switch (ToInteger (I000))
            {
                Case (0x01)
                {
                }
                Case (0x02)
                {
                }
                Case (0x03)
                {
                }
                Case (0x04)
                {
                }
                Case (0x05)
                {
                }
                Case (0x06)
                {
                }
                Case (0x07)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x11 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x37)
        }

        If (RN02)
        {
            Local4 = 0x01
            _TCI (C200, Local0)
            Switch (ToInteger (Local4))
            {
                Case (0x01)
                {
                }
                Case (0x02)
                {
                }
                Case (0x03)
                {
                }
                Case (0x04)
                {
                }
                Case (0x05)
                {
                }
                Case (0x06)
                {
                }
                Case (0x07)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x03 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x38)
            Local4 = 0x07
            _TCI (C200, Local0)
            Switch (ToInteger (Local4))
            {
                Case (0x01)
                {
                }
                Case (0x02)
                {
                }
                Case (0x03)
                {
                }
                Case (0x04)
                {
                }
                Case (0x05)
                {
                }
                Case (0x06)
                {
                }
                Case (0x07)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x11 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x39)
            Local4 = 0x2710
            _TCI (C200, Local0)
            Switch (ToInteger (Local4))
            {
                Case (0x01)
                {
                }
                Case (0x02)
                {
                }
                Case (0x03)
                {
                }
                Case (0x04)
                {
                }
                Case (0x05)
                {
                }
                Case (0x06)
                {
                }
                Case (0x07)
                {
                }
                Default
                {
                }

            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x11 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3A)
        }

        /* ======================== Method */

        If (RN00)
        {
            Debug = "Method"
            _TCI (C200, Local0)
            M000 ()
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3B)
            _TCI (C200, Local0)
            M001 ()
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3C)
            _TCI (C200, Local0)
            M002 (0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x06 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3D)
            _TCI (C200, Local0)
            M003 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x08 /* Integer */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3E)
            _TCI (C200, Local0)
            M004 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x10 /* Integer */
            PP00 [C01C] = 0x0C /* LOCAL_REFERENCE */
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x3F)
        }

        /* ======================== NoOp */

        If (RN00)
        {
            Debug = "NoOp"
            _TCI (C200, Local0)
            Noop
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x40)
        }

        RST0 ()
    }
