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
     * DynObj: ASL declarations
     */
    Name (Z130, 0x82)
    /* Check declarations */

    Method (M373, 0, Serialized)
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

        Name (NUM, 0x05)
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (BCF0, Buffer (0x08){})
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Name (I000, 0x00)
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
        SET0 (Z130, "m373", 0x00)
        /* ======================== Name */

        If (RN00)
        {
            Debug = "Name"
            _TCI (C200, Local0)
            Name (I100, 0x00)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            PP02 [C226] = 0x01 /* CLIST_ID_NAMESPACE */
            PP02 [C228] = 0x01 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x00)
        }

        If (RN00)
        {
            _TCI (C200, Local0)
            Name (S100, "qsdrtghyuiopmngsxz")
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x01 /* String */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            PP02 [C226] = 0x01 /* CLIST_ID_NAMESPACE */
            PP02 [C228] = 0x01 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x01)
            _TCI (C200, Local0)
            Name (B100, Buffer (0x10)
            {
                 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
            })
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C00B] = 0x01 /* Buffer */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP02 = M3A9 ()
            PP02 [C226] = 0x01 /* CLIST_ID_NAMESPACE */
            PP02 [C228] = 0x01 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x02)
            _TCI (C200, Local0)
            Name (P100, Package (0x10)
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
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x09 /* Integer */
            PP00 [C00C] = 0x01 /* Package */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP02 = M3A9 ()
            PP02 [C226] = 0x01 /* CLIST_ID_NAMESPACE */
            PP02 [C228] = 0x09 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x03)
        }

        If (RN00)
        {
            _TCI (C200, Local0)
            Name (P101, Package (0x10)
            {
                0x01,
                0x02,
                0x03,
                0x04,
                0x05,
                0x06,
                0x07,
                0x08,
                I000
            })
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x09 /* Integer */
            PP00 [C00C] = 0x01 /* Package */
            PP00 [C01C] = 0x01 /* LOCAL_REFERENCE */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP02 = M3A9 ()
            PP02 [C226] = 0x01 /* CLIST_ID_NAMESPACE */
            PP02 [C228] = 0x0A /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x04)
        }

        /* ======================== CreateField */

        If (RN00)
        {
            Debug = "CreateField"
            _TCI (C200, Local0)
            CreateField (BCF0, 0x01, 0x03, BF00)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            PP00 [C016] = 0x01 /* BufferField */
            PP00 [C024] = 0x01 /* LOCAL_EXTRA */
            PP01 = M3A8 ()
            PP01 [C009] = 0x02 /* Integer */
            PP02 = M3A9 ()
            PP02 [C226] = 0x01 /* CLIST_ID_NAMESPACE */
            PP02 [C228] = 0x02 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x05)
        }

        /* //////// Resource Descriptor macros */
        /* ======================== DMA */
        If (RN00)
        {
            Debug = "DMA"
            _TCI (C200, Local0)
            Name (RT00, ResourceTemplate () /* Integer */ /* Buffer */ /* Integer */ /* CLIST_ID_NAMESPACE */ /* CLIST_ID_OPERAND */
            {
                DMA (Compatibility, NotBusMaster, Transfer8, )
                    {}
            })
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01
            PP00 [C00B] = 0x01
            PP01 = M3A8 ()
            PP01 [C009] = 0x01
            PP02 = M3A9 ()
            PP02 [C226] = 0x01
            PP02 [C228] = 0x01
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x06)
        }

        /* ======================== DataTableRegion */

        If (RN00)
        {
            Debug = "DataTableRegion"
            _TCI (C200, Local0)
            DataTableRegion (HDR, "DSDT", "", "")
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00A] = 0x03 /* String */
            PP00 [C012] = 0x01 /* Operation Region */
            PP00 [C024] = 0x01 /* LOCAL_EXTRA */
            PP01 = M3A8 ()
            PP01 [C00A] = 0x03 /* String */
            PP02 = M3A9 ()
            PP02 [C226] = 0x01 /* CLIST_ID_NAMESPACE */
            PP02 [C228] = 0x02 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x07)
        }

        /* ======================== Field */

        If (RN04)
        {
            Debug = "Field"
            _TCI (C200, Local0)
            Field (R000, ByteAcc, NoLock, Preserve)
            {
                F000,   8
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C019] = 0x01 /* LOCAL_REGION_FIELD */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            PP02 [C228] = 0x01 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x08)
        }

        /* ======================== BankField */

        If (RN04)
        {
            Debug = "BankField"
            Field (R000, ByteAcc, NoLock, Preserve)
            {
                F001,   8
            }

            _TCI (C200, Local0)
            BankField (R000, F001, 0x00, ByteAcc, NoLock, Preserve)
            {
                BN00,   4
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01A] = 0x01 /* LOCAL_BANK_FIELD */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            PP02 [C228] = 0x01 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x09)
        }

        /* ======================== IndexField */

        If (RN04)
        {
            Debug = "IndexField"
            Field (R000, ByteAcc, NoLock, Preserve)
            {
                F002,   8,
                F003,   8
            }

            _TCI (C200, Local0)
            IndexField (F002, F003, ByteAcc, NoLock, Preserve)
            {
                IF00,   8,
                IF01,   8
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C01B] = 0x02 /* LOCAL_INDEX_FIELD */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            PP02 [C228] = 0x02 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x0A)
        }

        /* ======================== Event */

        If (RN00)
        {
            Debug = "Event"
            _TCI (C200, Local0)
            Event (E900)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00F] = 0x01 /* Event */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            PP02 [C226] = 0x01 /* CLIST_ID_NAMESPACE */
            PP02 [C228] = 0x01 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x0B)
        }

        /* ======================== Mutex */

        If (RN00)
        {
            Debug = "Mutex"
            _TCI (C200, Local0)
            Mutex (MT00, 0x00)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x01 /* Integer */
            PP00 [C011] = 0x01 /* Mutex */
            PP01 = M3A8 ()
            PP01 [C009] = 0x01 /* Integer */
            PP02 = M3A9 ()
            PP02 [C226] = 0x01 /* CLIST_ID_NAMESPACE */
            PP02 [C228] = 0x01 /* CLIST_ID_OPERAND */
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x0C)
        }

        /* ======================== OperationRegion */

        If (RN04)
        {
            Debug = "OperationRegion"
            _TCI (C200, Local0)
            OperationRegion (R001, SystemMemory, 0x0100, 0x0100)
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C009] = 0x02 /* Integer */
            /*	Store(1, Index(pp00, c012)) // OperationRegion */

            PP01 = M3A8 ()
            PP02 = M3A9 ()
            M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x0D)
        }

        /* ======================== Device */

        If (RN03)
        {
            /* Causes AE_AML_NAME_NOT_FOUND exception */

            Debug = "Device"
            _TCI (C200, Local0)
            Device (D000)
            {
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C00E] = 0x01 /* Device */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x0E)
        }

        /* ======================== Method */

        If (RN03)
        {
            /* Causes AE_AML_NAME_NOT_FOUND exception */

            Debug = "Method"
            _TCI (C200, Local0)
            Method (M000, 0, NotSerialized)
            {
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C010] = 0x01 /* Method */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x0F)
        }

        /* ======================== ThermalZone */

        If (RN03)
        {
            /* Causes AE_AML_NAME_NOT_FOUND exception */

            Debug = "ThermalZone"
            _TCI (C200, Local0)
            ThermalZone (TZ00)
            {
            }

            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C015] = 0x01 /* ThermalZone */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x10)
        }

        /* ======================== Processor */

        If (RN03)
        {
            /* Causes AE_AML_NAME_NOT_FOUND exception */

            Debug = "Processor"
            _TCI (C200, Local0)
            Processor (PR00, 0x00, 0xFFFFFFFF, 0x00){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C014] = 0x01 /* Processor */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x11)
        }

        /* ======================== PowerResource */

        If (RN03)
        {
            /* Causes AE_AML_NAME_NOT_FOUND exception */

            Debug = "PowerResource"
            _TCI (C200, Local0)
            PowerResource (PW00, 0x01, 0x0000){}
            _TCI (C201, PP0A)
            M3A3 (Local0, PP0A, Local1)
            PP00 = M3A8 ()
            PP00 [C013] = 0x01 /* PowerResource */
            PP01 = M3A8 ()
            PP02 = M3A9 ()
            M3A4 (Local0, PP0A, Local1, PP00, PP01, PP02, 0x12)
        }

        RST0 ()
    }
