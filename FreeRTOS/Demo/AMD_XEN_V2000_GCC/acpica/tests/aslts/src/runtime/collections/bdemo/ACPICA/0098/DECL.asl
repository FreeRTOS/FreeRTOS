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
     * Bug 0098:
     *
     * SUMMARY: Crash on a specific AML code
     */
    Method (ME51, 1, NotSerialized)
    {
        Local0 = ObjectType (Arg0)
        Debug = Local0
    }

    Method (ME52, 0, Serialized)
    {
        Name (RUN0, 0x01)
        Name (RUN1, 0x01)
        Name (RUN2, 0x01)
        Name (P000, Package (0x20)
        {
            0x00,
            DD08,
            SD01,
            BD04,
            0x00
        })
        Debug = "============= Test started:"
        If (RUN0)
        {
            Debug = "============= Integer:"
            Local0 = Local1 = P000 [0x01]
            Debug = Local1
            ME51 (Local1)
            Debug = Local0
        }

        If (RUN1)
        {
            Debug = "============= String:"
            Local0 = Local1 = P000 [0x02]
            Debug = Local1
            ME51 (Local1)
            Debug = Local0
        }

        If (RUN2)
        {
            Debug = "============= Buffer:"
            Local0 = Local1 = P000 [0x03]
            Debug = Local1
            ME51 (Local1)
            Debug = Local0
        }

        Debug = "============= Test finished."
    }

    /* Arg0 - the type of object */
    /* (for 8 (- Method) causes crash, Bug 0097) */
    Method (ME54, 1, Serialized)
    {
        Name (PD02, Package (0x20)
        {
            0x00,
            ID0C,
            SD02,
            BD05,
            PD02,
            FD02,
            DD09,
            ED01,
            ME53,
            MXD1,
            RD03,
            PWD0,
            PRD0,
            TZD0,
            BFD0
        })
        Debug = "============= Test started:"
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Debug = "============= Uninitialized:"
            }
            Case (0x01)
            {
                Debug = "============= Integer:"
                Local0 = Local1 = PD02 [0x01]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x02)
            {
                Debug = "============= String:"
                Local0 = Local1 = PD02 [0x02]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x03)
            {
                Debug = "============= Buffer:"
                Local0 = Local1 = PD02 [0x03]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x04)
            {
                Debug = "============= Package:"
                Local0 = Local1 = PD02 [0x04]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x05)
            {
                Debug = "============= Field Unit:"
                Local0 = Local1 = PD02 [0x05]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x06)
            {
                Debug = "============= Device:"
                Local0 = Local1 = PD02 [0x06]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x07)
            {
                Debug = "============= Event:"
                Local0 = Local1 = PD02 [0x07]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x08)
            {
                Debug = "============= Method:"
                Local0 = Local1 = PD02 [0x08]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x09)
            {
                Debug = "============= Mutex:"
                Local0 = Local1 = PD02 [0x09]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x0A)
            {
                Debug = "============= OperationRegion:"
                Local0 = Local1 = PD02 [0x0A]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x0B)
            {
                Debug = "============= PowerResource:"
                Local0 = Local1 = PD02 [0x0B]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x0C)
            {
                Debug = "============= Processor:"
                Local0 = Local1 = PD02 [0x0C]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x0D)
            {
                Debug = "============= ThermalZone:"
                Local0 = Local1 = PD02 [0x0D]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }
            Case (0x0E)
            {
                Debug = "============= Buffer Field:"
                Local0 = Local1 = PD02 [0x0E]
                Debug = Local1
                ME56 (Local1)
                Debug = Local0
            }

        } /* Switch */

        Debug = "============= Test finished."
    }

    /*
     * The same as me54 but all the cases are invoked not
     * one by one calling to the me54() Method with the next
     * in turn type of data but all the types of data are
     * exercised simultaneously  during one call to me55
     * method.
     */
    Method (ME55, 0, Serialized)
    {
        Name (PD02, Package (0x20)
        {
            0x00,
            ID0C,
            SD02,
            BD05,
            PD02,
            FD02,
            DD09,
            ED01,
            ME53,
            MXD1,
            RD03,
            PWD0,
            PRD0,
            TZD0,
            BFD0
        })
        Debug = "============= Test started:"
        /*	Switch (Arg0) { */
        /*	Case (0) { */
        Debug = "============= Uninitialized:"
        /*	} */
        /*	Case (1) { */
        Debug = "============= Integer:"
        Local0 = Local1 = PD02 [0x01]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (2) { */
        Debug = "============= String:"
        Local0 = Local1 = PD02 [0x02]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (3) { */
        Debug = "============= Buffer:"
        Local0 = Local1 = PD02 [0x03]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (4) { */
        Debug = "============= Package:"
        Local0 = Local1 = PD02 [0x04]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (5) { */
        Debug = "============= Field Unit:"
        Local0 = Local1 = PD02 [0x05]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (6) { */
        Debug = "============= Device:"
        Local0 = Local1 = PD02 [0x06]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (7) { */
        Debug = "============= Event:"
        Local0 = Local1 = PD02 [0x07]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*
         * Causes crash, Bug 0097
         *
         *	//	Case (8) {
         *			Store("============= Method:", Debug)
         *			Store(Index(pd02, 8, Local1), Local0)
         *			Store(Local1, Debug)
         *			me56(Local1)
         *			Store(Local0, Debug)
         *	//	}
         */
        /*	Case (9) { */
        Debug = "============= Mutex:"
        Local0 = Local1 = PD02 [0x09]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (10) { */
        Debug = "============= OperationRegion:"
        Local0 = Local1 = PD02 [0x0A]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (11) { */
        Debug = "============= PowerResource:"
        Local0 = Local1 = PD02 [0x0B]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (12) { */
        Debug = "============= Processor:"
        Local0 = Local1 = PD02 [0x0C]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (13) { */
        Debug = "============= ThermalZone:"
        Local0 = Local1 = PD02 [0x0D]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	Case (14) { */
        Debug = "============= Buffer Field:"
        Local0 = Local1 = PD02 [0x0E]
        Debug = Local1
        ME56 (Local1)
        Debug = Local0
        /*	} */
        /*	} // Switch */
        Debug = "============= Test finished."
    }

    Method (ME56, 1, NotSerialized)
    {
        Local0 = ObjectType (Arg0)
        Debug = Local0
    }

    Method (ME57, 0, NotSerialized)
    {
        ME54 (0x00)
        ME54 (0x01)
        ME54 (0x02)
        ME54 (0x03)
        ME54 (0x04)
        ME54 (0x05)
        ME54 (0x06)
        ME54 (0x07)
        /*
         * Causes crash, Bug 0097
         *		me54(8)
         */
        ME54 (0x09)
        ME54 (0x0A)
        ME54 (0x0B)
        ME54 (0x0C)
        ME54 (0x0D)
        ME54 (0x0E)
    }

    Method (ME58, 0, NotSerialized)
    {
        /*
         * Exercise one particular type of data
         * which is specified by Arg0.
         *
         * Arg0 - the type of object (0-14)
         * for 8 (Method) causes crash, Bug 0097
         */
        ME54 (0x0E)
        /*
         * Call to me54 for each type of data excluding
         * 8 (Method) (causes crash, Bug 0097).
         */
        ME57 ()
        /*
         * The same as me54 but all the cases are invoked not
         * one by one calling to the me54() Method with the next
         * in turn type of data but all the types of data are
         * exercised simultaneously  during one call to me55
         * method.
         */
        ME55 ()
    }
