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
     * Synchronization (events)
     */
    /*
     !!!!!!!!!!!!!!!!!!!!!!!!!!!!
     SEE: should be a few updated
     !!!!!!!!!!!!!!!!!!!!!!!!!!!!
     */
    /* The test for ASL-Events to be run on a single invocation only */
    /* */
    /* Note: additional checkings should be implemented to measure */
    /*       the actual idle time provided by Wait operator according */
    /*       to the time measuring provided by the Timer operator. */
    /* Pass TimeoutValues for Wait globally (all locals busy) */
    Name (TOT0, 0x00)
    Name (TOT1, 0x00)
    Name (TOT2, 0x00)
    Name (TOT3, 0x00)
    /* All events */

    Event (EVT0)
    Event (EVT1)
    Event (EVT2)
    Event (EVT3)
    /* Wait, expected Zero */

    Method (M050, 5, NotSerialized)
    {
        If (0x00)
        {
            Debug = "m050: Wait, expected Zero"
        }

        If (Arg1)
        {
            CH00 (Arg0, 0x00, 0x00, Wait (EVT0, TOT0))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x00, 0x01, Wait (EVT1, TOT1))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x00, 0x02, Wait (EVT2, TOT2))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x00, 0x03, Wait (EVT3, TOT3))
        }
    }

    /* Wait, expected Non-Zero */

    Method (M051, 5, NotSerialized)
    {
        If (0x00)
        {
            Debug = "m051: Wait, expected Non-Zero"
        }

        If (Arg1)
        {
            CH01 (Arg0, 0x01, 0x00, Wait (EVT0, TOT0))
        }

        If (Arg2)
        {
            CH01 (Arg0, 0x01, 0x01, Wait (EVT1, TOT1))
        }

        If (Arg3)
        {
            CH01 (Arg0, 0x01, 0x02, Wait (EVT2, TOT2))
        }

        If (Arg4)
        {
            CH01 (Arg0, 0x01, 0x03, Wait (EVT3, TOT3))
        }
    }

    /* Signal */

    Method (M052, 5, NotSerialized)
    {
        If (0x00)
        {
            Debug = "m052: Signal"
        }

        If (Arg1)
        {
            Signal (EVT0)
        }

        If (Arg2)
        {
            Signal (EVT1)
        }

        If (Arg3)
        {
            Signal (EVT2)
        }

        If (Arg4)
        {
            Signal (EVT3)
        }
    }

    /* Reset */

    Method (M053, 5, NotSerialized)
    {
        If (0x00)
        {
            Debug = "m053: Reset"
        }

        If (Arg1)
        {
            Reset (EVT0)
        }

        If (Arg2)
        {
            Reset (EVT1)
        }

        If (Arg3)
        {
            Reset (EVT2)
        }

        If (Arg4)
        {
            Reset (EVT3)
        }
    }

    /*
     * Package:={N lines}
     * Line:= consists of 6 elements:
     *   0:     operation:
     *          0 - Wait, expected Zero     (acquired)
     *          1 - Wait, expected Non-Zero (failed to acquire)
     *          2 - Signal
     *          3 - Reset
     *   1:     bit-mask of events operation to be applied to which
     *          bit 0x08 - 0th event
     *          bit 0x04 - 1th event
     *          bit 0x02 - 2th event
     *          bit 0x01 - 3th event
     *   2-5:   TimeoutValues for Wait operations (left->right too)
     */
    Name (P011, Package (0xF0)
    {
        /* 1. Wait without signals results in non-zero (failed to acquire) */
        /* 2. Applied to all 4 event-Objects */
        0x01,
        0x0F,
        0x00,
        0x01,
        0x02,
        0xFF,
        0x01,
        0x0F,
        0x01,
        0x02,
        0x03,
        0x04,
        0x01,
        0x0F,
        0x11,
        0x22,
        0x33,
        0x00,
        /* 1. Send Ni signals to i-th Object. */
        /* 2. All Ni events of i-th Object are successfully one */
        /*    by one acquired by Ni Waits applied to that Object. */
        /* 3. But, attempt to acquire one more failed. */
        /* 4. Applied to all 4 event-Objects. */
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x0F,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0x00,
        0x0F,
        0x8000,
        0x4000,
        0x2000,
        0x1000,
        0x00,
        0x0F,
        0x01,
        0x02,
        0x03,
        0x04,
        0x00,
        0x0F,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0x01,
        0x0F,
        0x01,
        0x02,
        0x03,
        0x04,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x07,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x03,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x01,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x01,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0x00,
        0x03,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0x00,
        0x07,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0x00,
        0x0F,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0xFFFF,
        0x01,
        0x0F,
        0x01,
        0x02,
        0x03,
        0x04,
        /* 1. Send Ni_s signals to i-th Object. */
        /* 2. Reset i-th object, one time. */
        /* 3. Wait of i-th Object results in non-zero (failed to acquire) */
        /* 4. Applied to all 4 event-Objects. */
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x03,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x01,
        0x0F,
        0x01,
        0x02,
        0x03,
        0x04,
        0x01,
        0x0F,
        0x01,
        0x02,
        0x03,
        0x04,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x0F,
        0x00,
        0x00,
        0x00,
        0x00,
        0x03,
        0x0A,
        0x00,
        0x00,
        0x00,
        0x00,
        0x01,
        0x0A,
        0x01,
        0x02,
        0x03,
        0x04,
        0x00,
        0x05,
        0x01,
        0x02,
        0x03,
        0x04,
        0x00,
        0x05,
        0x01,
        0x02,
        0x03,
        0x04,
        0x00,
        0x05,
        0x01,
        0x02,
        0x03,
        0x04,
        0x00,
        0x05,
        0x01,
        0x02,
        0x03,
        0x04,
        0x01,
        0x0F,
        0x01,
        0x02,
        0x03,
        0x04,
        /* For to track the current state only: */
        /* Wait() allows TimeoutValue greater then */
        /* 0xffff though cuts it to 16 bits. */
        0x01,
        0x0F,
        0x00010000,
        0x00010000,
        0x00010000,
        0x00010000
    })
    /*
     * Run operations one by one in accordance with the table passed by arg2.
     * arg1 - number of operations.
     */
    Method (M060, 4, NotSerialized)
    {
        Local7 = 0x00
        While (Arg1)
        {
            Local6 = (Local7 * 0x06)
            Local5 = DerefOf (Arg2 [Local6])
            Local6++
            Local1 = DerefOf (Arg2 [Local6])
            /* TimeoutValues for Wait */

            Local6++
            TOT0 = DerefOf (Arg2 [Local6])
            Local6++
            TOT1 = DerefOf (Arg2 [Local6])
            Local6++
            TOT2 = DerefOf (Arg2 [Local6])
            Local6++
            TOT3 = DerefOf (Arg2 [Local6])
            /* Local1 - run 0th event */

            Local2 = 0x00    /* run 1th event */
            Local3 = 0x00    /* run 2th event */
            Local4 = 0x00    /* run 3th event */
            If ((Local1 & 0x04))
            {
                Local2 = 0x01
            }

            If ((Local1 & 0x02))
            {
                Local3 = 0x01
            }

            If ((Local1 & 0x01))
            {
                Local4 = 0x01
            }

            If ((Local1 & 0x08))
            {
                Local1 = 0x01
            }
            Else
            {
                Local1 = 0x00
            }

            If ((Local5 == 0x00))
            {
                M050 (Arg0, Local1, Local2, Local3, Local4)
            }
            ElseIf ((Local5 == 0x01))
            {
                M051 (Arg0, Local1, Local2, Local3, Local4)
            }
            ElseIf ((Local5 == 0x02))
            {
                M052 (Arg0, Local1, Local2, Local3, Local4)
            }
            ElseIf ((Local5 == 0x03))
            {
                M053 (Arg0, Local1, Local2, Local3, Local4)
            }

            Local7++
            Arg1--
        }
    }

    Method (WAI0, 0, Serialized)
    {
        Debug = "TEST: WAI0, Wait for Events"
        M060 (__METHOD__, 0x28, P011, "p011")
    }

    /* Run-method */

    Method (EVN0, 0, NotSerialized)
    {
        Debug = "TEST: EVN0, Events"
        WAI0 ()
    }
