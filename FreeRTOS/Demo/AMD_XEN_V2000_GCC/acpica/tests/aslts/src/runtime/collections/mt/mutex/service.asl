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
     * Service routines of common use
     */
    Name (Z153, 0x99)
    /*
     * Fill the buffer with the same value
     *
     * arg0 - buffer
     * arg1 - the length of buffer
     * arg2 - the value
     */
    Method (M200, 3, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        LPN0 = Arg1
        LPC0 = 0x00
        While (LPN0)
        {
            /* For not a Control thread only */

            If ((LPC0 != 0x00))
            {
                Arg0 [LPC0] = Arg2
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * Fill the region of buffer with the same value
     *
     * arg0 - buffer
     * arg1 - the length of buffer
     * arg2 - the value
     *
     * arg3 - start index
     * arg4 - the length of region to be filled
     *        0 - everywhere from index to the end of buffer
     * arg5 - if non-zero than fill the ground value arg6 into the buffer
     *        everywhere outside the specified region
     * arg6 - the value of ground
     */
    Method (M210, 7, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (SZ01, 0x00)
        Name (IX02, 0x00)
        If ((Arg3 >= Arg1))
        {
            ERR ("m210", Z153, __LINE__, 0x00, 0x00, Arg3, Arg1)
            Return (Zero)
        }

        /* Sizes of fields */

        If (Arg4)
        {
            SZ01 = Arg4
        }
        Else
        {
            SZ01 = (Arg1 - Arg3)
        }

        IX02 = (Arg3 + SZ01) /* \M210.SZ01 */
        If ((IX02 > Arg1))
        {
            ERR ("m210", Z153, __LINE__, 0x00, 0x00, IX02, Arg1)
            Debug = Arg1
            Debug = Arg3
            Debug = Arg4
            Debug = Arg5
            Return (Zero)
        }

        If (Arg5)
        {
            LPN0 = Arg1
            LPC0 = 0x00
        }
        Else
        {
            LPN0 = SZ01 /* \M210.SZ01 */
            LPC0 = Arg3
        }

        While (LPN0)
        {
            If (((LPC0 < Arg3) || (LPC0 >= IX02)))
            {
                Local0 = Arg6
            }
            Else
            {
                Local0 = Arg2
            }

            Arg0 [LPC0] = Local0
            LPN0--
            LPC0++
        }
    }

    /*
     * Report message of thread
     * (adds index of thread and reports the message)
     *
     * arg0 - Index of current thread
     * arg1 - s-flag of verbal mode
     * arg2 - string
     */
    Method (M201, 3, NotSerialized)
    {
        If (Arg1)
        {
            Concatenate ("THREAD ", Arg0, Local0)
            Concatenate (Local0, ": ", Local1)
            Concatenate (Local1, Arg2, Local0)
            Debug = Local0
        }
    }

    /*
     * Report the message conditionally according to the relevant
     * flag of verbal mode.
     *
     * arg0 - Index of current thread
     * arg1 - mc-flag of verbal mode
     * arg2 - if do printing actually (or only return flag)
     * arg3 - message - object to be sent to Debug
     */
    Method (M202, 4, Serialized)
    {
        Local0 = 0x00
        Switch (Arg1)
        {
            Case (0x01)
            {
                /* allow only for Control Thread to report */

                If (!Arg0)
                {
                    Local0 = 0x01
                }
            }
            Case (0x02)
            {
                /* allow only for Worker Threads to report */

                If (Arg0)
                {
                    Local0 = 0x01
                }
            }
            Case (0x03)
            {
                /* allow for all threads to report */

                Local0 = 0x01
            }

        }

        If ((Local0 && Arg2))
        {
            Debug = Arg3
        }

        Return (Local0)
    }

    /*
     * Report start of test
     *
     * arg0 - name of test
     * arg1 - number of threads
     * arg2 - ID of current thread
     * arg3 - Index of current thread
     */
    Method (M204, 4, NotSerialized)
    {
        If (M202 (Arg3, VB01, 0x00, 0x00))
        {
            Concatenate ("Test ", Arg0, Local0)
            Concatenate (Local0, " started", Local1)
            Concatenate (Local1, ", threads num ", Local0)
            Concatenate (Local0, Arg1, Local1)
            Concatenate (Local1, ", ID of thread ", Local0)
            Concatenate (Local0, Arg2, Local1)
            Concatenate (Local1, ", Index of thread ", Local0)
            Concatenate (Local0, Arg3, Local1)
            Debug = Local1
        }
    }

    /*
     * Fulfill and report Sleep
     *
     * arg0 - Index of current thread
     * arg1 - number of milliseconds to sleep
     */
    Method (M206, 2, NotSerialized)
    {
        M201 (Arg0, VB03, "Sleep")
        /* Increment statistics of Sleep */

        If ((VB04 && CTL0))
        {
            M212 (RefOf (P104), Arg0)
        }

        Sleep (Arg1)
    }

    /*
     * Fulfill and report Stall
     *
     * arg0 - Index of current thread
     * arg1 - number of MicroSeconds to Stall
     */
    Method (M207, 2, NotSerialized)
    {
        M201 (Arg0, VB03, "Stall")
        Stall (Arg1)
    }

    /*
     * Put the value into i-th element of the buffer
     *
     * arg0 - buffer
     * arg1 - index
     * arg2 - the value
     */
    Method (M208, 3, NotSerialized)
    {
        Arg0 [Arg1] = Arg2
    }

    /*
     * Set up a sleeping mode
     *
     * arg0 - opcode of sleeping mode
     */
    Method (M209, 0, Serialized)
    {
        /* Milliseconds to sleep for non-zero slm0 */

        Switch (0x00)
        {
            Case (0x00)
            {
                I100 = 0x0A
                I101 = 0x0A
                I102 = 0x0A
                I103 = 0x0A
                I104 = 0x0A
                I105 = 0x0A
                I106 = 0x0A
                I107 = 0x0A
                I108 = 0x0A
            }
            Default
            {
                I100 = 0x32
                I101 = 0x64
                I102 = 0xC8
                I103 = 0x0190
                I104 = 0x01F4
                I105 = 0x4B
                I106 = 0x96
                I107 = 0xFA
                I108 = 0x012C
            }

        }
    }

    /*
     * Fill specified elements of buffer with the same value
     *
     * arg0 - buffer
     * arg1 - the length of buffer
     * arg2 - the value
     * arg3 - specificator of elements:
     *        Integer - all elements of arg0
     *        Buffer  - for non-zero elements of arg3 only
     */
    Method (M20A, 4, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (SLCT, 0x00)
        Name (RUN0, 0x00)
        Local0 = ObjectType (Arg3)
        If ((Local0 != C009))
        {
            SLCT = 0x01
        }

        LPN0 = Arg1
        LPC0 = 0x00
        While (LPN0)
        {
            RUN0 = 0x01
            If (SLCT)
            {
                RUN0 = DerefOf (Arg3 [LPC0])
            }

            If (RUN0)
            {
                Arg0 [LPC0] = Arg2
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * Print out all the auxiliary buffers
     *
     * arg0 - Index of current thread
     * arg1 - message
     */
    Method (M20B, 2, NotSerialized)
    {
        Concatenate ("Print out the auxiliary buffers (bs00,bs01,bs02) <", Arg1, Local0)
        Concatenate (Local0, ">", Local1)
        M201 (Arg0, 0x01, Local1)
        M201 (Arg0, 0x01, BS00)
        M201 (Arg0, 0x01, BS01)
        M201 (Arg0, 0x01, BS02)
        M201 (Arg0, 0x01, BS03)
    }

    /*
     * Return numbers of threads Buffer
     *
     * arg0 - number of threads (total)
     * arg1 - number of threads (threads actually in work, not extra idle ones)
     */
    Method (M20D, 2, Serialized)
    {
        Name (NTH0, Buffer (0x02){})
        NTH0 [0x00] = Arg0
        NTH0 [0x01] = Arg1
        Return (NTH0) /* \M20D.NTH0 */
    }

    /*
     * Prepare the exceptional conditions flags buffer
     *
     * arg0 - number of threads
     * arg1 - Exceptional conditions flags (buffer/Integer)
     */
    Method (M20E, 2, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Local0 = ObjectType (Arg1)
        If ((Local0 != C009))
        {
            /* Not Integer */

            Return (Arg1)
        }

        Name (B000, Buffer (Arg0){})
        LPN0 = Arg0
        LPC0 = 0x00
        While (LPN0)
        {
            /* Flag of exceptional condition */

            B000 [LPC0] = Arg1
            LPN0--
            LPC0++
        }

        Return (B000) /* \M20E.B000 */
    }

    /*
     * Initialize the exceptional conditions flags (p204 & FLG0)
     * (initialize expectation of exceptions).
     *
     * arg0 - number of threads
     * arg1 - exceptional conditions flags (buffer/Integer)
     * arg2 - non-zero means to check absence of exception
     *        before and after each operation additionally
     *        to the checking (if any) specified per-operation.
     */
    Method (M20F, 3, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (SLCT, 0x00)
        Name (EX00, 0x00)
        Local0 = ObjectType (Arg1)
        If ((Local0 == C009))
        {
            /* Integer */

            EX00 = Arg1
        }
        Else
        {
            /* Buffer/Package */

            SLCT = 0x01
        }

        LPN0 = Arg0
        LPC0 = 0x00
        While (LPN0)
        {
            If (SLCT)
            {
                /* Flag of exceptional condition */

                EX00 = DerefOf (Arg1 [LPC0])
            }

            P204 [LPC0] = EX00 /* \M20F.EX00 */
            LPN0--
            LPC0++
        }

        FLG0 = Arg2
    }

    /*
     * Initialize the TimeOutValue mapping buffer
     *
     * arg0 - number of threads (total)
     * arg1 - number of threads (threads actually in work)
     * arg2 - (buffer/Integer) of TimeOutValue
     */
    Method (M214, 3, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (SLCT, 0x00)
        Name (TOPC, 0x00)
        Local0 = ObjectType (Arg2)
        If ((Local0 == C009))
        {
            /* Integer */

            TOPC = Arg2
        }
        Else
        {
            /* Buffer/Package */

            SLCT = 0x01
        }

        LPN0 = Arg1
        LPC0 = 0x00
        While (LPN0)
        {
            If (SLCT)
            {
                TOPC = DerefOf (Arg2 [LPC0])
            }

            P205 [LPC0] = TOPC /* \M214.TOPC */
            LPN0--
            LPC0++
        }
    }

    /*
     * Reset TimeOutValue and exceptional conditions flags to default
     *
     * arg0 - number of threads (total)
     */
    Method (M215, 1, NotSerialized)
    {
        M20F (Arg0, 0x00, 0x00)       /* Reset the exceptional conditions flags */
        M214 (Arg0, Arg0, TOVF) /* Set TimeOutValue to default */
    }

    /*
     * Report statistics
     *
     * arg0 - number of threads
     */
    Method (M211, 1, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        /* global data not initialized */

        If (!GLDI)
        {
            Return (Zero)
        }

        Debug = "================ Per-thread statistics: ================"
        Local0 = "Errors   scale   : "
        Local1 = "          number : "
        Local2 = "Warnings   scale : "
        Local3 = "          number : "
        Local4 = "Sleep     number : "
        Local5 = "Acquire   number : "
        Local6 = "Release   number : "
        LPN0 = Arg0
        LPC0 = 0x00
        While (LPN0)
        {
            Local7 = DerefOf (P100 [LPC0])
            Concatenate (Local0, Local7, Local0)
            If ((LPN0 != 0x01))
            {
                Concatenate (Local0, ", ", Local0)
            }

            Local7 = DerefOf (P101 [LPC0])
            Concatenate (Local1, Local7, Local1)
            If ((LPN0 != 0x01))
            {
                Concatenate (Local1, ", ", Local1)
            }

            Local7 = DerefOf (P102 [LPC0])
            Concatenate (Local2, Local7, Local2)
            If ((LPN0 != 0x01))
            {
                Concatenate (Local2, ", ", Local2)
            }

            Local7 = DerefOf (P103 [LPC0])
            Concatenate (Local3, Local7, Local3)
            If ((LPN0 != 0x01))
            {
                Concatenate (Local3, ", ", Local3)
            }

            Local7 = DerefOf (P104 [LPC0])
            Concatenate (Local4, Local7, Local4)
            If ((LPN0 != 0x01))
            {
                Concatenate (Local4, ", ", Local4)
            }

            Local7 = DerefOf (P105 [LPC0])
            Concatenate (Local5, Local7, Local5)
            If ((LPN0 != 0x01))
            {
                Concatenate (Local5, ", ", Local5)
            }

            Local7 = DerefOf (P106 [LPC0])
            Concatenate (Local6, Local7, Local6)
            If ((LPN0 != 0x01))
            {
                Concatenate (Local6, ", ", Local6)
            }

            LPN0--
            LPC0++
        }

        Debug = Local0
        Debug = Local1
        Debug = Local2
        Debug = Local3
        Debug = Local4
        Debug = Local5
        Debug = Local6
        Concatenate ("Exceptions total : ", EX10, Debug)
        Debug = "========================================================"
    }

    /*
     * Increment element of Package
     *
     * arg0 - RefOf of Package
     * arg1 - index of element
     */
    Method (M212, 2, NotSerialized)
    {
        Local0 = DerefOf (DerefOf (Arg0) [Arg1])
        Local0++
        DerefOf (Arg0) [Arg1] = Local0
    }

    /*
     * Return the number of threads to be the number of threads actually in work
     * (including Control thread).
     * Should be not less than 3.
     *
     * Note: to be provided that arg0 is not less than the test needs
     *       to perform effective checking according to its scenario.
     *
     * arg0 - number of threads (total)
     * arg1 - maximal number of threads according to scenario of test (including Control thread)
     * arg2 - if non-zero, then the number of treads to be actually in work in reduced mode (including Control thread)
     */
    Method (M213, 3, Serialized)
    {
        Name (NUM, 0x00)
        NUM = Arg0
        If (Arg1)
        {
            NUM = Arg1
        }

        If (REDM)
        {
            If (Arg2)
            {
                NUM = Arg2
            }
        }

        If ((Arg0 < NUM))
        {
            NUM = Arg0
        }

        Return (NUM) /* \M213.NUM_ */
    }
