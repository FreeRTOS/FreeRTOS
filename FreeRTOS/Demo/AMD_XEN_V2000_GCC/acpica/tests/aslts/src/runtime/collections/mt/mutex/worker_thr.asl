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
     * Run only for the Worker threads,
     * they wait there for the Control
     * thread says 'all is ready',
     * 'go further'.
     *
     * arg0 - Index of current thread
     */
    Method (M116, 1, NotSerialized)
    {
        While (0x01)
        {
            If (CTL0)
            {
                /* Control thread says 'all is ready' */

                Break
            }

            M201 (Arg0, VB03, "Sleep, waiting for Control thread")
            M206 (Arg0, SL01)
        }
    }

    /*
     * Infinite loop of the Worker Threads
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     * arg3 - the depth of recursion of call
     */
    Method (M101, 4, Serialized)
    {
        /*
         * These internal variables are specified only to show that
         * recursive calls to methods having internal declarations
         * (as well as Switch operators) of objects works.
         */
        Name (I000, 0xABCD0000)
        Name (I001, 0xABCD0001)
        Name (I002, 0xABCD0002)
        Name (I003, 0xABCD0003)
        Local0 = DerefOf (BS04 [Arg2])
        If (Local0)
        {
            Return (            /* Go everywhere to the exit to "Terminate thread" */

Zero)
        }

        /* Wait for Control thread saying 'go further' */

        M116 (Arg2)
        /*
         * Local0 - command for worker to be executed
         *
         * Local7 - non-zero means to do break after
         *          confirming "I see zero do00".
         *          Keep Local7 zero otherwise.
         */
        Local7 = 0x00
        While (0x01)
        {
            If ((Arg2 >= Arg0))
            {
                SE00 (Arg2, ER06, "Error er06")
            }

            /* Determine the command for particular thread */

            Local0 = C100 /* \C100 */
            /* Control thread allows for worker threads to fulfill their commands */

            If (DO00)
            {
                Local1 = DerefOf (BS01 [Arg2])
                /* This thread doesn't yet fulfill its command */

                If (!Local1)
                {
                    /* Command to be fulfilled */

                    Local0 = DerefOf (BS00 [Arg2])
                }

                /* Unnecessary */

                If (!DO00)
                {
                    Local0 = C100 /* \C100 */
                }
            }

            If (!DO00)
            {
                Local1 = DerefOf (BS02 [Arg2])
                If (!Local1)
                {
                    /* Worker thread reports: "I see zero do00" */

                    BS02 [Arg2] = RS00 /* \RS00 */
                    If (Local7)
                    {
                        M201 (Arg2, VB03, "Break completed: exit invinitive loop")
                        Break
                    }
                }
            }

            Switch (Local0)
            {
                Case (0xF0)
                {
                    /* c100 (Idle thread) */
                    /*
                     * This command is fulfilled by worker thread
                     * without directive of Control thread.
                     */
                    M201 (Arg2, VB03, "Sleep")
                    M206 (Arg2, SL01)
                    BS03 [Arg2] = C100 /* \C100 */
                }
                Case (0xF1)
                {
                    /* c101 */

                    M201 (Arg2, VB03, "Break started")
                    BS01 [Arg2] = C101 /* \C101 */
                    /*
                     * se00(3, 0x12345, "")
                     * break
                     *
                     * Note:
                     * Non-zero Local7 means to do break after
                     * confirming "I see zero do00".
                     * Keep Local7 zero in all other entries.
                     */
                    Local7 = 0x01
                }
                Case (0xF2)
                {
                    /* c102 */

                    M201 (Arg2, VB03, "Sleep, command")
                    M206 (Arg2, SL01)
                    BS01 [Arg2] = C102 /* \C102 */
                }
                Case (0xF3)
                {
                    /* c103 */

                    M201 (Arg2, VB03, "Acquire/Release")
                    /*
                     * Local1 - Level of mutex
                     * Local2 - number of Levels of mutexes (only 1 here)
                     * Local3 - Index of mutex
                     * Local4 - number of mutexes of the same level
                     */
                    Local1 = DerefOf (P200 [Arg2])
                    /* Local2 - number of Levels of mutexes is 1 here, not used */

                    Local3 = DerefOf (P202 [Arg2])
                    Local4 = DerefOf (P203 [Arg2])
                    While (Local4)
                    {
                        /* Acquire */

                        Local7 = M310 (Arg1, Arg2, Local1, Local3, 0x00, 0x00, 0x01)
                        If (!Local7)
                        {
                            /* Release */

                            M311 (Arg1, Arg2, Local1, Local3, 0x00, 0x01)
                        }

                        Local4--
                        Local3++
                    }

                    BS01 [Arg2] = C103 /* \C103 */
                    Local7 = 0x00 /* keep Local7 zero */
                }
                Case (0xF4)
                {
                    /* c104 */

                    M201 (Arg2, VB03, "c104")
                    /*
                     * Local1 - Level of mutex
                     * Local2 - number of Levels of mutexes (only 1 here)
                     * Local3 - Index of mutex
                     * Local4 - number of mutexes of the same level
                     */
                    /* Acquire mutexes from 0 up to 15 level */
                    Local2 = MAX0 /* \MAX0 */
                    Local1 = 0x00
                    While (Local2)
                    {
                        Local3 = DerefOf (P202 [Arg2])
                        Local4 = DerefOf (P203 [Arg2])
                        While (Local4)
                        {
                            M310 (Arg1, Arg2, Local1, Local3, 0x00, 0x00, 0x01)
                            Local4--
                            Local3++
                        }

                        Local2--
                        Local1++
                    }

                    /* Levels - in the inverse order */
                    /* Release mutexes from 15 down t0 0 level */
                    Local2 = MAX0 /* \MAX0 */
                    Local1 = (MAX0 - 0x01)
                    While (Local2)
                    {
                        Local3 = DerefOf (P202 [Arg2])
                        Local4 = DerefOf (P203 [Arg2])
                        /* Indexes - in the inverse order too */

                        Local3 += Local4
                        Local3--
                        While (Local4)
                        {
                            M311 (Arg1, Arg2, Local1, Local3, 0x00, 0x01)
                            Local4--
                            Local3--
                        }

                        Local2--
                        Local1--
                    }

                    BS01 [Arg2] = C104 /* \C104 */
                }
                Case (0xF5)
                {
                    /* c105 */

                    M201 (Arg2, VB03, "Example 0")
                    Local1 = 0x0A
                    While (Local1)
                    {
                        Switch (Arg2)
                        {
                            Case (0x02)
                            {
                                C0AB (Arg1, Arg2)
                            }
                            Case (0x04)
                            {
                                C0AB (Arg1, Arg2)
                            }
                            Case (0x06)
                            {
                                C0AB (Arg1, Arg2)
                            }
                            Default
                            {
                                C0A2 (Arg1, Arg2, 0x01, 0x01, 0x01)
                            }

                        }

                        Local1--
                    }

                    BS01 [Arg2] = C105 /* \C105 */
                }
                Case (0xF6)
                {
                    /* c106 */

                    M201 (Arg2, VB03, "Acquire specified set of mutexes")
                    /*
                     * Local0 - auxiliary
                     * Local1 - Level of mutex
                     * Local2 - number of Levels of mutexes (only 1 here)
                     * Local3 - Index of mutex
                     * Local4 - number of mutexes of the same level
                     * Local5 - non-zero means that we generate exceptional condition
                     * Local6 - opcode of TimeOutValue
                     * Local7 - auxiliary
                     */
                    Local1 = DerefOf (P200 [Arg2])
                    Local2 = DerefOf (P201 [Arg2])
                    While (Local2)
                    {
                        Local3 = DerefOf (P202 [Arg2])
                        Local4 = DerefOf (P203 [Arg2])
                        Local5 = DerefOf (P204 [Arg2])
                        Local6 = DerefOf (P205 [Arg2])
                        While (Local4)
                        {
                            Local7 = M111 (Arg1, Arg2, Local5, "Acquire")
                            Local0 = M310 (Arg1, Arg2, Local1, Local3, Local7, Local6, 0x01)
                            M112 (Arg1, Arg2, Local5, Local0)
                            Local4--
                            Local3++
                        }

                        Local2--
                        Local1++
                    }

                    BS01 [Arg2] = C106 /* \C106 */
                    Local7 = 0x00 /* keep Local7 zero */
                }
                Case (0xF7)
                {
                    /* c107 */

                    M201 (Arg2, VB03, "Release specified set of mutexes")
                    /*
                     * Local1 - Level of mutex
                     * Local2 - number of Levels of mutexes (only 1 here)
                     * Local3 - Index of mutex
                     * Local4 - number of mutexes of the same level
                     * Local5 - non-zero means that we generate exceptional condition
                     * Local7 - auxiliary
                     */
                    Local1 = DerefOf (P200 [Arg2])
                    Local2 = DerefOf (P201 [Arg2])
                    /* Levels - in the inverse order */

                    Local1 += Local2
                    Local1--
                    While (Local2)
                    {
                        Local3 = DerefOf (P202 [Arg2])
                        Local4 = DerefOf (P203 [Arg2])
                        Local5 = DerefOf (P204 [Arg2])
                        /* Indexes - in the inverse order too */

                        Local3 += Local4
                        Local3--
                        While (Local4)
                        {
                            Local7 = M111 (Arg1, Arg2, Local5, "Release")
                            M311 (Arg1, Arg2, Local1, Local3, Local7, 0x01)
                            M112 (Arg1, Arg2, Local5, 0x00)
                            Local4--
                            Local3--
                        }

                        Local2--
                        Local1--
                    }

                    BS01 [Arg2] = C107 /* \C107 */
                    Local7 = 0x00 /* keep Local7 zero */
                }
                Case (0xF8)
                {
                    /* c108 */

                    M201 (Arg2, VB03, "Terminate thread")
                    BS04 [Arg2] = 0x01
                    Break
                }
                Case (0xF9)
                {
                    /* c109 */

                    If (!Arg3)
                    {
                        M201 (Arg2, VB03, "Invoke Serialized method")
                        M8FC (Arg0, Arg1, Arg2)
                    }
                    Else
                    {
                        /*
                         * Only after falling down to the second recurcive call
                         * to m101 report that you are completed c109 command and
                         * ready handle following commands.
                         */
                        M201 (Arg2, VB03, "Recursive call to m101 for \'Invoke Serialized method\'")
                        BS01 [Arg2] = C109 /* \C109 */
                    }
                }
                Case (0xFA)
                {
                    /* c10a */

                    If (!Arg3)
                    {
                        M201 (Arg2, VB03, "Invoke non-serialized method, use Mutex for critical section")
                        M8FA (Arg0, Arg1, Arg2)
                    }
                    Else
                    {
                        /*
                         * Only after falling down to the second recurcive call
                         * to m101 report that you are completed c109 command and
                         * ready handle following commands.
                         */
                        M201 (Arg2, VB03, "Recursive call to m101 for \'Mutex for critical section\'")
                        BS01 [Arg2] = C10A /* \C10A */
                    }
                }
                Case (0xFB)
                {
                    /* c10b */

                    If (!Arg3)
                    {
                        M201 (Arg2, VB03, "Non-serialized method is grabbed simultaneously by several threads")
                        M8F9 (Arg0, Arg1, Arg2)
                    }
                    Else
                    {
                        /*
                         * Only after falling down to the second recurcive call
                         * to m101 report that you are completed c109 command and
                         * ready handle following commands.
                         */
                        M201 (Arg2, VB03, "Recursive call to m101 for \'Non-serialized method\'")
                        BS01 [Arg2] = C10B /* \C10B */
                    }
                }
                Default
                {
                    SE00 (Arg2, ER05, "Error er05")
                    M201 (Arg2, VB03, "Sleep, bad command")
                    Debug = Local0
                    M206 (Arg2, SL01)
                }

            }
        }
    }
