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
     * Bug 47:
     *
     * SUMMARY: Timer operator doesn’t provide gradually increased values
     *
     * APPEARANCE
     *
     * The ASL Timer operator is declared as a 64-bit one
     * "17.5.117 Timer (Get 64-Bit Timer Value)" but actually,
     * we observe it is overrun during each 15 minutes, but we
     * expect that to be one time in more than 50 thousand years!
     *
     * SPECS (17.5.117)
     *
     * The value resulting from this opcode is 64-bits.
     * It is monotonically increasing, but it is not guaranteed
     * that every result will be unique,  i.e. two subsequent
     * instructions may return the same value. The only guarantee
     * is that each subsequent evaluation will be greater-than or
     * equal to the previous ones.
     *
     * Timer operator doesn’t provide
     * gradually increased values. The test takes long time,
     * and ends only when encounters error. Since the test is
     * based on Timer operator which is under testing and works
     * incorrectly we excluded this test from the normally run
     * tests set. We can't even control the time the run of test
     * is in progress from inside the test.
     */
    Method (MD77, 0, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (TSLP, 0x1388)    /* MilliSecs to sleep each cycle (5 secs) */
        Name (NCCL, 0xB4) /* Number of cycles */
        LPN0 = NCCL /* \MD77.NCCL */
        LPC0 = 0x00
        Local0 = (TSLP * LPN0) /* \MD77.LPN0 */
        Divide (Local0, 0x03E8, Local1, Local2)
        Debug = Concatenate ("Maximal time of execution (in seconds): 0x", Local2)
        Local0 = Timer
        Local5 = 0x00
        Debug = Concatenate ("Start value of Timer : 0x", Local0)
        While (LPN0)
        {
            Local7 = Timer
            Debug = Concatenate ("Timer: 0x", Local7)
            If ((Local0 > Local7))
            {
                /* if (Local5) { */

                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Local7)
                Debug = Concatenate ("Cur   timer    : 0x", Local7)
                Debug = Concatenate ("Start timer    : 0x", Local0)
                Debug = Concatenate ("Step of cycle  : 0x", TSLP)
                Break
                /* } */
                /* First time in more than 50 thousand years! */
                Local5 = 0x01
            }

            Sleep (TSLP)
            LPN0--
            LPC0++
        }

        Debug = Concatenate ("Start  timer: 0x", Local0)
        Debug = Concatenate ("Finish timer: 0x", Local7)
        Local6 = (Local7 - Local0)
        Local0 = TMR0 (Local6)
        Debug = Concatenate ("Run time (in seconds): 0x", Local0)
    }
