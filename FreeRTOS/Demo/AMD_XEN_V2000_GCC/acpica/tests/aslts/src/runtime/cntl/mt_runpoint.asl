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
     * Start points of execution for multi-threading mode
     */
    /* Flag of slack mode (non-zero - means slack mode) */
    Name (SLCK, 0x00)
    /*
     * Flag shows that the test has been run by means either
     * of MN00 or MN01 but not immediately by MAIN.
     * It is necessary to know in tests where the number of
     * preceding method calls is important.
     */
    Name (MLVL, 0x00)
    /*
     * ATTENTION: in future determine the actual SLCK mode
     * by accessing the table info or generating some exception
     * (see F64) and remove MN00 and MN01.
     *
     * Method applied to initiate normal (non-slack) mode.
     * Make sure that AcpiExec is actually in non-slack mode.
     */
    Method (MN00, 3, NotSerialized)
    {
        SLCK = 0x00
        MLVL = 0x01
        Local7 = MAIN (Arg0, Arg1, Arg2)
        Return (Local7)
    }

    /*
     * Method applied to initiate slack mode.
     * Make sure that AcpiExec is actually in slack mode.
     */
    Method (MN01, 3, NotSerialized)
    {
        SLCK = 0x01
        MLVL = 0x01
        Local7 = MAIN (Arg0, Arg1, Arg2)
        Return (Local7)
    }
