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
     * Check exceptions on storing
     */
    /* Run-method */
    Method (RES5, 0, NotSerialized)
    {
        Debug = "TEST: RES5, Exceptions on Result Object processing"
        /* Store */

        M689 ("RES5-m689", 0x00, 0x01)
        /*CopyObject */

        M689 ("RES5-m689", 0x01, 0x01)
        /* Increment */

        M692 (0x00, 0x01)
        /* Decrement */

        M692 (0x01, 0x01)
        /* Store the result of the explicit conversion operators */

        M693 (0x00, 0x01, B676, B677, 0x00)
        M693 (0x00, 0x01, B67D, B677, 0x01)
        /* CopyObject the result of the explicit conversion operators */

        M693 (0x01, 0x01, B676, B677, 0x00)
        M693 (0x01, 0x01, B67D, B677, 0x01)
        /* Optional storing of the result of the explicit conversion operators */

        M693 (0x02, 0x01, B676, B677, 0x00)
        M693 (0x02, 0x01, B67D, B677, 0x01)
        /* Store the result of the normal operators */

        M694 (0x00, 0x01, B676, B677, 0x00)
        M694 (0x00, 0x01, B67D, B677, 0x01)
        /* CopyObject the result of the normal operators */

        M694 (0x01, 0x01, B676, B677, 0x00)
        M694 (0x01, 0x01, B67D, B677, 0x01)
        /* Optional storing of the result of the normal operators */

        M694 (0x02, 0x01, B676, B677, 0x00)
        M694 (0x02, 0x01, B67D, B677, 0x01)
    }
