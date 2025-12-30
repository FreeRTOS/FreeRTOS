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
     * Bug 0087:
     *
     * SUMMARY: Exception on Switch operator applied to the result of ToBuffer operator
     */
    Method (ME3C, 0, Serialized)
    {
        Name (B000, Buffer (0x01)
        {
             0x0A                                             // .
        })
        Name (S000, "qwrtyuiop")
        If (0x01)
        {
            /* This code shows that ToBuffer() works correctly */

            Debug = "======================: ToBuffer(Buffer)"
            Local0 = ToBuffer (B000)
            Debug = Local0
            Local1 = ObjectType (Local0)
            Debug = Local1
            Local2 = SizeOf (Local0)
            Debug = Local2
            Debug = "======================: ToBuffer(String)"
            Local0 = ToBuffer (S000)
            Debug = Local0
            Local1 = ObjectType (Local0)
            Debug = Local1
            Local2 = SizeOf (Local0)
            Debug = Local2
            Debug = "======================."
        }

        /* This code shows that ToBuffer() causes exceptions in cases #2, #3 */
        /*		if (0) { */
        /* Case 1 */
        Switch (Buffer (0x01)
                {
                     0x0A                                             // .
                })
            {
            Case ("N")
            {
                Debug = "Case     (A)"
            }
            Default
            {
                Debug = "Default  (A)"
            }

        }

        /*		} elseif (1) { */
        /* Case 2 */
        Switch (ToBuffer (Buffer (0x01)
                    {
                         0x0A                                             // .
                    }))
        {
            Case ("N")
            {
                Debug = "Case     (B)"
            }
            Default
            {
                Debug = "Default  (B)"
            }

        }

        /*		} else { */
        /* Case 3 */
        Switch (ToBuffer (B000))
        {
            Case ("N")
            {
                Debug = "Case     (C)"
            }
            Default
            {
                Debug = "Default  (C)"
            }

        }
        /*		} */
    }
