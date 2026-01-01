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
     * Bug 276:
     *
     * SUMMARY: 'Large Reference Count' on AML code with LoadTable/UnLoad in a slack mode
     *
     * Note: Check the result of this test manually that there are no
     *       'Large Reference Count' reported.
     *
     * Note: these 'Large Reference Count' could be detected automatically by Do utility
     */
    Method (MC76, 0, Serialized)
    {
        Name (ERR5, 0x00)
        Name (ERRS, 0x00)
        Name (TMT0, 0x00)
        Name (TCLL, 0x00)
        Name (RMRC, 0x00)
        Name (RP0P, Package (0x08){})
        Name (NRMT, "")
        Name (STST, "STST")
        Name (TCNP, Package (0x09)
        {
            "compilation",
            "functional",
            "complex",
            "exceptions",
            "bug-demo",
            "service",
            "mt",
            "Identity2MS",
            "IMPL"
        })
        Method (TCN0, 1, NotSerialized)
        {
            Local7 = "?"
            Local7 = DerefOf (TCNP [Arg0])
            Return (Local7)
        }

        Method (MMM0, 0, NotSerialized)
        {
            ERRS++
        }

        Method (MC73, 0, Serialized)
        {
            Name (DDBH, 0x00)
            Method (M000, 0, NotSerialized)
            {
            }

            Method (M001, 0, NotSerialized)
            {
            }

            DDBH = LoadTable ("OEM1", "", "", "", "", 0x01)
            MMM0 ()
            Unload (DDBH)
            Debug = "OEM1 unloaded"
        }

        Method (MMM2, 5, NotSerialized)
        {
        }

        Method (MMM3, 0, Serialized)
        {
            Name (B000, Buffer (0x04){})
            Concatenate (":", TCN0 (TCLL), Local1)
            Concatenate (Local1, ":", Local0)
            Concatenate (Local0, "?", Local1)
            Concatenate (Local1, ":", Local0)
            Concatenate (Local0, NRMT, Local1)
            Concatenate (Local1, ":", Local0)
            Local7 = (ERRS - ERR5) /* \MC76.ERR5 */
            Concatenate (Local0, "FAIL:Errors # ", Local2)
            Concatenate (Local2, Local7, Local0)
            Concatenate (Local0, Local1, Local2)
            Debug = Local2
            Concatenate (":", STST, Local2)
            Concatenate (Local2, Local1, Local0)
            RP0P [RMRC] = Local0
        }

        Method (MMM1, 0, NotSerialized)
        {
            MMM2 (0x00, 0x00, 0x00, 0x00, 0x00)
            MMM3 ()
        }

        Method (MMM4, 1, NotSerialized)
        {
            TMT0 = Timer
        }

        Method (MMM5, 0, NotSerialized)
        {
            MMM4 (0x00)
            MC73 ()
            MMM1 ()
        }

        MMM5 ()
    }
