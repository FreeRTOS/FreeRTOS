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
     * All the Packages are declared dynamically
     * (NumElements specified by arg0) as locals
     * of Methods.
     */
    Method (MD6E, 1, Serialized)
    {
        Name (P504, Package (Arg0){})
        MD6A (P504, 0x00010000, 0x00, 0x9345, 0x39, 0x0A, 0x0A)                /* maximal number of written elements to be verified */
    }

    Method (MD6F, 1, Serialized)
    {
        Name (P505, Package (Arg0){})
        MD6A (P505, 0x64, 0x00, 0x49, 0x13, 0x0A, 0x0A)                /* maximal number of written elements to be verified */
    }

    Method (MD70, 1, Serialized)
    {
        Name (P506, Package (Arg0){})
        MD6A (P506, 0xFF, 0x00, 0x11, 0x13, 0x0A, 0x0A)                /* maximal number of written elements to be verified */
    }

    Method (MD71, 1, Serialized)
    {
        Name (P000, Package (Arg0){})
        MD6A (P000, 0x0100, 0x00, 0x11, 0x13, 0x0A, 0x0A)                /* maximal number of written elements to be verified */
    }

    Method (MD72, 1, Serialized)
    {
        Name (P000, Package (Arg0){})
        MD6A (P000, 0x0101, 0x00, (0x0101 - 0x37), 0x37, 0x0A, 0x37)                /* maximal number of written elements to be verified */
    }

    Method (MD73, 0, NotSerialized)
    {
        MD6E (0x00010000)
        MD6F (0x64)
        MD70 (0xFF)
        MD71 (0x0100)
        MD72 (0x0101)
    }
