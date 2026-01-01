    /*
     To be investigated.
     Many Outstanding allocations on Reference ASLTS test run:
     Outstanding: 0xDB allocations after execution
     ACPI Error (utalloc-1053): 100(64) Outstanding allocations [20060127]
     .............. Output of test:
     (.......)
     [ACPI Debug] String: [0x25] ":STST:functional:reference:m26a:PASS:"
     [ACPI Debug] String: [0x3A] ":STST:functional:reference:m26b:FAIL:Errors # 11 00 00 00:"
     [ACPI Debug] String: [0x25] ":STST:functional:reference:m26c:PASS:"
     [ACPI Debug] String: [0x25] ":STST:functional:reference:m26d:PASS:"
     [ACPI Debug] String: [0x3A] ":STST:functional:reference:m26e:FAIL:Errors # 01 00 00 00:"
     [ACPI Debug] String: [0x25] ":STST:functional:reference:m26f:PASS:"
     [ACPI Debug] String: [0x25] ":STST:functional:reference:m270:PASS:"
     [ACPI Debug] String: [0x25] ":STST:functional:reference:m276:PASS:"
     [ACPI Debug] String: [0x0E] "========= END."
     [ACPI Debug] String: [0x5B] "TEST ACPICA: 64-bit : FAIL : Errors # 0x0000000000000016, Failed tests # 0x0000000000000004"
     Outstanding: 0xDB allocations after execution
     Execution of \MAIN returned object 00326E38 Buflen 10
     [Integer] = 0000000000000001
     - q
     0049CCB8 Len 0028 utcache-407 [Operand] Integer R1
     00495CB8 Len 0005 dsobject-333 [UNDEFINED]
     0048C488 Len 0028 utcache-407 [Operand] Integer R1
     0047F068 Len 0028 utcache-407 [Operand] BankField R1
     0047C108 Len 0028 utcache-407 [Operand] RegionField R1
     0047D178 Len 0028 utcache-407 [Operand] IndexField R1
     0047EB88 Len 0028 utcache-407 [Operand] BufferField R1
     0047CF68 Len 0028 utcache-407 [Operand] RegionField R1
     0047E5B8 Len 0028 utcache-407 [Operand] Extra R1
     0047FFC8 Len 0028 utcache-407 [Operand] RegionField R1
     0047CE98 Len 0028 utcache-407 [Operand] RegionField R1
     0047CAB8 Len 0028 utcache-407 [Operand] IndexField R1
     0047FDD8 Len 0028 utcache-407 [Operand] BankField R1
     0047D748 Len 0028 utcache-407 [Operand] RegionField R1
     0046A2A8 Len 0028 utcache-407 [Operand] RegionField R1
     00459598 Len 0028 utcache-407 [Operand] RegionField R1
     00452F68 Len 0028 utcache-407 [Operand] RegionField R1
     00452FC8 Len 0028 utcache-407 [Operand] Extra R1
     004511B8 Len 0005 dsobject-333 [UNDEFINED]
     004532F8 Len 0028 utcache-407 [Operand] BufferField R1
     00451098 Len 0028 utcache-407 [Operand] Buffer R1
     00472138 Len 0028 utcache-407 [Operand] Buffer R1
     00495748 Len 0028 utcache-407 [Operand] Extra R1
     004934A8 Len 0028 utcache-407 [Node] ????
     00495058 Len 0028 utcache-407 [Node] ????
     004950B8 Len 0028 utcache-407 [Operand] Extra R1
     004951D8 Len 0028 utcache-407 [Operand] Region R5
     00495298 Len 0028 utcache-407 [Node] ????
     00495358 Len 0028 utcache-407 [Node] ????
     00490C88 Len 0028 utcache-407 [Node] ????
     00495C58 Len 0028 utcache-407 [Operand] Region R5
     0048F4D8 Len 0028 utcache-407 [Node] ????
     0048CB78 Len 0028 utcache-407 [Node] ????
     00497DE8 Len 0028 utcache-407 [Node] ????
     00497F08 Len 0028 utcache-407 [Node] ????
     00493B68 Len 0028 utcache-407 [Node] ????
     00493BC8 Len 0028 utcache-407 [Node] ????
     00493E68 Len 0028 utcache-407 [Node] ????
     00492278 Len 0028 utcache-407 [Node] ????
     00492528 Len 0028 utcache-407 [Node] ????
     00492AF8 Len 0028 utcache-407 [Node] ????
     00492CD8 Len 0028 utcache-407 [Node] ????
     00496F68 Len 0028 utcache-407 [Node] ????
     004972B8 Len 0028 utcache-407 [Node] ????
     004973D8 Len 0028 utcache-407 [Node] ????
     0048CAB8 Len 0028 utcache-407 [Node] ????
     0048F7F8 Len 0028 utcache-407 [Node] ????
     0048F398 Len 0028 utcache-407 [Node] ????
     0048B068 Len 0028 utcache-407 [Node] ????
     0047B198 Len 0028 utcache-407 [Node] ????
     004914E8 Len 0028 utcache-407 [Node] ????
     00491EA8 Len 0028 utcache-407 [Node] ????
     00491F08 Len 0028 utcache-407 [Node] ????
     00481F08 Len 0028 utcache-407 [Node] ????
     0047D358 Len 0005 dsobject-333 [UNDEFINED]
     00494468 Len 0028 utcache-407 [Node] ????
     0048F458 Len 0028 utcache-407 [Node] ????
     0048F858 Len 0028 utcache-407 [Operand] BankField R1
     0048F8F8 Len 0028 utcache-407 [Operand] RegionField R1
     0048F958 Len 0028 utcache-407 [Operand] IndexField R1
     0048FA08 Len 0028 utcache-407 [Operand] BufferField R1
     0048FAA8 Len 0028 utcache-407 [Operand] RegionField R1
     0048FB58 Len 0028 utcache-407 [Operand] Extra R1
     0048FBB8 Len 0028 utcache-407 [Operand] RegionField R1
     0048FC68 Len 0028 utcache-407 [Operand] RegionField R1
     0048FCC8 Len 0028 utcache-407 [Operand] IndexField R1
     0048FDC8 Len 0028 utcache-407 [Operand] BankField R1
     0048FE78 Len 0028 utcache-407 [Operand] RegionField R1
     0048FED8 Len 0028 utcache-407 [Operand] RegionField R1
     0048E0C8 Len 0028 utcache-407 [Operand] RegionField R1
     0048E128 Len 0028 utcache-407 [Operand] RegionField R1
     0048E188 Len 0028 utcache-407 [Operand] Extra R1
     0048E238 Len 0005 dsobject-333 [UNDEFINED]
     0048E278 Len 0028 utcache-407 [Operand] BufferField R1
     0048E368 Len 0028 utcache-407 [Operand] Buffer R1
     0048E528 Len 0028 utcache-407 [Operand] Buffer R1
     0048E898 Len 0028 utcache-407 [Node] ????
     0048ED08 Len 0028 utcache-407 [Node] ????
     0048EF18 Len 0028 utcache-407 [Operand] Extra R1
     0048EFC8 Len 0028 utcache-407 [Operand] Region R5
     0048D0E8 Len 0028 utcache-407 [Operand] Region R5
     0048C938 Len 0028 utcache-407 [Operand] Extra R1
     0048BB48 Len 0028 utcache-407 [Node] ????
     00489648 Len 0028 utcache-407 [Node] ????
     00489708 Len 0028 utcache-407 [Node] ????
     00489828 Len 0028 utcache-407 [Node] ????
     00489B88 Len 0028 utcache-407 [Node] ????
     0047E948 Len 0005 dsobject-333 [UNDEFINED]
     00471428 Len 0028 utcache-407 [Operand] AddrHandler R5
     0046E618 Len 0028 utcache-407 [Operand] IndexField R4
     0046E678 Len 0028 utcache-407 [Operand] BankField R4
     0046E6D8 Len 0028 utcache-407 [Operand] RegionField R4
     0046E738 Len 0028 utcache-407 [Operand] RegionField R4
     0046E798 Len 0028 utcache-407 [Operand] RegionField R4
     0046E7F8 Len 0028 utcache-407 [Operand] RegionField R4
     0046E858 Len 0028 utcache-407 [Operand] Extra R1
     0046E8B8 Len 0028 utcache-407 [Operand] BufferField R4
     0046E968 Len 0028 utcache-407 [Operand] Buffer R4
     00459C68 Len 0028 utcache-407 [Operand] Extra R1
     00459CC8 Len 0028 utcache-407 [Operand] Region R20
     ACPI Error (utalloc-1053): 100(64) Outstanding allocations [20060127]
     #
     ..............................
     */
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
     * Bug 203 (local-bugzilla-348):
     *
     * SUMMARY: ObjectType operation falls into infinite loop for ring of RefOf references
     *
     * Note: add verifications while sorting out and fixing the bug (CH03/CH04/..)
     */
    Method (M813, 0, NotSerialized)
    {
        Method (M000, 0, NotSerialized)
        {
            Local1 = RefOf (Local0)
            Local2 = RefOf (Local1)
            Local0 = RefOf (Local2)
            Local7 = ObjectType (Local0)
            /* ? */

            If ((Local7 != C008))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local7, C008)
            }
                /* or RING_OF_REFS_EXCEPTION? */
        }

        M000 ()
    }
