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
DefinitionBlock ("external", "SSDT", 2, "Intel", "Many", 0x00000001)
{
    /* All declarations */
    Include ("../../../../runtime/cntl/DECL.asl")
    Include ("../../../../runtime/collections/functional/external/DECL.asl")
    Method (MAIN, 0, NotSerialized)
    {
        /* Initialization */

        STRT (0x00)
        /* Run verification methods */
        Include ("../../../../runtime/collections/functional/external/RUN.asl")
        /* Final actions */

        Store (FNSH (), Local7)
        Return (Local7)
    }
}

DefinitionBlock ("external", "SSDT", 2, "Intel", "Many", 0x00000001)
{
    /* Name(EX00, UnknownObj) */

    Name (E000, 0x00)
    Name (E001, 0x01)
    Name (E002, "test string")
    Name (E003, Buffer (0x01)
    {
         0x00                                             // .
    })
    Name (E004, Package (0x00){})
    OperationRegion (E010, PCI_Config, Zero, 0xFF)
    Field (E010, AnyAcc, NoLock, Preserve)
    {
        E005,   8
    }

    Device (E006)
    {
    }

    Event (E007)
    Method (E008, 0, NotSerialized)
    {
        Return (0x01F4)
    }

    Mutex (E009, 0x00)
    PowerResource (E011, 0x00, 0x0000){}
    Processor (E012, 0x00, 0x00000001, 0x02){}
    ThermalZone (E013)
    {
    }

    CreateBitField (E003, 0x00, E014)
}

/*
 * bz 1389 test case provided by racerrehabman@gmail.com
 * This table should compile without error
 */
DefinitionBlock ("external", "SSDT", 2, "Intel", "Many", 0x00000001)
{
    External (RMCF.XPEE, IntObj)
    Device (RMCF)
    {
        Name (_ADR, 0x00)  // _ADR: Address
    }
}

/*
 * This is a variation on the table above. This should compile.
 */
DefinitionBlock ("external", "SSDT", 2, "Intel", "Many", 0x00000001)
{
    External (ABCD.XPEE, IntObj)
    External (ABCD.XPED, IntObj)
    Device (ABCD)
    {
        Name (_ADR, 0x00)  // _ADR: Address
        Name (XPEF, 0x00)
    }

    External (ABCD.XPEG, IntObj)
}
