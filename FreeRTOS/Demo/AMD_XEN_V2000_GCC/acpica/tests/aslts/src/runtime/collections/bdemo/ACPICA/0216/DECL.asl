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
     * Bug 216(local-bugzilla-341):
     *
     * SUMMARY: exception AE_NOT_FOUND on CreateField under specific conditions
     *
     * Failed to find Buffer for CreateField both declared inside
     * some of these types: Device/ThermalZone/Processor/PowerResource
     * which in turn are declared inside some method thus created
     * dynamically.
     *
     * APPEARANCE:
     * Call method which declares object of any of these types:
     *    Device
     *    ThermalZone
     *    Processor
     *    PowerResource
     * which contains internal declarations of Buffer of name which
     * there are no in the higher levels and run CreateField for that
     * Buffer. If run method then get mentioned exception.
     *
     * May suspect, at first glance, that if the name of that Buffer fit
     * the name of some higher level Buffer (no exception in that case)
     * then CreateField deals with that higher level Buffer. Though, the
     * example with dd12 doesn't count in favour of that reason.
     *
     * Note: add verifications while fixing the bug (access to Buffer Fields..).
     */
    /* ======== 0 ======= */
    Name (BD11, Buffer (0x05)
    {
         0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
    })
    Name (BD12, Buffer (0x05)
    {
         0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
    })
    Device (DD12)
    {
    }

    Device (DD0E)
    {
        Name (BD13, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD13, 0x00, 0x08, BF00)
    }

    ThermalZone (TZD3)
    {
        Name (BD13, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD13, 0x00, 0x08, BF00)
    }

    Processor (PRD3, 0x00, 0xFFFFFFFF, 0x00)
    {
        Name (BD13, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD13, 0x00, 0x08, BF00)
    }

    PowerResource (PWD3, 0x01, 0x0000)
    {
        Name (BD13, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD13, 0x00, 0x08, BF00)
    }

    Method (M81E, 0, Serialized)
    {
        Name (BD13, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD13, 0x00, 0x08, BF00)
    }

    /* ======== 1 ======= */

    Device (DD0F)
    {
        Name (BD11, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD11, 0x00, 0x08, BF00)
    }

    ThermalZone (TZD4)
    {
        Name (BD11, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD11, 0x00, 0x08, BF00)
    }

    Processor (PRD4, 0x00, 0xFFFFFFFF, 0x00)
    {
        Name (BD11, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD11, 0x00, 0x08, BF00)
    }

    PowerResource (PWD4, 0x01, 0x0000)
    {
        Name (BD11, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD11, 0x00, 0x08, BF00)
    }

    Method (M81F, 0, Serialized)
    {
        Name (BD11, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD11, 0x00, 0x08, BF00)
    }

    /* ======== 2 ======= */

    Device (DD10)
    {
        CreateField (BD11, 0x00, 0x08, BF00)
    }

    ThermalZone (TZD5)
    {
        CreateField (BD11, 0x00, 0x08, BF00)
    }

    Processor (PRD5, 0x00, 0xFFFFFFFF, 0x00)
    {
        CreateField (BD11, 0x00, 0x08, BF00)
    }

    PowerResource (PWD5, 0x01, 0x0000)
    {
        CreateField (BD11, 0x00, 0x08, BF00)
    }

    Method (M820, 0, NotSerialized)
    {
        CreateField (BD11, 0x00, 0x08, BF00)
    }

    /* ======== 3 ======= */

    Device (DD11)
    {
        /* ======== 0 ======= */

        Name (BD13, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD13, 0x00, 0x08, BF00)
        Device (DD0E)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD3)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        Processor (PRD3, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        PowerResource (PWD3, 0x01, 0x0000)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        Method (M81E, 0, Serialized)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        /* ======== 1 ======= */

        Device (DD0F)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD4)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Processor (PRD4, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        PowerResource (PWD4, 0x01, 0x0000)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Method (M81F, 0, Serialized)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        /* ======== 2 ======= */

        Device (DD10)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD5)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Processor (PRD5, 0x00, 0xFFFFFFFF, 0x00)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        PowerResource (PWD5, 0x01, 0x0000)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Method (M820, 0, NotSerialized)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }
    }

    ThermalZone (TZD6)
    {
        /* ======== 0 ======= */

        Name (BD13, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD13, 0x00, 0x08, BF00)
        Device (DD0E)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD3)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        Processor (PRD3, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        PowerResource (PWD3, 0x01, 0x0000)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        Method (M81E, 0, Serialized)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        /* ======== 1 ======= */

        Device (DD0F)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD4)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Processor (PRD4, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        PowerResource (PWD4, 0x01, 0x0000)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Method (M81F, 0, Serialized)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        /* ======== 2 ======= */

        Device (DD10)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD5)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Processor (PRD5, 0x00, 0xFFFFFFFF, 0x00)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        PowerResource (PWD5, 0x01, 0x0000)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Method (M820, 0, NotSerialized)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }
    }

    Processor (PRD6, 0x00, 0xFFFFFFFF, 0x00)
    {
        /* ======== 0 ======= */

        Name (BD13, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD13, 0x00, 0x08, BF00)
        Device (DD0E)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD3)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        Processor (PRD3, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        PowerResource (PWD3, 0x01, 0x0000)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        Method (M81E, 0, Serialized)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        /* ======== 1 ======= */

        Device (DD0F)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD4)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Processor (PRD4, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        PowerResource (PWD4, 0x01, 0x0000)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Method (M81F, 0, Serialized)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        /* ======== 2 ======= */

        Device (DD10)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD5)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Processor (PRD5, 0x00, 0xFFFFFFFF, 0x00)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        PowerResource (PWD5, 0x01, 0x0000)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Method (M820, 0, NotSerialized)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }
    }

    PowerResource (PWD6, 0x01, 0x0000)
    {
        /* ======== 0 ======= */

        Name (BD13, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD13, 0x00, 0x08, BF00)
        Device (DD0E)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD3)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        Processor (PRD3, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        PowerResource (PWD3, 0x01, 0x0000)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        Method (M81E, 0, Serialized)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        /* ======== 1 ======= */

        Device (DD0F)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD4)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Processor (PRD4, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        PowerResource (PWD4, 0x01, 0x0000)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Method (M81F, 0, Serialized)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        /* ======== 2 ======= */

        Device (DD10)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD5)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Processor (PRD5, 0x00, 0xFFFFFFFF, 0x00)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        PowerResource (PWD5, 0x01, 0x0000)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Method (M820, 0, NotSerialized)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }
    }

    Method (M821, 0, Serialized)
    {
        /* ======== 0 ======= */

        Name (BD13, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        CreateField (BD13, 0x00, 0x08, BF00)
        Device (DD0E)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD3)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        Processor (PRD3, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        PowerResource (PWD3, 0x01, 0x0000)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        Method (M81E, 0, Serialized)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }

        /* ======== 1 ======= */

        Device (DD0F)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD4)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Processor (PRD4, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        PowerResource (PWD4, 0x01, 0x0000)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Method (M81F, 0, Serialized)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        /* ======== 2 ======= */

        Device (DD10)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        ThermalZone (TZD5)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Processor (PRD5, 0x00, 0xFFFFFFFF, 0x00)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        PowerResource (PWD5, 0x01, 0x0000)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        Method (M820, 0, NotSerialized)
        {
            CreateField (BD11, 0x00, 0x08, BF00)
        }

        M81E ()
        M81F ()
        M820 ()
    }

    /* ======== 4 ======= */

    Method (M822, 0, Serialized)
    {
        Device (DD0E)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }
    }

    Method (M823, 0, Serialized)
    {
        ThermalZone (TZD3)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }
    }

    Method (M824, 0, Serialized)
    {
        Processor (PRD3, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }
    }

    Method (M825, 0, Serialized)
    {
        PowerResource (PWD3, 0x01, 0x0000)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }
    }

    Method (M826, 0, NotSerialized)
    {
        Method (M000, 0, Serialized)
        {
            Name (BD13, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD13, 0x00, 0x08, BF00)
        }
    }

    /* ======== 5 ======= */

    Method (M827, 0, Serialized)
    {
        Device (DD0E)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }
    }

    Method (M828, 0, Serialized)
    {
        ThermalZone (TZD3)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }
    }

    Method (M829, 0, Serialized)
    {
        Processor (PRD3, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }
    }

    Method (M82A, 0, Serialized)
    {
        PowerResource (PWD3, 0x01, 0x0000)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }
    }

    Method (M82B, 0, NotSerialized)
    {
        Method (M000, 0, Serialized)
        {
            Name (BD11, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (BD11, 0x00, 0x08, BF00)
        }
    }

    /* ======== 6 ======= */

    Method (M82C, 0, Serialized)
    {
        Device (DD0E)
        {
            CreateField (BD12, 0x00, 0x08, BF00)
        }
    }

    Method (M82D, 0, Serialized)
    {
        ThermalZone (TZD3)
        {
            CreateField (BD12, 0x00, 0x08, BF00)
        }
    }

    Method (M82E, 0, Serialized)
    {
        Processor (PRD3, 0x00, 0xFFFFFFFF, 0x00)
        {
            CreateField (BD12, 0x00, 0x08, BF00)
        }
    }

    Method (M82F, 0, Serialized)
    {
        PowerResource (PWD3, 0x01, 0x0000)
        {
            CreateField (BD12, 0x00, 0x08, BF00)
        }
    }

    Method (M830, 0, NotSerialized)
    {
        Method (M000, 0, NotSerialized)
        {
            CreateField (BD12, 0x00, 0x08, BF00)
        }
    }

    /* ======== 7 ======= */

    Method (M832, 0, Serialized)
    {
        Device (DD0E)
        {
            Name (DD12, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (DD12, 0x00, 0x08, BF00)
        }
    }

    Method (M833, 0, Serialized)
    {
        ThermalZone (TZD3)
        {
            Name (DD12, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (DD12, 0x00, 0x08, BF00)
        }
    }

    Method (M834, 0, Serialized)
    {
        Processor (PRD3, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (DD12, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (DD12, 0x00, 0x08, BF00)
        }
    }

    Method (M835, 0, Serialized)
    {
        PowerResource (PWD3, 0x01, 0x0000)
        {
            Name (DD12, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (DD12, 0x00, 0x08, BF00)
        }
    }

    Method (M836, 0, NotSerialized)
    {
        Method (M000, 0, Serialized)
        {
            Name (DD12, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            })
            CreateField (DD12, 0x00, 0x08, BF00)
        }
    }

    Method (M831, 0, NotSerialized)
    {
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("m831-0")
        If (0x01)
        {
            M81E ()
            M81F ()
            M820 ()
            M821 ()
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("m831-1")
        If (0x01)
        {
            M822 ()
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            M823 ()
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            M824 ()
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            M825 ()
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            M826 ()
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("m831-2")
        If (0x01)
        {
            M827 ()
            M828 ()
            M829 ()
            M82A ()
            M82B ()
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("m831-3")
        If (0x01)
        {
            M82C ()
            M82D ()
            M82E ()
            M82F ()
            M830 ()
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        SRMT ("m831-4")
        If (0x01)
        {
            M832 ()
            M833 ()
            M834 ()
            M835 ()
            M836 ()
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
