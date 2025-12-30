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
     * Exceptional conditions support
     */
    Name (Z063, 0x3F)
    /* The current number of exceptions handled */

    Name (EXC0, 0x00)
    /* The total number of exceptions handled */

    Name (EXC1, 0x00)
    /* Opcode of the last exception */

    Name (EX00, 0x00)
    /* Name of the last exception */

    Name (EX01, "")
    /* Opcode of the first exception */

    Name (EX04, 0x00)
    /* Name of the first exception */

    Name (EX05, "")
    /*
     * Undefined opcodes of exception
     */
    Name (EX0D, 0xFD)
    Name (EX0E, 0xFE)
    /* Undefined opcode of exception means 'any exceptions' */

    Name (EX0F, 0xFF)
    /* Description of all exceptional conditions */

    Name (PF00, Package (0x57)
    {
        /*          ix opcodes      names */

        Package (0x03)
        {
            0x00,
            0x00,
            "AE_OK"
        },

        Package (0x03)
        {
            0x01,
            0x01,
            "AE_ERROR"
        },

        Package (0x03)
        {
            0x02,
            0x02,
            "AE_NO_ACPI_TABLES"
        },

        Package (0x03)
        {
            0x03,
            0x03,
            "AE_NO_NAMESPACE"
        },

        Package (0x03)
        {
            0x04,
            0x04,
            "AE_NO_MEMORY"
        },

        Package (0x03)
        {
            0x05,
            0x05,
            "AE_NOT_FOUND"
        },

        Package (0x03)
        {
            0x06,
            0x06,
            "AE_NOT_EXIST"
        },

        Package (0x03)
        {
            0x07,
            0x07,
            "AE_ALREADY_EXISTS"
        },

        Package (0x03)
        {
            0x08,
            0x08,
            "AE_TYPE"
        },

        Package (0x03)
        {
            0x09,
            0x09,
            "AE_NULL_OBJECT"
        },

        Package (0x03)
        {
            0x0A,
            0x0A,
            "AE_NULL_ENTRY"
        },

        Package (0x03)
        {
            0x0B,
            0x0B,
            "AE_BUFFER_OVERFLOW"
        },

        Package (0x03)
        {
            0x0C,
            0x0C,
            "AE_STACK_OVERFLOW"
        },

        Package (0x03)
        {
            0x0D,
            0x0D,
            "AE_STACK_UNDERFLOW"
        },

        Package (0x03)
        {
            0x0E,
            0x0E,
            "AE_NOT_IMPLEMENTED"
        },

        Package (0x03)
        {
            0x0F,
            0x0F,
            "AE_VERSION_MISMATCH"
        },

        /* obsolete */

        Package (0x03)
        {
            0x10,
            0x0F,
            "AE_SUPPORT"
        },

        Package (0x03)
        {
            0x11,
            0x11,
            "AE_SHARE"
        },

        /* obsolete */

        Package (0x03)
        {
            0x12,
            0x10,
            "AE_LIMIT"
        },

        Package (0x03)
        {
            0x13,
            0x11,
            "AE_TIME"
        },

        Package (0x03)
        {
            0x14,
            0x14,
            "AE_UNKNOWN_STATUS"
        },

        /* obsolete */

        Package (0x03)
        {
            0x15,
            0x12,
            "AE_ACQUIRE_DEADLOCK"
        },

        Package (0x03)
        {
            0x16,
            0x13,
            "AE_RELEASE_DEADLOCK"
        },

        Package (0x03)
        {
            0x17,
            0x14,
            "AE_NOT_ACQUIRED"
        },

        Package (0x03)
        {
            0x18,
            0x15,
            "AE_ALREADY_ACQUIRED"
        },

        Package (0x03)
        {
            0x19,
            0x16,
            "AE_NO_HARDWARE_RESPONSE"
        },

        Package (0x03)
        {
            0x1A,
            0x17,
            "AE_NO_GLOBAL_LOCK"
        },

        Package (0x03)
        {
            0x1B,
            0x18,
            "AE_ABORT_METHOD"
        },

        Package (0x03)
        {
            0x1C,
            0x1001,
            "AE_BAD_PARAMETER"
        },

        Package (0x03)
        {
            0x1D,
            0x1002,
            "AE_BAD_CHARACTER"
        },

        Package (0x03)
        {
            0x1E,
            0x1003,
            "AE_BAD_PATHNAME"
        },

        Package (0x03)
        {
            0x1F,
            0x1004,
            "AE_BAD_DATA"
        },

        Package (0x03)
        {
            0x20,
            0x1005,
            "AE_BAD_ADDRESS"
        },

        /* obsolete */

        Package (0x03)
        {
            0x21,
            0x1006,
            "AE_ALIGNMENT"
        },

        /* obsolete */

        Package (0x03)
        {
            0x22,
            0x1005,
            "AE_BAD_HEX_CONSTANT"
        },

        Package (0x03)
        {
            0x23,
            0x1006,
            "AE_BAD_OCTAL_CONSTANT"
        },

        Package (0x03)
        {
            0x24,
            0x1007,
            "AE_BAD_DECIMAL_CONSTANT"
        },

        Package (0x03)
        {
            0x25,
            0x2001,
            "AE_BAD_SIGNATURE"
        },

        Package (0x03)
        {
            0x26,
            0x2002,
            "AE_BAD_HEADER"
        },

        Package (0x03)
        {
            0x27,
            0x2003,
            "AE_BAD_CHECKSUM"
        },

        Package (0x03)
        {
            0x28,
            0x2004,
            "AE_BAD_VALUE"
        },

        Package (0x03)
        {
            0x29,
            0x2005,
            "AE_TABLE_NOT_SUPPORTED"
        },

        /* obsolete */

        Package (0x03)
        {
            0x2A,
            0x2005,
            "AE_INVALID_TABLE_LENGTH"
        },

        Package (0x03)
        {
            0x2B,
            0x3001,
            "AE_AML_ERROR"
        },

        /* obsolete */

        Package (0x03)
        {
            0x2C,
            0x3002,
            "AE_AML_PARSE"
        },

        /* obsolete */

        Package (0x03)
        {
            0x2D,
            0x3001,
            "AE_AML_BAD_OPCODE"
        },

        Package (0x03)
        {
            0x2E,
            0x3002,
            "AE_AML_NO_OPERAND"
        },

        Package (0x03)
        {
            0x2F,
            0x3003,
            "AE_AML_OPERAND_TYPE"
        },

        Package (0x03)
        {
            0x30,
            0x3004,
            "AE_AML_OPERAND_VALUE"
        },

        Package (0x03)
        {
            0x31,
            0x3005,
            "AE_AML_UNINITIALIZED_LOCAL"
        },

        Package (0x03)
        {
            0x32,
            0x3006,
            "AE_AML_UNINITIALIZED_ARG"
        },

        Package (0x03)
        {
            0x33,
            0x3007,
            "AE_AML_UNINITIALIZED_ELEMENT"
        },

        Package (0x03)
        {
            0x34,
            0x3008,
            "AE_AML_NUMERIC_OVERFLOW"
        },

        Package (0x03)
        {
            0x35,
            0x3009,
            "AE_AML_REGION_LIMIT"
        },

        Package (0x03)
        {
            0x36,
            0x300A,
            "AE_AML_BUFFER_LIMIT"
        },

        Package (0x03)
        {
            0x37,
            0x300B,
            "AE_AML_PACKAGE_LIMIT"
        },

        Package (0x03)
        {
            0x38,
            0x300C,
            "AE_AML_DIVIDE_BY_ZERO"
        },

        Package (0x03)
        {
            0x39,
            0x300D,
            "AE_AML_BAD_NAME"
        },

        Package (0x03)
        {
            0x3A,
            0x300E,
            "AE_AML_NAME_NOT_FOUND"
        },

        Package (0x03)
        {
            0x3B,
            0x300F,
            "AE_AML_INTERNAL"
        },

        Package (0x03)
        {
            0x3C,
            0x3010,
            "AE_AML_INVALID_SPACE_ID"
        },

        Package (0x03)
        {
            0x3D,
            0x3011,
            "AE_AML_STRING_LIMIT"
        },

        Package (0x03)
        {
            0x3E,
            0x3012,
            "AE_AML_NO_RETURN_VALUE"
        },

        Package (0x03)
        {
            0x3F,
            0x3014,
            "AE_AML_NOT_OWNER"
        },

        Package (0x03)
        {
            0x40,
            0x3015,
            "AE_AML_MUTEX_ORDER"
        },

        Package (0x03)
        {
            0x41,
            0x3016,
            "AE_AML_MUTEX_NOT_ACQUIRED"
        },

        Package (0x03)
        {
            0x42,
            0x3017,
            "AE_AML_INVALID_RESOURCE_TYPE"
        },

        Package (0x03)
        {
            0x43,
            0x3018,
            "AE_AML_INVALID_INDEX"
        },

        Package (0x03)
        {
            0x44,
            0x3019,
            "AE_AML_REGISTER_LIMIT"
        },

        Package (0x03)
        {
            0x45,
            0x301A,
            "AE_AML_NO_WHILE"
        },

        Package (0x03)
        {
            0x46,
            0x301B,
            "AE_AML_ALIGNMENT"
        },

        Package (0x03)
        {
            0x47,
            0x301C,
            "AE_AML_NO_RESOURCE_END_TAG"
        },

        Package (0x03)
        {
            0x48,
            0x301D,
            "AE_AML_BAD_RESOURCE_VALUE"
        },

        Package (0x03)
        {
            0x49,
            0x301E,
            "AE_AML_CIRCULAR_REFERENCE"
        },

        Package (0x03)
        {
            0x4A,
            0x4001,
            "AE_CTRL_RETURN_VALUE"
        },

        Package (0x03)
        {
            0x4B,
            0x4002,
            "AE_CTRL_PENDING"
        },

        Package (0x03)
        {
            0x4C,
            0x4003,
            "AE_CTRL_TERMINATE"
        },

        Package (0x03)
        {
            0x4D,
            0x4004,
            "AE_CTRL_TRUE"
        },

        Package (0x03)
        {
            0x4E,
            0x4005,
            "AE_CTRL_FALSE"
        },

        Package (0x03)
        {
            0x4F,
            0x4006,
            "AE_CTRL_DEPTH"
        },

        Package (0x03)
        {
            0x50,
            0x4007,
            "AE_CTRL_END"
        },

        Package (0x03)
        {
            0x51,
            0x4008,
            "AE_CTRL_TRANSFER"
        },

        Package (0x03)
        {
            0x52,
            0x4009,
            "AE_CTRL_BREAK"
        },

        Package (0x03)
        {
            0x53,
            0x400A,
            "AE_CTRL_CONTINUE"
        },

        /* New additional are here not to touch previous indexes */

        Package (0x03)
        {
            0x54,
            0x3013,
            "AE_AML_METHOD_LIMIT"
        },

        Package (0x03)
        {
            0x55,
            0x100B,
            "AE_INDEX_TO_NOT_ATTACHED"
        },

        Package (0x03)
        {
            0x56,
            0x1B,
            "AE_OWNER_ID_LIMIT"
        }
    })
    /*
     * (multi-threading)
     *
     * Packages to store per-thread information about exceptions
     * (used in mt-mode)
     *
     * EXC2 - maximal number of exception can be registered
     * EX02 - package to store ID of thread where exception occurs
     * EX03 - package to store opcode of exception
     */
    Name (EXC2, 0xC8)
    Name (EX02, Package (EXC2){})
    Name (EX03, Package (EXC2){})
    /*
     * Exceptional conditions handler
     *
     * arg0 - AcpiStatus
     * arg1 - AsciiExceptionString
     * arg2 - ID of current thread
     */
    Method (_ERR, 3, NotSerialized)
    {
        EX00 = Arg0
        EX01 = Arg1
        If ((EX04 == 0x00))
        {
            EX04 = Arg0
            EX05 = Arg1
        }

        /* multi-threading */

        If (MTHR)
        {
            /* If the current number of exceptions handled doesn't exceed EXC2 */

            If ((EXC0 < EXC2))
            {
                EX02 [EXC0] = Arg2
                EX03 [EXC0] = Arg0
            }
            Else
            {
                Debug = "Maximal number of exceptions exceeded"
                ERR ("_ERR", Z063, __LINE__, 0x00, 0x00, EXC0, EXC2)
            }
        }

        EXC0++
        EXC1++
        /*	Store("Run-time exception:", Debug) */
        /*	Store(arg0, Debug) */
        /*	Store(arg1, Debug) */
        /*	Store(arg2, Debug) */
        Return (0x00) /* Map error to AE_OK */
    }

    /* Check that exceptions has not arisen at all */

    Method (CH02, 0, NotSerialized)
    {
        If (EXC1)
        {
            Concatenate ("Some unexpected exceptions were handled, 0x", EXC1, Local0)
            ERR ("CH02", Z063, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Return (EXC1) /* \EXC1 */
    }

    /*
     * Check that the counter of current exceptions is zero. Set it to zero.
     * arg0 - diagnostic message
     * arg1 - absolute index of file initiating the checking
     * arg2 - line number of checking
     * arg3 - arg5 of err, "received value"
     * arg4 - arg6 of err, "expected value"
     */
    Method (CH03, 5, NotSerialized)
    {
        Local7 = 0x00
        If (EXC0)
        {
            Concatenate ("Unexpected exceptions (count ", EXC0, Local0)
            Concatenate (Local0, "), the last is ", Local1)
            Concatenate (Local1, EX01, Local0)
            Concatenate (Local0, ", ", Local1)
            Concatenate (Local1, EX00, Debug)
            ERR (Arg0, Z063, __LINE__, Arg1, Arg2, Arg3, Arg4)
            Local7 = EXC0 /* \EXC0 */
        }

        EXC0 = 0x00
        EX04 = 0x00
        Return (Local7)
    }

    /* */
    /* Convert 32/64 bit integer to 16-bit Hex value */
    /* */
    Method (ST16, 1, Serialized)
    {
        Name (EBUF, Buffer (ISZC){})
        /* 8 or 16 bytes, depending on 32/64 mode */

        Name (RBUF, Buffer (0x04){})
        EBUF = ToHexString (Arg0)
        Mid (EBUF, (ISZC - 0x04), 0x04, RBUF) /* \ST16.RBUF */
        Return (Concatenate ("0x", ToString (RBUF, Ones)))
    }

    /*
     * Check that exceptions are handled as expected, report errors
     * (if any) and set the current number of exceptions to zero.
     *
     * Verified:
     * - exception has arisen
     * - check the number of exceptions
     * - the last arisen exception matches one described by arguments
     *
     * arg0 - diagnostic message
     * arg1 -
     *   zero means:
     *        - check that only one exception has arisen (current number is equal to 1)
     *        - check that opcode is equal to that specified by arg2
     *   non-zero means:
     *        - check that the number of exception arisen is not less than 1
     *          (current number is equal to 1 or greater)
     *     1:   check that the first opcode is equal to that specified by arg2
     *     2:   check that the last opcode is equal to that specified by arg2
     *
     * arg2 - index of exception info in pf00 Package
     * arg3 - absolute index of file initiating the checking
     * arg4 - line number of checking
     * arg5 - arg5 of err, "received value"
     * arg6 - arg6 of err, "expected value"
     */
    Method (CH04, 7, NotSerialized)
    {
        Local5 = 0x00
        If ((Arg2 == 0xFF))
        {
            If ((EXC0 == 0x00))
            {
                Local5 = 0x01
                Debug = "ERROR: No ANY exception has arisen."
            }
        }
        Else
        {
            /* Determine opcode and name of the expected exception */

            Local2 = DerefOf (PF00 [Arg2]) /* exception info */
            Local3 = DerefOf (Local2 [0x01])  /* opcode */
            Local4 = DerefOf (Local2 [0x02])  /* name */
            If ((EXC0 == 0x00))
            {
                Local5 = 0x01
                Concatenate ("No exception - expected: ", Local4, Local0)
                Concatenate (Local0, "-", Local0)
                Concatenate (Local0, ST16 (Local3), Local0)
                Debug = Local0
            }
            ElseIf ((!Arg1 && (EXC0 > 0x01)))
            {
                Local5 = 0x01
                Concatenate ("More than one exception: 0x", EXC0, Local0)
                Debug = Local0
            }
            Else
            {
                If ((Arg1 == 0x01))
                {
                    /* Opcode of the first exception */

                    Local6 = EX04 /* \EX04 */
                    Local7 = EX05 /* \EX05 */
                }
                Else
                {
                    /* Opcode of the last exception */

                    Local6 = EX00 /* \EX00 */
                    Local7 = EX01 /* \EX01 */
                }

                If ((Local3 != Local6))
                {
                    Local5 = 0x01
                    Concatenate ("Exception: ", Local7, Local0)
                    Concatenate (Local0, "-", Local0)
                    Concatenate (Local0, ST16 (Local6), Local0)
                    Concatenate (" differs from expected: ", Local4, Local1)
                    Concatenate (Local0, Local1, Local0)
                    Concatenate (Local0, "-", Local0)
                    Concatenate (Local0, ST16 (Local3), Local0)
                    Debug = Local0
                }

                If ((Local4 != Local7))
                {
                    Local5 = 0x01
                    Debug = "Unexpected exception:"
                    Debug = Concatenate ("Expected: ", Local4)
                    Debug = Concatenate ("Received: ", Local7)
                }
            }
        }

        /* if(LNotEqual(arg2,0xff)) */

        EXC0 = 0x00
        EX04 = 0x00
        If (Local5)
        {
            ERR (Arg0, Z063, __LINE__, Arg3, Arg4, Arg5, Arg6)
        }

        Return (Local5)
    }

    Method (CH05, 0, NotSerialized)
    {
        Return (CH03 ("CH05", 0x00, __LINE__, 0x00, 0x00))
    }

    Method (CH06, 3, NotSerialized)
    {
        If (EXCV)
        {
            Return (CH04 (Arg0, 0x00, Arg2, 0x00, __LINE__, 0x00, 0x00))
        }
        Else
        {
            /* Just only presence of ANY exception(s) */

            Return (CH04 (Arg0, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00))
        }
    }

    /*
     * Check for any exception when the slack mode is initiated
     */
    Method (CH07, 7, NotSerialized)
    {
        If (SLCK)
        {
            CH03 (Arg0, Arg3, __LINE__, 0x00, Arg6)
        }
        Else
        {
            CH04 (Arg0, Arg1, Arg2, Arg3, __LINE__, Arg5, Arg6)
        }
    }

    /* MULTI-THREADING */
    /*
     * Report message of thread
     * (adds ID of thread and reports the message)
     *
     * arg0 - ID of current thread
     * arg1 - string
     */
    Method (MSG0, 2, NotSerialized)
    {
        Concatenate ("THREAD ID ", Arg0, Local0)
        Concatenate (Local0, ": ", Local1)
        Concatenate (Local1, Arg1, Local0)
        Debug = Local0
    }

    /*
     * Used in multi-threading mode
     *
     * Return the first encountered exception corresponding to this Thread ID
     * and the total number of exceptions corresponding to this Thread ID.
     * Reset all the entries corresponding to the thread identified by arg0.
     *
     * Note: this method is used in mt-mode (by several threads simultaneously)
     *       but each of threads changes only its elements of EX02.
     *
     * arg0 - ID of current thread
     */
    Method (MTEX, 1, NotSerialized)
    {
        Local2 = Package (0x02)
            {
                0x00,
                0x00
            } /* Package to be returned */
        Local3 = 0x00 /* found */
        Local4 = EXC0 /* lpN0 */ /* \EXC0 */
        Local5 = 0x00    /* lpC0 */
        While (Local4)
        {
            Local0 = DerefOf (EX02 [Local5])
            /* Matching ID of current thread */

            If ((Local0 == Arg0))
            {
                Local1 = DerefOf (EX03 [Local5])
                If ((Local3 == 0x00))
                {
                    /* Opcode of the first exception */

                    Local2 [0x00] = Local1
                }

                Local3++
                /* Reset information about this exception */

                EX02 [Local5] = 0x00
            }

            Local4--
            Local5++
        }

        Local2 [0x01] = Local3
        Return (Local2)
    }

    /*
     * The same as CH03, but to be used in multi-threading mode
     *
     * arg0 - diagnostic message
     * arg1 - ID of current thread
     * arg2 - absolute index of file initiating the checking
     * arg3 - index of checking
     * arg4 - arg5 of err, "received value"
     * arg5 - arg6 of err, "expected value"
     *
     * Return: current number of exceptions occur on this thread
     */
    Method (CH08, 6, NotSerialized)
    {
        Local2 = MTEX (Arg1)
        Local3 = DerefOf (Local2 [0x00]) /* opcode of the first exception */
        Local4 = DerefOf (Local2 [0x01]) /* number of exceptions */
        Local7 = 0x00
        If (Local4)
        {
            Concatenate ("Unexpected exception 0x", Local3, Local0)
            Concatenate (Local0, ", number of exceptions 0x", Local1)
            Concatenate (Local1, Local4, Local0)
            MSG0 (Arg1, Local0)
            ERR (Arg0, Z063, __LINE__, Arg2, Arg3, Arg4, Arg5)
            Local7 = 0x01
        }

        /*
         * Reset of EXC0 should be done by Control thread
         * Store(0, EXC0)
         */
        Return (Local4)
    }

    /*
     * The same as CH04, but to be used in multi-threading mode
     *
     * arg0 - non-zero means to treat "More than one exceptions" as error
     * arg1 - ID of current thread
     * arg2 - index of exception info in pf00 Package
     * arg3 - absolute index of file initiating the checking
     * arg4 - index of checking
     * arg5 - RefOf to Integer to return 'current number of exceptions occur on this thread'
     *
     * Return: non-zero when errors detected
     */
    Method (CH09, 6, NotSerialized)
    {
        Local7 = MTEX (Arg1)
        Local6 = DerefOf (Local7 [0x00]) /* opcode of the first exception */
        Local7 = DerefOf (Local7 [0x01]) /* number of exceptions */
        Local5 = 0x00
        If ((Arg2 == 0xFF))
        {
            If ((Local7 == 0x00))
            {
                /* No exceptions */

                Local5 = 0x01
                MSG0 (Arg1, "ERROR: No ANY exception has arisen.")
            }
        }
        Else
        {
            /* Determine opcode and name of the expected exception */

            Local2 = DerefOf (PF00 [Arg2]) /* exception info */
            Local3 = DerefOf (Local2 [0x01])  /* opcode */
            Local4 = DerefOf (Local2 [0x02])  /* name */
            If ((Local7 == 0x00))
            {
                /* No exceptions */

                Local5 = 0x01
                Concatenate ("No exception has arisen, expected: ", Local4, Local0)
                Concatenate (", opcode 0x", Local3, Local1)
                Concatenate (Local0, Local1, Local0)
                MSG0 (Arg1, Local0)
            }
            ElseIf ((Arg0 && (Local7 > 0x01)))
            {
                Local5 = 0x01
                Concatenate ("More than one exception has arisen: 0x", Local7, Local0)
                MSG0 (Arg1, Local0)
            }
            ElseIf            /* Opcode of the first exception */

 ((Local3 != Local6))
            {
                Local5 = 0x01
                Concatenate ("The exception 0x", Local6, Local0)
                Concatenate (Local0, " differs from expected ", Local1)
                Concatenate (Local1, ST16 (Local3), Local0)
                MSG0 (Arg1, Local0)
            }
        }

        /* if(LNotEqual(arg2,0xff)) */
        /*
         * Reset of EXC0 should be done by Control thread
         * Store(0, EXC0)
         */
        If (Local5)
        {
            ERR (__METHOD__, Z063, __LINE__, Arg3, Arg4, 0x00, 0x00)
        }

        Arg5 = Local7
        Return (Local5)
    }

    /*
     * Reset EXC0 (the current number of exceptions handled)
     *
     * It should be invoked by the Control thread.
     */
    Method (CH0A, 0, NotSerialized)
    {
        EXC0 = 0x00
    }
