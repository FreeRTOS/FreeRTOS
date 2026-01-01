            /*
             * Flag, compiler the test in the abbu layout
             */
            Name (ABUU, 0x01)
            /*
             * Internal objects used in this file only
             */
            Name (AI03, 0x01)  /* Print out the name of test-case */
            Name (AI05, 0x00)  /* Print out the name of test */
            Name (AI06, 0x01)  /* Print out additional parameters of errors */
            /*
             * Objects from the common.asl used there also
             */
            Name (TCLT, 0x07)   /* Identity2MS test case ID */
            Name (ERRS, 0x00)   /* Errors counter */
            Name (RMRC, 0x00)   /* Current number of root Methods runs */
            /* Types, as returned by ObjectType */

            Name (C008, 0x00)   /* Uninitialized */
            Name (C009, 0x01)   /* Integer */
            Name (C00A, 0x02)   /* String */
            Name (C00B, 0x03)   /* Buffer */
            Name (C00C, 0x04)   /* Package */
            Name (C00D, 0x05)   /* Field Unit */
            Name (C00E, 0x06)   /* Device */
            Name (C00F, 0x07)   /* Event */
            Name (C010, 0x08)   /* Method */
            Name (C011, 0x09)   /* Mutex */
            Name (C012, 0x0A)  /* Operation Region */
            Name (C013, 0x0B)  /* Power Resource */
            Name (C014, 0x0C)  /* Processor */
            Name (C015, 0x0D)  /* Thermal Zone */
            Name (C016, 0x0E)  /* Buffer Field */
            Name (C017, 0x0F)  /* DDB Handle */
            Name (C018, 0x10)  /* Debug Object */
            Name (C019, 0x11)  /* LOCAL_REGION_FIELD */
            Name (C01A, 0x12)  /* LOCAL_BANK_FIELD */
            Name (C01B, 0x13)  /* LOCAL_INDEX_FIELD */
            Name (C01C, 0x14)  /* LOCAL_REFERENCE */
            Name (C01D, 0x15)  /* LOCAL_ALIAS */
            Name (C01E, 0x16)  /* LOCAL_METHOD_ALIAS */
            Name (C01F, 0x17)  /* LOCAL_NOTIFY */
            Name (C020, 0x18)  /* LOCAL_ADDRESS_HANDLER */
            Name (C021, 0x19)  /* LOCAL_RESOURCE */
            Name (C022, 0x1A)  /* LOCAL_RESOURCE_FIELD */
            Name (C023, 0x1B)  /* LOCAL_SCOPE */
            Name (C024, 0x1C)  /* LOCAL_EXTRA */
            Name (C025, 0x1D)  /* LOCAL_DATA */
            Name (C027, 0x1E)  /* Number of different types */
            /*
             * Methods from common.asl
             */
            Method (STRT, 1, NotSerialized)
            {
                /* Adjust some skippings of tests for different ACPICA rereales */

                SET2 (SETN)
            }

            Method (FNSH, 0, NotSerialized)
            {
                /* The usual layout of aslts summary lines */

                If (ERRS)
                {
                    OUUP ("\":STST:Identity2MS:abbu:mmmm:FAIL:Errors # 12 34 56 78:\"", 0x01)
                }
                Else
                {
                    OUUP ("\":STST:Identity2MS:abbu:mmmm:PASS:\"", 0x01)
                }

                OUUP (ERRS, 0x01)
                OUUP ("The number of tests has been executed:", 0x01)
                OUUP (RMRC, 0x01)
                Return (ERRS) /* \_SB_.ABBU.ERRS */
            }

            Method (STTT, 4, NotSerialized)
            {
                If (AI03)
                {
                    OUTP (Arg0)
                }

                Return (0x01)
            }

            Method (SRMT, 1, NotSerialized)
            {
                If (AI05)
                {
                    OUTP (Arg0)
                }

                RMRC++
            }

            Method (ERR, 7, NotSerialized)
            {
                OUTP (Arg0)
                If (AI06)
                {
                    OUTP (Arg2)
                    OUTP (Arg5)
                }

                ERRS++
            }

            Method (FTTT, 0, NotSerialized)
            {
            }

            Method (BLCK, 0, NotSerialized)
            {
            }

            /*
             * Methods from ehandle.asl
             */
            Method (CH02, 0, NotSerialized)
            {
                Return (0x00)
            }

            Method (CH03, 5, NotSerialized)
            {
                Return (0x00)
            }

            Method (CH04, 7, NotSerialized)
            {
                Return (0x00)
            }
