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
     * Run Tests Parameters Technique (RTPT)
     *
     * These parameters have effect only when
     * running a group of tests (collections)
     * such as all Functional tests, all Complex
     * tests, all Exceptions tests, Full test
     * (all enumerated above tests).
     *
     * Main flag:
     * 0 - run unconditionally all tests
     * 1 - run all the tests with non-zero params
     * 2 - run all the tests with zero params
     * 3 - run all the tests with params equal to RUN1
     * 4 - run a particular test specified by:
     *     RUN2 - index of collection
     *     RUN3 - index of the test inside the collection
     */
    Name (RUN0, 0x00)   /* main flag */
    Name (RUN1, 0x00)   /* level */
    Name (RUN2, 0x00)   /* collection */
    Name (RUN3, 0x00)   /* test */
    Name (RTPT, 0x00)   /* validity of RTPT mode */
    /* FUNCTIONAL */

    Name (W000, 0x00) /* arithmetic */
    Name (W001, 0x00) /* bfield */
    Name (W002, 0x00) /* constant */
    Name (W003, 0x00) /* control */
    Name (W004, 0x00) /* descriptor */
    Name (W005, 0x00) /* extern */
    Name (W006, 0x00) /* local */
    Name (W007, 0x00) /* logic */
    Name (W008, 0x00) /* manipulation */
    Name (W009, 0x00) /* name */
    Name (W00A, 0x00) /* reference */
    Name (W00B, 0x00) /* region */
    Name (W00C, 0x00) /* synchronization */
    Name (W00D, 0x00) /* table */
    Name (W01A, 0x00) /* module */
    /* COMPLEX */

    Name (W00E, 0x00) /* misc */
    Name (W00F, 0x00) /* provoke */
    Name (W010, 0x00) /* operand */
    Name (W011, 0x00) /* result */
    Name (W012, 0x00) /* namespace */
    Name (W022, 0x00) /* badasl */
    /* EXCEPTIONS */

    Name (W013, 0x00) /* exc */
    Name (W014, 0x00) /* exc_operand */
    Name (W015, 0x00) /* exc_result */
    Name (W016, 0x00) /* exc_ref */
    /* DEMO */

    Name (W017, 0x00) /* Bugs (0-N) */
    /* IMPL */

    Name (W021, 0x00) /* dynobj */
    /* SERVICE */

    Name (W018, 0x00) /* condbranches */
    /* Identity2MS */

    Name (W019, 0x00) /* abbu */
    /* Reserved names */

    Name (W020, 0x00)
    /*
     * Set RTPT technique.
     * Should be invoked in MAIN files of
     * ALL functional, complex, exceptions,...
     */
    Method (SRTP, 1, NotSerialized)
    {
        RTPT = Arg0
    }

    /*
     * Set up the particular desirable set of tests to be run
     *
     * These parameters have effect only when
     * running a group of test cases or even
     * collections) such as all Functional tests,
     * all Complex tests, all Exceptions tests,
     * Full test (all enumerated above tests)
     * compiled all as one DefinitionBlock.
     *
     * Parameters:
     *
     * RUN0 - main flag
     * 0 - run unconditionally all tests
     * 1 - run all the tests with non-zero params
     * 2 - run all the tests with zero params
     * 3 - run all the tests with params equal to RUN1
     * 4 - run a particular test specified by:
     *     RUN2 - index of collection
     *            1 - functional
     *            2 - complex
     *            3 - exceptions
     *     RUN3 - index of the test inside the collection
     * RUN1 - level
     * RUN2 - collection
     * RUN3 - test
     */
    Method (RTPI, 0, NotSerialized)
    {
        /* PARAMETERS OF MODE */

        RUN0 = 0x00 /* main flag */
        RUN1 = 0x00 /* level */
        RUN2 = 0x01 /* collection */
        RUN3 = 0x03 /* test */
        /* FUNCTIONAL, collection # 1 */

        W000 = 0x01 /* arithmetic        0 */
        W001 = 0x01 /* bfield            1 */
        W002 = 0x01 /* constant          2 */
        W003 = 0x01 /* control           3 */
        W004 = 0x01 /* descriptor        4 */
        W005 = 0x01 /* extern            5 */
        W006 = 0x01 /* local             6 */
        W007 = 0x01 /* logic             7 */
        W008 = 0x01 /* manipulation      8 */
        W009 = 0x01 /* name              9 */
        W00A = 0x01 /* reference        10 */
        W00B = 0x01 /* region           11 */
        W00C = 0x01 /* synchronization  12 */
        W00D = 0x01 /* table            13 */
        /* COMPLEX, collection # 2 */

        W00E = 0x01 /* misc              0 */
        W00F = 0x01 /* provoke           1 */
        W010 = 0x01 /* operand           2 */
        W011 = 0x01 /* result            3 */
        W021 = 0x01 /* dynobj            4 */
        W012 = 0x01 /* RESERVED, not in use */
        /* EXCEPTIONS, collection # 3 */

        W013 = 0x01 /* exc               0 */
        W014 = 0x01 /* exc_operand       1,2 */
        W015 = 0x01 /* exc_result        3,4 */
        W016 = 0x01 /* exc_ref           5 */
        W019 = 0x01 /* exc_tbl           6 */
        /* DEMO */

        W017 = 0x01 /* Bugs (0-N)		0 */
        /* SERVICE */

        W018 = 0x01 /* condbranches	0 */
    }

    /*
     * Variables below allow to exclude code which causes crashes
     * or hangs or prevents execution of other tests.
     *
     * ATTENTION: all these variables should be set to 1 eventually
     *            (after all bugs fixing).
     *
     * Format of variable name: y<xxx> - xxx is the number of bug
     *        0 - do not run
     * non-zero - run
     *
     * ATTENTION: see all the qXXX & rnXX conditions of the particular
     *            tests (which also provide the temporary exclusion).
     *
     * ATTENTION: all disablings must go through this technique of
     *            y<xxx> disable/enable variables.
     *
     * y<xxx>   - prevents undesirable consequences of the surrounded
     *            code (crashes, hangs etc. of tests). Should be finally
     *            set to non-zero (after the product-bug fixing) so
     *            enabling execution of the surrounded code.
     * X<xxx>   - surrounds particular Bugs. Used mostly to point out
     *            the reasons of test failures (xxx - number of bug)
     *            not to review the results of tests each time anew.
     *            So, as a rule these variables are set to non-zero.
     */
    /*
     * Bugs
     */
    Name (Y078, 0x00)
    Name (Y083, 0x00)
    Name (Y084, 0x01)
    Name (Y098, 0x01)
    Name (Y100, 0x00)
    Name (Y103, 0x01)
    Name (Y104, 0x01)
    Name (Y105, 0x01)
    Name (Y106, 0x00)
    Name (Y111, 0x01)
    Name (Y113, 0x00)
    Name (Y114, 0x00)
    Name (Y118, 0x00)   /* elements of Package are NamedX, failed access to Field Unit and Buffer Field */
    Name (Y119, 0x00)
    Name (Y120, 0x00)
    Name (Y121, 0x00)
    Name (Y126, 0x00)
    Name (Y127, 0x00)   /* Automatic dereference of Index in CopyObject */
    Name (Y128, 0x01)
    Name (Y132, 0x00)
    Name (Y133, 0x00)   /* Write access automatic dereference for Index reference */
    Name (Y134, 0x00)
    Name (Y135, 0x00)
    Name (Y136, 0x01)   /* CopyObject(A, B) for Buffers causes implicit */
    Name (Y157, 0x01)   /* problems when ParameterTypes declaration data omitted */
    Name (Y164, 0x01)   /* tests m22d and m26b of reference test */
    Name (Y176, 0x00)
    Name (Y178, 0x01)   /* Non-constant Bank values works since ACPICA release 20071211 */
    Name (Y182, 0x01)
    Name (Y192, 0x01)   /* AcpiExec is able to emulate access to BankField Objects since ACPICA release 20071211 */
    Name (Y200, 0x00)   /* The code path taken after exception in AcpiPsParseLoop is incorrect */
    Name (Y203, 0x00)   /* ObjectType operation falls into infinite loop for ring of RefOf references */
    Name (Y204, 0x00)   /* SizeOf operation falls into infinite loop for ring of RefOf references */
    Name (Y205, 0x00)   /* Store-to-Debug operation falls into infinite loop for ring of RefOf references */
    Name (Y206, 0x00)   /* ObjectType operation falls into infinite loop for ring of Index references */
    Name (Y207, 0x00)   /* SizeOf operation falls into infinite loop for ring of Index references */
    Name (Y208, 0x00)   /* Store-to-Debug operation falls into infinite loop for ring of Index references */
    Name (Y213, 0x00)   /* Crash */
    Name (Y214, 0x00)   /* Crash on repeated duplication of an OpRegion by CopyObject */
    Name (Y215, 0x00)   /* Exception AE_BUFFER_OVERFLOW when IndexName Field exceeds 32 bits */
    Name (Y216, 0x00)   /* exception AE_NOT_FOUND on CreateField under specific conditions */
    Name (Y217, 0x00)   /* Dynamic OpRegion _REG method execution problem */
    Name (Y220, 0x00)   /* Inconsistent "Access is available/unavailable" _REG method calls */
    Name (Y221, 0x01)   /* Alternating access to OpRegions covering different ranges */
    Name (Y222, 0x00)   /* Alternating access to OpRegions of different Address Spaces */
    Name (Y223, 0x01)   /* DataTableRegion with the non-constant *Strings works since ACPICA release 20071211 */
    Name (Y224, 0x00)   /* AcpiExec is unable to emulate access to IndexField Objects */
    Name (Y238, 0x00)   /* the jumping over levels in releasing mutexes is not prohibited */
    Name (Y242, 0x00)   /* Releasing the mutex the first Acquired on the non-zero level makes Releasing the residuary mutexes of that level impossible */
    Name (Y243, 0x00)   /* the normal work with mutexes is broken after the mutex Release order violation */
    Name (Y248, 0x00)   /* Incorrect ReferenceCount on Switch operation */
    Name (Y251, 0x00)   /* AE_ALREADY_EXISTS on multi-threading on Switch operator */
    Name (Y260, 0x00)   /* AE_AML_TARGET_TYPE on writing NewObj to ArgX [RefOf(OldObj)] instead of RefOf(NewObj) */
    Name (Y261, 0x00)   /* Crash when DDBHandle parameter of Load is an Indexed Reference */
    Name (Y262, 0x00)   /* Unexpected AE_STACK_OVERFLOW for a method call expression with nested calls */
    Name (Y263, 0x00)   /* The sequence of evaluating operands of expression with the named objects is violated */
    Name (Y264, 0x00)   /* Crash on re-writing named element of Package */
    Name (Y275, 0x00)   /* Pop result from bottom principle doesn't work */
    Name (Y276, 0x00)   /* 'Large Reference Count' on AML code with LoadTable/UnLoad in a slack mode */
    Name (Y281, 0x00)   /* Normal strings as the LoadTable parameters can cause the matching table to be not found */
    Name (Y282, 0x00)   /* Crash when the Buffer Object parameter of Load is used after an exception in it */
    Name (Y283, 0x01)   /* When the Object parameter of Load is a Field the checksum of the supplied SSDT should be verified */
    Name (Y284, 0x01)   /* An exception should be emitted on Load if the Length field of SSDT exceeds length of its source */
    Name (Y286, 0x01)   /* After an exception the elements of the Package passed to Unload are unexpectedly deleted */
    Name (Y287, 0x00)   /* If any string to match a proper field on LoadTable exceeds field's length an exception should be emitted */
    Name (Y288, 0x00)   /* iASL unexpectedly forbids ParameterData of Loadtable to be LocalX or UserTerm */
    Name (Y289, 0x00)   /* Search of the table matched Loadtable parameters should be restricted to XSDT */
    Name (Y290, 0x00)   /* AcpiExec is unable to emulate Load from OpRegion */
    Name (Y292, 0x00)   /* Different second and third UnLoad execution with the same argument behavior */
    Name (Y293, 0x00)   /* Incorrect zero-length Buffer to String conversion */
    Name (Y294, 0x00)   /* _ERR method can not be evaluated when AE_OWNER_ID_LIMIT is emitted */
    Name (Y296, 0x00)   /* AE_AML_INTERNAL unexpectedly occurs when the Loadtable ParameterData and its Target differ in the types */
    Name (Y297, 0x00)   /* After AE_LIMIT the further work of ACPICA mutex framework looks unstable */
    Name (Y300, 0x00)   /* Recursive calls to methods with the internal names (and Switches) should be provided */
    Name (Y301, 0x00)   /* Recursive call on the same thread to the Serialized method with the internal objects (Switches) causes AE_AML_INTERNAL */
    Name (Y302, 0x00)   /* Scope operation doesn't work for the root node Location */
    /*
     * Issues (replace them with the Bug indexes)
     */
    Name (Y349, 0x00)   /* to clarify what is the proper behaviour when Serialized Method is invoked recursively (now hangs) */
    Name (Y350, 0x00)   /* TermalZone AE_AML_NO_RETURN_VALUE exception */
    Name (Y361, 0x00)   /* OperationRegion in Result tests */
    Name (Y362, 0x00)   /* Investigate and uncomment m4ba */
    Name (Y364, 0x00)   /* if (Derefof(Refof(bf76))) exception in m61b-m06e */
    Name (Y365, 0x00)   /* Increment(Derefof(Refof(bf76))) exception in m61b-m64l */
    Name (Y366, 0x00)   /* exception on Store(Package, Derefof(Arg(Int/Str/Buf))) */
    Name (Y367, 0x00)   /* Increment(Refof(Named))) exception in m692-m00b */
    Name (Y500, 0x00)   /* Deletion of Named Object due to DeRefOf(m000()) */
    Name (Y501, 0x00)   /* Increment/Decrement for String/Buffer Named Object */
    Name (Y502, 0x00)   /* Exceptions on DeRefOf(Index(p000, 0)) */
    Name (Y503, 0x00)   /* AE_AML_OPERAND_TYPE => AE_AML_NO_RETURN_VALUE */
    Name (Y504, 0x00)   /* Exception on CopyObject(ThermalZone, ...) */
    Name (Y505, 0x00)   /* Buffer Field and Field Unit types should allow SizeOf() */
    Name (Y506, 0x00)   /* exc_ref: crash for DerefOf */
    Name (Y507, 0x00)   /* ref: read of ArgX-RefOf_References without DerefOf */
    Name (Y508, 0x00)   /* all about ThermalZone */
    Name (Y509, 0x00)   /* all about Method */
    Name (Y510, 0x00)   /* all about OperationRegion */
    Name (Y511, 0x00)   /* all about Device */
    Name (Y512, 0x00)   /* the checking causes unexpected exception */
    Name (Y513, 0x00)   /* m005(Index(s021, 1, Local0), RefOf(i020)) */
    /* m005(RefOf(i000), RefOf(i061)) */

    Name (Y514, 0x00)   /* repeated attempts to overwrite RefOf_Reference-ArgX cause exceptions */
    /* Name(y515, 0)	// Uninitialized element of Package (the same as y127) */

    Name (Y516, 0x00)   /* write from {Integer/String/Buffer} to Package */
    Name (Y517, 0x00)   /* Buffer Field (and Field Unit) as elements of Package */
    Name (Y518, 0x00)   /* utdelete-0487 [07] UtUpdateRefCount : **** Warning */
    /* **** Large Reference Count (EAEA) in object 00466BC8 */

    Name (Y519, 0x00)   /* ArgX term effectively becomes a LocalX term */
    /* Store(x,ArgX-Object) should be identical to Store(x,LocalX) */

    Name (Y520, 0x00)   /* ArgX term effectively becomes a LocalX term */
    /* CopyObject(x,ArgX-Object) should be identical to CopyObject(x,LocalX) */
    /* Now, DerefOf(arg0) causes exception */
    Name (Y521, 0x00)   /* Store reference to NamedX */
    Name (Y522, 0x01)   /* CopyObject reference to NamedX */
    Name (Y523, 0x00)   /* Store(RefOf(NamedX), NamedX) */
    Name (Y524, 0x00)   /* Store(RefOf(NamedX), DerefOf(Expr_resulting_in_ORef)) */
    Name (Y525, 0x00)   /* Store(RefOf(NamedX), RefOf(Named_X)) */
    Name (Y526, 0x00)   /* CopyObject(RefOf(NamedX), ArgX-ORef-to-Named_X) */
    Name (Y527, 0x00)   /* The code path taken after AE_OWNER_ID_LIMIT is incorrect */
    Name (Y600, 0x00)   /* Some oprators (not all) doesn't provide passing invocation */
    /* of Method as a parameter to them (though iASL succeeds). */
    /* Looks that Method is simply not invoked. But, since it doesn't */
    /* now look as an important feature for those particular operators */
    /* we don't file bug in this respect but exclude tesing. */
    Name (Y601, 0x00)   /* The Reference issues to be thought over in the future */
    Name (Y602, 0x01)   /* generalized - new specs of String to Integer conversion */
    Name (Y603, 0x00)   /* bunch of anomalies with references to be splited to separate bugs, */
    /* mostly - cyclical references (rings of references). */

    Name (Y900, 0x00)   /* Allow immediate Index(Buffer(){}), Index("qwerty"), Index(Package(){}) */
    Name (Y901, 0x01)   /* Predicate generates Implicit Return */
    Name (Y902, 0x01)   /* Expected is that Serialized method being invoked recursively on the same thread: */
    /* 1) 0 - doesn't cause */
    /* 2) otherwise - causes */
    /* exception in case it has either internal objects (including Methods) or Switches */
    /*
     * functional/reference
     *
     * Exclude temporary the relevant checking.
     *
     * All them should be set to non-zero after
     * clarifying the relevant issue, or provided
     * with the comment clarifying what is wrong in
     * the sub-test - don't remove them even in the
     * latter case.
     */
    Name (Q001, 0x01) /* Dereference of Store(Index(x,x,Index(x,x)), Index(x,x)) */
    Name (Q002, 0x00) /* The chain of Index_References */
    Name (Q003, 0x00) /* CURRENTLY: compiler failed CopyObject(xx, Index(xx,xx)) */
    Name (Q004, 0x00) /* Implicit Operand conversion on MS contradicts ACPI Spec */
    Name (Q005, 0x00) /* Method object as a Source of Index operation is treated as a call to that Method */
    Name (Q006, 0x00) /* on MS Name of an Object as an element of Package is treated as String */
    Name (Q007, 0x00) /* Disregard of the length Buffer Fields on MS are read as Buffers */
    Name (Q008, 0x00) /* On MS Store to LocalX containing a reference causes indirect access */
    Name (Q009, 0x00) /* It looks like on MS writing to a narrow Field Unit is splited on pieces */
    Name (Q00A, 0x00) /* On MS writing to unmodified bits of Field OpRegion implemented differently */
    Name (Q00B, 0x00) /* On MS Break in Switch is not implemented */
    /*
     * The non-zero value flags allow to run the relevant part of sub-tests.
     *
     * Each sub-test is conditioned by some rn0*.
     *
     * ATTENTION: many sub-tests conditioned by rn01-rn04 are not run now
     *            in general mode, they should be investigated.
     */
    Name (RN00, 0x01) /* Correct, no any remarks */
    Name (RN01, 0x00) /* Investigation needed */
    Name (RN02, 0x00) /* Classified as a bug */
    Name (RN03, 0x00) /* Causes exception */
    Name (RN04, 0x00) /* Regression */
    Name (RN05, 0x00) /* Long-time tests of bug-demo collection */
    Name (RN06, 0x00) /* 1 - CopyObject and Store of Method doesn't evaluate that Method */
    /*
     * Indicators of bugs.
     */
    Name (X104, 0x01)
    Name (X114, 0x01)
    Name (X127, 0x01)
    Name (X128, 0x01)
    Name (X131, 0x01)
    Name (X132, 0x01)
    Name (X133, 0x01)
    Name (X153, 0x01) /* Store() to Named Target allows to update the Source */
    Name (X170, 0x01)
    Name (X191, 0x01)
    Name (X192, 0x01)
    Name (X193, 0x01) /* 32-bit mode optional storing of Not, NAnd, or NOr */
    /* ASL operators result to Buffer Field produces 64-bit */

    Name (X194, 0x01) /* Unexpected implicit result object conversion when the */
    /* Target operand of ToBuffer operator is a Named Buffer */

    Name (X195, 0x00) /* Increment and Decrement of an either String or Buffer */
    /* Object will not change the type of the Object to Integer (~ y501) */
    /*
     * Flag, allows (when non-zero) access to the internal objects of method.
     *
     * No entry of type Method should occur in the declared path specified for search.
     */
    Name (FLG9, 0x00)
    /*
     * Set up run4 to non-zero when compile aslts (affects actually only Identity2MS)
     * for to run on MS, and reset it to zero when compile to run on ACPICA
     *
     *   for ACPICA - 0
     *   for MS     - non-zero
     */
    Name (RUN4, 0x00)
    /*
     * Current release of ASLTS test suite
     *
     * Layout:
     *   now simply incremental number
     *
     * Releases:
     *
     *   31.12.2004 - 1
     *   31.07.2005 - 2
     *   16.11.2005 - 3
     *   21.07.2006 - 4, (1115 files), with ACPICA version 20060721 released
     *   25.12.2006 - 5, (1277 files, 382 folder, 15.3 MB, 2006 tests, 38(44) test cases, 278 bugs of ACPICA)
     *   01.03.2007 - 6, (1403 files, 415 folder, 17.0 MB, 2227 tests, 40(46) test cases, 305 bugs of ACPICA)
     *   21.03.2007 - 7, (1409 files, 417 folder, 17.1 MB, 2236 tests, 40(46) test cases, 307 bugs of ACPICA)
     *   December 2011: - 0x15 (ACPI 5.0)
     *   April 2011: - 0x16, iASL fix for StartDependentFunction* descriptors to account for descriptor length.
     */
    Name (REL0, 0x16)
    /*
     * Settings number, used to adjust the aslts tests for different releases of ACPICA
     *
     * SETN - settings number of aslts:
     *        0 - release from Bob
     *        1 - release from Bob + my updates
     *        2 - new architecture of Method calculation
     *        3 - fixed bug 263,266
     *        4 - fixed bugs 275,276
     *        5 - fixed bugs 262 (corresponds to the 20070320 release of ACPICA)
     *        6 - 20074403
     *        all the greater - not used yet
     *
     * Used for to adjust some skippings of tests for different ACPICA releases
     * (set up this value manually). See Method SET2 below.
     *
     * Note: the value 5 of SETN corresponds to the 20070320 release of ACPICA.
     */
    Name (SETN, 0x05)
    /*
     * Adjust some skippings of tests for different ACPICA releases
     *
     * arg0 - settings number of aslts (see SETN for comment)
     */
    Method (SET2, 1, Serialized)
    {
        Local0 = Arg0
        /*
         if (ABUU) {
         Store(0, Local0)
         } else {
         Store(arg0, Local0)
         }
         */
        Switch (ToInteger (Local0))
        {
            Case (0x00)
            {
                Y135 = 0x00
                Y900 = 0x01
                Y901 = 0x00
                FLG9 = 0x01
                Y263 = 0x00
                Y275 = 0x00
                Y276 = 0x00
            }
            Case (0x01)
            {
                Y135 = 0x01
                Y900 = 0x00
                Y901 = 0x00
                FLG9 = 0x01
                Y263 = 0x00
                Y275 = 0x00
                Y276 = 0x00
            }
            Case (0x02)
            {
                Y135 = 0x00
                Y900 = 0x00
                Y901 = 0x01
                FLG9 = 0x00
                Y263 = 0x00
                Y275 = 0x00
                Y276 = 0x00
            }
            Case (0x03)
            {
                Y135 = 0x00
                Y900 = 0x01
                Y901 = 0x00
                FLG9 = 0x01
                Y263 = 0x01
                Y275 = 0x00
                Y276 = 0x00
                Y262 = 0x00
            }
            Case (0x04)
            {
                Y135 = 0x00 /* Store of Index reference to another element of the same Package causes hang */
                Y900 = 0x01 /* Allow immediate Index(Buffer(){}), Index("qwerty"), Index(Package(){}) */
                Y901 = 0x00 /* Predicate generates Implicit Return */
                FLG9 = 0x01 /* Non-zero allows accessing internal objects of method */
                Y263 = 0x01 /* The sequence of evaluating operands of expression with the named objects is violated */
                Y275 = 0x01 /* Pop result from bottom principle doesn't work */
                Y276 = 0x01 /* 'Large Reference Count' on AML code with LoadTable/UnLoad in a slack mode */
                Y262 = 0x00 /* Unexpected AE_STACK_OVERFLOW for a method call expression with nested calls */
                Y251 = 0x00 /* AE_ALREADY_EXISTS on multi-threading on Switch operator */
                Y300 = 0x00 /* Recursive calls to methods with the internal names (and Switches) should be provided */
            }
            Case (0x05)
            {
                Y135 = 0x00
                Y900 = 0x01
                Y901 = 0x01 /* Predicate generates Implicit Return since ACPICA release 20080926 */
                FLG9 = 0x01
                Y263 = 0x01
                Y275 = 0x01
                Y276 = 0x01
                Y262 = 0x01
                Y251 = 0x00
                Y300 = 0x00
            }
            Case (0x06)
            {
                Y135 = 0x00
                Y900 = 0x01
                Y901 = 0x00
                FLG9 = 0x01
                Y263 = 0x01
                Y275 = 0x01
                Y276 = 0x01
                Y262 = 0x01
                Y251 = 0x01
                Y300 = 0x01
                Y902 = 0x00
            }

        }

        If (!RUN4)
        {
            Concatenate ("Release of parent ACPICA code 0x", Revision, Debug)
            Concatenate ("Release of ASLTS test suite  0x", REL0, Debug)
            Concatenate ("Settings of ASLTS test suite 0x", Arg0, Debug)
        }
    }
