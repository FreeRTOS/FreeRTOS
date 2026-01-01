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
 * Expressions
 */

Name(z168, 168)

/*
 *  Table 1: operations applied in this file tests
 *
 *  1 - Add                    (arg0, arg1, RES)                    => Local7
 *  7 - Decrement              (arg0 --> RES)                       => Local7
 * 14 - Increment              (arg0 --> RES)                       => Local7
 *  9 - Divide                 (arg0, arg1, RES, RES)               => Local7
 * 38 - ShiftLeft              (arg0, arg1, RES)                    => Local7
 * 28 - Multiply               (arg0, arg1, RES)                    => Local7
 * 44 - Store                  (arg0, RES)                          => Local7
 * 33 - Or                     (arg0, arg1, RES)                    => Local7
 * 39 - ShiftRight             (arg0, arg1, RES)                    => Local7
 * 45 - Subtract               (arg0, arg1, RES)                    => Local7
 *  2 - And                    (arg0, arg1, RES)                    => Local7
 * 27 - Mod                    (arg0, arg1, RES)                    => Local7
 * 11 - FindSetLeftBit         (arg0, RES)                          => Local7
 * 12 - FindSetRightBit        (arg0, RES)                          => Local7
 * 53 - XOr                    (arg0, arg1, RES)                    => Local7
 * 29 - NAnd                   (arg0, arg1, RES)                    => Local7
 * 30 - NOr                    (arg0, arg1, RES)                    => Local7
 * 31 - Not                    (arg0, RES)                          => Local7
 * 22 - LNot                   (arg0)                               => Local7
 * 24 - LOr                    (arg0, arg1)                         => Local7
 * 16 - LAnd                   (arg0, arg1)                         => Local7
 * 17 - LEqual                 (arg0, arg1)                         => Local7
 * 18 - LGreater               (arg0, arg1)                         => Local7
 * 19 - LGreaterEqual          (arg0, arg1)                         => Local7
 * 20 - LLess                  (arg0, arg1)                         => Local7
 * 21 - LLessEqual             (arg0, arg1)                         => Local7
 * 23 - LNotEqual              (arg0, arg1)                         => Local7
 */

/*
 * This method doesn't contain verification and is
 * only used to determine opcodes not implemented on MS.
 * For verification is intended the method in51.
 *
 * The ASL Mod operation is not implemented on MS
 */
Method(in50,, Serialized)
{
  Name(ts, "in50")

  Store(0xabcd0000, Local0)
  Store(2, Local1)

  Add                    (Local0, Local1, Local2)
  Decrement              (Local0)
  Increment              (Local0)
  Divide                 (Local0, Local1, Local2, Local3)
  ShiftLeft              (Local0, Local1, Local2)
  Multiply               (Local0, Local1, Local2)
  Store                  (Local0, Local2)
  Or                     (Local0, Local1, Local2)
  ShiftRight             (Local0, Local1, Local2)
  Subtract               (Local0, Local1, Local2)
  And                    (Local0, Local1, Local2)
  if (chk0) {
    Mod              (Local0, Local1, Local2)
  }
  FindSetLeftBit         (Local0, Local2)
  FindSetRightBit        (Local0, Local2)
  XOr                    (Local0, Local1, Local2)
  NAnd                   (Local0, Local1, Local2)
  NOr                    (Local0, Local1, Local2)
  Not                    (Local0, Local2)
  Store(LNot             (Local0),         Local4)
  Store(LOr              (Local0, Local1), Local4)
  Store(LAnd             (Local0, Local1), Local4)
  Store(LEqual           (Local0, Local1), Local4)
  Store(LGreater         (Local0, Local1), Local4)
  Store(LGreaterEqual    (Local0, Local1), Local4)
  Store(LLess            (Local0, Local1), Local4)
  Store(LLessEqual       (Local0, Local1), Local4)
  Store(LNotEqual        (Local0, Local1), Local4)
}

/*
 * Internal objects of methods on MS consume some internal
 * resources of ACPI MS interpreter. We are forced to pull
 * some of internal objects of in51 out to prevent breakage
 * of MS interpreter.
 */
Name(ii31, 0xabcd0031)
Name(ii32, 0xabcd0032)
Name(ii33, 0xabcd0033)
Name(ii34, 0xabcd0034)
Name(ii35, 0xabcd0035)
Name(ii36, 0xabcd0036)
Name(ii37, 0xabcd0037)
Name(ii38, 0xabcd0038)
Name(ii39, 0xabcd0039)
Name(ii3a, 0xabcd003a)
Name(ii3b, 0xabcd003b)
Name(ii3c, 0xabcd003c)
Name(ii3d, 0xabcd003d)
Name(ii3e, 0xabcd003e)
Name(ii3f, 0xabcd003f)
Name(ii40, 0xabcd0040)
Name(ii41, 0xabcd0041)
Name(ii42, 0xabcd0042)
Name(ii43, 0xabcd0043)
Name(ii44, 0xabcd0044)
Name(ii45, 0xabcd0045)
Name(ii46, 0xabcd0046)
Name(ii47, 0xabcd0047)

/*
 * All opcodes of Table 1 above are applied in a single expression
 * and their results are then verified.
 *
 * The ASL Mod operation is not implemented on MS thus
 * it is not applied here. All other opcodes enumerated
 * in the table above are applied and verified in this test.
 */
Method(in51, 7, Serialized)
{
  Name(ts, "in51")

  Name(i000, 0x00010000)
  Name(i001, 0x0a510010)
  Name(i002, 0x15210800)
  Name(i003, 0xfeabc8d9)
  Name(i004, 0x1234bcde)
  Name(i005, 0xfe04bcde)
  Name(i006, 0x12345678)
  Name(i007, 0x01000000)
  Name(i008, 0x60f5c7a2)

  Name(ii00, 0xabcd0000)
  Name(ii01, 0xabcd0001)
  Name(ii02, 0xabcd0002)
  Name(ii03, 0xabcd0003)
  Name(ii04, 0xabcd0004)
  Name(ii05, 0xabcd0005)
  Name(ii06, 0xabcd0006)
  Name(ii07, 0xabcd0007)
  Name(ii08, 0xabcd0008)
  Name(ii09, 0xabcd0009)
  Name(ii0a, 0xabcd000a)
  Name(ii0b, 0xabcd000b)
  Name(ii0c, 0xabcd000c)
  Name(ii0d, 0xabcd000d)
  Name(ii0e, 0xabcd000e)
  Name(ii0f, 0xabcd000f)
  Name(ii10, 0xabcd0010)
  Name(ii11, 0xabcd0011)
  Name(ii12, 0xabcd0012)
  Name(ii13, 0xabcd0013)
  Name(ii14, 0xabcd0014)
  Name(ii15, 0xabcd0015)
  Name(ii16, 0xabcd0016)
  Name(ii17, 0xabcd0017)
  Name(ii18, 0xabcd0018)
  Name(ii19, 0xabcd0019)
  Name(ii1a, 0xabcd001a)
  Name(ii1b, 0xabcd001b)
  Name(ii1c, 0xabcd001c)
  Name(ii1d, 0xabcd001d)
  Name(ii1e, 0xabcd001e)
  Name(ii1f, 0xabcd001f)
  Name(ii20, 0xabcd0020)
  Name(ii21, 0xabcd0021)
  Name(ii22, 0xabcd0022)
  Name(ii23, 0xabcd0023)
  Name(ii24, 0xabcd0024)
  Name(ii25, 0xabcd0025)
  Name(ii26, 0xabcd0026)
  Name(ii27, 0xabcd0027)
  Name(ii28, 0xabcd0028)
  Name(ii29, 0xabcd0029)
  Name(ii2a, 0xabcd002a)
  Name(ii2b, 0xabcd002b)
  Name(ii2c, 0xabcd002c)
  Name(ii2d, 0xabcd002d)
  Name(ii2e, 0xabcd002e)
  Name(ii2f, 0xabcd002f)
  Name(ii30, 0xabcd0030)
/*
  Name(ii31, 0xabcd0031)
  Name(ii32, 0xabcd0032)
  Name(ii33, 0xabcd0033)
  Name(ii34, 0xabcd0034)
  Name(ii35, 0xabcd0035)
  Name(ii36, 0xabcd0036)
  Name(ii37, 0xabcd0037)
  Name(ii38, 0xabcd0038)
  Name(ii39, 0xabcd0039)
  Name(ii3a, 0xabcd003a)
  Name(ii3b, 0xabcd003b)
  Name(ii3c, 0xabcd003c)
  Name(ii3d, 0xabcd003d)
  Name(ii3e, 0xabcd003e)
  Name(ii3f, 0xabcd003f)
  Name(ii40, 0xabcd0040)
  Name(ii41, 0xabcd0041)
  Name(ii42, 0xabcd0042)
  Name(ii43, 0xabcd0043)
  Name(ii44, 0xabcd0044)
  Name(ii45, 0xabcd0045)
  Name(ii46, 0xabcd0046)
  Name(ii47, 0xabcd0047)
*/


  Add(
    Add(
      Add(
        Add(
          Add(
            Add(
              Add(
                Add(
                  Add(
                    Subtract(
                      Or(
                        And(
                          //Store(
                            Multiply(
                              ShiftLeft(
                                Divide(
                                  Add(
                                    Add(
                                      Add(
                                        Add(
                                          Increment(i000),
                                          Increment(i000),
                                          i000),
                                        Add(
                                          Increment(i000),
                                          Increment(i000),
                                          i000),
                                        Local0),
                                      Add(
                                        Add(
                                          Decrement(i000),
                                          Decrement(i000),
                                          i000),
                                        Add(
                                          Decrement(i000),
                                          Decrement(i000),
                                          i000),
                                        Local1),
                                      arg0),
                                    Add(
                                      Add(
                                        Increment(i000),
                                        Decrement(i000),
                                        i000),
                                      Add(
                                        Increment(i000),
                                        Decrement(i000),
                                        i000),
                                      Local2),
                                    arg1),
                                  17,			      // Divide
                                  ii00,
                                  Local3),	    // Divide
                                3,			      // ShiftLeft
                                ii01),		    // ShiftLeft
                              2,			      // Multiply
                              i000),		    // Multiply
                            //arg2),		    // Store
                          0xffffffff,	  // And
                          ii0c),		    // And
                        0x20000000,		// Or
                        ii0d),		    // Or

                      Multiply(
                        And(
                          Add(
                            Add(
                              Add(
                                XOr(
                                  Add(
                                    Add(
                                      Add(
                                        //Store(
                                          And(
                                            ShiftRight(
                                              Or(
                                                i001,
                                                0x15210800,
                                                Local5),
                                              3,			      // ShiftRight
                                              ii02),		    // ShiftRight
                                            0x035E2102,	  // And
                                            Local6),		    // And
                                          //Local6),		  // Store
                                        //Add(0, 7, ii03),  // OLD
                                        Add(ii0d, 7, ii03), // NEW
                                        ii04),		  // Add
                                      FindSetLeftBit(0x7bcd0000, ii05),
                                      arg3),		    // Add
                                    FindSetRightBit(0x7bcd0000, ii06),
                                    arg4),		    // Add
                                  0x11b4937f,		// XOr
                                  arg5),		    // XOr
                                NAnd(i003, 0xffffffff, ii07),
                                arg6),		    // Add
                              NOr(i004, 0xf8f0f0f0, ii08),
                              Local7),		// Add
                            Not(i005, ii09),
                          ii0a),		    // Add
                        0xffffffff,		// And
                        ii0b),		// And
                      And(Store(LNot(Store(LNot(ii0b), ii0e)), ii0f), 0x01)),			// Multiply
                    Local4),		  // Subtract
                  Store(LNot(Store(LNot(i006), ii11)), ii12),
                  ii10),		    // Add
                Store(LOr(LNot(And(Store(LOr(i007, 0), ii14), 0x01)), 0), ii15),
                ii13),		// Add
              Store(LAnd(LNot(And(Store(LAnd(i007, 1), ii16), 0x01)), 0), ii17),
              ii18),		// Add
            Add(
              Store(LEqual(i008, 0x60f5c7a2), ii19),
              Store(LEqual(i008, 0x60f5c7a0), ii1a), ii1b),
            ii1c),		// Add
          Add(
            Add(
              Store(LGreater(i008, 0x60f5c7a2), ii1d),
              Store(LGreater(i008, 0x60f5c7a3), ii1e), ii1f),
            Add(
              Store(LGreater(i008, 0x60f5c7a1), ii20),
              Store(LGreater(i008, 0x60f5c7a0), ii21), ii22),
            ii23),
          ii24),		// Add
        Add(
          Add(
            Store(LGreaterEqual(i008, 0x60f5c7a2), ii25),
            Store(LGreaterEqual(i008, 0x60f5c7a3), ii26), ii27),
          Add(
            Store(LGreaterEqual(i008, 0x60f5c7a1), ii28),
            Store(LGreaterEqual(i008, 0x60f5c7a0), ii29), ii2a),
          ii2b),
        ii2c),		// Add
      Add(
        Add(
          Store(LLess(i008, 0x60f5c7a2), ii2d),
          Store(LLess(i008, 0x60f5c7a3), ii2e), ii2f),
        Add(
          Store(LLess(i008, 0x60f5c7a1), ii30),
          Store(LLess(i008, 0x60f5c7a0), ii31), ii32),
        ii33),
      ii34),		// Add
    Add(
      Add(
        Store(LLessEqual(i008, 0x60f5c7a2), ii35),
        Store(LLessEqual(i008, 0x60f5c7a3), ii36), ii37),
      Add(
        Store(LLessEqual(i008, 0x60f5c7a1), ii38),
        Store(LLessEqual(i008, 0x60f5c7a0), ii39), ii3a),
      ii3b),
    ii3c),		// Add
  Add(
    Add(
      Store(LNotEqual(i008, 0x60f5c7a2), ii3d),
      Store(LNotEqual(i008, 0x60f5c7a3), ii3e), ii3f),
    Add(
      Store(LNotEqual(i008, 0x60f5c7a1), ii40),
      Store(LNotEqual(i008, 0x60f5c7a0), ii41), ii42),
    ii43),
  ii44)			// Add


  if (LNotEqual(Local0, 0x0006000C)) {
    err(ts, z168, __LINE__, 0, 0, Local0, 0x0006000C)
  }
  if (LNotEqual(Local1, 0x0018002A)) {
    err(ts, z168, __LINE__, 0, 0, Local1, 0x0018002A)
  }
  if (LNotEqual(Local2, 0x006000A6)) {
    err(ts, z168, __LINE__, 0, 0, Local2, 0x006000A6)
  }
  if (LNotEqual(arg0, 0x001E0036)) {
    err(ts, z168, __LINE__, 0, 0, arg0, 0x001E0036)
  }
  if (LNotEqual(arg1, 0x007E00DC)) {
    err(ts, z168, __LINE__, 0, 0, arg1, 0x007E00DC)
  }
  if (LNotEqual(ii00, 0x00000006)) {
    err(ts, z168, __LINE__, 0, 0, ii00, 0x00000006)
  }
  if (LNotEqual(Local3, 0x00076976)) {
    err(ts, z168, __LINE__, 0, 0, Local3, 0x00076976)
  }
  if (LNotEqual(ii01, 0x003B4BB0)) {
    err(ts, z168, __LINE__, 0, 0, ii01, 0x003B4BB0)
  }
  if (LNotEqual(arg2, 0x00769760)) {
    err(ts, z168, __LINE__, 0, 0, arg2, 0x00769760)
  }
  if (LNotEqual(Local5, 0x1F710810)) {
    err(ts, z168, __LINE__, 0, 0, Local5, 0x1F710810)
  }
  if (LNotEqual(ii02, 0x03EE2102)) {
    err(ts, z168, __LINE__, 0, 0, ii02, 0x03EE2102)
  }
  if (LNotEqual(Local6, 0x034E2102)) {
    err(ts, z168, __LINE__, 0, 0, Local6, 0x034E2102)
  }
  if (LNotEqual(ii03, 0x00000007)) {
    err(ts, z168, __LINE__, 0, 0, ii03, 0x00000007)
  }
  if (LNotEqual(ii04, 0x034E2109)) {
    err(ts, z168, __LINE__, 0, 0, ii04, 0x034E2109)
  }
  if (LNotEqual(ii05, 0x0000001F)) {
    err(ts, z168, __LINE__, 0, 0, ii05, 0x0000001F)
  }
  if (LNotEqual(arg3, 0x034E2128)) {
    err(ts, z168, __LINE__, 0, 0, arg3, 0x034E2128)
  }
  if (LNotEqual(ii06, 0x00000011)) {
    err(ts, z168, __LINE__, 0, 0, ii06, 0x00000011)
  }
  if (LNotEqual(arg4, 0x034E2139)) {
    err(ts, z168, __LINE__, 0, 0, arg4, 0x034E2139)
  }
  if (LNotEqual(arg5, 0x12FAB246)) {
    err(ts, z168, __LINE__, 0, 0, arg5, 0x12FAB246)
  }
  if (LNotEqual(ii07, 0xFFFFFFFF01543726)) {
    err(ts, z168, __LINE__, 0, 0, ii07, 0xFFFFFFFF01543726)
  }
  if (LNotEqual(arg6, 0xFFFFFFFF144EE96C)) {
    err(ts, z168, __LINE__, 0, 0, arg6, 0xFFFFFFFF144EE96C)
  }
  if (LNotEqual(ii08, 0xFFFFFFFF050B0301)) {
    err(ts, z168, __LINE__, 0, 0, ii08, 0xFFFFFFFF050B0301)
  }
  if (LNotEqual(Local7, 0xFFFFFFFE1959EC6D)) {
    err(ts, z168, __LINE__, 0, 0, Local7, 0xFFFFFFFE1959EC6D)
  }
  if (LNotEqual(ii09, 0xFFFFFFFF01FB4321)) {
    err(ts, z168, __LINE__, 0, 0, ii09, 0xFFFFFFFF01FB4321)
  }
  if (LNotEqual(ii0a, 0xFFFFFFFD1B552F8E)) {
    err(ts, z168, __LINE__, 0, 0, ii0a, 0xFFFFFFFD1B552F8E)
  }
  if (LNotEqual(ii0b, 0x1B552F8E)) {
    err(ts, z168, __LINE__, 0, 0, ii0b, 0x1B552F8E)
  }
  if (LNotEqual(ii0c, 0x00769760)) {
    err(ts, z168, __LINE__, 0, 0, ii0c, 0x00769760)
  }
  if (LNotEqual(ii0d, 0x20769760)) {
    err(ts, z168, __LINE__, 0, 0, ii0d, 0x20769760)
  }
  if (LNotEqual(ii0e, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii0e, 0)
  }
  if (LNotEqual(ii0f, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii0f, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(Local4, 0x052167D2)) {
    err(ts, z168, __LINE__, 0, 0, Local4, 0x052167D2)
  }
  if (LNotEqual(ii10, 0x052167D1)) {
    err(ts, z168, __LINE__, 0, 0, ii10, 0x052167D1)
  }
  if (LNotEqual(ii11, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii11, 0)
  }
  if (LNotEqual(ii12, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii12, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii13, 0x00000000052167D1)) {
    err(ts, z168, __LINE__, 0, 0, ii13, 0x00000000052167D1)
  }
  if (LNotEqual(ii14, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii14, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii15, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii15, 0)
  }
  if (LNotEqual(ii16, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii16, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii17, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii17, 0)
  }
  if (LNotEqual(ii18, 0x052167D1)) {
    err(ts, z168, __LINE__, 0, 0, ii18, 0x052167D1)
  }
  if (LNotEqual(ii19, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii19, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii1a, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii1a, 0)
  }
  if (LNotEqual(ii1b, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii1c, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii1c, 0x052167D0)) {
    err(ts, z168, __LINE__, 0, 0, ii1d, 0x052167D0)
  }
  if (LNotEqual(ii1d, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii1d, 0)
  }
  if (LNotEqual(ii1e, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii1e, 0)
  }
  if (LNotEqual(ii1f, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii1f, 0)
  }
  if (LNotEqual(ii20, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii20, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii21, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii21, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii22, 0xFFFFFFFFFFFFFFFE)) {
    err(ts, z168, __LINE__, 0, 0, ii22, 0xFFFFFFFFFFFFFFFE)
  }
  if (LNotEqual(ii23, 0xFFFFFFFFFFFFFFFE)) {
    err(ts, z168, __LINE__, 0, 0, ii23, 0xFFFFFFFFFFFFFFFE)
  }
  if (LNotEqual(ii24, 0x052167CE)) {
    err(ts, z168, __LINE__, 0, 0, ii24, 0x052167CE)
  }
  if (LNotEqual(ii25, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii25, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii26, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii26, 0)
  }
  if (LNotEqual(ii27, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii27, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii28, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii28, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii29, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii29, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii2a, 0xFFFFFFFFFFFFFFFE)) {
    err(ts, z168, __LINE__, 0, 0, ii2a, 0xFFFFFFFFFFFFFFFE)
  }
  if (LNotEqual(ii2b, 0xFFFFFFFFFFFFFFFD)) {
    err(ts, z168, __LINE__, 0, 0, ii2b, 0xFFFFFFFFFFFFFFFD)
  }
  if (LNotEqual(ii2c, 0x052167CB)) {
    err(ts, z168, __LINE__, 0, 0, ii2c, 0x052167CB)
  }
  if (LNotEqual(ii2d, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii2d, 0)
  }
  if (LNotEqual(ii2e, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii2e, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii2f, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii2f, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii30, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii30, 0)
  }
  if (LNotEqual(ii31, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii31, 0)
  }
  if (LNotEqual(ii32, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii32, 0)
  }
  if (LNotEqual(ii33, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii33, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii34, 0x052167CA)) {
    err(ts, z168, __LINE__, 0, 0, ii34, 0x052167CA)
  }
  if (LNotEqual(ii35, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii35, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii36, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii36, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii37, 0xFFFFFFFFFFFFFFFE)) {
    err(ts, z168, __LINE__, 0, 0, ii37, 0xFFFFFFFFFFFFFFFE)
  }
  if (LNotEqual(ii38, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii38, 0)
  }
  if (LNotEqual(ii39, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii39, 0)
  }
  if (LNotEqual(ii3a, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii3a, 0)
  }
  if (LNotEqual(ii3b, 0xFFFFFFFFFFFFFFFE)) {
    err(ts, z168, __LINE__, 0, 0, ii3b, 0xFFFFFFFFFFFFFFFE)
  }
  if (LNotEqual(ii3c, 0x052167C8)) {
    err(ts, z168, __LINE__, 0, 0, ii3c, 0x052167C8)
  }
  if (LNotEqual(ii3d, 0)) {
    err(ts, z168, __LINE__, 0, 0, ii3d, 0)
  }
  if (LNotEqual(ii3e, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii3e, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii3f, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii3f, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii40, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii40, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii41, 0xFFFFFFFFFFFFFFFF)) {
    err(ts, z168, __LINE__, 0, 0, ii41, 0xFFFFFFFFFFFFFFFF)
  }
  if (LNotEqual(ii42, 0xFFFFFFFFFFFFFFFE)) {
    err(ts, z168, __LINE__, 0, 0, ii42, 0xFFFFFFFFFFFFFFFE)
  }
  if (LNotEqual(ii43, 0xFFFFFFFFFFFFFFFD)) {
    err(ts, z168, __LINE__, 0, 0, ii43, 0xFFFFFFFFFFFFFFFD)
  }
  if (LNotEqual(ii44, 0x052167C5)) {
    err(ts, z168, __LINE__, 0, 0, ii44, 0x052167C5)
  }
}

Method(ini5)
{
  SRMT("in50")
  in50()

  SRMT("in51")
  in51(0,0,0,0,0,0,0)

  CH03("ini5", z168, 0x000, __LINE__, 0)
}
