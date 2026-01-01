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
 * Test of Return
 */

Name(z139, 139)

Method(mf72, 1, Serialized)
{
	Name(i000, 0)
	Name(cmp0, 0)
	Name(md00, 0)

	Store(arg0, md00)

	Name(ts, "mf72")

	Method(m000)
	{
	}

	Method(m001)
	{
		if (0xabcd0001) {
			return (0xabcd0010)
		}
	}

	Method(m002)
	{
		if (0xabcd0000) {
		if (0xabcd0001) {
			return (0xabcd0010)
		}}
	}

	Method(m003)
	{
		while (0xabcd0000) {
			return (0xabcd0020)
		}
	}

	Method(m004, 7, Serialized)
	{
	Name(ret4, 0)
	Name(r400, 0)
	Name(r401, 0)
	Name(r402, 0)
	Name(r403, 0)
	Name(r404, 0)
	Name(r405, 0)
	Name(r406, 0)
	Name(r407, 0)

	Method(m005, 7, Serialized)
	{
	Name(ret5, 0)
	Name(r500, 0)
	Name(r501, 0)
	Name(r502, 0)
	Name(r503, 0)
	Name(r504, 0)
	Name(r505, 0)
	Name(r506, 0)
	Name(r507, 0)

	Method(m006, 7, Serialized)
	{
	Name(ret6, 0)
	Name(r600, 0)
	Name(r601, 0)
	Name(r602, 0)
	Name(r603, 0)
	Name(r604, 0)
	Name(r605, 0)
	Name(r606, 0)
	Name(r607, 0)

	Method(m007, 7, Serialized)
	{
	Name(ret7, 0)
	Name(r700, 0)
	Name(r701, 0)
	Name(r702, 0)
	Name(r703, 0)
	Name(r704, 0)
	Name(r705, 0)
	Name(r706, 0)
	Name(r707, 0)

	Method(m008, 7)
	{
	Name(ret8, 0)
	Name(i000, 0)
	Name(i001, 0)
	Name(i002, 0)
	Name(i003, 0)

          m000()
          m001()
          if (Store(0xaaaa0007, i001)) {
              Increment(i002)
              Store(Add(0xaaaa0008, 0), Local5)
              Store(Subtract(0xaaaa0009, 0), Local5)
              if (LEqual(arg0, 0)) {
                  return (0x55550000)
              }
              Store(Multiply(0xaaaa000a, 1), Local5)
              Store(0xaaaa000d, i001)
              Decrement(i001)
          }
          m002()
          m003()
          while (0xabcd0000) {
            m000()
            m001()
            if (LEqual(arg0, 1)) {
                return (0x55550001)
            }
            Store(0, i000)
            m002()
            m003()

            Switch (0xabcd0100) {
            case (0xabcd0100) {

            if (0xabcd0001) {
              while (0xabcd0002) {
                if (LNotEqual(arg0, 2)) {
                  while (0xabcd0004) {
                    if (Store(0xaaaa0007, i001)) {
                        Increment(i002)
                        Store(Add(0xaaaa0008, 0), Local5)
                        Store(Subtract(0xaaaa0009, 0), Local5)
                        if (LEqual(arg0, 3)) {
                            return (0x55550003)
                        }
                        Store(Multiply(0xaaaa000a, 1), Local5)
                        Store(0xaaaa000d, i001)
                        Decrement(i001)
                    }

                    Switch (0xabcd0200) {
                    case (0xabcd0300) {
                          Store("Never", Debug)
                    }
                    Default {

                    if (0xabcd0005) {
                      while (0xabcd0006) {
                        if (LNotEqual(arg0, 4)) {
                          m000()
                          m001()
                          if (LEqual(arg0, 5)) {
                              return (0x55550005)
                          }
                          m002()
                          m003()
                          while (0xabcd0008) {
                            if (LEqual(arg0, 6)) {
                                return (0x55550006)
                            }
                            if (0xabcd0009) {
                              if (LEqual(arg0, 7)) {
                                  return (0x55550007)
                              }
                              while (0xabcd000a) {
                                if (LNotEqual(arg0, 8)) {
                                  while (0xabcd000c) {
                                    if (0xabcd000d) {
                                      while (0xabcd000e) {
                                        if (0xabcd000f) {
                                          if (0) {
                                              Store("Impossible 0", Debug)
                                          } else {
                                              if (0xabcd0010) {
                                                  Store(100, i003)
                                                  switch (i003) {
                                                  case (1) {
                                                     return (0xdddd0000)
                                                  }
                                                  case (2) {
                                                     return (0xdddd0001)
                                                  }
                                                  Default {
                                                     return (0x55550009)
                                                  }
                                                  }
                                                  return (0xdddd0002)
                                              }
                                          }
                                        }
                                      }
                                    }
                                  }
                                  m000()
                                  m001()
                                } else {
                                  m002()
                                  m003()
                                  Store(1, i003)
                                  switch (i003) {
                                  case (1) {
                                     return (0x55550008)
                                  }
                                  case (2) {
                                     return (0xdddd0003)
                                  }
                                  Default {
                                     return (0xdddd0004)
                                  }
                                  }
                                  return (0xdddd0005)
                                }
                              }
                            }
                          }
                          m000()
                          m001()
                          m002()
                          m003()
                        } else {
                          Store(2, i003)
                          switch (i003) {
                          case (1) {
                             return (0xdddd0006)
                          }
                          case (2) {
                             return (0x55550004)
                          }
                          Default {
                             return (0xdddd0007)
                          }
                          }
                          return (0xdddd0008)
                        }
                      }
                    }
                    } /* Default 0xabcd0300 */
                    } /* Switch (0xabcd0200) */
                  }
                } else {
                  return (0x55550002)
                }
              }
            }
            } /* case (0xabcd0100) */
            } /* Switch (0xabcd0100) */
          }

	return (ret8)
	} /* m008 */

	Method(m009, 7)
	{
	Name(ret9, 0)
	Name(r900, 0)
	Name(r901, 0)
	Name(r902, 0)
	Name(r903, 0)
	Name(r904, 0)
	Name(r905, 0)
	Name(r906, 0)
	Name(r907, 0)

	Name(i000, 0)
	Name(i001, 0)
	Name(i002, 0)
	Name(i003, 0)

          m000()
          m001()
          if (Store(0xaaaa0007, i001)) {
              Increment(i002)
              Store(Add(0xaaaa0008, 0), Local5)
              Store(Subtract(0xaaaa0009, 0), Local5)
              if (LEqual(arg0, 0)) {
                  CopyObject(Store(CopyObject(Store(CopyObject(CopyObject(Store(Store(
                      m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
                      r900), r901), r902), r903), r904), r905), r906), ret9)
                  return (ret9)
              //  return (0x55550000)
              }
              Store(Multiply(0xaaaa000a, 1), Local5)
              Store(0xaaaa000d, i001)
              Decrement(i001)
          }
          m002()
          m003()
          while (0xabcd0000) {
            m000()
            m001()
            if (LEqual(arg0, 1)) {
                Store(Store(CopyObject(Store(Store(Store(Store(Store(
                      m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
                      r900), r901), r902), r903), r904), r905), r906), ret9)
                return (ret9)
             // return (0x55550001)
            }
            Store(0, i000)
            m002()
            m003()

            Switch (0xabcd0100) {
            case (0xabcd0100) {

            if (0xabcd0001) {
              while (0xabcd0002) {
                if (LNotEqual(arg0, 2)) {
                  while (0xabcd0004) {
                    if (Store(0xaaaa0007, i001)) {
                        Increment(i002)
                        Store(Add(0xaaaa0008, 0), Local5)
                        Store(Subtract(0xaaaa0009, 0), Local5)
                        if (LEqual(arg0, 3)) {
                            Store(Store(CopyObject(Store(Store(Store(Store(Store(
                                  m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
                                  r900), r901), r902), r903), r904), r905), r906), ret9)
                            return (ret9)
                         // return (0x55550003)
                        }
                        Store(Multiply(0xaaaa000a, 1), Local5)
                        Store(0xaaaa000d, i001)
                        Decrement(i001)
                    }

                    Switch (0xabcd0200) {
                    case (0xabcd0300) {
                          Store("Never", Debug)
                    }
                    Default {

                    if (0xabcd0005) {
                      while (0xabcd0006) {
                        if (LNotEqual(arg0, 4)) {
                          m000()
                          m001()
                          if (LEqual(arg0, 5)) {
                              Store(Store(CopyObject(Store(Store(Store(Store(Store(
                                    m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
                                    r900), r901), r902), r903), r904), r905), r906), ret9)
                              return (ret9)
                           // return (0x55550005)
                          }
                          m002()
                          m003()
                          while (0xabcd0008) {
                            if (LEqual(arg0, 6)) {
                                Store(Store(CopyObject(Store(Store(Store(Store(Store(
                                      m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
                                      r900), r901), r902), r903), r904), r905), r906), ret9)
                                return (ret9)
                             // return (0x55550006)
                            }
                            if (0xabcd0009) {
                              if (LEqual(arg0, 7)) {
                                  Store(Store(CopyObject(Store(Store(Store(Store(Store(
                                        m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
                                        r900), r901), r902), r903), r904), r905), r906), ret9)
                                  return (ret9)
                               // return (0x55550007)
                              }
                              while (0xabcd000a) {
                                if (LNotEqual(arg0, 8)) {
                                  while (0xabcd000c) {
                                    if (0xabcd000d) {
                                      while (0xabcd000e) {
                                        if (0xabcd000f) {
                                          if (0) {
                                              Store("Impossible 0", Debug)
                                          } else {
                                              if (0xabcd0010) {
                                                  Store(100, i003)
                                                  switch (i003) {
                                                  case (1) {
                                                     return (0xdddd0000)
                                                  }
                                                  case (2) {
                                                     return (0xdddd0001)
                                                  }
                                                  Default {
                                                     Store(Store(CopyObject(Store(Store(Store(Store(Store(
                                                           m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
                                                           r900), r901), r902), r903), r904), r905), r906), ret9)
                                                     return (ret9)
                                                  // return (0x55550009)
                                                  }
                                                  }
                                                  return (0xdddd0002)
                                              }
                                          }
                                        }
                                      }
                                    }
                                  }
                                  m000()
                                  m001()
                                } else {
                                  m002()
                                  m003()
                                  Store(1, i003)
                                  switch (i003) {
                                  case (1) {
                                     Store(Store(CopyObject(Store(Store(Store(Store(Store(
                                           m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
                                           r900), r901), r902), r903), r904), r905), r906), ret9)
                                     return (ret9)
                                  // return (0x55550008)
                                  }
                                  case (2) {
                                     return (0xdddd0003)
                                  }
                                  Default {
                                     return (0xdddd0004)
                                  }
                                  }
                                  return (0xdddd0005)
                                }
                              }
                            }
                          }
                          m000()
                          m001()
                          m002()
                          m003()
                        } else {
                          Store(2, i003)
                          switch (i003) {
                          case (1) {
                             return (0xdddd0006)
                          }
                          case (2) {
                             Store(Store(CopyObject(Store(Store(Store(Store(Store(
                                   m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
                                   r900), r901), r902), r903), r904), r905), r906), ret9)
                             return (ret9)
                          // return (0x55550004)
                          }
                          Default {
                             return (0xdddd0007)
                          }
                          }
                          return (0xdddd0008)
                        }
                      }
                    }
                    } /* Default 0xabcd0300 */
                    } /* Switch (0xabcd0200) */
                  }
                } else {
                  Store(Store(CopyObject(Store(Store(Store(Store(Store(
                        m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
                        r900), r901), r902), r903), r904), r905), r906), ret9)
                  return (ret9)
               // return (0x55550002)
                }
              }
            }
            } /* case (0xabcd0100) */
            } /* Switch (0xabcd0100) */
          }

	return (ret9)
	} /* m009 */

	Store(arg0, Local0)
	Store(arg1, Local1)
	Store(arg2, Local2)
	Store(arg3, Local3)
	Store(arg4, Local4)
	Store(arg5, Local5)
	Store(arg6, Local6)

	if (LEqual(md00, 0)) {
		CopyObject(Store(CopyObject(Store(CopyObject(CopyObject(Store(Store(
			m008(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
			r700), r701), r702), r703), r704), r705), r706), ret7)
	} else {
		Store(Store(Store(Store(Store(Store(Store(Store(
			m009(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
			r700), r701), r702), r703), r704), r705), r706), ret7)
	}

	m4c0(ts, arg0, Local0, Local0)
	m4c0(ts, arg1, Local1, Local1)
	m4c0(ts, arg2, Local2, Local2)
	m4c0(ts, arg3, Local3, Local3)
	m4c0(ts, arg4, Local4, Local4)
	m4c0(ts, arg5, Local5, Local5)
	m4c0(ts, arg6, Local6, Local6)

	return (ret7)
	} /* m007 */

	Store(arg0, Local0)
	Store(arg1, Local1)
	Store(arg2, Local2)
	Store(arg3, Local3)
	Store(arg4, Local4)
	Store(arg5, Local5)
	Store(arg6, Local6)

//	CopyObject(CopyObject(CopyObject(CopyObject(CopyObject(CopyObject(CopyObject(CopyObject(
	CopyObject(CopyObject(CopyObject(CopyObject(CopyObject(CopyObject(CopyObject(Store(
			m007(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
			r600), r601), r602), r603), r604), r605), r606), ret6)

	m4c0(ts, arg0, Local0, Local0)
	m4c0(ts, arg1, Local1, Local1)
	m4c0(ts, arg2, Local2, Local2)
	m4c0(ts, arg3, Local3, Local3)
	m4c0(ts, arg4, Local4, Local4)
	m4c0(ts, arg5, Local5, Local5)
	m4c0(ts, arg6, Local6, Local6)

	return (ret6)
	} /* m006 */

	Store(arg0, Local0)
	Store(arg1, Local1)
	Store(arg2, Local2)
	Store(arg3, Local3)
	Store(arg4, Local4)
	Store(arg5, Local5)
	Store(arg6, Local6)

	Store(Store(Store(Store(Store(Store(Store(Store(
			m006(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
			r500), r501), r502), r503), r504), r505), r506), ret5)

	m4c0(ts, arg0, Local0, Local0)
	m4c0(ts, arg1, Local1, Local1)
	m4c0(ts, arg2, Local2, Local2)
	m4c0(ts, arg3, Local3, Local3)
	m4c0(ts, arg4, Local4, Local4)
	m4c0(ts, arg5, Local5, Local5)
	m4c0(ts, arg6, Local6, Local6)

	return (ret5)
	} /* m005 */

	Store(arg0, Local0)
	Store(arg1, Local1)
	Store(arg2, Local2)
	Store(arg3, Local3)
	Store(arg4, Local4)
	Store(arg5, Local5)
	Store(arg6, Local6)

	Store(Store(Store(Store(Store(Store(Store(Store(
			m005(arg0, arg1, arg2, arg3, arg4, arg5, arg6),
			r400), r401), r402), r403), r404), r405), r406), ret4)

	m4c0(ts, arg0, Local0, Local0)
	m4c0(ts, arg1, Local1, Local1)
	m4c0(ts, arg2, Local2, Local2)
	m4c0(ts, arg3, Local3, Local3)
	m4c0(ts, arg4, Local4, Local4)
	m4c0(ts, arg5, Local5, Local5)
	m4c0(ts, arg6, Local6, Local6)

	return (ret4)
	} /* m004 */

	// ===================== 0:

	Store(0x55550000, cmp0)
	Store(0, Local0)
	Store(0xaaaa0001, Local1)
	Store(0xaaaa0002, Local2)
	Store(0xaaaa0003, Local3)
	Store(0xaaaa0004, Local4)
	Store(0xaaaa0005, Local5)
	Store(0xaaaa0006, Local6)
	Store(0xaaaa0007, Local7)

	Store(
		m004(Local0, Local1, Local2, Local3, Local4, Local5, Local6),
		i000)
	if (LNotEqual(i000, cmp0)) {
		err("", z139, __LINE__, 0, 0, i000, cmp0)
	}
	m4c0(ts, Local0, 0, 0)
	m4c0(ts, Local1, 0xaaaa0001, 0xaaaa0001)
	m4c0(ts, Local2, 0xaaaa0002, 0xaaaa0002)
	m4c0(ts, Local3, 0xaaaa0003, 0xaaaa0003)
	m4c0(ts, Local4, 0xaaaa0004, 0xaaaa0004)
	m4c0(ts, Local5, 0xaaaa0005, 0xaaaa0005)
	m4c0(ts, Local6, 0xaaaa0006, 0xaaaa0006)
	m4c0(ts, Local7, 0xaaaa0007, 0xaaaa0007)

	// ===================== 1:

	Store(0x55550001, cmp0)
	Store(1, Local0)

	Store(
		m004(Local0, Local1, Local2, Local3, Local4, Local5, Local6),
		i000)
	if (LNotEqual(i000, cmp0)) {
		err("", z139, __LINE__, 0, 0, i000, cmp0)
	}
	m4c0(ts, Local0, 1, 1)
	m4c0(ts, Local1, 0xaaaa0001, 0xaaaa0001)
	m4c0(ts, Local2, 0xaaaa0002, 0xaaaa0002)
	m4c0(ts, Local3, 0xaaaa0003, 0xaaaa0003)
	m4c0(ts, Local4, 0xaaaa0004, 0xaaaa0004)
	m4c0(ts, Local5, 0xaaaa0005, 0xaaaa0005)
	m4c0(ts, Local6, 0xaaaa0006, 0xaaaa0006)
	m4c0(ts, Local7, 0xaaaa0007, 0xaaaa0007)

	// ===================== 2:

	Store(0x55550002, cmp0)
	Store(2, Local0)

	Store(
		m004(Local0, Local1, Local2, Local3, Local4, Local5, Local6),
		i000)
	if (LNotEqual(i000, cmp0)) {
		err("", z139, __LINE__, 0, 0, i000, cmp0)
	}
	m4c0(ts, Local0, 2, 2)
	m4c0(ts, Local1, 0xaaaa0001, 0xaaaa0001)
	m4c0(ts, Local2, 0xaaaa0002, 0xaaaa0002)
	m4c0(ts, Local3, 0xaaaa0003, 0xaaaa0003)
	m4c0(ts, Local4, 0xaaaa0004, 0xaaaa0004)
	m4c0(ts, Local5, 0xaaaa0005, 0xaaaa0005)
	m4c0(ts, Local6, 0xaaaa0006, 0xaaaa0006)
	m4c0(ts, Local7, 0xaaaa0007, 0xaaaa0007)

	// ===================== 3:

	Store(0x55550003, cmp0)
	Store(3, Local0)

	Store(
		m004(Local0, Local1, Local2, Local3, Local4, Local5, Local6),
		i000)
	if (LNotEqual(i000, cmp0)) {
		err("", z139, __LINE__, 0, 0, i000, cmp0)
	}
	m4c0(ts, Local0, 3, 3)
	m4c0(ts, Local1, 0xaaaa0001, 0xaaaa0001)
	m4c0(ts, Local2, 0xaaaa0002, 0xaaaa0002)
	m4c0(ts, Local3, 0xaaaa0003, 0xaaaa0003)
	m4c0(ts, Local4, 0xaaaa0004, 0xaaaa0004)
	m4c0(ts, Local5, 0xaaaa0005, 0xaaaa0005)
	m4c0(ts, Local6, 0xaaaa0006, 0xaaaa0006)
	m4c0(ts, Local7, 0xaaaa0007, 0xaaaa0007)

	// ===================== 4:

	Store(0x55550004, cmp0)
	Store(4, Local0)

	Store(
		m004(Local0, Local1, Local2, Local3, Local4, Local5, Local6),
		i000)
	if (LNotEqual(i000, cmp0)) {
		err("", z139, __LINE__, 0, 0, i000, cmp0)
	}
	m4c0(ts, Local0, 4, 4)
	m4c0(ts, Local1, 0xaaaa0001, 0xaaaa0001)
	m4c0(ts, Local2, 0xaaaa0002, 0xaaaa0002)
	m4c0(ts, Local3, 0xaaaa0003, 0xaaaa0003)
	m4c0(ts, Local4, 0xaaaa0004, 0xaaaa0004)
	m4c0(ts, Local5, 0xaaaa0005, 0xaaaa0005)
	m4c0(ts, Local6, 0xaaaa0006, 0xaaaa0006)
	m4c0(ts, Local7, 0xaaaa0007, 0xaaaa0007)

	// ===================== 5:

	Store(0x55550005, cmp0)
	Store(5, Local0)

	Store(
		m004(Local0, Local1, Local2, Local3, Local4, Local5, Local6),
		i000)
	if (LNotEqual(i000, cmp0)) {
		err("", z139, __LINE__, 0, 0, i000, cmp0)
	}
	m4c0(ts, Local0, 5, 5)
	m4c0(ts, Local1, 0xaaaa0001, 0xaaaa0001)
	m4c0(ts, Local2, 0xaaaa0002, 0xaaaa0002)
	m4c0(ts, Local3, 0xaaaa0003, 0xaaaa0003)
	m4c0(ts, Local4, 0xaaaa0004, 0xaaaa0004)
	m4c0(ts, Local5, 0xaaaa0005, 0xaaaa0005)
	m4c0(ts, Local6, 0xaaaa0006, 0xaaaa0006)
	m4c0(ts, Local7, 0xaaaa0007, 0xaaaa0007)

	// ===================== 6:

	Store(0x55550006, cmp0)
	Store(6, Local0)

	Store(
		m004(Local0, Local1, Local2, Local3, Local4, Local5, Local6),
		i000)
	if (LNotEqual(i000, cmp0)) {
		err("", z139, __LINE__, 0, 0, i000, cmp0)
	}
	m4c0(ts, Local0, 6, 6)
	m4c0(ts, Local1, 0xaaaa0001, 0xaaaa0001)
	m4c0(ts, Local2, 0xaaaa0002, 0xaaaa0002)
	m4c0(ts, Local3, 0xaaaa0003, 0xaaaa0003)
	m4c0(ts, Local4, 0xaaaa0004, 0xaaaa0004)
	m4c0(ts, Local5, 0xaaaa0005, 0xaaaa0005)
	m4c0(ts, Local6, 0xaaaa0006, 0xaaaa0006)
	m4c0(ts, Local7, 0xaaaa0007, 0xaaaa0007)

	// ===================== 7:

	Store(0x55550007, cmp0)
	Store(7, Local0)

	Store(
		m004(Local0, Local1, Local2, Local3, Local4, Local5, Local6),
		i000)
	if (LNotEqual(i000, cmp0)) {
		err("", z139, __LINE__, 0, 0, i000, cmp0)
	}
	m4c0(ts, Local0, 7, 7)
	m4c0(ts, Local1, 0xaaaa0001, 0xaaaa0001)
	m4c0(ts, Local2, 0xaaaa0002, 0xaaaa0002)
	m4c0(ts, Local3, 0xaaaa0003, 0xaaaa0003)
	m4c0(ts, Local4, 0xaaaa0004, 0xaaaa0004)
	m4c0(ts, Local5, 0xaaaa0005, 0xaaaa0005)
	m4c0(ts, Local6, 0xaaaa0006, 0xaaaa0006)
	m4c0(ts, Local7, 0xaaaa0007, 0xaaaa0007)

	// ===================== 8:

	Store(0x55550008, cmp0)
	Store(8, Local0)

	Store(
		m004(Local0, Local1, Local2, Local3, Local4, Local5, Local6),
		i000)
	if (LNotEqual(i000, cmp0)) {
		err("", z139, __LINE__, 0, 0, i000, cmp0)
	}
	m4c0(ts, Local0, 8, 8)
	m4c0(ts, Local1, 0xaaaa0001, 0xaaaa0001)
	m4c0(ts, Local2, 0xaaaa0002, 0xaaaa0002)
	m4c0(ts, Local3, 0xaaaa0003, 0xaaaa0003)
	m4c0(ts, Local4, 0xaaaa0004, 0xaaaa0004)
	m4c0(ts, Local5, 0xaaaa0005, 0xaaaa0005)
	m4c0(ts, Local6, 0xaaaa0006, 0xaaaa0006)
	m4c0(ts, Local7, 0xaaaa0007, 0xaaaa0007)

	// ===================== 9:

	Store(0x55550009, cmp0)
	Store(9, Local0)

	Store(
		m004(Local0, Local1, Local2, Local3, Local4, Local5, Local6),
		i000)
	if (LNotEqual(i000, cmp0)) {
		err("", z139, __LINE__, 0, 0, i000, cmp0)
	}
	m4c0(ts, Local0, 9, 9)
	m4c0(ts, Local1, 0xaaaa0001, 0xaaaa0001)
	m4c0(ts, Local2, 0xaaaa0002, 0xaaaa0002)
	m4c0(ts, Local3, 0xaaaa0003, 0xaaaa0003)
	m4c0(ts, Local4, 0xaaaa0004, 0xaaaa0004)
	m4c0(ts, Local5, 0xaaaa0005, 0xaaaa0005)
	m4c0(ts, Local6, 0xaaaa0006, 0xaaaa0006)
	m4c0(ts, Local7, 0xaaaa0007, 0xaaaa0007)
}

Method(mf73)
{
	SRMT("mf72(0)")
	mf72(0)

	SRMT("mf72(1)")
	mf72(1)
}
