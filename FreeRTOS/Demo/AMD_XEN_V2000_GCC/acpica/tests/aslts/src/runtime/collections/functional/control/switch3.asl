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
 * Method execution control
 *
 * Switch, Case, Default operators
 *
 * Switch, _T_X
 */

/*
If bug 84 will be positively resolved, then return back:
Declaration of Method
Expression
Declaration of Method

  //         m000(m0c2), m001(SW03)        //
  //         unfolded Methods(m0c0,SW02)   //
  //         m002(m0c3), m003(SW04)        //

*/


Name(z070, 70)

Method(m0de, 1)
{

  // ===================================== //
  //         m000(m0c2), m001(SW03)        //
  // ===================================== //

  // Method(m0c2)
  Method(m000)
  {
	// equivalent to embedded if (36 levels):
	// if(){
	//   if(){
	//     if(){
	//     ...
	//     } else {
	//     }
	//   } else {
	//   }
	// } else {
	// }

	Store(0x12345678, Local0)

      Switch (DeRefOf(Index(b0sw, 0))) {
      Case (0) {
      Store(0, Local0)
        Switch (DeRefOf(Index(b0sw, 1))) {
        Case (0) {
        Store(1, Local0)
          Switch (DeRefOf(Index(b0sw, 2))) {
          Case (0) {
          Store(2, Local0)
            Switch (DeRefOf(Index(b0sw, 3))) {
            Case (0) {
            Store(3, Local0)
              Switch (DeRefOf(Index(b0sw, 4))) {
              Case (0) {
              Store(4, Local0)
                Switch (DeRefOf(Index(b0sw, 5))) {
                Case (0) {
                Store(5, Local0)
                  Switch (DeRefOf(Index(b0sw, 6))) {
                  Case (0) {
                  Store(6, Local0)
                    Switch (DeRefOf(Index(b0sw, 7))) {
                    Case (0) {
                    Store(7, Local0)
                      Switch (DeRefOf(Index(b0sw, 8))) {
                      Case (0) {
                      Store(8, Local0)
                        Switch (DeRefOf(Index(b0sw, 9))) {
                        Case (0) {
                        Store(9, Local0)
                          Switch (DeRefOf(Index(b0sw, 10))) {
                          Case (0) {
                          Store(10, Local0)
                            Switch (DeRefOf(Index(b0sw, 11))) {
                            Case (0) {
                            Store(11, Local0)
                              Switch (DeRefOf(Index(b0sw, 12))) {
                              Case (0) {
                              Store(12, Local0)
                                Switch (DeRefOf(Index(b0sw, 13))) {
                                Case (0) {
                                Store(13, Local0)
                                  Switch (DeRefOf(Index(b0sw, 14))) {
                                  Case (0) {
                                  Store(14, Local0)
                                    Switch (DeRefOf(Index(b0sw, 15))) {
                                    Case (0) {
                                    Store(15, Local0)
                                      Switch (DeRefOf(Index(b0sw, 16))) {
                                      Case (0) {
                                      Store(16, Local0)
                                        Switch (DeRefOf(Index(b0sw, 17))) {
                                        Case (0) {
                                        Store(17, Local0)
                                          Switch (DeRefOf(Index(b0sw, 18))) {
                                          Case (0) {
                                          Store(18, Local0)
                                            Switch (DeRefOf(Index(b0sw, 19))) {
                                            Case (0) {
                                            Store(19, Local0)
                                              Switch (DeRefOf(Index(b0sw, 20))) {
                                              Case (0) {
                                              Store(20, Local0)
                                                Switch (DeRefOf(Index(b0sw, 21))) {
                                                Case (0) {
                                                Store(21, Local0)
                                                  Switch (DeRefOf(Index(b0sw, 22))) {
                                                  Case (0) {
                                                  Store(22, Local0)
                                                    Switch (DeRefOf(Index(b0sw, 23))) {
                                                    Case (0) {
                                                    Store(23, Local0)
                                                      Switch (DeRefOf(Index(b0sw, 24))) {
                                                      Case (0) {
                                                      Store(24, Local0)
                                                        Switch (DeRefOf(Index(b0sw, 25))) {
                                                        Case (0) {
                                                        Store(25, Local0)
                                                          Switch (DeRefOf(Index(b0sw, 26))) {
                                                          Case (0) {
                                                          Store(26, Local0)
                                                            Switch (DeRefOf(Index(b0sw, 27))) {
                                                            Case (0) {
                                                            Store(27, Local0)
                                                              Switch (DeRefOf(Index(b0sw, 28))) {
                                                              Case (0) {
                                                              Store(28, Local0)
                                                                Switch (DeRefOf(Index(b0sw, 29))) {
                                                                Case (0) {
                                                                Store(29, Local0)
                                                                  Switch (DeRefOf(Index(b0sw, 30))) {
                                                                  Case (0) {
                                                                  Store(30, Local0)
                                                                    Switch (DeRefOf(Index(b0sw, 31))) {
                                                                    Case (0) {
                                                                    Store(31, Local0)
                                                                      Switch (DeRefOf(Index(b0sw, 32))) {
                                                                      Case (0) {
                                                                      Store(32, Local0)
                                                                        Switch (DeRefOf(Index(b0sw, 33))) {
                                                                        Case (0) {
                                                                        Store(33, Local0)
                                                                          Switch (DeRefOf(Index(b0sw, 34))) {
                                                                          Case (0) {
                                                                          Store(34, Local0)
                                                                            Switch (DeRefOf(Index(b0sw, 35))) {
                                                                            Case (0) {
                                                                            Store(35, Local0)
                                                                            }
                                                                            Case (1) {
                                                                            Store(71, Local0)
                                                                            }}
                                                                          }
                                                                          Case (1) {
                                                                          Store(70, Local0)
                                                                          }}
                                                                        }
                                                                        Case (1) {
                                                                        Store(69, Local0)
                                                                        }}
                                                                      }
                                                                      Case (1) {
                                                                      Store(68, Local0)
                                                                      }}
                                                                    }
                                                                    Case (1) {
                                                                    Store(67, Local0)
                                                                    }}
                                                                  }
                                                                  Case (1) {
                                                                  Store(66, Local0)
                                                                  }}
                                                                }
                                                                Case (1) {
                                                                Store(65, Local0)
                                                                }}
                                                              }
                                                              Case (1) {
                                                              Store(64, Local0)
                                                              }}
                                                            }
                                                            Case (1) {
                                                            Store(63, Local0)
                                                            }}
                                                          }
                                                          Case (1) {
                                                          Store(62, Local0)
                                                          }}
                                                        }
                                                        Case (1) {
                                                        Store(61, Local0)
                                                        }}
                                                      }
                                                      Case (1) {
                                                      Store(60, Local0)
                                                      }}
                                                    }
                                                    Case (1) {
                                                    Store(59, Local0)
                                                    }}
                                                  }
                                                  Case (1) {
                                                  Store(58, Local0)
                                                  }}
                                                }
                                                Case (1) {
                                                Store(57, Local0)
                                                }}
                                              }
                                              Case (1) {
                                              Store(56, Local0)
                                              }}
                                            }
                                            Case (1) {
                                            Store(55, Local0)
                                            }}
                                          }
                                          Case (1) {
                                          Store(54, Local0)
                                          }}
                                        }
                                        Case (1) {
                                        Store(53, Local0)
                                        }}
                                      }
                                      Case (1) {
                                      Store(52, Local0)
                                      }}
                                    }
                                    Case (1) {
                                    Store(51, Local0)
                                    }}
                                  }
                                  Case (1) {
                                  Store(50, Local0)
                                  }}
                                }
                                Case (1) {
                                Store(49, Local0)
                                }}
                              }
                              Case (1) {
                              Store(48, Local0)
                              }}
                            }
                            Case (1) {
                            Store(47, Local0)
                            }}
                          }
                          Case (1) {
                          Store(46, Local0)
                          }}
                        }
                        Case (1) {
                        Store(45, Local0)
                        }}
                      }
                      Case (1) {
                      Store(44, Local0)
                      }}
                    }
                    Case (1) {
                    Store(43, Local0)
                    }}
                  }
                  Case (1) {
                  Store(42, Local0)
                  }}
                }
                Case (1) {
                Store(41, Local0)
                }}
              }
              Case (1) {
              Store(40, Local0)
              }}
            }
            Case (1) {
            Store(39, Local0)
            }}
          }
          Case (1) {
          Store(38, Local0)
          }}
        }
        Case (1) {
        Store(37, Local0)
        }}
      }
      Case (1) {
      Store(36, Local0)
      }}

	return (Local0)
  }

  // Method(SW03)
  Method(m001, 1, Serialized)
  {
	// Store("m001 started", Debug)

	Name(lpN0, 0)
	Name(lpC0, 0)

	// Check each Switch/Case(0) pair
	// from dipper pair to upper one.

	Store(TMAX, lpN0)
	Store(0, lpC0)
	m0c1(0)

	While (lpN0) {
		Store(m000(), Local1)
		Decrement(lpN0)
		Increment(lpC0)
		if (LNotEqual(Local1, lpN0)) {
			err(arg0, z070, __LINE__, 0, 0, Local1, lpN0)
			return (Ones)
		}
		Store(2, Index(b0sw, lpN0))
	}

	// Check each Switch/Case(1) pair
	// from dipper pair to upper one.

	Store(TMAX, lpN0)
	Store(0, lpC0)
	m0c1(0)

	While (lpN0) {
		Subtract(lpN0, 1, Local7)
		Store(1, Index(b0sw, Local7))
		Store(m000(), Local1)
		Decrement(lpN0)
		Increment(lpC0)
		Add(TMAX, lpN0, Local7)
		if (LNotEqual(Local1, Local7)) {
			err(arg0, z070, __LINE__, 0, 0, Local1, Local7)
			return (Ones)
		}
	}

	return (0)
  }

  // ===================================== //
  //         m002(m0c3), m003(SW04)        //
  // ===================================== //

  // Method(m0c3)
  Method(m002)
  {
	// equivalent to embedded else (36 levels):
	//  if(){
	//  } else {
	//    if(){
	//    } else {
	//      if(){
	//      } else {
	//        ...
	//      }
	//    }
	//  }

	Store(0x12345678, Local0)

      Switch (DeRefOf(Index(b0sw, 0))) {
      Case (0) {
      Store(0, Local0)
      }
      Default {
      Store(36, Local0)

        Switch (DeRefOf(Index(b0sw, 1))) {
        Case (0) {
        Store(1, Local0)
        }
        Default {
        Store(37, Local0)

          Switch (DeRefOf(Index(b0sw, 2))) {
          Case (0) {
          Store(2, Local0)
          }
          Default {
          Store(38, Local0)

            Switch (DeRefOf(Index(b0sw, 3))) {
            Case (0) {
            Store(3, Local0)
            }
            Default {
            Store(39, Local0)

              Switch (DeRefOf(Index(b0sw, 4))) {
              Case (0) {
              Store(4, Local0)
              }
              Default {
              Store(40, Local0)

                Switch (DeRefOf(Index(b0sw, 5))) {
                Case (0) {
                Store(5, Local0)
                }
                Default {
                Store(41, Local0)

                  Switch (DeRefOf(Index(b0sw, 6))) {
                  Case (0) {
                  Store(6, Local0)
                  }
                  Default {
                  Store(42, Local0)

                    Switch (DeRefOf(Index(b0sw, 7))) {
                    Case (0) {
                    Store(7, Local0)
                    }
                    Default {
                    Store(43, Local0)

                      Switch (DeRefOf(Index(b0sw, 8))) {
                      Case (0) {
                      Store(8, Local0)
                      }
                      Default {
                      Store(44, Local0)

                        Switch (DeRefOf(Index(b0sw, 9))) {
                        Case (0) {
                        Store(9, Local0)
                        }
                        Default {
                        Store(45, Local0)

                          Switch (DeRefOf(Index(b0sw, 10))) {
                          Case (0) {
                          Store(10, Local0)
                          }
                          Default {
                          Store(46, Local0)

                            Switch (DeRefOf(Index(b0sw, 11))) {
                            Case (0) {
                            Store(11, Local0)
                            }
                            Default {
                            Store(47, Local0)

                              Switch (DeRefOf(Index(b0sw, 12))) {
                              Case (0) {
                              Store(12, Local0)
                              }
                              Default {
                              Store(48, Local0)

                                Switch (DeRefOf(Index(b0sw, 13))) {
                                Case (0) {
                                Store(13, Local0)
                                }
                                Default {
                                Store(49, Local0)

                                  Switch (DeRefOf(Index(b0sw, 14))) {
                                  Case (0) {
                                  Store(14, Local0)
                                  }
                                  Default {
                                  Store(50, Local0)

                                    Switch (DeRefOf(Index(b0sw, 15))) {
                                    Case (0) {
                                    Store(15, Local0)
                                    }
                                    Default {
                                    Store(51, Local0)

                                      Switch (DeRefOf(Index(b0sw, 16))) {
                                      Case (0) {
                                      Store(16, Local0)
                                      }
                                      Default {
                                      Store(52, Local0)

                                        Switch (DeRefOf(Index(b0sw, 17))) {
                                        Case (0) {
                                        Store(17, Local0)
                                        }
                                        Default {
                                        Store(53, Local0)

                                          Switch (DeRefOf(Index(b0sw, 18))) {
                                          Case (0) {
                                          Store(18, Local0)
                                          }
                                          Default {
                                          Store(54, Local0)

                                            Switch (DeRefOf(Index(b0sw, 19))) {
                                            Case (0) {
                                            Store(19, Local0)
                                            }
                                            Default {
                                            Store(55, Local0)

                                              Switch (DeRefOf(Index(b0sw, 20))) {
                                              Case (0) {
                                              Store(20, Local0)
                                              }
                                              Default {
                                              Store(56, Local0)

                                                Switch (DeRefOf(Index(b0sw, 21))) {
                                                Case (0) {
                                                Store(21, Local0)
                                                }
                                                Default {
                                                Store(57, Local0)

                                                  Switch (DeRefOf(Index(b0sw, 22))) {
                                                  Case (0) {
                                                  Store(22, Local0)
                                                  }
                                                  Default {
                                                  Store(58, Local0)

                                                    Switch (DeRefOf(Index(b0sw, 23))) {
                                                    Case (0) {
                                                    Store(23, Local0)
                                                    }
                                                    Default {
                                                    Store(59, Local0)

                                                      Switch (DeRefOf(Index(b0sw, 24))) {
                                                      Case (0) {
                                                      Store(24, Local0)
                                                      }
                                                      Default {
                                                      Store(60, Local0)

                                                        Switch (DeRefOf(Index(b0sw, 25))) {
                                                        Case (0) {
                                                        Store(25, Local0)
                                                        }
                                                        Default {
                                                        Store(61, Local0)

                                                          Switch (DeRefOf(Index(b0sw, 26))) {
                                                          Case (0) {
                                                          Store(26, Local0)
                                                          }
                                                          Default {
                                                          Store(62, Local0)

                                                            Switch (DeRefOf(Index(b0sw, 27))) {
                                                            Case (0) {
                                                            Store(27, Local0)
                                                            }
                                                            Default {
                                                            Store(63, Local0)

                                                              Switch (DeRefOf(Index(b0sw, 28))) {
                                                              Case (0) {
                                                              Store(28, Local0)
                                                              }
                                                              Default {
                                                              Store(64, Local0)

                                                                Switch (DeRefOf(Index(b0sw, 29))) {
                                                                Case (0) {
                                                                Store(29, Local0)
                                                                }
                                                                Default {
                                                                Store(65, Local0)

                                                                  Switch (DeRefOf(Index(b0sw, 30))) {
                                                                  Case (0) {
                                                                  Store(30, Local0)
                                                                  }
                                                                  Default {
                                                                  Store(66, Local0)

                                                                    Switch (DeRefOf(Index(b0sw, 31))) {
                                                                    Case (0) {
                                                                    Store(31, Local0)
                                                                    }
                                                                    Default {
                                                                    Store(67, Local0)

                                                                      Switch (DeRefOf(Index(b0sw, 32))) {
                                                                      Case (0) {
                                                                      Store(32, Local0)
                                                                      }
                                                                      Default {
                                                                      Store(68, Local0)

                                                                        Switch (DeRefOf(Index(b0sw, 33))) {
                                                                        Case (0) {
                                                                        Store(33, Local0)
                                                                        }
                                                                        Default {
                                                                        Store(69, Local0)

                                                                          Switch (DeRefOf(Index(b0sw, 34))) {
                                                                          Case (0) {
                                                                          Store(34, Local0)
                                                                          }
                                                                          Default {
                                                                          Store(70, Local0)

                                                                            Switch (DeRefOf(Index(b0sw, 35))) {
                                                                            Case (0) {
                                                                            Store(35, Local0)
                                                                            }
                                                                            Default {
                                                                            Store(71, Local0)
                                                                            }}
                                                                          }}
                                                                        }}
                                                                      }}
                                                                    }}
                                                                  }}
                                                                }}
                                                              }}
                                                            }}
                                                          }}
                                                        }}
                                                      }}
                                                    }}
                                                  }}
                                                }}
                                              }}
                                            }}
                                          }}
                                        }}
                                      }}
                                    }}
                                  }}
                                }}
                              }}
                            }}
                          }}
                        }}
                      }}
                    }}
                  }}
                }}
              }}
            }}
          }}
        }}
      }}

	return (Local0)
  }

  // Method(SW04)
  Method(m003, 1, Serialized)
  {
	// Store("m003 started", Debug)

	Name(lpN0, 0)
	Name(lpC0, 0)

	// Check each Switch/Case(0) pair
	// from dipper pair to upper one.

	Store(TMAX, lpN0)
	Store(0, lpC0)
	m0c1(1)

	Multiply(TMAX, 2, Local7)
	Decrement(Local7)

	// Check dippest Switch/Default pair

	Store(m002(), Local1)
	if (LNotEqual(Local1, Local7)) {
		err(arg0, z070, __LINE__, 0, 0, Local1, Local7)
		return (Ones)
	}

	// Check each Switch/Case(0) pair
	// from dipper pair to upper one,
	// while go through all the previous Defaults.

	While (lpN0) {
		Subtract(lpN0, 1, Local7)
		Store(0, Index(b0sw, Local7))
		Store(m002(), Local1)
		Decrement(lpN0)
		Increment(lpC0)
		if (LNotEqual(Local1, lpN0)) {
			err(arg0, z070, __LINE__, 0, 0, Local1, lpN0)
			return (Ones)
		}
	}

	return (0)
  }

  m001(arg0)

  // =========================================== //
  //         unfolded Methods(m0c0,SW02)         //
  // =========================================== //

  // unfolded Method(SW02)

  // Store("unfolded (m0c0,SW02) started", Debug)

  Name(lpN0, 0)
  Name(lpC0, 0)

  // Check each Switch/Case(0) pair
  // from dipper pair to upper one.

  Store(TMAX, lpN0)
  Store(0, lpC0)
  m0c1(0)

  While (lpN0) {


	// equivalent to embedded if (36 levels):
	// if(){ if() { if() {......
	// }}}

	Store(0x12345678, Local0)

      Switch (DeRefOf(Index(b0sw, 0))) {
      Case (0) {
      Store(0, Local0)
        Switch (DeRefOf(Index(b0sw, 1))) {
        Case (0) {
        Store(1, Local0)
          Switch (DeRefOf(Index(b0sw, 2))) {
          Case (0) {
          Store(2, Local0)
            Switch (DeRefOf(Index(b0sw, 3))) {
            Case (0) {
            Store(3, Local0)
              Switch (DeRefOf(Index(b0sw, 4))) {
              Case (0) {
              Store(4, Local0)
                Switch (DeRefOf(Index(b0sw, 5))) {
                Case (0) {
                Store(5, Local0)
                  Switch (DeRefOf(Index(b0sw, 6))) {
                  Case (0) {
                  Store(6, Local0)
                    Switch (DeRefOf(Index(b0sw, 7))) {
                    Case (0) {
                    Store(7, Local0)
                      Switch (DeRefOf(Index(b0sw, 8))) {
                      Case (0) {
                      Store(8, Local0)
                        Switch (DeRefOf(Index(b0sw, 9))) {
                        Case (0) {
                        Store(9, Local0)
                          Switch (DeRefOf(Index(b0sw, 10))) {
                          Case (0) {
                          Store(10, Local0)
                            Switch (DeRefOf(Index(b0sw, 11))) {
                            Case (0) {
                            Store(11, Local0)
                              Switch (DeRefOf(Index(b0sw, 12))) {
                              Case (0) {
                              Store(12, Local0)
                                Switch (DeRefOf(Index(b0sw, 13))) {
                                Case (0) {
                                Store(13, Local0)
                                  Switch (DeRefOf(Index(b0sw, 14))) {
                                  Case (0) {
                                  Store(14, Local0)
                                    Switch (DeRefOf(Index(b0sw, 15))) {
                                    Case (0) {
                                    Store(15, Local0)
                                      Switch (DeRefOf(Index(b0sw, 16))) {
                                      Case (0) {
                                      Store(16, Local0)
                                        Switch (DeRefOf(Index(b0sw, 17))) {
                                        Case (0) {
                                        Store(17, Local0)
                                          Switch (DeRefOf(Index(b0sw, 18))) {
                                          Case (0) {
                                          Store(18, Local0)
                                            Switch (DeRefOf(Index(b0sw, 19))) {
                                            Case (0) {
                                            Store(19, Local0)
                                              Switch (DeRefOf(Index(b0sw, 20))) {
                                              Case (0) {
                                              Store(20, Local0)
                                                Switch (DeRefOf(Index(b0sw, 21))) {
                                                Case (0) {
                                                Store(21, Local0)
                                                  Switch (DeRefOf(Index(b0sw, 22))) {
                                                  Case (0) {
                                                  Store(22, Local0)
                                                    Switch (DeRefOf(Index(b0sw, 23))) {
                                                    Case (0) {
                                                    Store(23, Local0)
                                                      Switch (DeRefOf(Index(b0sw, 24))) {
                                                      Case (0) {
                                                      Store(24, Local0)
                                                        Switch (DeRefOf(Index(b0sw, 25))) {
                                                        Case (0) {
                                                        Store(25, Local0)
                                                          Switch (DeRefOf(Index(b0sw, 26))) {
                                                          Case (0) {
                                                          Store(26, Local0)
                                                            Switch (DeRefOf(Index(b0sw, 27))) {
                                                            Case (0) {
                                                            Store(27, Local0)
                                                              Switch (DeRefOf(Index(b0sw, 28))) {
                                                              Case (0) {
                                                              Store(28, Local0)
                                                                Switch (DeRefOf(Index(b0sw, 29))) {
                                                                Case (0) {
                                                                Store(29, Local0)
                                                                  Switch (DeRefOf(Index(b0sw, 30))) {
                                                                  Case (0) {
                                                                  Store(30, Local0)
                                                                    Switch (DeRefOf(Index(b0sw, 31))) {
                                                                    Case (0) {
                                                                    Store(31, Local0)
                                                                      Switch (DeRefOf(Index(b0sw, 32))) {
                                                                      Case (0) {
                                                                      Store(32, Local0)
                                                                        Switch (DeRefOf(Index(b0sw, 33))) {
                                                                        Case (0) {
                                                                        Store(33, Local0)
                                                                          Switch (DeRefOf(Index(b0sw, 34))) {
                                                                          Case (0) {
                                                                          Store(34, Local0)
                                                                            Switch (DeRefOf(Index(b0sw, 35))) {
                                                                            Case (0) {
                                                                            Store(35, Local0)
                                                                            }}
                                                                          }}
                                                                        }}
                                                                      }}
                                                                    }}
                                                                  }}
                                                                }}
                                                              }}
                                                            }}
                                                          }}
                                                        }}
                                                      }}
                                                    }}
                                                  }}
                                                }}
                                              }}
                                            }}
                                          }}
                                        }}
                                      }}
                                    }}
                                  }}
                                }}
                              }}
                            }}
                          }}
                        }}
                      }}
                    }}
                  }}
                }}
              }}
            }}
          }}
        }}
      }}

	Decrement(lpN0)
	Increment(lpC0)
	if (LNotEqual(Local0, lpN0)) {
		err(arg0, z070, __LINE__, 0, 0, Local0, lpN0)
		return (Ones)
	}
	Store(1, Index(b0sw, lpN0))

  } // While(lpN0)

  m003(arg0)

  return (0)
}

// Run-method
Method(SW07,, Serialized)
{
	Store("TEST: SW07, Switch, Case, Default operators", Debug)

	Name(ts, "SW07")

	m0de(ts)

	return (0)
}
