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
 * Huge, many levels embedded {Switch, Case, Default}
 * The test similar to ctl2
 */

/*
See comments, dipper ????
identical to ctl2
do for 3 states in tests were there are not Defaults for all - 0,1,2 values
use the same methods for several SW0X
*/

// Switch, Case, Default operators

Name(z069, 69)

// The maximal number of temporary variables
// (_T_X) on ACPICA is equal to 36.
Name(TMAX, 36)

Name(b0sw, Buffer(TMAX) {})

// Put value to all elements of buffer
Method(m0c1, 1, Serialized)
{
	Name(lpN0, 0)
	Name(lpC0, 0)

	Store(TMAX, lpN0)

	While (lpN0) {
		Store(arg0, Index(b0sw, lpC0))
		Decrement(lpN0)
		Increment(lpC0)
	}
}

Method(m0c0)
{
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

	return (Local0)
}

// Run-method
Method(SW02,, Serialized)
{
	Store("TEST: SW02, Switch, Case, Default operators", Debug)

	Name(ts, "SW02")

	Name(lpN0, 0)
	Name(lpC0, 0)

	// Check each Switch/Case(0) pair
	// from dipper pair to upper one.

	Store(TMAX, lpN0)
	Store(0, lpC0)
	m0c1(0)

	While (lpN0) {
		Store(m0c0(), Local1)
		Decrement(lpN0)
		Increment(lpC0)
		if (LNotEqual(Local1, lpN0)) {
			err(ts, z069, __LINE__, 0, 0, Local1, lpN0)
			return (Ones)
		}
		Store(1, Index(b0sw, lpN0))
	}

	return (0)
}

Method(m0c2)
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

// Run-method
Method(SW03,, Serialized)
{
	Store("TEST: SW03, Switch, Case, Default operators", Debug)

	Name(ts, "SW03")

	Name(lpN0, 0)
	Name(lpC0, 0)

	// Check each Switch/Case(0) pair
	// from dipper pair to upper one.

	Store(TMAX, lpN0)
	Store(0, lpC0)
	m0c1(0)

	While (lpN0) {
		Store(m0c2(), Local1)
		Decrement(lpN0)
		Increment(lpC0)
		if (LNotEqual(Local1, lpN0)) {
			err(ts, z069, __LINE__, 0, 0, Local1, lpN0)
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
		Store(m0c2(), Local1)
		Decrement(lpN0)
		Increment(lpC0)
		Add(TMAX, lpN0, Local7)
		if (LNotEqual(Local1, Local7)) {
			err(ts, z069, __LINE__, 0, 0, Local1, Local7)
			return (Ones)
		}
	}

	return (0)
}

Method(m0c3)
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

// Run-method
Method(SW04,, Serialized)
{
	Store("TEST: SW04, Switch, Case, Default operators", Debug)

	Name(ts, "SW04")

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

	Store(m0c3(), Local1)
	if (LNotEqual(Local1, Local7)) {
		err(ts, z069, __LINE__, 0, 0, Local1, Local7)
		return (Ones)
	}

	// Check each Switch/Case(0) pair
	// from dipper pair to upper one,
	// while go through all the previous Defaults.

	While (lpN0) {
		Subtract(lpN0, 1, Local7)
		Store(0, Index(b0sw, Local7))
		Store(m0c3(), Local1)
		Decrement(lpN0)
		Increment(lpC0)
		if (LNotEqual(Local1, lpN0)) {
			err(ts, z069, __LINE__, 0, 0, Local1, lpN0)
			return (Ones)
		}
	}

	return (0)
}

Method(m0c4, 1)
{
	// equivalent to elseif (101):
	// if() {
	// } elseif() {
	// } elseif() {
	// ...
	// } elseif() {
	// }

	Store(0x12345678, Local0)

	Switch (Arg0) {
		Case (0) {
			Store(0, Local0)
		}
		Case (1) {
			Store(1, Local0)
		}
		Case (2) {
			Store(2, Local0)
		}
		Case (3) {
			Store(3, Local0)
		}
		Case (4) {
			Store(4, Local0)
		}
		Case (5) {
			Store(5, Local0)
		}
		Case (6) {
			Store(6, Local0)
		}
		Case (7) {
			Store(7, Local0)
		}
		Case (8) {
			Store(8, Local0)
		}
		Case (9) {
			Store(9, Local0)
		}
		Case (10) {
			Store(10, Local0)
		}
		Case (11) {
			Store(11, Local0)
		}
		Case (12) {
			Store(12, Local0)
		}
		Case (13) {
			Store(13, Local0)
		}
		Case (14) {
			Store(14, Local0)
		}
		Case (15) {
			Store(15, Local0)
		}
		Case (16) {
			Store(16, Local0)
		}
		Case (17) {
			Store(17, Local0)
		}
		Case (18) {
			Store(18, Local0)
		}
		Case (19) {
			Store(19, Local0)
		}
		Case (20) {
			Store(20, Local0)
		}
		Case (21) {
			Store(21, Local0)
		}
		Case (22) {
			Store(22, Local0)
		}
		Case (23) {
			Store(23, Local0)
		}
		Case (24) {
			Store(24, Local0)
		}
		Case (25) {
			Store(25, Local0)
		}
		Case (26) {
			Store(26, Local0)
		}
		Case (27) {
			Store(27, Local0)
		}
		Case (28) {
			Store(28, Local0)
		}
		Case (29) {
			Store(29, Local0)
		}
		Case (30) {
			Store(30, Local0)
		}
		Case (31) {
			Store(31, Local0)
		}
		Case (32) {
			Store(32, Local0)
		}
		Case (33) {
			Store(33, Local0)
		}
		Case (34) {
			Store(34, Local0)
		}
		Case (35) {
			Store(35, Local0)
		}
		Case (36) {
			Store(36, Local0)
		}
		Case (37) {
			Store(37, Local0)
		}
		Case (38) {
			Store(38, Local0)
		}
		Case (39) {
			Store(39, Local0)
		}
		Case (40) {
			Store(40, Local0)
		}
		Case (41) {
			Store(41, Local0)
		}
		Case (42) {
			Store(42, Local0)
		}
		Case (43) {
			Store(43, Local0)
		}
		Case (44) {
			Store(44, Local0)
		}
		Case (45) {
			Store(45, Local0)
		}
		Case (46) {
			Store(46, Local0)
		}
		Case (47) {
			Store(47, Local0)
		}
		Case (48) {
			Store(48, Local0)
		}
		Case (49) {
			Store(49, Local0)
		}

		////////////////////////
		Default {
			Store(100, Local0)
		}
		////////////////////////

		Case (50) {
			Store(50, Local0)
		}
		Case (51) {
			Store(51, Local0)
		}
		Case (52) {
			Store(52, Local0)
		}
		Case (53) {
			Store(53, Local0)
		}
		Case (54) {
			Store(54, Local0)
		}
		Case (55) {
			Store(55, Local0)
		}
		Case (56) {
			Store(56, Local0)
		}
		Case (57) {
			Store(57, Local0)
		}
		Case (58) {
			Store(58, Local0)
		}
		Case (59) {
			Store(59, Local0)
		}
		Case (60) {
			Store(60, Local0)
		}
		Case (61) {
			Store(61, Local0)
		}
		Case (62) {
			Store(62, Local0)
		}
		Case (63) {
			Store(63, Local0)
		}
		Case (64) {
			Store(64, Local0)
		}
		Case (65) {
			Store(65, Local0)
		}
		Case (66) {
			Store(66, Local0)
		}
		Case (67) {
			Store(67, Local0)
		}
		Case (68) {
			Store(68, Local0)
		}
		Case (69) {
			Store(69, Local0)
		}
		Case (70) {
			Store(70, Local0)
		}
		Case (71) {
			Store(71, Local0)
		}
		Case (72) {
			Store(72, Local0)
		}
		Case (73) {
			Store(73, Local0)
		}
		Case (74) {
			Store(74, Local0)
		}
		Case (75) {
			Store(75, Local0)
		}
		Case (76) {
			Store(76, Local0)
		}
		Case (77) {
			Store(77, Local0)
		}
		Case (78) {
			Store(78, Local0)
		}
		Case (79) {
			Store(79, Local0)
		}
		Case (80) {
			Store(80, Local0)
		}
		Case (81) {
			Store(81, Local0)
		}
		Case (82) {
			Store(82, Local0)
		}
		Case (83) {
			Store(83, Local0)
		}
		Case (84) {
			Store(84, Local0)
		}
		Case (85) {
			Store(85, Local0)
		}
		Case (86) {
			Store(86, Local0)
		}
		Case (87) {
			Store(87, Local0)
		}
		Case (88) {
			Store(88, Local0)
		}
		Case (89) {
			Store(89, Local0)
		}
		Case (90) {
			Store(90, Local0)
		}
		Case (91) {
			Store(91, Local0)
		}
		Case (92) {
			Store(92, Local0)
		}
		Case (93) {
			Store(93, Local0)
		}
		Case (94) {
			Store(94, Local0)
		}
		Case (95) {
			Store(95, Local0)
		}
		Case (96) {
			Store(96, Local0)
		}
		Case (97) {
			Store(97, Local0)
		}
		Case (98) {
			Store(98, Local0)
		}
		Case (99) {
			Store(99, Local0)
		}
	}

	return (Local0)
}

// Run-method
Method(SW05,, Serialized)
{
	Store("TEST: SW05, Switch, Case, Default operators", Debug)

	Name(ts, "SW05")

	Name(lpN0, 101)
	Name(lpC0, 0)

	// Check ??????????????????

	While (lpN0) {

		Store(m0c4(lpC0), Local1)
		if (LNotEqual(Local1, lpC0)) {
			err(ts, z069, __LINE__, 0, 0, Local1, lpC0)
			return (Ones)
		}
		Decrement(lpN0)
		Increment(lpC0)
	}

	return (0)
}

Method(m0c5)
{
	// equivalent to embedded elseif (36 levels):
	// if() {
	// } elseif() {
	//   if() {
	//   } elseif() {
	//     if() {
	//     } elseif() {
	//       ...
	//     }
	//   }
	// }

	Store(0x12345678, Local0)

      Switch (DeRefOf(Index(b0sw, 0))) {
      Case (0) {
      Store(0, Local0)
      }
      Case (1) {
      Store(36, Local0)

        Switch (DeRefOf(Index(b0sw, 1))) {
        Case (0) {
        Store(1, Local0)
        }
        Case (1) {
        Store(37, Local0)

          Switch (DeRefOf(Index(b0sw, 2))) {
          Case (0) {
          Store(2, Local0)
          }
          Case (1) {
          Store(38, Local0)

            Switch (DeRefOf(Index(b0sw, 3))) {
            Case (0) {
            Store(3, Local0)
            }
            Case (1) {
            Store(39, Local0)

              Switch (DeRefOf(Index(b0sw, 4))) {
              Case (0) {
              Store(4, Local0)
              }
              Case (1) {
              Store(40, Local0)

                Switch (DeRefOf(Index(b0sw, 5))) {
                Case (0) {
                Store(5, Local0)
                }
                Case (1) {
                Store(41, Local0)

                  Switch (DeRefOf(Index(b0sw, 6))) {
                  Case (0) {
                  Store(6, Local0)
                  }
                  Case (1) {
                  Store(42, Local0)

                    Switch (DeRefOf(Index(b0sw, 7))) {
                    Case (0) {
                    Store(7, Local0)
                    }
                    Case (1) {
                    Store(43, Local0)

                      Switch (DeRefOf(Index(b0sw, 8))) {
                      Case (0) {
                      Store(8, Local0)
                      }
                      Case (1) {
                      Store(44, Local0)

                        Switch (DeRefOf(Index(b0sw, 9))) {
                        Case (0) {
                        Store(9, Local0)
                        }
                        Case (1) {
                        Store(45, Local0)

                          Switch (DeRefOf(Index(b0sw, 10))) {
                          Case (0) {
                          Store(10, Local0)
                          }
                          Case (1) {
                          Store(46, Local0)

                            Switch (DeRefOf(Index(b0sw, 11))) {
                            Case (0) {
                            Store(11, Local0)
                            }
                            Case (1) {
                            Store(47, Local0)

                              Switch (DeRefOf(Index(b0sw, 12))) {
                              Case (0) {
                              Store(12, Local0)
                              }
                              Case (1) {
                              Store(48, Local0)

                                Switch (DeRefOf(Index(b0sw, 13))) {
                                Case (0) {
                                Store(13, Local0)
                                }
                                Case (1) {
                                Store(49, Local0)

                                  Switch (DeRefOf(Index(b0sw, 14))) {
                                  Case (0) {
                                  Store(14, Local0)
                                  }
                                  Case (1) {
                                  Store(50, Local0)

                                    Switch (DeRefOf(Index(b0sw, 15))) {
                                    Case (0) {
                                    Store(15, Local0)
                                    }
                                    Case (1) {
                                    Store(51, Local0)

                                      Switch (DeRefOf(Index(b0sw, 16))) {
                                      Case (0) {
                                      Store(16, Local0)
                                      }
                                      Case (1) {
                                      Store(52, Local0)

                                        Switch (DeRefOf(Index(b0sw, 17))) {
                                        Case (0) {
                                        Store(17, Local0)
                                        }
                                        Case (1) {
                                        Store(53, Local0)

                                          Switch (DeRefOf(Index(b0sw, 18))) {
                                          Case (0) {
                                          Store(18, Local0)
                                          }
                                          Case (1) {
                                          Store(54, Local0)

                                            Switch (DeRefOf(Index(b0sw, 19))) {
                                            Case (0) {
                                            Store(19, Local0)
                                            }
                                            Case (1) {
                                            Store(55, Local0)

                                              Switch (DeRefOf(Index(b0sw, 20))) {
                                              Case (0) {
                                              Store(20, Local0)
                                              }
                                              Case (1) {
                                              Store(56, Local0)

                                                Switch (DeRefOf(Index(b0sw, 21))) {
                                                Case (0) {
                                                Store(21, Local0)
                                                }
                                                Case (1) {
                                                Store(57, Local0)

                                                  Switch (DeRefOf(Index(b0sw, 22))) {
                                                  Case (0) {
                                                  Store(22, Local0)
                                                  }
                                                  Case (1) {
                                                  Store(58, Local0)

                                                    Switch (DeRefOf(Index(b0sw, 23))) {
                                                    Case (0) {
                                                    Store(23, Local0)
                                                    }
                                                    Case (1) {
                                                    Store(59, Local0)

                                                      Switch (DeRefOf(Index(b0sw, 24))) {
                                                      Case (0) {
                                                      Store(24, Local0)
                                                      }
                                                      Case (1) {
                                                      Store(60, Local0)

                                                        Switch (DeRefOf(Index(b0sw, 25))) {
                                                        Case (0) {
                                                        Store(25, Local0)
                                                        }
                                                        Case (1) {
                                                        Store(61, Local0)

                                                          Switch (DeRefOf(Index(b0sw, 26))) {
                                                          Case (0) {
                                                          Store(26, Local0)
                                                          }
                                                          Case (1) {
                                                          Store(62, Local0)

                                                            Switch (DeRefOf(Index(b0sw, 27))) {
                                                            Case (0) {
                                                            Store(27, Local0)
                                                            }
                                                            Case (1) {
                                                            Store(63, Local0)

                                                              Switch (DeRefOf(Index(b0sw, 28))) {
                                                              Case (0) {
                                                              Store(28, Local0)
                                                              }
                                                              Case (1) {
                                                              Store(64, Local0)

                                                                Switch (DeRefOf(Index(b0sw, 29))) {
                                                                Case (0) {
                                                                Store(29, Local0)
                                                                }
                                                                Case (1) {
                                                                Store(65, Local0)

                                                                  Switch (DeRefOf(Index(b0sw, 30))) {
                                                                  Case (0) {
                                                                  Store(30, Local0)
                                                                  }
                                                                  Case (1) {
                                                                  Store(66, Local0)

                                                                    Switch (DeRefOf(Index(b0sw, 31))) {
                                                                    Case (0) {
                                                                    Store(31, Local0)
                                                                    }
                                                                    Case (1) {
                                                                    Store(67, Local0)

                                                                      Switch (DeRefOf(Index(b0sw, 32))) {
                                                                      Case (0) {
                                                                      Store(32, Local0)
                                                                      }
                                                                      Case (1) {
                                                                      Store(68, Local0)

                                                                        Switch (DeRefOf(Index(b0sw, 33))) {
                                                                        Case (0) {
                                                                        Store(33, Local0)
                                                                        }
                                                                        Case (1) {
                                                                        Store(69, Local0)

                                                                          Switch (DeRefOf(Index(b0sw, 34))) {
                                                                          Case (0) {
                                                                          Store(34, Local0)
                                                                          }
                                                                          Case (1) {
                                                                          Store(70, Local0)

                                                                            Switch (DeRefOf(Index(b0sw, 35))) {
                                                                            Case (0) {
                                                                            Store(35, Local0)
                                                                            }
                                                                            Case (1) {
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

// Run-method
Method(SW06,, Serialized)
{
	Store("TEST: SW06, Switch, Case, Default operators", Debug)

	Name(ts, "SW06")

	Name(lpN0, 101)
	Name(lpC0, 0)

	// Check ??????????????????

	Store(TMAX, lpN0)
	Store(0, lpC0)
	m0c1(1)

	While (lpN0) {
		Subtract(lpN0, 1, Local7)
		Store(0, Index(b0sw, Local7))
		Store(m0c5(), Local1)
		Decrement(lpN0)
		Increment(lpC0)
		if (LNotEqual(Local1, Local7)) {
			err(ts, z069, __LINE__, 0, 0, Local1, Local7)
			return (Ones)
		}
	}

	// Check ??????.

	Store(TMAX, lpN0)
	Store(0, lpC0)
	m0c1(1)

	While (lpN0) {
		Store(m0c5(), Local1)
		Decrement(lpN0)
		Increment(lpC0)
		Add(TMAX, lpN0, Local7)
		if (LNotEqual(Local1, Local7)) {
			err(ts, z069, __LINE__, 0, 0, Local1, Local7)
			return (Ones)
		}
		Store(2, Index(b0sw, lpN0))
	}

	return (0)
}
