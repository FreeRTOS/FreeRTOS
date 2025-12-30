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
 * Conditional execution
 *
 * Huge, many levels embedded {if,elseif,else}
 * Note: it was verified as C program.
 */

Name(z005, 5)

Method(m040, 1)
{
	Store(0x71286345, Local0)

	if (RNG0(arg0, 0, 26)) {

		Store(0, Local0)

		// embedded if (20 levels)

		if (RNG0(arg0, 1, 21)) {	// 1
		  Store(1, Local0)
		  if (RNG0(arg0, 2, 21)) {
			Store(2, Local0)
			if (RNG0(arg0, 3, 21)) {
			  Store(3, Local0)
			  if (RNG0(arg0, 4, 21)) {
				Store(4, Local0)
				if (RNG0(arg0, 5, 21)) {
				  Store(5, Local0)
				  if (RNG0(arg0, 6, 21)) {
					Store(6, Local0)
					if (RNG0(arg0, 7, 21)) {
					  Store(7, Local0)
					  if (RNG0(arg0, 8, 21)) {
						Store(8, Local0)
						if (RNG0(arg0, 9, 21)) {
						  Store(9, Local0)
						  if (RNG0(arg0, 10, 21)) {
							Store(10, Local0)
							if (RNG0(arg0, 11, 21)) {	// 11
							  Store(11, Local0)
							  if (RNG0(arg0, 12, 21)) {
								Store(12, Local0)
								if (RNG0(arg0, 13, 21)) {
								  Store(13, Local0)
								  if (RNG0(arg0, 14, 21)) {
									Store(14, Local0)
									if (RNG0(arg0, 15, 21)) {
									  Store(15, Local0)
									  if (RNG0(arg0, 16, 21)) {
										Store(16, Local0)
										if (RNG0(arg0, 17, 21)) {
										  Store(17, Local0)
										  if (RNG0(arg0, 18, 21)) {
											Store(18, Local0)
											if (RNG0(arg0, 19, 21)) {
											  Store(19, Local0)
											  if (RNG0(arg0, 20, 21)) {
												Store(20, Local0)
												if (LEqual(arg0, 21)) {	// 21
												  Store(21, Local0)
												}
											  }
											}
										  }
										}
									  }
									}
								  }
								}
							  }
							}
						  }
						}
					  }
					}
				  }
				}
			  }
			}
		  }
		}

		if (LEqual(arg0, 22)) {
			Store(22, Local0)
		} elseif (LEqual(arg0, 23)) {
			Store(23, Local0)
		}

		if (LEqual(arg0, 24)) {
			Store(24, Local0)
		} elseif (LEqual(arg0, 25)) {
			Store(25, Local0)
		} elseif (LEqual(arg0, 26)) {
			Store(26, Local0)
		}

	} elseif (RNG0(arg0, 27, 49)) {

		if (LEqual(arg0, 27)) {
			Store(27, Local0)
		} else {

			// embedded else (20 levels)

			if (LEqual(arg0, 28)) {
			    Store(28, Local0)
			} else {	// 1
			  if (LEqual(arg0, 29)) {
				Store(29, Local0)
			  } else {
				if (LEqual(arg0, 30)) {
				  Store(30, Local0)
				} else {
				  if (LEqual(arg0, 31)) {
					Store(31, Local0)
				  } else {
					if (LEqual(arg0, 32)) {
					  Store(32, Local0)
					} else {
					  if (LEqual(arg0, 33)) {
						Store(33, Local0)
					  } else {
						if (LEqual(arg0, 34)) {
						  Store(34, Local0)
						} else {
						  if (LEqual(arg0, 35)) {
							Store(35, Local0)
						  } else {
							if (LEqual(arg0, 36)) {
							  Store(36, Local0)
							} else {
							  if (LEqual(arg0, 37)) {
								Store(37, Local0)
							  } else {
								if (LEqual(arg0, 38)) {
								  Store(38, Local0)
								} else {	// 11
								  if (LEqual(arg0, 39)) {
									Store(39, Local0)
								  } else {
									if (LEqual(arg0, 40)) {
									  Store(40, Local0)
									} else {
									  if (LEqual(arg0, 41)) {
										Store(41, Local0)
									  } else {
										if (LEqual(arg0, 42)) {
										  Store(42, Local0)
										} else {
										  if (LEqual(arg0, 43)) {
											Store(43, Local0)
										  } else {
											if (LEqual(arg0, 44)) {
											  Store(44, Local0)
											} else {
											  if (LEqual(arg0, 45)) {
												Store(45, Local0)
											  } else {
												if (LEqual(arg0, 46)) {
												  Store(46, Local0)
												} else {
												  if (LEqual(arg0, 47)) {
													Store(47, Local0)
												  } else {
													if (LEqual(arg0, 48)) {
													  Store(48, Local0)
													} else {	// 21
													  Store(49, Local0)
													}
												  }
												}
											  }
											}
										  }
										}
									  }
									}
								  }
								}
							  }
							}
						  }
						}
					  }
					}
				  }
				}
			  }
			}
		}
	} elseif (RNG0(arg0, 50, 52)) {

		if (LEqual(arg0, 50)) {
			Store(50, Local0)
		} elseif (LEqual(arg0, 51)) {
			Store(51, Local0)
		} else {
			Store(52, Local0)
		}
	} elseif (RNG0(arg0, 53, 56)) {

		if (LEqual(arg0, 53)) {
			Store(53, Local0)
		} elseif (LEqual(arg0, 54)) {
			Store(54, Local0)
		} elseif (LEqual(arg0, 55)) {
			Store(55, Local0)
		} else {
			Store(56, Local0)
		}

	// 100 elseif

	} elseif (LEqual(arg0, 57)) {	// 1
		Store(57, Local0)
	} elseif (LEqual(arg0, 58)) {
		Store(58, Local0)
	} elseif (LEqual(arg0, 59)) {
		Store(59, Local0)
	} elseif (LEqual(arg0, 60)) {
		Store(60, Local0)
	} elseif (LEqual(arg0, 61)) {
		Store(61, Local0)
	} elseif (LEqual(arg0, 62)) {
		Store(62, Local0)
	} elseif (LEqual(arg0, 63)) {
		Store(63, Local0)
	} elseif (LEqual(arg0, 64)) {
		Store(64, Local0)
	} elseif (LEqual(arg0, 65)) {
		Store(65, Local0)
	} elseif (LEqual(arg0, 66)) {
		Store(66, Local0)
	} elseif (LEqual(arg0, 67)) {	// 11
		Store(67, Local0)
	} elseif (LEqual(arg0, 68)) {
		Store(68, Local0)
	} elseif (LEqual(arg0, 69)) {
		Store(69, Local0)
	} elseif (LEqual(arg0, 70)) {
		Store(70, Local0)
	} elseif (LEqual(arg0, 71)) {
		Store(71, Local0)
	} elseif (LEqual(arg0, 72)) {
		Store(72, Local0)
	} elseif (LEqual(arg0, 73)) {
		Store(73, Local0)
	} elseif (LEqual(arg0, 74)) {
		Store(74, Local0)
	} elseif (LEqual(arg0, 75)) {
		Store(75, Local0)
	} elseif (LEqual(arg0, 76)) {
		Store(76, Local0)
	} elseif (LEqual(arg0, 77)) {	// 21
		Store(77, Local0)
	} elseif (LEqual(arg0, 78)) {
		Store(78, Local0)
	} elseif (LEqual(arg0, 79)) {
		Store(79, Local0)
	} elseif (LEqual(arg0, 80)) {
		Store(80, Local0)
	} elseif (LEqual(arg0, 81)) {
		Store(81, Local0)
	} elseif (LEqual(arg0, 82)) {
		Store(82, Local0)
	} elseif (LEqual(arg0, 83)) {
		Store(83, Local0)
	} elseif (LEqual(arg0, 84)) {
		Store(84, Local0)
	} elseif (LEqual(arg0, 85)) {
		Store(85, Local0)
	} elseif (LEqual(arg0, 86)) {
		Store(86, Local0)
	} elseif (LEqual(arg0, 87)) {	// 31
		Store(87, Local0)
	} elseif (LEqual(arg0, 88)) {
		Store(88, Local0)
	} elseif (LEqual(arg0, 89)) {
		Store(89, Local0)
	} elseif (LEqual(arg0, 90)) {
		Store(90, Local0)
	} elseif (LEqual(arg0, 91)) {
		Store(91, Local0)
	} elseif (LEqual(arg0, 92)) {
		Store(92, Local0)
	} elseif (LEqual(arg0, 93)) {
		Store(93, Local0)
	} elseif (LEqual(arg0, 94)) {
		Store(94, Local0)
	} elseif (LEqual(arg0, 95)) {
		Store(95, Local0)
	} elseif (LEqual(arg0, 96)) {
		Store(96, Local0)
	} elseif (LEqual(arg0, 97)) {	// 41
		Store(97, Local0)
	} elseif (LEqual(arg0, 98)) {
		Store(98, Local0)
	} elseif (LEqual(arg0, 99)) {
		Store(99, Local0)
	} elseif (LEqual(arg0, 100)) {
		Store(100, Local0)
	} elseif (LEqual(arg0, 101)) {
		Store(101, Local0)
	} elseif (LEqual(arg0, 102)) {
		Store(102, Local0)
	} elseif (LEqual(arg0, 103)) {
		Store(103, Local0)
	} elseif (LEqual(arg0, 104)) {
		Store(104, Local0)
	} elseif (LEqual(arg0, 105)) {
		Store(105, Local0)
	} elseif (LEqual(arg0, 106)) {
		Store(106, Local0)
	} elseif (LEqual(arg0, 107)) {	// 51
		Store(107, Local0)
	} elseif (LEqual(arg0, 108)) {
		Store(108, Local0)
	} elseif (LEqual(arg0, 109)) {
		Store(109, Local0)
	} elseif (LEqual(arg0, 110)) {
		Store(110, Local0)
	} elseif (LEqual(arg0, 111)) {
		Store(111, Local0)
	} elseif (LEqual(arg0, 112)) {
		Store(112, Local0)
	} elseif (LEqual(arg0, 113)) {
		Store(113, Local0)
	} elseif (LEqual(arg0, 114)) {
		Store(114, Local0)
	} elseif (LEqual(arg0, 115)) {
		Store(115, Local0)
	} elseif (LEqual(arg0, 116)) {
		Store(116, Local0)
	} elseif (LEqual(arg0, 117)) {	// 61
		Store(117, Local0)
	} elseif (LEqual(arg0, 118)) {
		Store(118, Local0)
	} elseif (LEqual(arg0, 119)) {
		Store(119, Local0)
	} elseif (LEqual(arg0, 120)) {
		Store(120, Local0)
	} elseif (LEqual(arg0, 121)) {
		Store(121, Local0)
	} elseif (LEqual(arg0, 122)) {
		Store(122, Local0)
	} elseif (LEqual(arg0, 123)) {
		Store(123, Local0)
	} elseif (LEqual(arg0, 124)) {
		Store(124, Local0)
	} elseif (LEqual(arg0, 125)) {
		Store(125, Local0)
	} elseif (LEqual(arg0, 126)) {
		Store(126, Local0)
	} elseif (LEqual(arg0, 127)) {	// 71
		Store(127, Local0)
	} elseif (LEqual(arg0, 128)) {
		Store(128, Local0)
	} elseif (LEqual(arg0, 129)) {
		Store(129, Local0)
	} elseif (LEqual(arg0, 130)) {
		Store(130, Local0)
	} elseif (LEqual(arg0, 131)) {
		Store(131, Local0)
	} elseif (LEqual(arg0, 132)) {
		Store(132, Local0)
	} elseif (LEqual(arg0, 133)) {
		Store(133, Local0)
	} elseif (LEqual(arg0, 134)) {
		Store(134, Local0)
	} elseif (LEqual(arg0, 135)) {
		Store(135, Local0)
	} elseif (LEqual(arg0, 136)) {
		Store(136, Local0)
	} elseif (LEqual(arg0, 137)) {	// 81
		Store(137, Local0)
	} elseif (LEqual(arg0, 138)) {
		Store(138, Local0)
	} elseif (LEqual(arg0, 139)) {
		Store(139, Local0)
	} elseif (LEqual(arg0, 140)) {
		Store(140, Local0)
	} elseif (LEqual(arg0, 141)) {
		Store(141, Local0)
	} elseif (LEqual(arg0, 142)) {
		Store(142, Local0)
	} elseif (LEqual(arg0, 143)) {
		Store(143, Local0)
	} elseif (LEqual(arg0, 144)) {
		Store(144, Local0)
	} elseif (LEqual(arg0, 145)) {
		Store(145, Local0)
	} elseif (LEqual(arg0, 146)) {
		Store(146, Local0)
	} elseif (LEqual(arg0, 147)) {	// 91
		Store(147, Local0)
	} elseif (LEqual(arg0, 148)) {
		Store(148, Local0)
	} elseif (LEqual(arg0, 149)) {
		Store(149, Local0)
	} elseif (LEqual(arg0, 150)) {
		Store(150, Local0)
	} elseif (LEqual(arg0, 151)) {
		Store(151, Local0)
	} elseif (LEqual(arg0, 152)) {
		Store(152, Local0)
	} elseif (LEqual(arg0, 153)) {
		Store(153, Local0)
	} elseif (LEqual(arg0, 154)) {
		Store(154, Local0)
	} elseif (LEqual(arg0, 155)) {
		Store(155, Local0)
	} elseif (LEqual(arg0, 156)) {
		Store(156, Local0)
	} elseif (RNG0(arg0, 157, 199)) {	// 101

		// embedded elseif (20 levels)

		if (LEqual(arg0, 157)) {
		    Store(157, Local0)
		} elseif (RNG0(arg0, 158, 198)) {	// 1
			if (LEqual(arg0, 158)) {
			  Store(158, Local0)
			} elseif (RNG0(arg0, 159, 197)) {
			  if (LEqual(arg0, 159)) {
				Store(159, Local0)
			  } elseif (RNG0(arg0, 160, 196)) {
				if (LEqual(arg0, 160)) {
				    Store(160, Local0)
				} elseif (RNG0(arg0, 157, 195)) {
				  if (LEqual(arg0, 161)) {
					Store(161, Local0)
				  } elseif (RNG0(arg0, 162, 194)) {
					if (LEqual(arg0, 162)) {
					  Store(162, Local0)
					} elseif (RNG0(arg0, 163, 193)) {
					  if (LEqual(arg0, 163)) {
						Store(163, Local0)
					  } elseif (RNG0(arg0, 164, 192)) {
						if (LEqual(arg0, 164)) {
						  Store(164, Local0)
						} elseif (RNG0(arg0, 165, 191)) {
						  if (LEqual(arg0, 165)) {
							Store(165, Local0)
						  } elseif (RNG0(arg0, 166, 190)) {
							if (LEqual(arg0, 166)) {
							  Store(166, Local0)
							} elseif (RNG0(arg0, 167, 189)) {
							  if (LEqual(arg0, 167)) {
								Store(167, Local0)
							  } elseif (RNG0(arg0, 168, 188)) {	// 11
								if (LEqual(arg0, 168)) {
								  Store(168, Local0)
								} elseif (RNG0(arg0, 169, 187)) {
								  if (LEqual(arg0, 169)) {
									Store(169, Local0)
								  } elseif (RNG0(arg0, 170, 186)) {
									if (LEqual(arg0, 170)) {
									  Store(170, Local0)
									} elseif (RNG0(arg0, 171, 185)) {
									  if (LEqual(arg0, 171)) {
										Store(171, Local0)
									  } elseif (RNG0(arg0, 172, 184)) {
										if (LEqual(arg0, 172)) {
										  Store(172, Local0)
										} elseif (RNG0(arg0, 173, 183)) {
										  if (LEqual(arg0, 173)) {
											Store(173, Local0)
										  } elseif (RNG0(arg0, 174, 182)) {
											if (LEqual(arg0, 174)) {
											  Store(174, Local0)
											} elseif (RNG0(arg0, 175, 181)) {
											  if (LEqual(arg0, 175)) {
												Store(175, Local0)
											  } elseif (RNG0(arg0, 176, 180)) {
												if (LEqual(arg0, 176)) {
												  Store(176, Local0)
												} elseif (RNG0(arg0, 177, 179)) {
												  if (LEqual(arg0, 177)) {
													Store(177, Local0)
												  } elseif (LEqual(arg0, 178)) {	// 21
													Store(178, Local0)
												  } else {
													Store(179, Local0)
												  }
												} else {
												  Store(180, Local0)
												}
											  } else {
												Store(181, Local0)
											  }
											} else {
											  Store(182, Local0)
											}
										  } else {
											Store(183, Local0)
										  }
										} else {
										  Store(184, Local0)
										}
									  } else {
										Store(185, Local0)
									  }
									} else {
									  Store(186, Local0)
									}
								  } else {
									Store(187, Local0)
								  }
								} else {
								  Store(188, Local0)
								}
							  } else {
								Store(189, Local0)
							  }
							} else {
							  Store(190, Local0)
							}
						  } else {
							Store(191, Local0)
						  }
						} else {
						  Store(192, Local0)
						}
					  } else {
						Store(193, Local0)
					  }
					} else {
					  Store(194, Local0)
					}
				  } else {
					Store(195, Local0)
				  }
				} else {
				  Store(196, Local0)
				}
			  } else {
				Store(197, Local0)
			  }
			} else {
			Store(198, Local0)
			}
		} else {
			Store(199, Local0)
		}

	// 100 elseif

	} elseif (LEqual(arg0, 200)) {	// 1
		Store(200, Local0)
	} elseif (LEqual(arg0, 201)) {
		Store(201, Local0)
	} elseif (LEqual(arg0, 202)) {
		Store(202, Local0)
	} elseif (LEqual(arg0, 203)) {
		Store(203, Local0)
	} elseif (LEqual(arg0, 204)) {
		Store(204, Local0)
	} elseif (LEqual(arg0, 205)) {
		Store(205, Local0)
	} elseif (LEqual(arg0, 206)) {
		Store(206, Local0)
	} elseif (LEqual(arg0, 207)) {
		Store(207, Local0)
	} elseif (LEqual(arg0, 208)) {
		Store(208, Local0)
	} elseif (LEqual(arg0, 209)) {
		Store(209, Local0)
	} elseif (LEqual(arg0, 210)) {	// 11
		Store(210, Local0)
	} elseif (LEqual(arg0, 211)) {
		Store(211, Local0)
	} elseif (LEqual(arg0, 212)) {
		Store(212, Local0)
	} elseif (LEqual(arg0, 213)) {
		Store(213, Local0)
	} elseif (LEqual(arg0, 214)) {
		Store(214, Local0)
	} elseif (LEqual(arg0, 215)) {
		Store(215, Local0)
	} elseif (LEqual(arg0, 216)) {
		Store(216, Local0)
	} elseif (LEqual(arg0, 217)) {
		Store(217, Local0)
	} elseif (LEqual(arg0, 218)) {
		Store(218, Local0)
	} elseif (LEqual(arg0, 219)) {
		Store(219, Local0)
	} elseif (LEqual(arg0, 220)) {	// 21
		Store(220, Local0)
	} elseif (LEqual(arg0, 221)) {
		Store(221, Local0)
	} elseif (LEqual(arg0, 222)) {
		Store(222, Local0)
	} elseif (LEqual(arg0, 223)) {
		Store(223, Local0)
	} elseif (LEqual(arg0, 224)) {
		Store(224, Local0)
	} elseif (LEqual(arg0, 225)) {
		Store(225, Local0)
	} elseif (LEqual(arg0, 226)) {
		Store(226, Local0)
	} elseif (LEqual(arg0, 227)) {
		Store(227, Local0)
	} elseif (LEqual(arg0, 228)) {
		Store(228, Local0)
	} elseif (LEqual(arg0, 229)) {
		Store(229, Local0)
	} elseif (LEqual(arg0, 230)) {	// 31
		Store(230, Local0)
	} elseif (LEqual(arg0, 231)) {
		Store(231, Local0)
	} elseif (LEqual(arg0, 232)) {
		Store(232, Local0)
	} elseif (LEqual(arg0, 233)) {
		Store(233, Local0)
	} elseif (LEqual(arg0, 234)) {
		Store(234, Local0)
	} elseif (LEqual(arg0, 235)) {
		Store(235, Local0)
	} elseif (LEqual(arg0, 236)) {
		Store(236, Local0)
	} elseif (LEqual(arg0, 237)) {
		Store(237, Local0)
	} elseif (LEqual(arg0, 238)) {
		Store(238, Local0)
	} elseif (LEqual(arg0, 239)) {
		Store(239, Local0)
	} elseif (LEqual(arg0, 240)) {	// 41
		Store(240, Local0)
	} elseif (LEqual(arg0, 241)) {
		Store(241, Local0)
	} elseif (LEqual(arg0, 242)) {
		Store(242, Local0)
	} elseif (LEqual(arg0, 243)) {
		Store(243, Local0)
	} elseif (LEqual(arg0, 244)) {
		Store(244, Local0)
	} elseif (LEqual(arg0, 245)) {
		Store(245, Local0)
	} elseif (LEqual(arg0, 246)) {
		Store(246, Local0)
	} elseif (LEqual(arg0, 247)) {
		Store(247, Local0)
	} elseif (LEqual(arg0, 248)) {
		Store(248, Local0)
	} elseif (LEqual(arg0, 249)) {
		Store(249, Local0)
	} elseif (LEqual(arg0, 250)) {	// 51
		Store(250, Local0)
	} elseif (LEqual(arg0, 251)) {
		Store(251, Local0)
	} elseif (LEqual(arg0, 252)) {
		Store(252, Local0)
	} elseif (LEqual(arg0, 253)) {
		Store(253, Local0)
	} elseif (LEqual(arg0, 254)) {
		Store(254, Local0)
	} elseif (LEqual(arg0, 255)) {
		Store(255, Local0)
	} elseif (LEqual(arg0, 256)) {
		Store(256, Local0)
	} elseif (LEqual(arg0, 257)) {
		Store(257, Local0)
	} elseif (LEqual(arg0, 258)) {
		Store(258, Local0)
	} elseif (LEqual(arg0, 259)) {
		Store(259, Local0)
	} elseif (LEqual(arg0, 260)) {	// 61
		Store(260, Local0)
	} elseif (LEqual(arg0, 261)) {
		Store(261, Local0)
	} elseif (LEqual(arg0, 262)) {
		Store(262, Local0)
	} elseif (LEqual(arg0, 263)) {
		Store(263, Local0)
	} elseif (LEqual(arg0, 264)) {
		Store(264, Local0)
	} elseif (LEqual(arg0, 265)) {
		Store(265, Local0)
	} elseif (LEqual(arg0, 266)) {
		Store(266, Local0)
	} elseif (LEqual(arg0, 267)) {
		Store(267, Local0)
	} elseif (LEqual(arg0, 268)) {
		Store(268, Local0)
	} elseif (LEqual(arg0, 269)) {
		Store(269, Local0)
	} elseif (LEqual(arg0, 270)) {	// 71
		Store(270, Local0)
	} elseif (LEqual(arg0, 271)) {
		Store(271, Local0)
	} elseif (LEqual(arg0, 272)) {
		Store(272, Local0)
	} elseif (LEqual(arg0, 273)) {
		Store(273, Local0)
	} elseif (LEqual(arg0, 274)) {
		Store(274, Local0)
	} elseif (LEqual(arg0, 275)) {
		Store(275, Local0)
	} elseif (LEqual(arg0, 276)) {
		Store(276, Local0)
	} elseif (LEqual(arg0, 277)) {
		Store(277, Local0)
	} elseif (LEqual(arg0, 278)) {
		Store(278, Local0)
	} elseif (LEqual(arg0, 279)) {
		Store(279, Local0)
	} elseif (LEqual(arg0, 280)) {	// 81
		Store(280, Local0)
	} elseif (LEqual(arg0, 281)) {
		Store(281, Local0)
	} elseif (LEqual(arg0, 282)) {
		Store(282, Local0)
	} elseif (LEqual(arg0, 283)) {
		Store(283, Local0)
	} elseif (LEqual(arg0, 284)) {
		Store(284, Local0)
	} elseif (LEqual(arg0, 285)) {
		Store(285, Local0)
	} elseif (LEqual(arg0, 286)) {
		Store(286, Local0)
	} elseif (LEqual(arg0, 287)) {
		Store(287, Local0)
	} elseif (LEqual(arg0, 288)) {
		Store(288, Local0)
	} elseif (LEqual(arg0, 289)) {
		Store(289, Local0)
	} elseif (LEqual(arg0, 290)) {	// 91
		Store(290, Local0)
	} elseif (LEqual(arg0, 291)) {
		Store(291, Local0)
	} elseif (LEqual(arg0, 292)) {
		Store(292, Local0)
	} elseif (LEqual(arg0, 293)) {
		Store(293, Local0)
	} elseif (LEqual(arg0, 294)) {
		Store(294, Local0)
	} elseif (LEqual(arg0, 295)) {
		Store(295, Local0)
	} elseif (LEqual(arg0, 296)) {
		Store(296, Local0)
	} elseif (LEqual(arg0, 297)) {
		Store(297, Local0)
	} elseif (LEqual(arg0, 298)) {
		Store(298, Local0)
	} elseif (LEqual(arg0, 299)) {
		Store(299, Local0)
	} elseif (LEqual(arg0, 300)) {	// 101
		Store(300, Local0)
	} else {
		Store(301, Local0)
	}

	return (Local0)
}

Method(IF00,, Serialized)
{
	Name(ts, "IF00")

	Store("TEST: IF00, Huge, many levels embedded {if,elseif,else)", Debug)

	Store(0, Local7)

	While (LLess(Local7, 302)) {
		Store(m040(Local7), Local0)
		if (LNotEqual(Local0, Local7)) {
			err(ts, z005, __LINE__, 0, 0, Local0, 0)
		}
		Increment(Local7)
	}
}

// Run-method
Method(CTL2)
{
	Store("TEST: CTL2, Conditional execution", Debug)

	IF00()
}
