#undef CRL_APB_RPLL_CTRL_OFFSET 
#define CRL_APB_RPLL_CTRL_OFFSET                                                   0XFF5E0030
#undef CRL_APB_RPLL_CTRL_OFFSET 
#define CRL_APB_RPLL_CTRL_OFFSET                                                   0XFF5E0030
#undef CRL_APB_RPLL_CTRL_OFFSET 
#define CRL_APB_RPLL_CTRL_OFFSET                                                   0XFF5E0030
#undef CRL_APB_RPLL_CTRL_OFFSET 
#define CRL_APB_RPLL_CTRL_OFFSET                                                   0XFF5E0030
#undef CRL_APB_RPLL_CTRL_OFFSET 
#define CRL_APB_RPLL_CTRL_OFFSET                                                   0XFF5E0030
#undef CRL_APB_RPLL_TO_FPD_CTRL_OFFSET 
#define CRL_APB_RPLL_TO_FPD_CTRL_OFFSET                                            0XFF5E0048
#undef CRL_APB_IOPLL_CTRL_OFFSET 
#define CRL_APB_IOPLL_CTRL_OFFSET                                                  0XFF5E0020
#undef CRL_APB_IOPLL_CTRL_OFFSET 
#define CRL_APB_IOPLL_CTRL_OFFSET                                                  0XFF5E0020
#undef CRL_APB_IOPLL_CTRL_OFFSET 
#define CRL_APB_IOPLL_CTRL_OFFSET                                                  0XFF5E0020
#undef CRL_APB_IOPLL_CTRL_OFFSET 
#define CRL_APB_IOPLL_CTRL_OFFSET                                                  0XFF5E0020
#undef CRL_APB_IOPLL_CTRL_OFFSET 
#define CRL_APB_IOPLL_CTRL_OFFSET                                                  0XFF5E0020
#undef CRL_APB_IOPLL_TO_FPD_CTRL_OFFSET 
#define CRL_APB_IOPLL_TO_FPD_CTRL_OFFSET                                           0XFF5E0044
#undef CRF_APB_APLL_CTRL_OFFSET 
#define CRF_APB_APLL_CTRL_OFFSET                                                   0XFD1A0020
#undef CRF_APB_APLL_CTRL_OFFSET 
#define CRF_APB_APLL_CTRL_OFFSET                                                   0XFD1A0020
#undef CRF_APB_APLL_CTRL_OFFSET 
#define CRF_APB_APLL_CTRL_OFFSET                                                   0XFD1A0020
#undef CRF_APB_APLL_CTRL_OFFSET 
#define CRF_APB_APLL_CTRL_OFFSET                                                   0XFD1A0020
#undef CRF_APB_APLL_CTRL_OFFSET 
#define CRF_APB_APLL_CTRL_OFFSET                                                   0XFD1A0020
#undef CRF_APB_APLL_TO_LPD_CTRL_OFFSET 
#define CRF_APB_APLL_TO_LPD_CTRL_OFFSET                                            0XFD1A0048
#undef CRF_APB_DPLL_CTRL_OFFSET 
#define CRF_APB_DPLL_CTRL_OFFSET                                                   0XFD1A002C
#undef CRF_APB_DPLL_CTRL_OFFSET 
#define CRF_APB_DPLL_CTRL_OFFSET                                                   0XFD1A002C
#undef CRF_APB_DPLL_CTRL_OFFSET 
#define CRF_APB_DPLL_CTRL_OFFSET                                                   0XFD1A002C
#undef CRF_APB_DPLL_CTRL_OFFSET 
#define CRF_APB_DPLL_CTRL_OFFSET                                                   0XFD1A002C
#undef CRF_APB_DPLL_CTRL_OFFSET 
#define CRF_APB_DPLL_CTRL_OFFSET                                                   0XFD1A002C
#undef CRF_APB_DPLL_TO_LPD_CTRL_OFFSET 
#define CRF_APB_DPLL_TO_LPD_CTRL_OFFSET                                            0XFD1A004C
#undef CRF_APB_VPLL_CTRL_OFFSET 
#define CRF_APB_VPLL_CTRL_OFFSET                                                   0XFD1A0038
#undef CRF_APB_VPLL_CTRL_OFFSET 
#define CRF_APB_VPLL_CTRL_OFFSET                                                   0XFD1A0038
#undef CRF_APB_VPLL_CTRL_OFFSET 
#define CRF_APB_VPLL_CTRL_OFFSET                                                   0XFD1A0038
#undef CRF_APB_VPLL_CTRL_OFFSET 
#define CRF_APB_VPLL_CTRL_OFFSET                                                   0XFD1A0038
#undef CRF_APB_VPLL_CTRL_OFFSET 
#define CRF_APB_VPLL_CTRL_OFFSET                                                   0XFD1A0038
#undef CRF_APB_VPLL_TO_LPD_CTRL_OFFSET 
#define CRF_APB_VPLL_TO_LPD_CTRL_OFFSET                                            0XFD1A0050

/*The integer portion of the feedback divider to the PLL*/
#undef CRL_APB_RPLL_CTRL_FBDIV_DEFVAL 
#undef CRL_APB_RPLL_CTRL_FBDIV_SHIFT 
#undef CRL_APB_RPLL_CTRL_FBDIV_MASK 
#define CRL_APB_RPLL_CTRL_FBDIV_DEFVAL                                             0x00012C09
#define CRL_APB_RPLL_CTRL_FBDIV_SHIFT                                              8
#define CRL_APB_RPLL_CTRL_FBDIV_MASK                                               0x00007F00U

/*This turns on the divide by 2 that is inside of the PLL. This does not change the VCO frequency, just the output frequency*/
#undef CRL_APB_RPLL_CTRL_DIV2_DEFVAL 
#undef CRL_APB_RPLL_CTRL_DIV2_SHIFT 
#undef CRL_APB_RPLL_CTRL_DIV2_MASK 
#define CRL_APB_RPLL_CTRL_DIV2_DEFVAL                                              0x00012C09
#define CRL_APB_RPLL_CTRL_DIV2_SHIFT                                               16
#define CRL_APB_RPLL_CTRL_DIV2_MASK                                                0x00010000U

/*Bypasses the PLL clock. The usable clock will be determined from the POST_SRC field. (This signal may only be toggled after 4
		cycles of the old clock and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_RPLL_CTRL_BYPASS_DEFVAL 
#undef CRL_APB_RPLL_CTRL_BYPASS_SHIFT 
#undef CRL_APB_RPLL_CTRL_BYPASS_MASK 
#define CRL_APB_RPLL_CTRL_BYPASS_DEFVAL                                            0x00012C09
#define CRL_APB_RPLL_CTRL_BYPASS_SHIFT                                             3
#define CRL_APB_RPLL_CTRL_BYPASS_MASK                                              0x00000008U

/*Asserts Reset to the PLL*/
#undef CRL_APB_RPLL_CTRL_RESET_DEFVAL 
#undef CRL_APB_RPLL_CTRL_RESET_SHIFT 
#undef CRL_APB_RPLL_CTRL_RESET_MASK 
#define CRL_APB_RPLL_CTRL_RESET_DEFVAL                                             0x00012C09
#define CRL_APB_RPLL_CTRL_RESET_SHIFT                                              0
#define CRL_APB_RPLL_CTRL_RESET_MASK                                               0x00000001U

/*Asserts Reset to the PLL*/
#undef CRL_APB_RPLL_CTRL_RESET_DEFVAL 
#undef CRL_APB_RPLL_CTRL_RESET_SHIFT 
#undef CRL_APB_RPLL_CTRL_RESET_MASK 
#define CRL_APB_RPLL_CTRL_RESET_DEFVAL                                             0x00012C09
#define CRL_APB_RPLL_CTRL_RESET_SHIFT                                              0
#define CRL_APB_RPLL_CTRL_RESET_MASK                                               0x00000001U

/*RPLL is locked*/
#undef CRL_APB_PLL_STATUS_RPLL_LOCK_DEFVAL 
#undef CRL_APB_PLL_STATUS_RPLL_LOCK_SHIFT 
#undef CRL_APB_PLL_STATUS_RPLL_LOCK_MASK 
#define CRL_APB_PLL_STATUS_RPLL_LOCK_DEFVAL                                        0x00000018
#define CRL_APB_PLL_STATUS_RPLL_LOCK_SHIFT                                         1
#define CRL_APB_PLL_STATUS_RPLL_LOCK_MASK                                          0x00000002U
#define CRL_APB_PLL_STATUS_OFFSET                                                  0XFF5E0040

/*Bypasses the PLL clock. The usable clock will be determined from the POST_SRC field. (This signal may only be toggled after 4
		cycles of the old clock and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_RPLL_CTRL_BYPASS_DEFVAL 
#undef CRL_APB_RPLL_CTRL_BYPASS_SHIFT 
#undef CRL_APB_RPLL_CTRL_BYPASS_MASK 
#define CRL_APB_RPLL_CTRL_BYPASS_DEFVAL                                            0x00012C09
#define CRL_APB_RPLL_CTRL_BYPASS_SHIFT                                             3
#define CRL_APB_RPLL_CTRL_BYPASS_MASK                                              0x00000008U

/*Divisor value for this clock.*/
#undef CRL_APB_RPLL_TO_FPD_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_RPLL_TO_FPD_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_RPLL_TO_FPD_CTRL_DIVISOR0_MASK 
#define CRL_APB_RPLL_TO_FPD_CTRL_DIVISOR0_DEFVAL                                   0x00000400
#define CRL_APB_RPLL_TO_FPD_CTRL_DIVISOR0_SHIFT                                    8
#define CRL_APB_RPLL_TO_FPD_CTRL_DIVISOR0_MASK                                     0x00003F00U

/*The integer portion of the feedback divider to the PLL*/
#undef CRL_APB_IOPLL_CTRL_FBDIV_DEFVAL 
#undef CRL_APB_IOPLL_CTRL_FBDIV_SHIFT 
#undef CRL_APB_IOPLL_CTRL_FBDIV_MASK 
#define CRL_APB_IOPLL_CTRL_FBDIV_DEFVAL                                            0x00012C09
#define CRL_APB_IOPLL_CTRL_FBDIV_SHIFT                                             8
#define CRL_APB_IOPLL_CTRL_FBDIV_MASK                                              0x00007F00U

/*This turns on the divide by 2 that is inside of the PLL. This does not change the VCO frequency, just the output frequency*/
#undef CRL_APB_IOPLL_CTRL_DIV2_DEFVAL 
#undef CRL_APB_IOPLL_CTRL_DIV2_SHIFT 
#undef CRL_APB_IOPLL_CTRL_DIV2_MASK 
#define CRL_APB_IOPLL_CTRL_DIV2_DEFVAL                                             0x00012C09
#define CRL_APB_IOPLL_CTRL_DIV2_SHIFT                                              16
#define CRL_APB_IOPLL_CTRL_DIV2_MASK                                               0x00010000U

/*Bypasses the PLL clock. The usable clock will be determined from the POST_SRC field. (This signal may only be toggled after 4
		cycles of the old clock and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_IOPLL_CTRL_BYPASS_DEFVAL 
#undef CRL_APB_IOPLL_CTRL_BYPASS_SHIFT 
#undef CRL_APB_IOPLL_CTRL_BYPASS_MASK 
#define CRL_APB_IOPLL_CTRL_BYPASS_DEFVAL                                           0x00012C09
#define CRL_APB_IOPLL_CTRL_BYPASS_SHIFT                                            3
#define CRL_APB_IOPLL_CTRL_BYPASS_MASK                                             0x00000008U

/*Asserts Reset to the PLL*/
#undef CRL_APB_IOPLL_CTRL_RESET_DEFVAL 
#undef CRL_APB_IOPLL_CTRL_RESET_SHIFT 
#undef CRL_APB_IOPLL_CTRL_RESET_MASK 
#define CRL_APB_IOPLL_CTRL_RESET_DEFVAL                                            0x00012C09
#define CRL_APB_IOPLL_CTRL_RESET_SHIFT                                             0
#define CRL_APB_IOPLL_CTRL_RESET_MASK                                              0x00000001U

/*Asserts Reset to the PLL*/
#undef CRL_APB_IOPLL_CTRL_RESET_DEFVAL 
#undef CRL_APB_IOPLL_CTRL_RESET_SHIFT 
#undef CRL_APB_IOPLL_CTRL_RESET_MASK 
#define CRL_APB_IOPLL_CTRL_RESET_DEFVAL                                            0x00012C09
#define CRL_APB_IOPLL_CTRL_RESET_SHIFT                                             0
#define CRL_APB_IOPLL_CTRL_RESET_MASK                                              0x00000001U

/*IOPLL is locked*/
#undef CRL_APB_PLL_STATUS_IOPLL_LOCK_DEFVAL 
#undef CRL_APB_PLL_STATUS_IOPLL_LOCK_SHIFT 
#undef CRL_APB_PLL_STATUS_IOPLL_LOCK_MASK 
#define CRL_APB_PLL_STATUS_IOPLL_LOCK_DEFVAL                                       0x00000018
#define CRL_APB_PLL_STATUS_IOPLL_LOCK_SHIFT                                        0
#define CRL_APB_PLL_STATUS_IOPLL_LOCK_MASK                                         0x00000001U
#define CRL_APB_PLL_STATUS_OFFSET                                                  0XFF5E0040

/*Bypasses the PLL clock. The usable clock will be determined from the POST_SRC field. (This signal may only be toggled after 4
		cycles of the old clock and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_IOPLL_CTRL_BYPASS_DEFVAL 
#undef CRL_APB_IOPLL_CTRL_BYPASS_SHIFT 
#undef CRL_APB_IOPLL_CTRL_BYPASS_MASK 
#define CRL_APB_IOPLL_CTRL_BYPASS_DEFVAL                                           0x00012C09
#define CRL_APB_IOPLL_CTRL_BYPASS_SHIFT                                            3
#define CRL_APB_IOPLL_CTRL_BYPASS_MASK                                             0x00000008U

/*Divisor value for this clock.*/
#undef CRL_APB_IOPLL_TO_FPD_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_IOPLL_TO_FPD_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_IOPLL_TO_FPD_CTRL_DIVISOR0_MASK 
#define CRL_APB_IOPLL_TO_FPD_CTRL_DIVISOR0_DEFVAL                                  0x00000400
#define CRL_APB_IOPLL_TO_FPD_CTRL_DIVISOR0_SHIFT                                   8
#define CRL_APB_IOPLL_TO_FPD_CTRL_DIVISOR0_MASK                                    0x00003F00U

/*The integer portion of the feedback divider to the PLL*/
#undef CRF_APB_APLL_CTRL_FBDIV_DEFVAL 
#undef CRF_APB_APLL_CTRL_FBDIV_SHIFT 
#undef CRF_APB_APLL_CTRL_FBDIV_MASK 
#define CRF_APB_APLL_CTRL_FBDIV_DEFVAL                                             0x00012C09
#define CRF_APB_APLL_CTRL_FBDIV_SHIFT                                              8
#define CRF_APB_APLL_CTRL_FBDIV_MASK                                               0x00007F00U

/*This turns on the divide by 2 that is inside of the PLL. This does not change the VCO frequency, just the output frequency*/
#undef CRF_APB_APLL_CTRL_DIV2_DEFVAL 
#undef CRF_APB_APLL_CTRL_DIV2_SHIFT 
#undef CRF_APB_APLL_CTRL_DIV2_MASK 
#define CRF_APB_APLL_CTRL_DIV2_DEFVAL                                              0x00012C09
#define CRF_APB_APLL_CTRL_DIV2_SHIFT                                               16
#define CRF_APB_APLL_CTRL_DIV2_MASK                                                0x00010000U

/*Bypasses the PLL clock. The usable clock will be determined from the POST_SRC field. (This signal may only be toggled after 4
		cycles of the old clock and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_APLL_CTRL_BYPASS_DEFVAL 
#undef CRF_APB_APLL_CTRL_BYPASS_SHIFT 
#undef CRF_APB_APLL_CTRL_BYPASS_MASK 
#define CRF_APB_APLL_CTRL_BYPASS_DEFVAL                                            0x00012C09
#define CRF_APB_APLL_CTRL_BYPASS_SHIFT                                             3
#define CRF_APB_APLL_CTRL_BYPASS_MASK                                              0x00000008U

/*Asserts Reset to the PLL*/
#undef CRF_APB_APLL_CTRL_RESET_DEFVAL 
#undef CRF_APB_APLL_CTRL_RESET_SHIFT 
#undef CRF_APB_APLL_CTRL_RESET_MASK 
#define CRF_APB_APLL_CTRL_RESET_DEFVAL                                             0x00012C09
#define CRF_APB_APLL_CTRL_RESET_SHIFT                                              0
#define CRF_APB_APLL_CTRL_RESET_MASK                                               0x00000001U

/*Asserts Reset to the PLL*/
#undef CRF_APB_APLL_CTRL_RESET_DEFVAL 
#undef CRF_APB_APLL_CTRL_RESET_SHIFT 
#undef CRF_APB_APLL_CTRL_RESET_MASK 
#define CRF_APB_APLL_CTRL_RESET_DEFVAL                                             0x00012C09
#define CRF_APB_APLL_CTRL_RESET_SHIFT                                              0
#define CRF_APB_APLL_CTRL_RESET_MASK                                               0x00000001U

/*APLL is locked*/
#undef CRF_APB_PLL_STATUS_APLL_LOCK_DEFVAL 
#undef CRF_APB_PLL_STATUS_APLL_LOCK_SHIFT 
#undef CRF_APB_PLL_STATUS_APLL_LOCK_MASK 
#define CRF_APB_PLL_STATUS_APLL_LOCK_DEFVAL                                        0x00000038
#define CRF_APB_PLL_STATUS_APLL_LOCK_SHIFT                                         0
#define CRF_APB_PLL_STATUS_APLL_LOCK_MASK                                          0x00000001U
#define CRF_APB_PLL_STATUS_OFFSET                                                  0XFD1A0044

/*Bypasses the PLL clock. The usable clock will be determined from the POST_SRC field. (This signal may only be toggled after 4
		cycles of the old clock and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_APLL_CTRL_BYPASS_DEFVAL 
#undef CRF_APB_APLL_CTRL_BYPASS_SHIFT 
#undef CRF_APB_APLL_CTRL_BYPASS_MASK 
#define CRF_APB_APLL_CTRL_BYPASS_DEFVAL                                            0x00012C09
#define CRF_APB_APLL_CTRL_BYPASS_SHIFT                                             3
#define CRF_APB_APLL_CTRL_BYPASS_MASK                                              0x00000008U

/*Divisor value for this clock.*/
#undef CRF_APB_APLL_TO_LPD_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_APLL_TO_LPD_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_APLL_TO_LPD_CTRL_DIVISOR0_MASK 
#define CRF_APB_APLL_TO_LPD_CTRL_DIVISOR0_DEFVAL                                   0x00000400
#define CRF_APB_APLL_TO_LPD_CTRL_DIVISOR0_SHIFT                                    8
#define CRF_APB_APLL_TO_LPD_CTRL_DIVISOR0_MASK                                     0x00003F00U

/*The integer portion of the feedback divider to the PLL*/
#undef CRF_APB_DPLL_CTRL_FBDIV_DEFVAL 
#undef CRF_APB_DPLL_CTRL_FBDIV_SHIFT 
#undef CRF_APB_DPLL_CTRL_FBDIV_MASK 
#define CRF_APB_DPLL_CTRL_FBDIV_DEFVAL                                             0x00002C09
#define CRF_APB_DPLL_CTRL_FBDIV_SHIFT                                              8
#define CRF_APB_DPLL_CTRL_FBDIV_MASK                                               0x00007F00U

/*This turns on the divide by 2 that is inside of the PLL. This does not change the VCO frequency, just the output frequency*/
#undef CRF_APB_DPLL_CTRL_DIV2_DEFVAL 
#undef CRF_APB_DPLL_CTRL_DIV2_SHIFT 
#undef CRF_APB_DPLL_CTRL_DIV2_MASK 
#define CRF_APB_DPLL_CTRL_DIV2_DEFVAL                                              0x00002C09
#define CRF_APB_DPLL_CTRL_DIV2_SHIFT                                               16
#define CRF_APB_DPLL_CTRL_DIV2_MASK                                                0x00010000U

/*Bypasses the PLL clock. The usable clock will be determined from the POST_SRC field. (This signal may only be toggled after 4
		cycles of the old clock and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_DPLL_CTRL_BYPASS_DEFVAL 
#undef CRF_APB_DPLL_CTRL_BYPASS_SHIFT 
#undef CRF_APB_DPLL_CTRL_BYPASS_MASK 
#define CRF_APB_DPLL_CTRL_BYPASS_DEFVAL                                            0x00002C09
#define CRF_APB_DPLL_CTRL_BYPASS_SHIFT                                             3
#define CRF_APB_DPLL_CTRL_BYPASS_MASK                                              0x00000008U

/*Asserts Reset to the PLL*/
#undef CRF_APB_DPLL_CTRL_RESET_DEFVAL 
#undef CRF_APB_DPLL_CTRL_RESET_SHIFT 
#undef CRF_APB_DPLL_CTRL_RESET_MASK 
#define CRF_APB_DPLL_CTRL_RESET_DEFVAL                                             0x00002C09
#define CRF_APB_DPLL_CTRL_RESET_SHIFT                                              0
#define CRF_APB_DPLL_CTRL_RESET_MASK                                               0x00000001U

/*Asserts Reset to the PLL*/
#undef CRF_APB_DPLL_CTRL_RESET_DEFVAL 
#undef CRF_APB_DPLL_CTRL_RESET_SHIFT 
#undef CRF_APB_DPLL_CTRL_RESET_MASK 
#define CRF_APB_DPLL_CTRL_RESET_DEFVAL                                             0x00002C09
#define CRF_APB_DPLL_CTRL_RESET_SHIFT                                              0
#define CRF_APB_DPLL_CTRL_RESET_MASK                                               0x00000001U

/*DPLL is locked*/
#undef CRF_APB_PLL_STATUS_DPLL_LOCK_DEFVAL 
#undef CRF_APB_PLL_STATUS_DPLL_LOCK_SHIFT 
#undef CRF_APB_PLL_STATUS_DPLL_LOCK_MASK 
#define CRF_APB_PLL_STATUS_DPLL_LOCK_DEFVAL                                        0x00000038
#define CRF_APB_PLL_STATUS_DPLL_LOCK_SHIFT                                         1
#define CRF_APB_PLL_STATUS_DPLL_LOCK_MASK                                          0x00000002U
#define CRF_APB_PLL_STATUS_OFFSET                                                  0XFD1A0044

/*Bypasses the PLL clock. The usable clock will be determined from the POST_SRC field. (This signal may only be toggled after 4
		cycles of the old clock and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_DPLL_CTRL_BYPASS_DEFVAL 
#undef CRF_APB_DPLL_CTRL_BYPASS_SHIFT 
#undef CRF_APB_DPLL_CTRL_BYPASS_MASK 
#define CRF_APB_DPLL_CTRL_BYPASS_DEFVAL                                            0x00002C09
#define CRF_APB_DPLL_CTRL_BYPASS_SHIFT                                             3
#define CRF_APB_DPLL_CTRL_BYPASS_MASK                                              0x00000008U

/*Divisor value for this clock.*/
#undef CRF_APB_DPLL_TO_LPD_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_DPLL_TO_LPD_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_DPLL_TO_LPD_CTRL_DIVISOR0_MASK 
#define CRF_APB_DPLL_TO_LPD_CTRL_DIVISOR0_DEFVAL                                   0x00000400
#define CRF_APB_DPLL_TO_LPD_CTRL_DIVISOR0_SHIFT                                    8
#define CRF_APB_DPLL_TO_LPD_CTRL_DIVISOR0_MASK                                     0x00003F00U

/*The integer portion of the feedback divider to the PLL*/
#undef CRF_APB_VPLL_CTRL_FBDIV_DEFVAL 
#undef CRF_APB_VPLL_CTRL_FBDIV_SHIFT 
#undef CRF_APB_VPLL_CTRL_FBDIV_MASK 
#define CRF_APB_VPLL_CTRL_FBDIV_DEFVAL                                             0x00012809
#define CRF_APB_VPLL_CTRL_FBDIV_SHIFT                                              8
#define CRF_APB_VPLL_CTRL_FBDIV_MASK                                               0x00007F00U

/*This turns on the divide by 2 that is inside of the PLL. This does not change the VCO frequency, just the output frequency*/
#undef CRF_APB_VPLL_CTRL_DIV2_DEFVAL 
#undef CRF_APB_VPLL_CTRL_DIV2_SHIFT 
#undef CRF_APB_VPLL_CTRL_DIV2_MASK 
#define CRF_APB_VPLL_CTRL_DIV2_DEFVAL                                              0x00012809
#define CRF_APB_VPLL_CTRL_DIV2_SHIFT                                               16
#define CRF_APB_VPLL_CTRL_DIV2_MASK                                                0x00010000U

/*Bypasses the PLL clock. The usable clock will be determined from the POST_SRC field. (This signal may only be toggled after 4
		cycles of the old clock and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_VPLL_CTRL_BYPASS_DEFVAL 
#undef CRF_APB_VPLL_CTRL_BYPASS_SHIFT 
#undef CRF_APB_VPLL_CTRL_BYPASS_MASK 
#define CRF_APB_VPLL_CTRL_BYPASS_DEFVAL                                            0x00012809
#define CRF_APB_VPLL_CTRL_BYPASS_SHIFT                                             3
#define CRF_APB_VPLL_CTRL_BYPASS_MASK                                              0x00000008U

/*Asserts Reset to the PLL*/
#undef CRF_APB_VPLL_CTRL_RESET_DEFVAL 
#undef CRF_APB_VPLL_CTRL_RESET_SHIFT 
#undef CRF_APB_VPLL_CTRL_RESET_MASK 
#define CRF_APB_VPLL_CTRL_RESET_DEFVAL                                             0x00012809
#define CRF_APB_VPLL_CTRL_RESET_SHIFT                                              0
#define CRF_APB_VPLL_CTRL_RESET_MASK                                               0x00000001U

/*Asserts Reset to the PLL*/
#undef CRF_APB_VPLL_CTRL_RESET_DEFVAL 
#undef CRF_APB_VPLL_CTRL_RESET_SHIFT 
#undef CRF_APB_VPLL_CTRL_RESET_MASK 
#define CRF_APB_VPLL_CTRL_RESET_DEFVAL                                             0x00012809
#define CRF_APB_VPLL_CTRL_RESET_SHIFT                                              0
#define CRF_APB_VPLL_CTRL_RESET_MASK                                               0x00000001U

/*VPLL is locked*/
#undef CRF_APB_PLL_STATUS_VPLL_LOCK_DEFVAL 
#undef CRF_APB_PLL_STATUS_VPLL_LOCK_SHIFT 
#undef CRF_APB_PLL_STATUS_VPLL_LOCK_MASK 
#define CRF_APB_PLL_STATUS_VPLL_LOCK_DEFVAL                                        0x00000038
#define CRF_APB_PLL_STATUS_VPLL_LOCK_SHIFT                                         2
#define CRF_APB_PLL_STATUS_VPLL_LOCK_MASK                                          0x00000004U
#define CRF_APB_PLL_STATUS_OFFSET                                                  0XFD1A0044

/*Bypasses the PLL clock. The usable clock will be determined from the POST_SRC field. (This signal may only be toggled after 4
		cycles of the old clock and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_VPLL_CTRL_BYPASS_DEFVAL 
#undef CRF_APB_VPLL_CTRL_BYPASS_SHIFT 
#undef CRF_APB_VPLL_CTRL_BYPASS_MASK 
#define CRF_APB_VPLL_CTRL_BYPASS_DEFVAL                                            0x00012809
#define CRF_APB_VPLL_CTRL_BYPASS_SHIFT                                             3
#define CRF_APB_VPLL_CTRL_BYPASS_MASK                                              0x00000008U

/*Divisor value for this clock.*/
#undef CRF_APB_VPLL_TO_LPD_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_VPLL_TO_LPD_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_VPLL_TO_LPD_CTRL_DIVISOR0_MASK 
#define CRF_APB_VPLL_TO_LPD_CTRL_DIVISOR0_DEFVAL                                   0x00000400
#define CRF_APB_VPLL_TO_LPD_CTRL_DIVISOR0_SHIFT                                    8
#define CRF_APB_VPLL_TO_LPD_CTRL_DIVISOR0_MASK                                     0x00003F00U
#undef CRL_APB_GEM0_REF_CTRL_OFFSET 
#define CRL_APB_GEM0_REF_CTRL_OFFSET                                               0XFF5E0050
#undef CRL_APB_GEM1_REF_CTRL_OFFSET 
#define CRL_APB_GEM1_REF_CTRL_OFFSET                                               0XFF5E0054
#undef CRL_APB_GEM2_REF_CTRL_OFFSET 
#define CRL_APB_GEM2_REF_CTRL_OFFSET                                               0XFF5E0058
#undef CRL_APB_GEM3_REF_CTRL_OFFSET 
#define CRL_APB_GEM3_REF_CTRL_OFFSET                                               0XFF5E005C
#undef CRL_APB_USB0_BUS_REF_CTRL_OFFSET 
#define CRL_APB_USB0_BUS_REF_CTRL_OFFSET                                           0XFF5E0060
#undef CRL_APB_USB3_DUAL_REF_CTRL_OFFSET 
#define CRL_APB_USB3_DUAL_REF_CTRL_OFFSET                                          0XFF5E004C
#undef CRL_APB_QSPI_REF_CTRL_OFFSET 
#define CRL_APB_QSPI_REF_CTRL_OFFSET                                               0XFF5E0068
#undef CRL_APB_SDIO0_REF_CTRL_OFFSET 
#define CRL_APB_SDIO0_REF_CTRL_OFFSET                                              0XFF5E006C
#undef CRL_APB_SDIO1_REF_CTRL_OFFSET 
#define CRL_APB_SDIO1_REF_CTRL_OFFSET                                              0XFF5E0070
#undef CRL_APB_UART0_REF_CTRL_OFFSET 
#define CRL_APB_UART0_REF_CTRL_OFFSET                                              0XFF5E0074
#undef CRL_APB_UART1_REF_CTRL_OFFSET 
#define CRL_APB_UART1_REF_CTRL_OFFSET                                              0XFF5E0078
#undef CRL_APB_I2C0_REF_CTRL_OFFSET 
#define CRL_APB_I2C0_REF_CTRL_OFFSET                                               0XFF5E0120
#undef CRL_APB_I2C1_REF_CTRL_OFFSET 
#define CRL_APB_I2C1_REF_CTRL_OFFSET                                               0XFF5E0124
#undef CRL_APB_SPI0_REF_CTRL_OFFSET 
#define CRL_APB_SPI0_REF_CTRL_OFFSET                                               0XFF5E007C
#undef CRL_APB_SPI1_REF_CTRL_OFFSET 
#define CRL_APB_SPI1_REF_CTRL_OFFSET                                               0XFF5E0080
#undef CRL_APB_CAN0_REF_CTRL_OFFSET 
#define CRL_APB_CAN0_REF_CTRL_OFFSET                                               0XFF5E0084
#undef CRL_APB_CAN1_REF_CTRL_OFFSET 
#define CRL_APB_CAN1_REF_CTRL_OFFSET                                               0XFF5E0088
#undef CRL_APB_CPU_R5_CTRL_OFFSET 
#define CRL_APB_CPU_R5_CTRL_OFFSET                                                 0XFF5E0090
#undef CRL_APB_IOU_SWITCH_CTRL_OFFSET 
#define CRL_APB_IOU_SWITCH_CTRL_OFFSET                                             0XFF5E009C
#undef CRL_APB_PCAP_CTRL_OFFSET 
#define CRL_APB_PCAP_CTRL_OFFSET                                                   0XFF5E00A4
#undef CRL_APB_LPD_SWITCH_CTRL_OFFSET 
#define CRL_APB_LPD_SWITCH_CTRL_OFFSET                                             0XFF5E00A8
#undef CRL_APB_LPD_LSBUS_CTRL_OFFSET 
#define CRL_APB_LPD_LSBUS_CTRL_OFFSET                                              0XFF5E00AC
#undef CRL_APB_DBG_LPD_CTRL_OFFSET 
#define CRL_APB_DBG_LPD_CTRL_OFFSET                                                0XFF5E00B0
#undef CRL_APB_NAND_REF_CTRL_OFFSET 
#define CRL_APB_NAND_REF_CTRL_OFFSET                                               0XFF5E00B4
#undef CRL_APB_ADMA_REF_CTRL_OFFSET 
#define CRL_APB_ADMA_REF_CTRL_OFFSET                                               0XFF5E00B8
#undef CRL_APB_AMS_REF_CTRL_OFFSET 
#define CRL_APB_AMS_REF_CTRL_OFFSET                                                0XFF5E0108
#undef CRL_APB_DLL_REF_CTRL_OFFSET 
#define CRL_APB_DLL_REF_CTRL_OFFSET                                                0XFF5E0104
#undef CRL_APB_TIMESTAMP_REF_CTRL_OFFSET 
#define CRL_APB_TIMESTAMP_REF_CTRL_OFFSET                                          0XFF5E0128
#undef CRF_APB_PCIE_REF_CTRL_OFFSET 
#define CRF_APB_PCIE_REF_CTRL_OFFSET                                               0XFD1A00B4
#undef CRF_APB_DP_VIDEO_REF_CTRL_OFFSET 
#define CRF_APB_DP_VIDEO_REF_CTRL_OFFSET                                           0XFD1A0070
#undef CRF_APB_DP_AUDIO_REF_CTRL_OFFSET 
#define CRF_APB_DP_AUDIO_REF_CTRL_OFFSET                                           0XFD1A0074
#undef CRF_APB_DP_STC_REF_CTRL_OFFSET 
#define CRF_APB_DP_STC_REF_CTRL_OFFSET                                             0XFD1A007C
#undef CRF_APB_ACPU_CTRL_OFFSET 
#define CRF_APB_ACPU_CTRL_OFFSET                                                   0XFD1A0060
#undef CRF_APB_DBG_TRACE_CTRL_OFFSET 
#define CRF_APB_DBG_TRACE_CTRL_OFFSET                                              0XFD1A0064
#undef CRF_APB_DBG_FPD_CTRL_OFFSET 
#define CRF_APB_DBG_FPD_CTRL_OFFSET                                                0XFD1A0068
#undef CRF_APB_DDR_CTRL_OFFSET 
#define CRF_APB_DDR_CTRL_OFFSET                                                    0XFD1A0080
#undef CRF_APB_GPU_REF_CTRL_OFFSET 
#define CRF_APB_GPU_REF_CTRL_OFFSET                                                0XFD1A0084
#undef CRF_APB_GDMA_REF_CTRL_OFFSET 
#define CRF_APB_GDMA_REF_CTRL_OFFSET                                               0XFD1A00B8
#undef CRF_APB_DPDMA_REF_CTRL_OFFSET 
#define CRF_APB_DPDMA_REF_CTRL_OFFSET                                              0XFD1A00BC
#undef CRF_APB_TOPSW_MAIN_CTRL_OFFSET 
#define CRF_APB_TOPSW_MAIN_CTRL_OFFSET                                             0XFD1A00C0
#undef CRF_APB_TOPSW_LSBUS_CTRL_OFFSET 
#define CRF_APB_TOPSW_LSBUS_CTRL_OFFSET                                            0XFD1A00C4
#undef CRF_APB_GTGREF0_REF_CTRL_OFFSET 
#define CRF_APB_GTGREF0_REF_CTRL_OFFSET                                            0XFD1A00C8
#undef CRF_APB_DBG_TSTMP_CTRL_OFFSET 
#define CRF_APB_DBG_TSTMP_CTRL_OFFSET                                              0XFD1A00F8

/*Clock active for the RX channel*/
#undef CRL_APB_GEM0_REF_CTRL_RX_CLKACT_DEFVAL 
#undef CRL_APB_GEM0_REF_CTRL_RX_CLKACT_SHIFT 
#undef CRL_APB_GEM0_REF_CTRL_RX_CLKACT_MASK 
#define CRL_APB_GEM0_REF_CTRL_RX_CLKACT_DEFVAL                                     0x00002500
#define CRL_APB_GEM0_REF_CTRL_RX_CLKACT_SHIFT                                      26
#define CRL_APB_GEM0_REF_CTRL_RX_CLKACT_MASK                                       0x04000000U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_GEM0_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_GEM0_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_GEM0_REF_CTRL_CLKACT_MASK 
#define CRL_APB_GEM0_REF_CTRL_CLKACT_DEFVAL                                        0x00002500
#define CRL_APB_GEM0_REF_CTRL_CLKACT_SHIFT                                         25
#define CRL_APB_GEM0_REF_CTRL_CLKACT_MASK                                          0x02000000U

/*6 bit divider*/
#undef CRL_APB_GEM0_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_GEM0_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_GEM0_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_GEM0_REF_CTRL_DIVISOR1_DEFVAL                                      0x00002500
#define CRL_APB_GEM0_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_GEM0_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_GEM0_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_GEM0_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_GEM0_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_GEM0_REF_CTRL_DIVISOR0_DEFVAL                                      0x00002500
#define CRL_APB_GEM0_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_GEM0_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_GEM0_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_GEM0_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_GEM0_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_GEM0_REF_CTRL_SRCSEL_DEFVAL                                        0x00002500
#define CRL_APB_GEM0_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_GEM0_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active for the RX channel*/
#undef CRL_APB_GEM1_REF_CTRL_RX_CLKACT_DEFVAL 
#undef CRL_APB_GEM1_REF_CTRL_RX_CLKACT_SHIFT 
#undef CRL_APB_GEM1_REF_CTRL_RX_CLKACT_MASK 
#define CRL_APB_GEM1_REF_CTRL_RX_CLKACT_DEFVAL                                     0x00002500
#define CRL_APB_GEM1_REF_CTRL_RX_CLKACT_SHIFT                                      26
#define CRL_APB_GEM1_REF_CTRL_RX_CLKACT_MASK                                       0x04000000U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_GEM1_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_GEM1_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_GEM1_REF_CTRL_CLKACT_MASK 
#define CRL_APB_GEM1_REF_CTRL_CLKACT_DEFVAL                                        0x00002500
#define CRL_APB_GEM1_REF_CTRL_CLKACT_SHIFT                                         25
#define CRL_APB_GEM1_REF_CTRL_CLKACT_MASK                                          0x02000000U

/*6 bit divider*/
#undef CRL_APB_GEM1_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_GEM1_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_GEM1_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_GEM1_REF_CTRL_DIVISOR1_DEFVAL                                      0x00002500
#define CRL_APB_GEM1_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_GEM1_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_GEM1_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_GEM1_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_GEM1_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_GEM1_REF_CTRL_DIVISOR0_DEFVAL                                      0x00002500
#define CRL_APB_GEM1_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_GEM1_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_GEM1_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_GEM1_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_GEM1_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_GEM1_REF_CTRL_SRCSEL_DEFVAL                                        0x00002500
#define CRL_APB_GEM1_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_GEM1_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active for the RX channel*/
#undef CRL_APB_GEM2_REF_CTRL_RX_CLKACT_DEFVAL 
#undef CRL_APB_GEM2_REF_CTRL_RX_CLKACT_SHIFT 
#undef CRL_APB_GEM2_REF_CTRL_RX_CLKACT_MASK 
#define CRL_APB_GEM2_REF_CTRL_RX_CLKACT_DEFVAL                                     0x00002500
#define CRL_APB_GEM2_REF_CTRL_RX_CLKACT_SHIFT                                      26
#define CRL_APB_GEM2_REF_CTRL_RX_CLKACT_MASK                                       0x04000000U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_GEM2_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_GEM2_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_GEM2_REF_CTRL_CLKACT_MASK 
#define CRL_APB_GEM2_REF_CTRL_CLKACT_DEFVAL                                        0x00002500
#define CRL_APB_GEM2_REF_CTRL_CLKACT_SHIFT                                         25
#define CRL_APB_GEM2_REF_CTRL_CLKACT_MASK                                          0x02000000U

/*6 bit divider*/
#undef CRL_APB_GEM2_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_GEM2_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_GEM2_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_GEM2_REF_CTRL_DIVISOR1_DEFVAL                                      0x00002500
#define CRL_APB_GEM2_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_GEM2_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_GEM2_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_GEM2_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_GEM2_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_GEM2_REF_CTRL_DIVISOR0_DEFVAL                                      0x00002500
#define CRL_APB_GEM2_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_GEM2_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_GEM2_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_GEM2_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_GEM2_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_GEM2_REF_CTRL_SRCSEL_DEFVAL                                        0x00002500
#define CRL_APB_GEM2_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_GEM2_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active for the RX channel*/
#undef CRL_APB_GEM3_REF_CTRL_RX_CLKACT_DEFVAL 
#undef CRL_APB_GEM3_REF_CTRL_RX_CLKACT_SHIFT 
#undef CRL_APB_GEM3_REF_CTRL_RX_CLKACT_MASK 
#define CRL_APB_GEM3_REF_CTRL_RX_CLKACT_DEFVAL                                     0x00002500
#define CRL_APB_GEM3_REF_CTRL_RX_CLKACT_SHIFT                                      26
#define CRL_APB_GEM3_REF_CTRL_RX_CLKACT_MASK                                       0x04000000U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_GEM3_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_GEM3_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_GEM3_REF_CTRL_CLKACT_MASK 
#define CRL_APB_GEM3_REF_CTRL_CLKACT_DEFVAL                                        0x00002500
#define CRL_APB_GEM3_REF_CTRL_CLKACT_SHIFT                                         25
#define CRL_APB_GEM3_REF_CTRL_CLKACT_MASK                                          0x02000000U

/*6 bit divider*/
#undef CRL_APB_GEM3_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_GEM3_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_GEM3_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_GEM3_REF_CTRL_DIVISOR1_DEFVAL                                      0x00002500
#define CRL_APB_GEM3_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_GEM3_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_GEM3_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_GEM3_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_GEM3_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_GEM3_REF_CTRL_DIVISOR0_DEFVAL                                      0x00002500
#define CRL_APB_GEM3_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_GEM3_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_GEM3_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_GEM3_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_GEM3_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_GEM3_REF_CTRL_SRCSEL_DEFVAL                                        0x00002500
#define CRL_APB_GEM3_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_GEM3_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_USB0_BUS_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_USB0_BUS_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_USB0_BUS_REF_CTRL_CLKACT_MASK 
#define CRL_APB_USB0_BUS_REF_CTRL_CLKACT_DEFVAL                                    0x00052000
#define CRL_APB_USB0_BUS_REF_CTRL_CLKACT_SHIFT                                     25
#define CRL_APB_USB0_BUS_REF_CTRL_CLKACT_MASK                                      0x02000000U

/*6 bit divider*/
#undef CRL_APB_USB0_BUS_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_USB0_BUS_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_USB0_BUS_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_USB0_BUS_REF_CTRL_DIVISOR1_DEFVAL                                  0x00052000
#define CRL_APB_USB0_BUS_REF_CTRL_DIVISOR1_SHIFT                                   16
#define CRL_APB_USB0_BUS_REF_CTRL_DIVISOR1_MASK                                    0x003F0000U

/*6 bit divider*/
#undef CRL_APB_USB0_BUS_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_USB0_BUS_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_USB0_BUS_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_USB0_BUS_REF_CTRL_DIVISOR0_DEFVAL                                  0x00052000
#define CRL_APB_USB0_BUS_REF_CTRL_DIVISOR0_SHIFT                                   8
#define CRL_APB_USB0_BUS_REF_CTRL_DIVISOR0_MASK                                    0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_USB0_BUS_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_USB0_BUS_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_USB0_BUS_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_USB0_BUS_REF_CTRL_SRCSEL_DEFVAL                                    0x00052000
#define CRL_APB_USB0_BUS_REF_CTRL_SRCSEL_SHIFT                                     0
#define CRL_APB_USB0_BUS_REF_CTRL_SRCSEL_MASK                                      0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_USB3_DUAL_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_USB3_DUAL_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_USB3_DUAL_REF_CTRL_CLKACT_MASK 
#define CRL_APB_USB3_DUAL_REF_CTRL_CLKACT_DEFVAL                                   0x00052000
#define CRL_APB_USB3_DUAL_REF_CTRL_CLKACT_SHIFT                                    25
#define CRL_APB_USB3_DUAL_REF_CTRL_CLKACT_MASK                                     0x02000000U

/*6 bit divider*/
#undef CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR1_DEFVAL                                 0x00052000
#define CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR1_SHIFT                                  16
#define CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR1_MASK                                   0x003F0000U

/*6 bit divider*/
#undef CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR0_DEFVAL                                 0x00052000
#define CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR0_SHIFT                                  8
#define CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR0_MASK                                   0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL. (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_USB3_DUAL_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_USB3_DUAL_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_USB3_DUAL_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_USB3_DUAL_REF_CTRL_SRCSEL_DEFVAL                                   0x00052000
#define CRL_APB_USB3_DUAL_REF_CTRL_SRCSEL_SHIFT                                    0
#define CRL_APB_USB3_DUAL_REF_CTRL_SRCSEL_MASK                                     0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_QSPI_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_QSPI_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_QSPI_REF_CTRL_CLKACT_MASK 
#define CRL_APB_QSPI_REF_CTRL_CLKACT_DEFVAL                                        0x01000800
#define CRL_APB_QSPI_REF_CTRL_CLKACT_SHIFT                                         24
#define CRL_APB_QSPI_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRL_APB_QSPI_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_QSPI_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_QSPI_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_QSPI_REF_CTRL_DIVISOR1_DEFVAL                                      0x01000800
#define CRL_APB_QSPI_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_QSPI_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_QSPI_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_QSPI_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_QSPI_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_QSPI_REF_CTRL_DIVISOR0_DEFVAL                                      0x01000800
#define CRL_APB_QSPI_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_QSPI_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_QSPI_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_QSPI_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_QSPI_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_QSPI_REF_CTRL_SRCSEL_DEFVAL                                        0x01000800
#define CRL_APB_QSPI_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_QSPI_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_SDIO0_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_SDIO0_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_SDIO0_REF_CTRL_CLKACT_MASK 
#define CRL_APB_SDIO0_REF_CTRL_CLKACT_DEFVAL                                       0x01000F00
#define CRL_APB_SDIO0_REF_CTRL_CLKACT_SHIFT                                        24
#define CRL_APB_SDIO0_REF_CTRL_CLKACT_MASK                                         0x01000000U

/*6 bit divider*/
#undef CRL_APB_SDIO0_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_SDIO0_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_SDIO0_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_SDIO0_REF_CTRL_DIVISOR1_DEFVAL                                     0x01000F00
#define CRL_APB_SDIO0_REF_CTRL_DIVISOR1_SHIFT                                      16
#define CRL_APB_SDIO0_REF_CTRL_DIVISOR1_MASK                                       0x003F0000U

/*6 bit divider*/
#undef CRL_APB_SDIO0_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_SDIO0_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_SDIO0_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_SDIO0_REF_CTRL_DIVISOR0_DEFVAL                                     0x01000F00
#define CRL_APB_SDIO0_REF_CTRL_DIVISOR0_SHIFT                                      8
#define CRL_APB_SDIO0_REF_CTRL_DIVISOR0_MASK                                       0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = VPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_SDIO0_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_SDIO0_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_SDIO0_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_SDIO0_REF_CTRL_SRCSEL_DEFVAL                                       0x01000F00
#define CRL_APB_SDIO0_REF_CTRL_SRCSEL_SHIFT                                        0
#define CRL_APB_SDIO0_REF_CTRL_SRCSEL_MASK                                         0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_SDIO1_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_SDIO1_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_SDIO1_REF_CTRL_CLKACT_MASK 
#define CRL_APB_SDIO1_REF_CTRL_CLKACT_DEFVAL                                       0x01000F00
#define CRL_APB_SDIO1_REF_CTRL_CLKACT_SHIFT                                        24
#define CRL_APB_SDIO1_REF_CTRL_CLKACT_MASK                                         0x01000000U

/*6 bit divider*/
#undef CRL_APB_SDIO1_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_SDIO1_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_SDIO1_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_SDIO1_REF_CTRL_DIVISOR1_DEFVAL                                     0x01000F00
#define CRL_APB_SDIO1_REF_CTRL_DIVISOR1_SHIFT                                      16
#define CRL_APB_SDIO1_REF_CTRL_DIVISOR1_MASK                                       0x003F0000U

/*6 bit divider*/
#undef CRL_APB_SDIO1_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_SDIO1_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_SDIO1_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_SDIO1_REF_CTRL_DIVISOR0_DEFVAL                                     0x01000F00
#define CRL_APB_SDIO1_REF_CTRL_DIVISOR0_SHIFT                                      8
#define CRL_APB_SDIO1_REF_CTRL_DIVISOR0_MASK                                       0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = VPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_SDIO1_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_SDIO1_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_SDIO1_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_SDIO1_REF_CTRL_SRCSEL_DEFVAL                                       0x01000F00
#define CRL_APB_SDIO1_REF_CTRL_SRCSEL_SHIFT                                        0
#define CRL_APB_SDIO1_REF_CTRL_SRCSEL_MASK                                         0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_UART0_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_UART0_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_UART0_REF_CTRL_CLKACT_MASK 
#define CRL_APB_UART0_REF_CTRL_CLKACT_DEFVAL                                       0x01001800
#define CRL_APB_UART0_REF_CTRL_CLKACT_SHIFT                                        24
#define CRL_APB_UART0_REF_CTRL_CLKACT_MASK                                         0x01000000U

/*6 bit divider*/
#undef CRL_APB_UART0_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_UART0_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_UART0_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_UART0_REF_CTRL_DIVISOR1_DEFVAL                                     0x01001800
#define CRL_APB_UART0_REF_CTRL_DIVISOR1_SHIFT                                      16
#define CRL_APB_UART0_REF_CTRL_DIVISOR1_MASK                                       0x003F0000U

/*6 bit divider*/
#undef CRL_APB_UART0_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_UART0_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_UART0_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_UART0_REF_CTRL_DIVISOR0_DEFVAL                                     0x01001800
#define CRL_APB_UART0_REF_CTRL_DIVISOR0_SHIFT                                      8
#define CRL_APB_UART0_REF_CTRL_DIVISOR0_MASK                                       0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_UART0_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_UART0_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_UART0_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_UART0_REF_CTRL_SRCSEL_DEFVAL                                       0x01001800
#define CRL_APB_UART0_REF_CTRL_SRCSEL_SHIFT                                        0
#define CRL_APB_UART0_REF_CTRL_SRCSEL_MASK                                         0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_UART1_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_UART1_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_UART1_REF_CTRL_CLKACT_MASK 
#define CRL_APB_UART1_REF_CTRL_CLKACT_DEFVAL                                       0x01001800
#define CRL_APB_UART1_REF_CTRL_CLKACT_SHIFT                                        24
#define CRL_APB_UART1_REF_CTRL_CLKACT_MASK                                         0x01000000U

/*6 bit divider*/
#undef CRL_APB_UART1_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_UART1_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_UART1_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_UART1_REF_CTRL_DIVISOR1_DEFVAL                                     0x01001800
#define CRL_APB_UART1_REF_CTRL_DIVISOR1_SHIFT                                      16
#define CRL_APB_UART1_REF_CTRL_DIVISOR1_MASK                                       0x003F0000U

/*6 bit divider*/
#undef CRL_APB_UART1_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_UART1_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_UART1_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_UART1_REF_CTRL_DIVISOR0_DEFVAL                                     0x01001800
#define CRL_APB_UART1_REF_CTRL_DIVISOR0_SHIFT                                      8
#define CRL_APB_UART1_REF_CTRL_DIVISOR0_MASK                                       0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_UART1_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_UART1_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_UART1_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_UART1_REF_CTRL_SRCSEL_DEFVAL                                       0x01001800
#define CRL_APB_UART1_REF_CTRL_SRCSEL_SHIFT                                        0
#define CRL_APB_UART1_REF_CTRL_SRCSEL_MASK                                         0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_I2C0_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_I2C0_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_I2C0_REF_CTRL_CLKACT_MASK 
#define CRL_APB_I2C0_REF_CTRL_CLKACT_DEFVAL                                        0x01000500
#define CRL_APB_I2C0_REF_CTRL_CLKACT_SHIFT                                         24
#define CRL_APB_I2C0_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRL_APB_I2C0_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_I2C0_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_I2C0_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_I2C0_REF_CTRL_DIVISOR1_DEFVAL                                      0x01000500
#define CRL_APB_I2C0_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_I2C0_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_I2C0_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_I2C0_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_I2C0_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_I2C0_REF_CTRL_DIVISOR0_DEFVAL                                      0x01000500
#define CRL_APB_I2C0_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_I2C0_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_I2C0_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_I2C0_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_I2C0_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_I2C0_REF_CTRL_SRCSEL_DEFVAL                                        0x01000500
#define CRL_APB_I2C0_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_I2C0_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_I2C1_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_I2C1_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_I2C1_REF_CTRL_CLKACT_MASK 
#define CRL_APB_I2C1_REF_CTRL_CLKACT_DEFVAL                                        0x01000500
#define CRL_APB_I2C1_REF_CTRL_CLKACT_SHIFT                                         24
#define CRL_APB_I2C1_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRL_APB_I2C1_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_I2C1_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_I2C1_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_I2C1_REF_CTRL_DIVISOR1_DEFVAL                                      0x01000500
#define CRL_APB_I2C1_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_I2C1_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_I2C1_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_I2C1_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_I2C1_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_I2C1_REF_CTRL_DIVISOR0_DEFVAL                                      0x01000500
#define CRL_APB_I2C1_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_I2C1_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_I2C1_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_I2C1_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_I2C1_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_I2C1_REF_CTRL_SRCSEL_DEFVAL                                        0x01000500
#define CRL_APB_I2C1_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_I2C1_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_SPI0_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_SPI0_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_SPI0_REF_CTRL_CLKACT_MASK 
#define CRL_APB_SPI0_REF_CTRL_CLKACT_DEFVAL                                        0x01001800
#define CRL_APB_SPI0_REF_CTRL_CLKACT_SHIFT                                         24
#define CRL_APB_SPI0_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRL_APB_SPI0_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_SPI0_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_SPI0_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_SPI0_REF_CTRL_DIVISOR1_DEFVAL                                      0x01001800
#define CRL_APB_SPI0_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_SPI0_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_SPI0_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_SPI0_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_SPI0_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_SPI0_REF_CTRL_DIVISOR0_DEFVAL                                      0x01001800
#define CRL_APB_SPI0_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_SPI0_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_SPI0_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_SPI0_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_SPI0_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_SPI0_REF_CTRL_SRCSEL_DEFVAL                                        0x01001800
#define CRL_APB_SPI0_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_SPI0_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_SPI1_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_SPI1_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_SPI1_REF_CTRL_CLKACT_MASK 
#define CRL_APB_SPI1_REF_CTRL_CLKACT_DEFVAL                                        0x01001800
#define CRL_APB_SPI1_REF_CTRL_CLKACT_SHIFT                                         24
#define CRL_APB_SPI1_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRL_APB_SPI1_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_SPI1_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_SPI1_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_SPI1_REF_CTRL_DIVISOR1_DEFVAL                                      0x01001800
#define CRL_APB_SPI1_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_SPI1_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_SPI1_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_SPI1_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_SPI1_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_SPI1_REF_CTRL_DIVISOR0_DEFVAL                                      0x01001800
#define CRL_APB_SPI1_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_SPI1_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_SPI1_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_SPI1_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_SPI1_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_SPI1_REF_CTRL_SRCSEL_DEFVAL                                        0x01001800
#define CRL_APB_SPI1_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_SPI1_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_CAN0_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_CAN0_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_CAN0_REF_CTRL_CLKACT_MASK 
#define CRL_APB_CAN0_REF_CTRL_CLKACT_DEFVAL                                        0x01001800
#define CRL_APB_CAN0_REF_CTRL_CLKACT_SHIFT                                         24
#define CRL_APB_CAN0_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRL_APB_CAN0_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_CAN0_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_CAN0_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_CAN0_REF_CTRL_DIVISOR1_DEFVAL                                      0x01001800
#define CRL_APB_CAN0_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_CAN0_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_CAN0_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_CAN0_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_CAN0_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_CAN0_REF_CTRL_DIVISOR0_DEFVAL                                      0x01001800
#define CRL_APB_CAN0_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_CAN0_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_CAN0_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_CAN0_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_CAN0_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_CAN0_REF_CTRL_SRCSEL_DEFVAL                                        0x01001800
#define CRL_APB_CAN0_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_CAN0_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_CAN1_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_CAN1_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_CAN1_REF_CTRL_CLKACT_MASK 
#define CRL_APB_CAN1_REF_CTRL_CLKACT_DEFVAL                                        0x01001800
#define CRL_APB_CAN1_REF_CTRL_CLKACT_SHIFT                                         24
#define CRL_APB_CAN1_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRL_APB_CAN1_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_CAN1_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_CAN1_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_CAN1_REF_CTRL_DIVISOR1_DEFVAL                                      0x01001800
#define CRL_APB_CAN1_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_CAN1_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_CAN1_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_CAN1_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_CAN1_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_CAN1_REF_CTRL_DIVISOR0_DEFVAL                                      0x01001800
#define CRL_APB_CAN1_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_CAN1_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_CAN1_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_CAN1_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_CAN1_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_CAN1_REF_CTRL_SRCSEL_DEFVAL                                        0x01001800
#define CRL_APB_CAN1_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_CAN1_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_CPU_R5_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_CPU_R5_CTRL_CLKACT_SHIFT 
#undef CRL_APB_CPU_R5_CTRL_CLKACT_MASK 
#define CRL_APB_CPU_R5_CTRL_CLKACT_DEFVAL                                          0x03000600
#define CRL_APB_CPU_R5_CTRL_CLKACT_SHIFT                                           24
#define CRL_APB_CPU_R5_CTRL_CLKACT_MASK                                            0x01000000U

/*6 bit divider*/
#undef CRL_APB_CPU_R5_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_CPU_R5_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_CPU_R5_CTRL_DIVISOR0_MASK 
#define CRL_APB_CPU_R5_CTRL_DIVISOR0_DEFVAL                                        0x03000600
#define CRL_APB_CPU_R5_CTRL_DIVISOR0_SHIFT                                         8
#define CRL_APB_CPU_R5_CTRL_DIVISOR0_MASK                                          0x00003F00U

/*000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_CPU_R5_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_CPU_R5_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_CPU_R5_CTRL_SRCSEL_MASK 
#define CRL_APB_CPU_R5_CTRL_SRCSEL_DEFVAL                                          0x03000600
#define CRL_APB_CPU_R5_CTRL_SRCSEL_SHIFT                                           0
#define CRL_APB_CPU_R5_CTRL_SRCSEL_MASK                                            0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_IOU_SWITCH_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_IOU_SWITCH_CTRL_CLKACT_SHIFT 
#undef CRL_APB_IOU_SWITCH_CTRL_CLKACT_MASK 
#define CRL_APB_IOU_SWITCH_CTRL_CLKACT_DEFVAL                                      0x00001500
#define CRL_APB_IOU_SWITCH_CTRL_CLKACT_SHIFT                                       24
#define CRL_APB_IOU_SWITCH_CTRL_CLKACT_MASK                                        0x01000000U

/*6 bit divider*/
#undef CRL_APB_IOU_SWITCH_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_IOU_SWITCH_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_IOU_SWITCH_CTRL_DIVISOR0_MASK 
#define CRL_APB_IOU_SWITCH_CTRL_DIVISOR0_DEFVAL                                    0x00001500
#define CRL_APB_IOU_SWITCH_CTRL_DIVISOR0_SHIFT                                     8
#define CRL_APB_IOU_SWITCH_CTRL_DIVISOR0_MASK                                      0x00003F00U

/*000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_IOU_SWITCH_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_IOU_SWITCH_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_IOU_SWITCH_CTRL_SRCSEL_MASK 
#define CRL_APB_IOU_SWITCH_CTRL_SRCSEL_DEFVAL                                      0x00001500
#define CRL_APB_IOU_SWITCH_CTRL_SRCSEL_SHIFT                                       0
#define CRL_APB_IOU_SWITCH_CTRL_SRCSEL_MASK                                        0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_PCAP_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_PCAP_CTRL_CLKACT_SHIFT 
#undef CRL_APB_PCAP_CTRL_CLKACT_MASK 
#define CRL_APB_PCAP_CTRL_CLKACT_DEFVAL                                            0x00001500
#define CRL_APB_PCAP_CTRL_CLKACT_SHIFT                                             24
#define CRL_APB_PCAP_CTRL_CLKACT_MASK                                              0x01000000U

/*6 bit divider*/
#undef CRL_APB_PCAP_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_PCAP_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_PCAP_CTRL_DIVISOR0_MASK 
#define CRL_APB_PCAP_CTRL_DIVISOR0_DEFVAL                                          0x00001500
#define CRL_APB_PCAP_CTRL_DIVISOR0_SHIFT                                           8
#define CRL_APB_PCAP_CTRL_DIVISOR0_MASK                                            0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_PCAP_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_PCAP_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_PCAP_CTRL_SRCSEL_MASK 
#define CRL_APB_PCAP_CTRL_SRCSEL_DEFVAL                                            0x00001500
#define CRL_APB_PCAP_CTRL_SRCSEL_SHIFT                                             0
#define CRL_APB_PCAP_CTRL_SRCSEL_MASK                                              0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_LPD_SWITCH_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_LPD_SWITCH_CTRL_CLKACT_SHIFT 
#undef CRL_APB_LPD_SWITCH_CTRL_CLKACT_MASK 
#define CRL_APB_LPD_SWITCH_CTRL_CLKACT_DEFVAL                                      0x01000500
#define CRL_APB_LPD_SWITCH_CTRL_CLKACT_SHIFT                                       24
#define CRL_APB_LPD_SWITCH_CTRL_CLKACT_MASK                                        0x01000000U

/*6 bit divider*/
#undef CRL_APB_LPD_SWITCH_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_LPD_SWITCH_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_LPD_SWITCH_CTRL_DIVISOR0_MASK 
#define CRL_APB_LPD_SWITCH_CTRL_DIVISOR0_DEFVAL                                    0x01000500
#define CRL_APB_LPD_SWITCH_CTRL_DIVISOR0_SHIFT                                     8
#define CRL_APB_LPD_SWITCH_CTRL_DIVISOR0_MASK                                      0x00003F00U

/*000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_LPD_SWITCH_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_LPD_SWITCH_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_LPD_SWITCH_CTRL_SRCSEL_MASK 
#define CRL_APB_LPD_SWITCH_CTRL_SRCSEL_DEFVAL                                      0x01000500
#define CRL_APB_LPD_SWITCH_CTRL_SRCSEL_SHIFT                                       0
#define CRL_APB_LPD_SWITCH_CTRL_SRCSEL_MASK                                        0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_LPD_LSBUS_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_LPD_LSBUS_CTRL_CLKACT_SHIFT 
#undef CRL_APB_LPD_LSBUS_CTRL_CLKACT_MASK 
#define CRL_APB_LPD_LSBUS_CTRL_CLKACT_DEFVAL                                       0x01001800
#define CRL_APB_LPD_LSBUS_CTRL_CLKACT_SHIFT                                        24
#define CRL_APB_LPD_LSBUS_CTRL_CLKACT_MASK                                         0x01000000U

/*6 bit divider*/
#undef CRL_APB_LPD_LSBUS_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_LPD_LSBUS_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_LPD_LSBUS_CTRL_DIVISOR0_MASK 
#define CRL_APB_LPD_LSBUS_CTRL_DIVISOR0_DEFVAL                                     0x01001800
#define CRL_APB_LPD_LSBUS_CTRL_DIVISOR0_SHIFT                                      8
#define CRL_APB_LPD_LSBUS_CTRL_DIVISOR0_MASK                                       0x00003F00U

/*000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_LPD_LSBUS_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_LPD_LSBUS_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_LPD_LSBUS_CTRL_SRCSEL_MASK 
#define CRL_APB_LPD_LSBUS_CTRL_SRCSEL_DEFVAL                                       0x01001800
#define CRL_APB_LPD_LSBUS_CTRL_SRCSEL_SHIFT                                        0
#define CRL_APB_LPD_LSBUS_CTRL_SRCSEL_MASK                                         0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_DBG_LPD_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_DBG_LPD_CTRL_CLKACT_SHIFT 
#undef CRL_APB_DBG_LPD_CTRL_CLKACT_MASK 
#define CRL_APB_DBG_LPD_CTRL_CLKACT_DEFVAL                                         0x01002000
#define CRL_APB_DBG_LPD_CTRL_CLKACT_SHIFT                                          24
#define CRL_APB_DBG_LPD_CTRL_CLKACT_MASK                                           0x01000000U

/*6 bit divider*/
#undef CRL_APB_DBG_LPD_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_DBG_LPD_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_DBG_LPD_CTRL_DIVISOR0_MASK 
#define CRL_APB_DBG_LPD_CTRL_DIVISOR0_DEFVAL                                       0x01002000
#define CRL_APB_DBG_LPD_CTRL_DIVISOR0_SHIFT                                        8
#define CRL_APB_DBG_LPD_CTRL_DIVISOR0_MASK                                         0x00003F00U

/*000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_DBG_LPD_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_DBG_LPD_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_DBG_LPD_CTRL_SRCSEL_MASK 
#define CRL_APB_DBG_LPD_CTRL_SRCSEL_DEFVAL                                         0x01002000
#define CRL_APB_DBG_LPD_CTRL_SRCSEL_SHIFT                                          0
#define CRL_APB_DBG_LPD_CTRL_SRCSEL_MASK                                           0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_NAND_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_NAND_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_NAND_REF_CTRL_CLKACT_MASK 
#define CRL_APB_NAND_REF_CTRL_CLKACT_DEFVAL                                        0x00052000
#define CRL_APB_NAND_REF_CTRL_CLKACT_SHIFT                                         24
#define CRL_APB_NAND_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRL_APB_NAND_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_NAND_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_NAND_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_NAND_REF_CTRL_DIVISOR1_DEFVAL                                      0x00052000
#define CRL_APB_NAND_REF_CTRL_DIVISOR1_SHIFT                                       16
#define CRL_APB_NAND_REF_CTRL_DIVISOR1_MASK                                        0x003F0000U

/*6 bit divider*/
#undef CRL_APB_NAND_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_NAND_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_NAND_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_NAND_REF_CTRL_DIVISOR0_DEFVAL                                      0x00052000
#define CRL_APB_NAND_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_NAND_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_NAND_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_NAND_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_NAND_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_NAND_REF_CTRL_SRCSEL_DEFVAL                                        0x00052000
#define CRL_APB_NAND_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_NAND_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_ADMA_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_ADMA_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_ADMA_REF_CTRL_CLKACT_MASK 
#define CRL_APB_ADMA_REF_CTRL_CLKACT_DEFVAL                                        0x00002000
#define CRL_APB_ADMA_REF_CTRL_CLKACT_SHIFT                                         24
#define CRL_APB_ADMA_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRL_APB_ADMA_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_ADMA_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_ADMA_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_ADMA_REF_CTRL_DIVISOR0_DEFVAL                                      0x00002000
#define CRL_APB_ADMA_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRL_APB_ADMA_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_ADMA_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_ADMA_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_ADMA_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_ADMA_REF_CTRL_SRCSEL_DEFVAL                                        0x00002000
#define CRL_APB_ADMA_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRL_APB_ADMA_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*6 bit divider*/
#undef CRL_APB_AMS_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRL_APB_AMS_REF_CTRL_DIVISOR1_SHIFT 
#undef CRL_APB_AMS_REF_CTRL_DIVISOR1_MASK 
#define CRL_APB_AMS_REF_CTRL_DIVISOR1_DEFVAL                                       0x01001800
#define CRL_APB_AMS_REF_CTRL_DIVISOR1_SHIFT                                        16
#define CRL_APB_AMS_REF_CTRL_DIVISOR1_MASK                                         0x003F0000U

/*6 bit divider*/
#undef CRL_APB_AMS_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_AMS_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_AMS_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_AMS_REF_CTRL_DIVISOR0_DEFVAL                                       0x01001800
#define CRL_APB_AMS_REF_CTRL_DIVISOR0_SHIFT                                        8
#define CRL_APB_AMS_REF_CTRL_DIVISOR0_MASK                                         0x00003F00U

/*000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_AMS_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_AMS_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_AMS_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_AMS_REF_CTRL_SRCSEL_DEFVAL                                         0x01001800
#define CRL_APB_AMS_REF_CTRL_SRCSEL_SHIFT                                          0
#define CRL_APB_AMS_REF_CTRL_SRCSEL_MASK                                           0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_AMS_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_AMS_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_AMS_REF_CTRL_CLKACT_MASK 
#define CRL_APB_AMS_REF_CTRL_CLKACT_DEFVAL                                         0x01001800
#define CRL_APB_AMS_REF_CTRL_CLKACT_SHIFT                                          24
#define CRL_APB_AMS_REF_CTRL_CLKACT_MASK                                           0x01000000U

/*000 = IOPLL; 001 = RPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new clock. This
		is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_DLL_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_DLL_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_DLL_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_DLL_REF_CTRL_SRCSEL_DEFVAL                                         0x00000000
#define CRL_APB_DLL_REF_CTRL_SRCSEL_SHIFT                                          0
#define CRL_APB_DLL_REF_CTRL_SRCSEL_MASK                                           0x00000007U

/*6 bit divider*/
#undef CRL_APB_TIMESTAMP_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRL_APB_TIMESTAMP_REF_CTRL_DIVISOR0_SHIFT 
#undef CRL_APB_TIMESTAMP_REF_CTRL_DIVISOR0_MASK 
#define CRL_APB_TIMESTAMP_REF_CTRL_DIVISOR0_DEFVAL                                 0x00001800
#define CRL_APB_TIMESTAMP_REF_CTRL_DIVISOR0_SHIFT                                  8
#define CRL_APB_TIMESTAMP_REF_CTRL_DIVISOR0_MASK                                   0x00003F00U

/*1XX = pss_ref_clk; 000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 
		 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRL_APB_TIMESTAMP_REF_CTRL_SRCSEL_DEFVAL 
#undef CRL_APB_TIMESTAMP_REF_CTRL_SRCSEL_SHIFT 
#undef CRL_APB_TIMESTAMP_REF_CTRL_SRCSEL_MASK 
#define CRL_APB_TIMESTAMP_REF_CTRL_SRCSEL_DEFVAL                                   0x00001800
#define CRL_APB_TIMESTAMP_REF_CTRL_SRCSEL_SHIFT                                    0
#define CRL_APB_TIMESTAMP_REF_CTRL_SRCSEL_MASK                                     0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRL_APB_TIMESTAMP_REF_CTRL_CLKACT_DEFVAL 
#undef CRL_APB_TIMESTAMP_REF_CTRL_CLKACT_SHIFT 
#undef CRL_APB_TIMESTAMP_REF_CTRL_CLKACT_MASK 
#define CRL_APB_TIMESTAMP_REF_CTRL_CLKACT_DEFVAL                                   0x00001800
#define CRL_APB_TIMESTAMP_REF_CTRL_CLKACT_SHIFT                                    24
#define CRL_APB_TIMESTAMP_REF_CTRL_CLKACT_MASK                                     0x01000000U

/*000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_PCIE_REF_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_PCIE_REF_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_PCIE_REF_CTRL_SRCSEL_MASK 
#define CRF_APB_PCIE_REF_CTRL_SRCSEL_DEFVAL                                        0x00001500
#define CRF_APB_PCIE_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRF_APB_PCIE_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_PCIE_REF_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_PCIE_REF_CTRL_CLKACT_SHIFT 
#undef CRF_APB_PCIE_REF_CTRL_CLKACT_MASK 
#define CRF_APB_PCIE_REF_CTRL_CLKACT_DEFVAL                                        0x00001500
#define CRF_APB_PCIE_REF_CTRL_CLKACT_SHIFT                                         24
#define CRF_APB_PCIE_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRF_APB_PCIE_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_PCIE_REF_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_PCIE_REF_CTRL_DIVISOR0_MASK 
#define CRF_APB_PCIE_REF_CTRL_DIVISOR0_DEFVAL                                      0x00001500
#define CRF_APB_PCIE_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRF_APB_PCIE_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*6 bit divider*/
#undef CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR1_SHIFT 
#undef CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR1_MASK 
#define CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR1_DEFVAL                                  0x01002300
#define CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR1_SHIFT                                   16
#define CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR1_MASK                                    0x003F0000U

/*6 bit divider*/
#undef CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR0_MASK 
#define CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR0_DEFVAL                                  0x01002300
#define CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR0_SHIFT                                   8
#define CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR0_MASK                                    0x00003F00U

/*000 = VPLL; 010 = DPLL; 011 = RPLL - might be using extra mux; (This signal may only be toggled after 4 cycles of the old clo
		k and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_DP_VIDEO_REF_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_DP_VIDEO_REF_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_DP_VIDEO_REF_CTRL_SRCSEL_MASK 
#define CRF_APB_DP_VIDEO_REF_CTRL_SRCSEL_DEFVAL                                    0x01002300
#define CRF_APB_DP_VIDEO_REF_CTRL_SRCSEL_SHIFT                                     0
#define CRF_APB_DP_VIDEO_REF_CTRL_SRCSEL_MASK                                      0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_DP_VIDEO_REF_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_DP_VIDEO_REF_CTRL_CLKACT_SHIFT 
#undef CRF_APB_DP_VIDEO_REF_CTRL_CLKACT_MASK 
#define CRF_APB_DP_VIDEO_REF_CTRL_CLKACT_DEFVAL                                    0x01002300
#define CRF_APB_DP_VIDEO_REF_CTRL_CLKACT_SHIFT                                     24
#define CRF_APB_DP_VIDEO_REF_CTRL_CLKACT_MASK                                      0x01000000U

/*6 bit divider*/
#undef CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR1_SHIFT 
#undef CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR1_MASK 
#define CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR1_DEFVAL                                  0x01032300
#define CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR1_SHIFT                                   16
#define CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR1_MASK                                    0x003F0000U

/*6 bit divider*/
#undef CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR0_MASK 
#define CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR0_DEFVAL                                  0x01032300
#define CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR0_SHIFT                                   8
#define CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR0_MASK                                    0x00003F00U

/*000 = VPLL; 010 = DPLL; 011 = RPLL - might be using extra mux; (This signal may only be toggled after 4 cycles of the old clo
		k and 4 cycles of the new clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_DP_AUDIO_REF_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_DP_AUDIO_REF_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_DP_AUDIO_REF_CTRL_SRCSEL_MASK 
#define CRF_APB_DP_AUDIO_REF_CTRL_SRCSEL_DEFVAL                                    0x01032300
#define CRF_APB_DP_AUDIO_REF_CTRL_SRCSEL_SHIFT                                     0
#define CRF_APB_DP_AUDIO_REF_CTRL_SRCSEL_MASK                                      0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_DP_AUDIO_REF_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_DP_AUDIO_REF_CTRL_CLKACT_SHIFT 
#undef CRF_APB_DP_AUDIO_REF_CTRL_CLKACT_MASK 
#define CRF_APB_DP_AUDIO_REF_CTRL_CLKACT_DEFVAL                                    0x01032300
#define CRF_APB_DP_AUDIO_REF_CTRL_CLKACT_SHIFT                                     24
#define CRF_APB_DP_AUDIO_REF_CTRL_CLKACT_MASK                                      0x01000000U

/*6 bit divider*/
#undef CRF_APB_DP_STC_REF_CTRL_DIVISOR1_DEFVAL 
#undef CRF_APB_DP_STC_REF_CTRL_DIVISOR1_SHIFT 
#undef CRF_APB_DP_STC_REF_CTRL_DIVISOR1_MASK 
#define CRF_APB_DP_STC_REF_CTRL_DIVISOR1_DEFVAL                                    0x01203200
#define CRF_APB_DP_STC_REF_CTRL_DIVISOR1_SHIFT                                     16
#define CRF_APB_DP_STC_REF_CTRL_DIVISOR1_MASK                                      0x003F0000U

/*6 bit divider*/
#undef CRF_APB_DP_STC_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_DP_STC_REF_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_DP_STC_REF_CTRL_DIVISOR0_MASK 
#define CRF_APB_DP_STC_REF_CTRL_DIVISOR0_DEFVAL                                    0x01203200
#define CRF_APB_DP_STC_REF_CTRL_DIVISOR0_SHIFT                                     8
#define CRF_APB_DP_STC_REF_CTRL_DIVISOR0_MASK                                      0x00003F00U

/*000 = VPLL; 010 = DPLL; 011 = RPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new 
		lock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_DP_STC_REF_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_DP_STC_REF_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_DP_STC_REF_CTRL_SRCSEL_MASK 
#define CRF_APB_DP_STC_REF_CTRL_SRCSEL_DEFVAL                                      0x01203200
#define CRF_APB_DP_STC_REF_CTRL_SRCSEL_SHIFT                                       0
#define CRF_APB_DP_STC_REF_CTRL_SRCSEL_MASK                                        0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_DP_STC_REF_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_DP_STC_REF_CTRL_CLKACT_SHIFT 
#undef CRF_APB_DP_STC_REF_CTRL_CLKACT_MASK 
#define CRF_APB_DP_STC_REF_CTRL_CLKACT_DEFVAL                                      0x01203200
#define CRF_APB_DP_STC_REF_CTRL_CLKACT_SHIFT                                       24
#define CRF_APB_DP_STC_REF_CTRL_CLKACT_MASK                                        0x01000000U

/*6 bit divider*/
#undef CRF_APB_ACPU_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_ACPU_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_ACPU_CTRL_DIVISOR0_MASK 
#define CRF_APB_ACPU_CTRL_DIVISOR0_DEFVAL                                          0x03000400
#define CRF_APB_ACPU_CTRL_DIVISOR0_SHIFT                                           8
#define CRF_APB_ACPU_CTRL_DIVISOR0_MASK                                            0x00003F00U

/*000 = APLL; 010 = DPLL; 011 = VPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new 
		lock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_ACPU_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_ACPU_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_ACPU_CTRL_SRCSEL_MASK 
#define CRF_APB_ACPU_CTRL_SRCSEL_DEFVAL                                            0x03000400
#define CRF_APB_ACPU_CTRL_SRCSEL_SHIFT                                             0
#define CRF_APB_ACPU_CTRL_SRCSEL_MASK                                              0x00000007U

/*Clock active signal. Switch to 0 to disable the clock. For the half speed APU Clock*/
#undef CRF_APB_ACPU_CTRL_CLKACT_HALF_DEFVAL 
#undef CRF_APB_ACPU_CTRL_CLKACT_HALF_SHIFT 
#undef CRF_APB_ACPU_CTRL_CLKACT_HALF_MASK 
#define CRF_APB_ACPU_CTRL_CLKACT_HALF_DEFVAL                                       0x03000400
#define CRF_APB_ACPU_CTRL_CLKACT_HALF_SHIFT                                        25
#define CRF_APB_ACPU_CTRL_CLKACT_HALF_MASK                                         0x02000000U

/*Clock active signal. Switch to 0 to disable the clock. For the full speed ACPUX Clock. This will shut off the high speed cloc
		 to the entire APU*/
#undef CRF_APB_ACPU_CTRL_CLKACT_FULL_DEFVAL 
#undef CRF_APB_ACPU_CTRL_CLKACT_FULL_SHIFT 
#undef CRF_APB_ACPU_CTRL_CLKACT_FULL_MASK 
#define CRF_APB_ACPU_CTRL_CLKACT_FULL_DEFVAL                                       0x03000400
#define CRF_APB_ACPU_CTRL_CLKACT_FULL_SHIFT                                        24
#define CRF_APB_ACPU_CTRL_CLKACT_FULL_MASK                                         0x01000000U

/*6 bit divider*/
#undef CRF_APB_DBG_TRACE_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_DBG_TRACE_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_DBG_TRACE_CTRL_DIVISOR0_MASK 
#define CRF_APB_DBG_TRACE_CTRL_DIVISOR0_DEFVAL                                     0x00002500
#define CRF_APB_DBG_TRACE_CTRL_DIVISOR0_SHIFT                                      8
#define CRF_APB_DBG_TRACE_CTRL_DIVISOR0_MASK                                       0x00003F00U

/*000 = IOPLL; 010 = DPLL; 011 = APLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_DBG_TRACE_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_DBG_TRACE_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_DBG_TRACE_CTRL_SRCSEL_MASK 
#define CRF_APB_DBG_TRACE_CTRL_SRCSEL_DEFVAL                                       0x00002500
#define CRF_APB_DBG_TRACE_CTRL_SRCSEL_SHIFT                                        0
#define CRF_APB_DBG_TRACE_CTRL_SRCSEL_MASK                                         0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_DBG_TRACE_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_DBG_TRACE_CTRL_CLKACT_SHIFT 
#undef CRF_APB_DBG_TRACE_CTRL_CLKACT_MASK 
#define CRF_APB_DBG_TRACE_CTRL_CLKACT_DEFVAL                                       0x00002500
#define CRF_APB_DBG_TRACE_CTRL_CLKACT_SHIFT                                        24
#define CRF_APB_DBG_TRACE_CTRL_CLKACT_MASK                                         0x01000000U

/*6 bit divider*/
#undef CRF_APB_DBG_FPD_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_DBG_FPD_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_DBG_FPD_CTRL_DIVISOR0_MASK 
#define CRF_APB_DBG_FPD_CTRL_DIVISOR0_DEFVAL                                       0x01002500
#define CRF_APB_DBG_FPD_CTRL_DIVISOR0_SHIFT                                        8
#define CRF_APB_DBG_FPD_CTRL_DIVISOR0_MASK                                         0x00003F00U

/*000 = IOPLL; 010 = DPLL; 011 = APLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_DBG_FPD_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_DBG_FPD_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_DBG_FPD_CTRL_SRCSEL_MASK 
#define CRF_APB_DBG_FPD_CTRL_SRCSEL_DEFVAL                                         0x01002500
#define CRF_APB_DBG_FPD_CTRL_SRCSEL_SHIFT                                          0
#define CRF_APB_DBG_FPD_CTRL_SRCSEL_MASK                                           0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_DBG_FPD_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_DBG_FPD_CTRL_CLKACT_SHIFT 
#undef CRF_APB_DBG_FPD_CTRL_CLKACT_MASK 
#define CRF_APB_DBG_FPD_CTRL_CLKACT_DEFVAL                                         0x01002500
#define CRF_APB_DBG_FPD_CTRL_CLKACT_SHIFT                                          24
#define CRF_APB_DBG_FPD_CTRL_CLKACT_MASK                                           0x01000000U

/*6 bit divider*/
#undef CRF_APB_DDR_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_DDR_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_DDR_CTRL_DIVISOR0_MASK 
#define CRF_APB_DDR_CTRL_DIVISOR0_DEFVAL                                           0x01000500
#define CRF_APB_DDR_CTRL_DIVISOR0_SHIFT                                            8
#define CRF_APB_DDR_CTRL_DIVISOR0_MASK                                             0x00003F00U

/*000 = DPLL; 001 = VPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new clock. This 
		s not usually an issue, but designers must be aware.)*/
#undef CRF_APB_DDR_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_DDR_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_DDR_CTRL_SRCSEL_MASK 
#define CRF_APB_DDR_CTRL_SRCSEL_DEFVAL                                             0x01000500
#define CRF_APB_DDR_CTRL_SRCSEL_SHIFT                                              0
#define CRF_APB_DDR_CTRL_SRCSEL_MASK                                               0x00000007U

/*6 bit divider*/
#undef CRF_APB_GPU_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_GPU_REF_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_GPU_REF_CTRL_DIVISOR0_MASK 
#define CRF_APB_GPU_REF_CTRL_DIVISOR0_DEFVAL                                       0x00001500
#define CRF_APB_GPU_REF_CTRL_DIVISOR0_SHIFT                                        8
#define CRF_APB_GPU_REF_CTRL_DIVISOR0_MASK                                         0x00003F00U

/*000 = IOPLL; 010 = VPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_GPU_REF_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_GPU_REF_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_GPU_REF_CTRL_SRCSEL_MASK 
#define CRF_APB_GPU_REF_CTRL_SRCSEL_DEFVAL                                         0x00001500
#define CRF_APB_GPU_REF_CTRL_SRCSEL_SHIFT                                          0
#define CRF_APB_GPU_REF_CTRL_SRCSEL_MASK                                           0x00000007U

/*Clock active signal. Switch to 0 to disable the clock. Will stop clock for both Pixel Processors below*/
#undef CRF_APB_GPU_REF_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_GPU_REF_CTRL_CLKACT_SHIFT 
#undef CRF_APB_GPU_REF_CTRL_CLKACT_MASK 
#define CRF_APB_GPU_REF_CTRL_CLKACT_DEFVAL                                         0x00001500
#define CRF_APB_GPU_REF_CTRL_CLKACT_SHIFT                                          24
#define CRF_APB_GPU_REF_CTRL_CLKACT_MASK                                           0x01000000U

/*Clock active signal for Pixel Processor. Switch to 0 to disable the clock*/
#undef CRF_APB_GPU_REF_CTRL_PP0_CLKACT_DEFVAL 
#undef CRF_APB_GPU_REF_CTRL_PP0_CLKACT_SHIFT 
#undef CRF_APB_GPU_REF_CTRL_PP0_CLKACT_MASK 
#define CRF_APB_GPU_REF_CTRL_PP0_CLKACT_DEFVAL                                     0x00001500
#define CRF_APB_GPU_REF_CTRL_PP0_CLKACT_SHIFT                                      25
#define CRF_APB_GPU_REF_CTRL_PP0_CLKACT_MASK                                       0x02000000U

/*Clock active signal for Pixel Processor. Switch to 0 to disable the clock*/
#undef CRF_APB_GPU_REF_CTRL_PP1_CLKACT_DEFVAL 
#undef CRF_APB_GPU_REF_CTRL_PP1_CLKACT_SHIFT 
#undef CRF_APB_GPU_REF_CTRL_PP1_CLKACT_MASK 
#define CRF_APB_GPU_REF_CTRL_PP1_CLKACT_DEFVAL                                     0x00001500
#define CRF_APB_GPU_REF_CTRL_PP1_CLKACT_SHIFT                                      26
#define CRF_APB_GPU_REF_CTRL_PP1_CLKACT_MASK                                       0x04000000U

/*6 bit divider*/
#undef CRF_APB_GDMA_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_GDMA_REF_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_GDMA_REF_CTRL_DIVISOR0_MASK 
#define CRF_APB_GDMA_REF_CTRL_DIVISOR0_DEFVAL                                      0x01000500
#define CRF_APB_GDMA_REF_CTRL_DIVISOR0_SHIFT                                       8
#define CRF_APB_GDMA_REF_CTRL_DIVISOR0_MASK                                        0x00003F00U

/*000 = APLL; 010 = VPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new 
		lock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_GDMA_REF_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_GDMA_REF_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_GDMA_REF_CTRL_SRCSEL_MASK 
#define CRF_APB_GDMA_REF_CTRL_SRCSEL_DEFVAL                                        0x01000500
#define CRF_APB_GDMA_REF_CTRL_SRCSEL_SHIFT                                         0
#define CRF_APB_GDMA_REF_CTRL_SRCSEL_MASK                                          0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_GDMA_REF_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_GDMA_REF_CTRL_CLKACT_SHIFT 
#undef CRF_APB_GDMA_REF_CTRL_CLKACT_MASK 
#define CRF_APB_GDMA_REF_CTRL_CLKACT_DEFVAL                                        0x01000500
#define CRF_APB_GDMA_REF_CTRL_CLKACT_SHIFT                                         24
#define CRF_APB_GDMA_REF_CTRL_CLKACT_MASK                                          0x01000000U

/*6 bit divider*/
#undef CRF_APB_DPDMA_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_DPDMA_REF_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_DPDMA_REF_CTRL_DIVISOR0_MASK 
#define CRF_APB_DPDMA_REF_CTRL_DIVISOR0_DEFVAL                                     0x01000500
#define CRF_APB_DPDMA_REF_CTRL_DIVISOR0_SHIFT                                      8
#define CRF_APB_DPDMA_REF_CTRL_DIVISOR0_MASK                                       0x00003F00U

/*000 = APLL; 010 = VPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new 
		lock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_DPDMA_REF_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_DPDMA_REF_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_DPDMA_REF_CTRL_SRCSEL_MASK 
#define CRF_APB_DPDMA_REF_CTRL_SRCSEL_DEFVAL                                       0x01000500
#define CRF_APB_DPDMA_REF_CTRL_SRCSEL_SHIFT                                        0
#define CRF_APB_DPDMA_REF_CTRL_SRCSEL_MASK                                         0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_DPDMA_REF_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_DPDMA_REF_CTRL_CLKACT_SHIFT 
#undef CRF_APB_DPDMA_REF_CTRL_CLKACT_MASK 
#define CRF_APB_DPDMA_REF_CTRL_CLKACT_DEFVAL                                       0x01000500
#define CRF_APB_DPDMA_REF_CTRL_CLKACT_SHIFT                                        24
#define CRF_APB_DPDMA_REF_CTRL_CLKACT_MASK                                         0x01000000U

/*6 bit divider*/
#undef CRF_APB_TOPSW_MAIN_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_TOPSW_MAIN_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_TOPSW_MAIN_CTRL_DIVISOR0_MASK 
#define CRF_APB_TOPSW_MAIN_CTRL_DIVISOR0_DEFVAL                                    0x01000400
#define CRF_APB_TOPSW_MAIN_CTRL_DIVISOR0_SHIFT                                     8
#define CRF_APB_TOPSW_MAIN_CTRL_DIVISOR0_MASK                                      0x00003F00U

/*000 = APLL; 010 = VPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new 
		lock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_TOPSW_MAIN_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_TOPSW_MAIN_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_TOPSW_MAIN_CTRL_SRCSEL_MASK 
#define CRF_APB_TOPSW_MAIN_CTRL_SRCSEL_DEFVAL                                      0x01000400
#define CRF_APB_TOPSW_MAIN_CTRL_SRCSEL_SHIFT                                       0
#define CRF_APB_TOPSW_MAIN_CTRL_SRCSEL_MASK                                        0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_TOPSW_MAIN_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_TOPSW_MAIN_CTRL_CLKACT_SHIFT 
#undef CRF_APB_TOPSW_MAIN_CTRL_CLKACT_MASK 
#define CRF_APB_TOPSW_MAIN_CTRL_CLKACT_DEFVAL                                      0x01000400
#define CRF_APB_TOPSW_MAIN_CTRL_CLKACT_SHIFT                                       24
#define CRF_APB_TOPSW_MAIN_CTRL_CLKACT_MASK                                        0x01000000U

/*6 bit divider*/
#undef CRF_APB_TOPSW_LSBUS_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_TOPSW_LSBUS_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_TOPSW_LSBUS_CTRL_DIVISOR0_MASK 
#define CRF_APB_TOPSW_LSBUS_CTRL_DIVISOR0_DEFVAL                                   0x01000800
#define CRF_APB_TOPSW_LSBUS_CTRL_DIVISOR0_SHIFT                                    8
#define CRF_APB_TOPSW_LSBUS_CTRL_DIVISOR0_MASK                                     0x00003F00U

/*000 = APLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_TOPSW_LSBUS_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_TOPSW_LSBUS_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_TOPSW_LSBUS_CTRL_SRCSEL_MASK 
#define CRF_APB_TOPSW_LSBUS_CTRL_SRCSEL_DEFVAL                                     0x01000800
#define CRF_APB_TOPSW_LSBUS_CTRL_SRCSEL_SHIFT                                      0
#define CRF_APB_TOPSW_LSBUS_CTRL_SRCSEL_MASK                                       0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_TOPSW_LSBUS_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_TOPSW_LSBUS_CTRL_CLKACT_SHIFT 
#undef CRF_APB_TOPSW_LSBUS_CTRL_CLKACT_MASK 
#define CRF_APB_TOPSW_LSBUS_CTRL_CLKACT_DEFVAL                                     0x01000800
#define CRF_APB_TOPSW_LSBUS_CTRL_CLKACT_SHIFT                                      24
#define CRF_APB_TOPSW_LSBUS_CTRL_CLKACT_MASK                                       0x01000000U

/*6 bit divider*/
#undef CRF_APB_GTGREF0_REF_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_GTGREF0_REF_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_GTGREF0_REF_CTRL_DIVISOR0_MASK 
#define CRF_APB_GTGREF0_REF_CTRL_DIVISOR0_DEFVAL                                   0x00000800
#define CRF_APB_GTGREF0_REF_CTRL_DIVISOR0_SHIFT                                    8
#define CRF_APB_GTGREF0_REF_CTRL_DIVISOR0_MASK                                     0x00003F00U

/*000 = IOPLL; 010 = APLL; 011 = DPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new
		clock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_GTGREF0_REF_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_GTGREF0_REF_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_GTGREF0_REF_CTRL_SRCSEL_MASK 
#define CRF_APB_GTGREF0_REF_CTRL_SRCSEL_DEFVAL                                     0x00000800
#define CRF_APB_GTGREF0_REF_CTRL_SRCSEL_SHIFT                                      0
#define CRF_APB_GTGREF0_REF_CTRL_SRCSEL_MASK                                       0x00000007U

/*Clock active signal. Switch to 0 to disable the clock*/
#undef CRF_APB_GTGREF0_REF_CTRL_CLKACT_DEFVAL 
#undef CRF_APB_GTGREF0_REF_CTRL_CLKACT_SHIFT 
#undef CRF_APB_GTGREF0_REF_CTRL_CLKACT_MASK 
#define CRF_APB_GTGREF0_REF_CTRL_CLKACT_DEFVAL                                     0x00000800
#define CRF_APB_GTGREF0_REF_CTRL_CLKACT_SHIFT                                      24
#define CRF_APB_GTGREF0_REF_CTRL_CLKACT_MASK                                       0x01000000U

/*6 bit divider*/
#undef CRF_APB_DBG_TSTMP_CTRL_DIVISOR0_DEFVAL 
#undef CRF_APB_DBG_TSTMP_CTRL_DIVISOR0_SHIFT 
#undef CRF_APB_DBG_TSTMP_CTRL_DIVISOR0_MASK 
#define CRF_APB_DBG_TSTMP_CTRL_DIVISOR0_DEFVAL                                     0x00000A00
#define CRF_APB_DBG_TSTMP_CTRL_DIVISOR0_SHIFT                                      8
#define CRF_APB_DBG_TSTMP_CTRL_DIVISOR0_MASK                                       0x00003F00U

/*000 = APLL; 010 = DPLL; 011 = VPLL; (This signal may only be toggled after 4 cycles of the old clock and 4 cycles of the new 
		lock. This is not usually an issue, but designers must be aware.)*/
#undef CRF_APB_DBG_TSTMP_CTRL_SRCSEL_DEFVAL 
#undef CRF_APB_DBG_TSTMP_CTRL_SRCSEL_SHIFT 
#undef CRF_APB_DBG_TSTMP_CTRL_SRCSEL_MASK 
#define CRF_APB_DBG_TSTMP_CTRL_SRCSEL_DEFVAL                                       0x00000A00
#define CRF_APB_DBG_TSTMP_CTRL_SRCSEL_SHIFT                                        0
#define CRF_APB_DBG_TSTMP_CTRL_SRCSEL_MASK                                         0x00000007U
#undef IOU_SLCR_MIO_PIN_0_OFFSET 
#define IOU_SLCR_MIO_PIN_0_OFFSET                                                  0XFF180000
#undef IOU_SLCR_MIO_PIN_1_OFFSET 
#define IOU_SLCR_MIO_PIN_1_OFFSET                                                  0XFF180004
#undef IOU_SLCR_MIO_PIN_2_OFFSET 
#define IOU_SLCR_MIO_PIN_2_OFFSET                                                  0XFF180008
#undef IOU_SLCR_MIO_PIN_3_OFFSET 
#define IOU_SLCR_MIO_PIN_3_OFFSET                                                  0XFF18000C
#undef IOU_SLCR_MIO_PIN_4_OFFSET 
#define IOU_SLCR_MIO_PIN_4_OFFSET                                                  0XFF180010
#undef IOU_SLCR_MIO_PIN_5_OFFSET 
#define IOU_SLCR_MIO_PIN_5_OFFSET                                                  0XFF180014
#undef IOU_SLCR_MIO_PIN_6_OFFSET 
#define IOU_SLCR_MIO_PIN_6_OFFSET                                                  0XFF180018
#undef IOU_SLCR_MIO_PIN_7_OFFSET 
#define IOU_SLCR_MIO_PIN_7_OFFSET                                                  0XFF18001C
#undef IOU_SLCR_MIO_PIN_8_OFFSET 
#define IOU_SLCR_MIO_PIN_8_OFFSET                                                  0XFF180020
#undef IOU_SLCR_MIO_PIN_9_OFFSET 
#define IOU_SLCR_MIO_PIN_9_OFFSET                                                  0XFF180024
#undef IOU_SLCR_MIO_PIN_10_OFFSET 
#define IOU_SLCR_MIO_PIN_10_OFFSET                                                 0XFF180028
#undef IOU_SLCR_MIO_PIN_11_OFFSET 
#define IOU_SLCR_MIO_PIN_11_OFFSET                                                 0XFF18002C
#undef IOU_SLCR_MIO_PIN_12_OFFSET 
#define IOU_SLCR_MIO_PIN_12_OFFSET                                                 0XFF180030
#undef IOU_SLCR_MIO_PIN_13_OFFSET 
#define IOU_SLCR_MIO_PIN_13_OFFSET                                                 0XFF180034
#undef IOU_SLCR_MIO_PIN_14_OFFSET 
#define IOU_SLCR_MIO_PIN_14_OFFSET                                                 0XFF180038
#undef IOU_SLCR_MIO_PIN_15_OFFSET 
#define IOU_SLCR_MIO_PIN_15_OFFSET                                                 0XFF18003C
#undef IOU_SLCR_MIO_PIN_16_OFFSET 
#define IOU_SLCR_MIO_PIN_16_OFFSET                                                 0XFF180040
#undef IOU_SLCR_MIO_PIN_17_OFFSET 
#define IOU_SLCR_MIO_PIN_17_OFFSET                                                 0XFF180044
#undef IOU_SLCR_MIO_PIN_18_OFFSET 
#define IOU_SLCR_MIO_PIN_18_OFFSET                                                 0XFF180048
#undef IOU_SLCR_MIO_PIN_19_OFFSET 
#define IOU_SLCR_MIO_PIN_19_OFFSET                                                 0XFF18004C
#undef IOU_SLCR_MIO_PIN_20_OFFSET 
#define IOU_SLCR_MIO_PIN_20_OFFSET                                                 0XFF180050
#undef IOU_SLCR_MIO_PIN_21_OFFSET 
#define IOU_SLCR_MIO_PIN_21_OFFSET                                                 0XFF180054
#undef IOU_SLCR_MIO_PIN_22_OFFSET 
#define IOU_SLCR_MIO_PIN_22_OFFSET                                                 0XFF180058
#undef IOU_SLCR_MIO_PIN_23_OFFSET 
#define IOU_SLCR_MIO_PIN_23_OFFSET                                                 0XFF18005C
#undef IOU_SLCR_MIO_PIN_24_OFFSET 
#define IOU_SLCR_MIO_PIN_24_OFFSET                                                 0XFF180060
#undef IOU_SLCR_MIO_PIN_25_OFFSET 
#define IOU_SLCR_MIO_PIN_25_OFFSET                                                 0XFF180064
#undef IOU_SLCR_MIO_PIN_26_OFFSET 
#define IOU_SLCR_MIO_PIN_26_OFFSET                                                 0XFF180068
#undef IOU_SLCR_MIO_PIN_27_OFFSET 
#define IOU_SLCR_MIO_PIN_27_OFFSET                                                 0XFF18006C
#undef IOU_SLCR_MIO_PIN_28_OFFSET 
#define IOU_SLCR_MIO_PIN_28_OFFSET                                                 0XFF180070
#undef IOU_SLCR_MIO_PIN_29_OFFSET 
#define IOU_SLCR_MIO_PIN_29_OFFSET                                                 0XFF180074
#undef IOU_SLCR_MIO_PIN_30_OFFSET 
#define IOU_SLCR_MIO_PIN_30_OFFSET                                                 0XFF180078
#undef IOU_SLCR_MIO_PIN_31_OFFSET 
#define IOU_SLCR_MIO_PIN_31_OFFSET                                                 0XFF18007C
#undef IOU_SLCR_MIO_PIN_32_OFFSET 
#define IOU_SLCR_MIO_PIN_32_OFFSET                                                 0XFF180080
#undef IOU_SLCR_MIO_PIN_33_OFFSET 
#define IOU_SLCR_MIO_PIN_33_OFFSET                                                 0XFF180084
#undef IOU_SLCR_MIO_PIN_34_OFFSET 
#define IOU_SLCR_MIO_PIN_34_OFFSET                                                 0XFF180088
#undef IOU_SLCR_MIO_PIN_35_OFFSET 
#define IOU_SLCR_MIO_PIN_35_OFFSET                                                 0XFF18008C
#undef IOU_SLCR_MIO_PIN_36_OFFSET 
#define IOU_SLCR_MIO_PIN_36_OFFSET                                                 0XFF180090
#undef IOU_SLCR_MIO_PIN_37_OFFSET 
#define IOU_SLCR_MIO_PIN_37_OFFSET                                                 0XFF180094
#undef IOU_SLCR_MIO_PIN_38_OFFSET 
#define IOU_SLCR_MIO_PIN_38_OFFSET                                                 0XFF180098
#undef IOU_SLCR_MIO_PIN_39_OFFSET 
#define IOU_SLCR_MIO_PIN_39_OFFSET                                                 0XFF18009C
#undef IOU_SLCR_MIO_PIN_40_OFFSET 
#define IOU_SLCR_MIO_PIN_40_OFFSET                                                 0XFF1800A0
#undef IOU_SLCR_MIO_PIN_41_OFFSET 
#define IOU_SLCR_MIO_PIN_41_OFFSET                                                 0XFF1800A4
#undef IOU_SLCR_MIO_PIN_42_OFFSET 
#define IOU_SLCR_MIO_PIN_42_OFFSET                                                 0XFF1800A8
#undef IOU_SLCR_MIO_PIN_43_OFFSET 
#define IOU_SLCR_MIO_PIN_43_OFFSET                                                 0XFF1800AC
#undef IOU_SLCR_MIO_PIN_44_OFFSET 
#define IOU_SLCR_MIO_PIN_44_OFFSET                                                 0XFF1800B0
#undef IOU_SLCR_MIO_PIN_45_OFFSET 
#define IOU_SLCR_MIO_PIN_45_OFFSET                                                 0XFF1800B4
#undef IOU_SLCR_MIO_PIN_46_OFFSET 
#define IOU_SLCR_MIO_PIN_46_OFFSET                                                 0XFF1800B8
#undef IOU_SLCR_MIO_PIN_47_OFFSET 
#define IOU_SLCR_MIO_PIN_47_OFFSET                                                 0XFF1800BC
#undef IOU_SLCR_MIO_PIN_48_OFFSET 
#define IOU_SLCR_MIO_PIN_48_OFFSET                                                 0XFF1800C0
#undef IOU_SLCR_MIO_PIN_49_OFFSET 
#define IOU_SLCR_MIO_PIN_49_OFFSET                                                 0XFF1800C4
#undef IOU_SLCR_MIO_PIN_50_OFFSET 
#define IOU_SLCR_MIO_PIN_50_OFFSET                                                 0XFF1800C8
#undef IOU_SLCR_MIO_PIN_51_OFFSET 
#define IOU_SLCR_MIO_PIN_51_OFFSET                                                 0XFF1800CC
#undef IOU_SLCR_MIO_PIN_52_OFFSET 
#define IOU_SLCR_MIO_PIN_52_OFFSET                                                 0XFF1800D0
#undef IOU_SLCR_MIO_PIN_53_OFFSET 
#define IOU_SLCR_MIO_PIN_53_OFFSET                                                 0XFF1800D4
#undef IOU_SLCR_MIO_PIN_54_OFFSET 
#define IOU_SLCR_MIO_PIN_54_OFFSET                                                 0XFF1800D8
#undef IOU_SLCR_MIO_PIN_55_OFFSET 
#define IOU_SLCR_MIO_PIN_55_OFFSET                                                 0XFF1800DC
#undef IOU_SLCR_MIO_PIN_56_OFFSET 
#define IOU_SLCR_MIO_PIN_56_OFFSET                                                 0XFF1800E0
#undef IOU_SLCR_MIO_PIN_57_OFFSET 
#define IOU_SLCR_MIO_PIN_57_OFFSET                                                 0XFF1800E4
#undef IOU_SLCR_MIO_PIN_58_OFFSET 
#define IOU_SLCR_MIO_PIN_58_OFFSET                                                 0XFF1800E8
#undef IOU_SLCR_MIO_PIN_59_OFFSET 
#define IOU_SLCR_MIO_PIN_59_OFFSET                                                 0XFF1800EC
#undef IOU_SLCR_MIO_PIN_60_OFFSET 
#define IOU_SLCR_MIO_PIN_60_OFFSET                                                 0XFF1800F0
#undef IOU_SLCR_MIO_PIN_61_OFFSET 
#define IOU_SLCR_MIO_PIN_61_OFFSET                                                 0XFF1800F4
#undef IOU_SLCR_MIO_PIN_62_OFFSET 
#define IOU_SLCR_MIO_PIN_62_OFFSET                                                 0XFF1800F8
#undef IOU_SLCR_MIO_PIN_63_OFFSET 
#define IOU_SLCR_MIO_PIN_63_OFFSET                                                 0XFF1800FC
#undef IOU_SLCR_MIO_PIN_64_OFFSET 
#define IOU_SLCR_MIO_PIN_64_OFFSET                                                 0XFF180100
#undef IOU_SLCR_MIO_PIN_65_OFFSET 
#define IOU_SLCR_MIO_PIN_65_OFFSET                                                 0XFF180104
#undef IOU_SLCR_MIO_PIN_66_OFFSET 
#define IOU_SLCR_MIO_PIN_66_OFFSET                                                 0XFF180108
#undef IOU_SLCR_MIO_PIN_67_OFFSET 
#define IOU_SLCR_MIO_PIN_67_OFFSET                                                 0XFF18010C
#undef IOU_SLCR_MIO_PIN_68_OFFSET 
#define IOU_SLCR_MIO_PIN_68_OFFSET                                                 0XFF180110
#undef IOU_SLCR_MIO_PIN_69_OFFSET 
#define IOU_SLCR_MIO_PIN_69_OFFSET                                                 0XFF180114
#undef IOU_SLCR_MIO_PIN_70_OFFSET 
#define IOU_SLCR_MIO_PIN_70_OFFSET                                                 0XFF180118
#undef IOU_SLCR_MIO_PIN_71_OFFSET 
#define IOU_SLCR_MIO_PIN_71_OFFSET                                                 0XFF18011C
#undef IOU_SLCR_MIO_PIN_72_OFFSET 
#define IOU_SLCR_MIO_PIN_72_OFFSET                                                 0XFF180120
#undef IOU_SLCR_MIO_PIN_73_OFFSET 
#define IOU_SLCR_MIO_PIN_73_OFFSET                                                 0XFF180124
#undef IOU_SLCR_MIO_PIN_74_OFFSET 
#define IOU_SLCR_MIO_PIN_74_OFFSET                                                 0XFF180128
#undef IOU_SLCR_MIO_PIN_75_OFFSET 
#define IOU_SLCR_MIO_PIN_75_OFFSET                                                 0XFF18012C
#undef IOU_SLCR_MIO_PIN_76_OFFSET 
#define IOU_SLCR_MIO_PIN_76_OFFSET                                                 0XFF180130
#undef IOU_SLCR_MIO_PIN_77_OFFSET 
#define IOU_SLCR_MIO_PIN_77_OFFSET                                                 0XFF180134
#undef IOU_SLCR_MIO_MST_TRI0_OFFSET 
#define IOU_SLCR_MIO_MST_TRI0_OFFSET                                               0XFF180204
#undef IOU_SLCR_MIO_MST_TRI1_OFFSET 
#define IOU_SLCR_MIO_MST_TRI1_OFFSET                                               0XFF180208
#undef IOU_SLCR_MIO_MST_TRI2_OFFSET 
#define IOU_SLCR_MIO_MST_TRI2_OFFSET                                               0XFF18020C
#undef IOU_SLCR_MIO_LOOPBACK_OFFSET 
#define IOU_SLCR_MIO_LOOPBACK_OFFSET                                               0XFF180200

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_sclk_out- (QSPI Clock)*/
#undef IOU_SLCR_MIO_PIN_0_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_0_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_0_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_0_L0_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_0_L0_SEL_SHIFT                                            1
#define IOU_SLCR_MIO_PIN_0_L0_SEL_MASK                                             0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_0_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_0_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_0_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_0_L1_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_0_L1_SEL_SHIFT                                            2
#define IOU_SLCR_MIO_PIN_0_L1_SEL_MASK                                             0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[0]- (Test Scan Port) = test_scan, Outp
		t, test_scan_out[0]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_0_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_0_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_0_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_0_L2_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_0_L2_SEL_SHIFT                                            3
#define IOU_SLCR_MIO_PIN_0_L2_SEL_MASK                                             0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[0]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[0]- (GPIO bank 0) 1= can
		, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL signa
		) 3= pjtag, Input, pjtag_tck- (PJTAG TCK) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, spi0_sclk_out- (SPI Cloc
		) 5= ttc3, Input, ttc3_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, Output, trace_
		lk- (Trace Port Clock)*/
#undef IOU_SLCR_MIO_PIN_0_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_0_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_0_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_0_L3_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_0_L3_SEL_SHIFT                                            5
#define IOU_SLCR_MIO_PIN_0_L3_SEL_MASK                                             0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi_mi1- (QSPI Databus) 1= qspi, Output, qspi_so_mo1- (QSPI Data
		us)*/
#undef IOU_SLCR_MIO_PIN_1_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_1_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_1_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_1_L0_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_1_L0_SEL_SHIFT                                            1
#define IOU_SLCR_MIO_PIN_1_L0_SEL_MASK                                             0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_1_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_1_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_1_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_1_L1_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_1_L1_SEL_SHIFT                                            2
#define IOU_SLCR_MIO_PIN_1_L1_SEL_MASK                                             0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[1]- (Test Scan Port) = test_scan, Outp
		t, test_scan_out[1]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_1_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_1_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_1_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_1_L2_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_1_L2_SEL_SHIFT                                            3
#define IOU_SLCR_MIO_PIN_1_L2_SEL_MASK                                             0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[1]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[1]- (GPIO bank 0) 1= can
		, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA signal
		 3= pjtag, Input, pjtag_tdi- (PJTAG TDI) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5= ttc3, Output, ttc3_wave_o
		t- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7= trace, Output, trace_ctl- (Trace Port Control
		Signal)*/
#undef IOU_SLCR_MIO_PIN_1_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_1_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_1_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_1_L3_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_1_L3_SEL_SHIFT                                            5
#define IOU_SLCR_MIO_PIN_1_L3_SEL_MASK                                             0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi2- (QSPI Databus) 1= qspi, Output, qspi_mo2- (QSPI Databus)*/
#undef IOU_SLCR_MIO_PIN_2_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_2_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_2_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_2_L0_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_2_L0_SEL_SHIFT                                            1
#define IOU_SLCR_MIO_PIN_2_L0_SEL_MASK                                             0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_2_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_2_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_2_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_2_L1_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_2_L1_SEL_SHIFT                                            2
#define IOU_SLCR_MIO_PIN_2_L1_SEL_MASK                                             0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[2]- (Test Scan Port) = test_scan, Outp
		t, test_scan_out[2]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_2_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_2_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_2_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_2_L2_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_2_L2_SEL_SHIFT                                            3
#define IOU_SLCR_MIO_PIN_2_L2_SEL_MASK                                             0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[2]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[2]- (GPIO bank 0) 1= can
		, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL signal
		 3= pjtag, Output, pjtag_tdo- (PJTAG TDO) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= ttc2, Input, ttc2_clk_in
		 (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Output, tracedq[0]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_2_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_2_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_2_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_2_L3_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_2_L3_SEL_SHIFT                                            5
#define IOU_SLCR_MIO_PIN_2_L3_SEL_MASK                                             0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi3- (QSPI Databus) 1= qspi, Output, qspi_mo3- (QSPI Databus)*/
#undef IOU_SLCR_MIO_PIN_3_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_3_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_3_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_3_L0_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_3_L0_SEL_SHIFT                                            1
#define IOU_SLCR_MIO_PIN_3_L0_SEL_MASK                                             0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_3_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_3_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_3_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_3_L1_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_3_L1_SEL_SHIFT                                            2
#define IOU_SLCR_MIO_PIN_3_L1_SEL_MASK                                             0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[3]- (Test Scan Port) = test_scan, Outp
		t, test_scan_out[3]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_3_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_3_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_3_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_3_L2_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_3_L2_SEL_SHIFT                                            3
#define IOU_SLCR_MIO_PIN_3_L2_SEL_MASK                                             0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[3]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[3]- (GPIO bank 0) 1= can
		, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA signa
		) 3= pjtag, Input, pjtag_tms- (PJTAG TMS) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi0, Output, spi0_n_ss_out[0
		- (SPI Master Selects) 5= ttc2, Output, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial
		output) 7= trace, Output, tracedq[1]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_3_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_3_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_3_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_3_L3_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_3_L3_SEL_SHIFT                                            5
#define IOU_SLCR_MIO_PIN_3_L3_SEL_MASK                                             0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_mo_mo0- (QSPI Databus) 1= qspi, Input, qspi_si_mi0- (QSPI Data
		us)*/
#undef IOU_SLCR_MIO_PIN_4_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_4_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_4_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_4_L0_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_4_L0_SEL_SHIFT                                            1
#define IOU_SLCR_MIO_PIN_4_L0_SEL_MASK                                             0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_4_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_4_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_4_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_4_L1_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_4_L1_SEL_SHIFT                                            2
#define IOU_SLCR_MIO_PIN_4_L1_SEL_MASK                                             0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[4]- (Test Scan Port) = test_scan, Outp
		t, test_scan_out[4]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_4_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_4_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_4_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_4_L2_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_4_L2_SEL_SHIFT                                            3
#define IOU_SLCR_MIO_PIN_4_L2_SEL_MASK                                             0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[4]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[4]- (GPIO bank 0) 1= can
		, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL signa
		) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= spi0, Output, spi0_s
		- (MISO signal) 5= ttc1, Input, ttc1_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, 
		utput, tracedq[2]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_4_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_4_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_4_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_4_L3_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_4_L3_SEL_SHIFT                                            5
#define IOU_SLCR_MIO_PIN_4_L3_SEL_MASK                                             0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_n_ss_out- (QSPI Slave Select)*/
#undef IOU_SLCR_MIO_PIN_5_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_5_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_5_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_5_L0_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_5_L0_SEL_SHIFT                                            1
#define IOU_SLCR_MIO_PIN_5_L0_SEL_MASK                                             0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_5_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_5_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_5_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_5_L1_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_5_L1_SEL_SHIFT                                            2
#define IOU_SLCR_MIO_PIN_5_L1_SEL_MASK                                             0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[5]- (Test Scan Port) = test_scan, Outp
		t, test_scan_out[5]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_5_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_5_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_5_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_5_L2_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_5_L2_SEL_SHIFT                                            3
#define IOU_SLCR_MIO_PIN_5_L2_SEL_MASK                                             0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[5]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[5]- (GPIO bank 0) 1= can
		, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA signal
		 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4= spi0, Input, spi0
		si- (MOSI signal) 5= ttc1, Output, ttc1_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7
		 trace, Output, tracedq[3]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_5_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_5_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_5_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_5_L3_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_5_L3_SEL_SHIFT                                            5
#define IOU_SLCR_MIO_PIN_5_L3_SEL_MASK                                             0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_clk_for_lpbk- (QSPI Clock to be fed-back)*/
#undef IOU_SLCR_MIO_PIN_6_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_6_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_6_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_6_L0_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_6_L0_SEL_SHIFT                                            1
#define IOU_SLCR_MIO_PIN_6_L0_SEL_MASK                                             0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_6_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_6_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_6_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_6_L1_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_6_L1_SEL_SHIFT                                            2
#define IOU_SLCR_MIO_PIN_6_L1_SEL_MASK                                             0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[6]- (Test Scan Port) = test_scan, Outp
		t, test_scan_out[6]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_6_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_6_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_6_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_6_L2_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_6_L2_SEL_SHIFT                                            3
#define IOU_SLCR_MIO_PIN_6_L2_SEL_MASK                                             0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[6]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[6]- (GPIO bank 0) 1= can
		, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL signal
		 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4= spi1, Output, spi1
		sclk_out- (SPI Clock) 5= ttc0, Input, ttc0_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace,
		Output, tracedq[4]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_6_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_6_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_6_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_6_L3_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_6_L3_SEL_SHIFT                                            5
#define IOU_SLCR_MIO_PIN_6_L3_SEL_MASK                                             0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_n_ss_out_upper- (QSPI Slave Select upper)*/
#undef IOU_SLCR_MIO_PIN_7_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_7_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_7_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_7_L0_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_7_L0_SEL_SHIFT                                            1
#define IOU_SLCR_MIO_PIN_7_L0_SEL_MASK                                             0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_7_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_7_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_7_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_7_L1_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_7_L1_SEL_SHIFT                                            2
#define IOU_SLCR_MIO_PIN_7_L1_SEL_MASK                                             0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[7]- (Test Scan Port) = test_scan, Outp
		t, test_scan_out[7]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_7_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_7_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_7_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_7_L2_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_7_L2_SEL_SHIFT                                            3
#define IOU_SLCR_MIO_PIN_7_L2_SEL_MASK                                             0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[7]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[7]- (GPIO bank 0) 1= can
		, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA signa
		) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_n_ss_out[2]- (SPI Master Selects) 5= 
		tc0, Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial output) 7= trace, Output, 
		racedq[5]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_7_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_7_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_7_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_7_L3_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_7_L3_SEL_SHIFT                                            5
#define IOU_SLCR_MIO_PIN_7_L3_SEL_MASK                                             0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi_upper[0]- (QSPI Upper Databus) 1= qspi, Output, qspi_mo_uppe
		[0]- (QSPI Upper Databus)*/
#undef IOU_SLCR_MIO_PIN_8_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_8_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_8_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_8_L0_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_8_L0_SEL_SHIFT                                            1
#define IOU_SLCR_MIO_PIN_8_L0_SEL_MASK                                             0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_8_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_8_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_8_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_8_L1_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_8_L1_SEL_SHIFT                                            2
#define IOU_SLCR_MIO_PIN_8_L1_SEL_MASK                                             0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[8]- (Test Scan Port) = test_scan, Outp
		t, test_scan_out[8]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_8_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_8_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_8_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_8_L2_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_8_L2_SEL_SHIFT                                            3
#define IOU_SLCR_MIO_PIN_8_L2_SEL_MASK                                             0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[8]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[8]- (GPIO bank 0) 1= can
		, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL signa
		) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Master Selects) 5= ttc
		, Input, ttc3_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, Output, tracedq[6]- (Tr
		ce Port Databus)*/
#undef IOU_SLCR_MIO_PIN_8_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_8_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_8_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_8_L3_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_8_L3_SEL_SHIFT                                            5
#define IOU_SLCR_MIO_PIN_8_L3_SEL_MASK                                             0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi_upper[1]- (QSPI Upper Databus) 1= qspi, Output, qspi_mo_uppe
		[1]- (QSPI Upper Databus)*/
#undef IOU_SLCR_MIO_PIN_9_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_9_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_9_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_9_L0_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_9_L0_SEL_SHIFT                                            1
#define IOU_SLCR_MIO_PIN_9_L0_SEL_MASK                                             0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_ce[1]- (NAND chip enable)*/
#undef IOU_SLCR_MIO_PIN_9_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_9_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_9_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_9_L1_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_9_L1_SEL_SHIFT                                            2
#define IOU_SLCR_MIO_PIN_9_L1_SEL_MASK                                             0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[9]- (Test Scan Port) = test_scan, Outp
		t, test_scan_out[9]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_9_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_9_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_9_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_9_L2_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_9_L2_SEL_SHIFT                                            3
#define IOU_SLCR_MIO_PIN_9_L2_SEL_MASK                                             0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[9]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[9]- (GPIO bank 0) 1= can
		, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA signal
		 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi1, Input, spi1_n_ss_in- (SPI Master Selects) 4= spi1, 
		utput, spi1_n_ss_out[0]- (SPI Master Selects) 5= ttc3, Output, ttc3_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (U
		RT receiver serial input) 7= trace, Output, tracedq[7]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_9_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_9_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_9_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_9_L3_SEL_DEFVAL                                           0x00000000
#define IOU_SLCR_MIO_PIN_9_L3_SEL_SHIFT                                            5
#define IOU_SLCR_MIO_PIN_9_L3_SEL_MASK                                             0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi_upper[2]- (QSPI Upper Databus) 1= qspi, Output, qspi_mo_uppe
		[2]- (QSPI Upper Databus)*/
#undef IOU_SLCR_MIO_PIN_10_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_10_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_10_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_10_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_10_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_10_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_rb_n[0]- (NAND Ready/Busy)*/
#undef IOU_SLCR_MIO_PIN_10_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_10_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_10_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_10_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_10_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_10_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[10]- (Test Scan Port) = test_scan, Out
		ut, test_scan_out[10]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_10_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_10_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_10_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_10_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_10_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_10_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[10]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[10]- (GPIO bank 0) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= spi1, Output, spi1_
		o- (MISO signal) 5= ttc2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Outp
		t, tracedq[8]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_10_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_10_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_10_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_10_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_10_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_10_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi_upper[3]- (QSPI Upper Databus) 1= qspi, Output, qspi_mo_uppe
		[3]- (QSPI Upper Databus)*/
#undef IOU_SLCR_MIO_PIN_11_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_11_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_11_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_11_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_11_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_11_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_rb_n[1]- (NAND Ready/Busy)*/
#undef IOU_SLCR_MIO_PIN_11_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_11_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_11_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_11_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_11_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_11_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[11]- (Test Scan Port) = test_scan, Out
		ut, test_scan_out[11]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_11_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_11_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_11_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_11_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_11_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_11_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[11]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[11]- (GPIO bank 0) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal) 4= spi1, Input, s
		i1_si- (MOSI signal) 5= ttc2, Output, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial o
		tput) 7= trace, Output, tracedq[9]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_11_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_11_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_11_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_11_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_11_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_11_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_sclk_out_upper- (QSPI Upper Clock)*/
#undef IOU_SLCR_MIO_PIN_12_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_12_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_12_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_12_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_12_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_12_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dqs_in- (NAND Strobe) 1= nand, Output, nfc_dqs_out- (NAND Strobe
		*/
#undef IOU_SLCR_MIO_PIN_12_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_12_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_12_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_12_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_12_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_12_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input, test_scan_in[12]- (Test Scan Port) = test_scan, Out
		ut, test_scan_out[12]- (Test Scan Port) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_12_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_12_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_12_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_12_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_12_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_12_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[12]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[12]- (GPIO bank 0) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= pjtag, Input, pjtag_tck- (PJTAG TCK) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, spi0_sclk_out- (SPI Cl
		ck) 5= ttc1, Input, ttc1_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, Output, trac
		dq[10]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_12_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_12_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_12_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_12_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_12_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_12_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_13_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_13_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_13_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_13_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_13_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_13_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_ce[0]- (NAND chip enable)*/
#undef IOU_SLCR_MIO_PIN_13_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_13_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_13_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_13_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_13_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_13_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[0]- (8-bit Data bus) = sd0, Output, sdio0_data_out[0]- (8
		bit Data bus) 2= test_scan, Input, test_scan_in[13]- (Test Scan Port) = test_scan, Output, test_scan_out[13]- (Test Scan Port
		 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_13_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_13_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_13_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_13_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_13_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_13_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[13]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[13]- (GPIO bank 0) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= pjtag, Input, pjtag_tdi- (PJTAG TDI) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5= ttc1, Output, ttc1_wave
		out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7= trace, Output, tracedq[11]- (Trace Port Dat
		bus)*/
#undef IOU_SLCR_MIO_PIN_13_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_13_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_13_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_13_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_13_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_13_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_14_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_14_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_14_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_14_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_14_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_14_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_cle- (NAND Command Latch Enable)*/
#undef IOU_SLCR_MIO_PIN_14_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_14_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_14_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_14_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_14_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_14_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[1]- (8-bit Data bus) = sd0, Output, sdio0_data_out[1]- (8
		bit Data bus) 2= test_scan, Input, test_scan_in[14]- (Test Scan Port) = test_scan, Output, test_scan_out[14]- (Test Scan Port
		 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_14_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_14_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_14_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_14_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_14_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_14_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[14]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[14]- (GPIO bank 0) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= pjtag, Output, pjtag_tdo- (PJTAG TDO) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= ttc0, Input, ttc0_clk_
		n- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Output, tracedq[12]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_14_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_14_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_14_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_14_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_14_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_14_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_15_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_15_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_15_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_15_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_15_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_15_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_ale- (NAND Address Latch Enable)*/
#undef IOU_SLCR_MIO_PIN_15_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_15_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_15_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_15_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_15_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_15_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[2]- (8-bit Data bus) = sd0, Output, sdio0_data_out[2]- (8
		bit Data bus) 2= test_scan, Input, test_scan_in[15]- (Test Scan Port) = test_scan, Output, test_scan_out[15]- (Test Scan Port
		 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_15_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_15_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_15_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_15_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_15_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_15_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[15]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[15]- (GPIO bank 0) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= pjtag, Input, pjtag_tms- (PJTAG TMS) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi0, Output, spi0_n_ss_out
		0]- (SPI Master Selects) 5= ttc0, Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter seri
		l output) 7= trace, Output, tracedq[13]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_15_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_15_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_15_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_15_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_15_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_15_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_16_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_16_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_16_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_16_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_16_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_16_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[0]- (NAND Data Bus) 1= nand, Output, nfc_dq_out[0]- (NAND 
		ata Bus)*/
#undef IOU_SLCR_MIO_PIN_16_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_16_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_16_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_16_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_16_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_16_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[3]- (8-bit Data bus) = sd0, Output, sdio0_data_out[3]- (8
		bit Data bus) 2= test_scan, Input, test_scan_in[16]- (Test Scan Port) = test_scan, Output, test_scan_out[16]- (Test Scan Port
		 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_16_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_16_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_16_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_16_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_16_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_16_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[16]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[16]- (GPIO bank 0) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= spi0, Output, spi0
		so- (MISO signal) 5= ttc3, Input, ttc3_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace
		 Output, tracedq[14]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_16_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_16_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_16_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_16_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_16_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_16_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_17_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_17_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_17_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_17_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_17_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_17_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[1]- (NAND Data Bus) 1= nand, Output, nfc_dq_out[1]- (NAND 
		ata Bus)*/
#undef IOU_SLCR_MIO_PIN_17_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_17_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_17_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_17_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_17_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_17_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[4]- (8-bit Data bus) = sd0, Output, sdio0_data_out[4]- (8
		bit Data bus) 2= test_scan, Input, test_scan_in[17]- (Test Scan Port) = test_scan, Output, test_scan_out[17]- (Test Scan Port
		 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_17_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_17_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_17_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_17_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_17_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_17_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[17]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[17]- (GPIO bank 0) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4= spi0, Input, sp
		0_si- (MOSI signal) 5= ttc3, Output, ttc3_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input)
		7= trace, Output, tracedq[15]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_17_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_17_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_17_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_17_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_17_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_17_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_18_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_18_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_18_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_18_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_18_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_18_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[2]- (NAND Data Bus) 1= nand, Output, nfc_dq_out[2]- (NAND 
		ata Bus)*/
#undef IOU_SLCR_MIO_PIN_18_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_18_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_18_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_18_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_18_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_18_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[5]- (8-bit Data bus) = sd0, Output, sdio0_data_out[5]- (8
		bit Data bus) 2= test_scan, Input, test_scan_in[18]- (Test Scan Port) = test_scan, Output, test_scan_out[18]- (Test Scan Port
		 3= csu, Input, csu_ext_tamper- (CSU Ext Tamper)*/
#undef IOU_SLCR_MIO_PIN_18_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_18_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_18_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_18_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_18_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_18_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[18]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[18]- (GPIO bank 0) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= spi1, Output, spi1_
		o- (MISO signal) 5= ttc2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_18_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_18_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_18_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_18_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_18_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_18_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_19_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_19_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_19_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_19_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_19_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_19_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[3]- (NAND Data Bus) 1= nand, Output, nfc_dq_out[3]- (NAND 
		ata Bus)*/
#undef IOU_SLCR_MIO_PIN_19_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_19_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_19_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_19_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_19_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_19_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[6]- (8-bit Data bus) = sd0, Output, sdio0_data_out[6]- (8
		bit Data bus) 2= test_scan, Input, test_scan_in[19]- (Test Scan Port) = test_scan, Output, test_scan_out[19]- (Test Scan Port
		 3= csu, Input, csu_ext_tamper- (CSU Ext Tamper)*/
#undef IOU_SLCR_MIO_PIN_19_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_19_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_19_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_19_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_19_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_19_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[19]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[19]- (GPIO bank 0) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_n_ss_out[2]- (SPI Master Selects) 5
		 ttc2, Output, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial output) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_19_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_19_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_19_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_19_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_19_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_19_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_20_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_20_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_20_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_20_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_20_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_20_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[4]- (NAND Data Bus) 1= nand, Output, nfc_dq_out[4]- (NAND 
		ata Bus)*/
#undef IOU_SLCR_MIO_PIN_20_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_20_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_20_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_20_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_20_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_20_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[7]- (8-bit Data bus) = sd0, Output, sdio0_data_out[7]- (8
		bit Data bus) 2= test_scan, Input, test_scan_in[20]- (Test Scan Port) = test_scan, Output, test_scan_out[20]- (Test Scan Port
		 3= csu, Input, csu_ext_tamper- (CSU Ext Tamper)*/
#undef IOU_SLCR_MIO_PIN_20_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_20_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_20_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_20_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_20_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_20_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[20]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[20]- (GPIO bank 0) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Master Selects) 5= t
		c1, Input, ttc1_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_20_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_20_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_20_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_20_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_20_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_20_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_21_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_21_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_21_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_21_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_21_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_21_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[5]- (NAND Data Bus) 1= nand, Output, nfc_dq_out[5]- (NAND 
		ata Bus)*/
#undef IOU_SLCR_MIO_PIN_21_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_21_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_21_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_21_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_21_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_21_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_cmd_in- (Command Indicator) = sd0, Output, sdio0_cmd_out- (Comman
		 Indicator) 2= test_scan, Input, test_scan_in[21]- (Test Scan Port) = test_scan, Output, test_scan_out[21]- (Test Scan Port) 
		= csu, Input, csu_ext_tamper- (CSU Ext Tamper)*/
#undef IOU_SLCR_MIO_PIN_21_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_21_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_21_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_21_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_21_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_21_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[21]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[21]- (GPIO bank 0) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi1, Input, spi1_n_ss_in- (SPI Master Selects) 4= spi1
		 Output, spi1_n_ss_out[0]- (SPI Master Selects) 5= ttc1, Output, ttc1_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- 
		UART receiver serial input) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_21_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_21_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_21_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_21_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_21_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_21_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_22_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_22_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_22_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_22_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_22_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_22_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_we_b- (NAND Write Enable)*/
#undef IOU_SLCR_MIO_PIN_22_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_22_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_22_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_22_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_22_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_22_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_clk_out- (SDSDIO clock) 2= test_scan, Input, test_scan_in[22]-
		(Test Scan Port) = test_scan, Output, test_scan_out[22]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU Ext Tamper)*/
#undef IOU_SLCR_MIO_PIN_22_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_22_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_22_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_22_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_22_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_22_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[22]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[22]- (GPIO bank 0) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4= spi1, Output, sp
		1_sclk_out- (SPI Clock) 5= ttc0, Input, ttc0_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= Not 
		sed*/
#undef IOU_SLCR_MIO_PIN_22_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_22_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_22_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_22_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_22_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_22_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_23_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_23_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_23_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_23_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_23_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_23_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[6]- (NAND Data Bus) 1= nand, Output, nfc_dq_out[6]- (NAND 
		ata Bus)*/
#undef IOU_SLCR_MIO_PIN_23_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_23_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_23_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_23_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_23_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_23_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_bus_pow- (SD card bus power) 2= test_scan, Input, test_scan_in
		23]- (Test Scan Port) = test_scan, Output, test_scan_out[23]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU Ext Tamper
		*/
#undef IOU_SLCR_MIO_PIN_23_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_23_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_23_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_23_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_23_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_23_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[23]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[23]- (GPIO bank 0) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal) 4= spi1, Input, s
		i1_si- (MOSI signal) 5= ttc0, Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial o
		tput) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_23_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_23_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_23_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_23_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_23_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_23_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_24_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_24_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_24_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_24_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_24_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_24_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[7]- (NAND Data Bus) 1= nand, Output, nfc_dq_out[7]- (NAND 
		ata Bus)*/
#undef IOU_SLCR_MIO_PIN_24_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_24_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_24_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_24_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_24_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_24_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_cd_n- (SD card detect from connector) 2= test_scan, Input, test
		scan_in[24]- (Test Scan Port) = test_scan, Output, test_scan_out[24]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU Ex
		 Tamper)*/
#undef IOU_SLCR_MIO_PIN_24_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_24_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_24_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_24_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_24_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_24_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[24]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[24]- (GPIO bank 0) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= Not Used 5= ttc3, Input, ttc3_clk_in- (TTC Clock) 6= ua1,
		Output, ua1_txd- (UART transmitter serial output) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_24_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_24_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_24_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_24_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_24_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_24_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_25_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_25_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_25_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_25_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_25_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_25_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_re_n- (NAND Read Enable)*/
#undef IOU_SLCR_MIO_PIN_25_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_25_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_25_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_25_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_25_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_25_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_wp- (SD card write protect from connector) 2= test_scan, Input,
		test_scan_in[25]- (Test Scan Port) = test_scan, Output, test_scan_out[25]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (C
		U Ext Tamper)*/
#undef IOU_SLCR_MIO_PIN_25_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_25_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_25_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_25_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_25_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_25_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[25]- (GPIO bank 0) 0= gpio0, Output, gpio_0_pin_out[25]- (GPIO bank 0) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= Not Used 5= ttc3, Output, ttc3_wave_out- (TTC Waveform 
		lock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_25_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_25_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_25_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_25_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_25_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_25_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_tx_clk- (TX RGMII clock)*/
#undef IOU_SLCR_MIO_PIN_26_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_26_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_26_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_26_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_26_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_26_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_ce[1]- (NAND chip enable)*/
#undef IOU_SLCR_MIO_PIN_26_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_26_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_26_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_26_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_26_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_26_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[0]- (PMU GPI) 2= test_scan, Input, test_scan_in[26]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[26]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU Ext Tamper)*/
#undef IOU_SLCR_MIO_PIN_26_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_26_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_26_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_26_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_26_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_26_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[0]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[0]- (GPIO bank 1) 1= can
		, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL signal
		 3= pjtag, Input, pjtag_tck- (PJTAG TCK) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, spi0_sclk_out- (SPI Clock
		 5= ttc2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Output, tracedq[4]- 
		Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_26_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_26_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_26_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_26_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_26_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_26_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_txd[0]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_27_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_27_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_27_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_27_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_27_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_27_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_rb_n[0]- (NAND Ready/Busy)*/
#undef IOU_SLCR_MIO_PIN_27_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_27_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_27_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_27_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_27_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_27_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[1]- (PMU GPI) 2= test_scan, Input, test_scan_in[27]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[27]- (Test Scan Port) 3= dpaux, Input, dp_aux_data_in- (Dp Aux Data) = dpaux, Outp
		t, dp_aux_data_out- (Dp Aux Data)*/
#undef IOU_SLCR_MIO_PIN_27_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_27_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_27_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_27_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_27_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_27_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[1]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[1]- (GPIO bank 1) 1= can
		, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA signa
		) 3= pjtag, Input, pjtag_tdi- (PJTAG TDI) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5= ttc2, Output, ttc2_wave_
		ut- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial output) 7= trace, Output, tracedq[5]- (Trace Port 
		atabus)*/
#undef IOU_SLCR_MIO_PIN_27_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_27_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_27_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_27_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_27_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_27_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_txd[1]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_28_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_28_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_28_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_28_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_28_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_28_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_rb_n[1]- (NAND Ready/Busy)*/
#undef IOU_SLCR_MIO_PIN_28_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_28_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_28_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_28_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_28_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_28_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[2]- (PMU GPI) 2= test_scan, Input, test_scan_in[28]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[28]- (Test Scan Port) 3= dpaux, Input, dp_hot_plug_detect- (Dp Aux Hot Plug)*/
#undef IOU_SLCR_MIO_PIN_28_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_28_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_28_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_28_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_28_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_28_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[2]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[2]- (GPIO bank 1) 1= can
		, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL signa
		) 3= pjtag, Output, pjtag_tdo- (PJTAG TDO) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= ttc1, Input, ttc1_clk_i
		- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, Output, tracedq[6]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_28_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_28_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_28_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_28_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_28_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_28_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_txd[2]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_29_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_29_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_29_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_29_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_29_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_29_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (PCIE Reset signal)*/
#undef IOU_SLCR_MIO_PIN_29_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_29_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_29_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_29_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_29_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_29_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[3]- (PMU GPI) 2= test_scan, Input, test_scan_in[29]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[29]- (Test Scan Port) 3= dpaux, Input, dp_aux_data_in- (Dp Aux Data) = dpaux, Outp
		t, dp_aux_data_out- (Dp Aux Data)*/
#undef IOU_SLCR_MIO_PIN_29_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_29_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_29_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_29_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_29_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_29_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[3]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[3]- (GPIO bank 1) 1= can
		, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA signal
		 3= pjtag, Input, pjtag_tms- (PJTAG TMS) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi0, Output, spi0_n_ss_out[0]
		 (SPI Master Selects) 5= ttc1, Output, ttc1_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial inpu
		) 7= trace, Output, tracedq[7]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_29_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_29_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_29_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_29_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_29_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_29_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_txd[3]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_30_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_30_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_30_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_30_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_30_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_30_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (PCIE Reset signal)*/
#undef IOU_SLCR_MIO_PIN_30_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_30_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_30_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_30_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_30_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_30_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[4]- (PMU GPI) 2= test_scan, Input, test_scan_in[30]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[30]- (Test Scan Port) 3= dpaux, Input, dp_hot_plug_detect- (Dp Aux Hot Plug)*/
#undef IOU_SLCR_MIO_PIN_30_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_30_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_30_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_30_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_30_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_30_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[4]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[4]- (GPIO bank 1) 1= can
		, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL signal
		 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= spi0, Output, spi0_so
		 (MISO signal) 5= ttc0, Input, ttc0_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Output
		 tracedq[8]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_30_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_30_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_30_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_30_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_30_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_30_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_tx_ctl- (TX RGMII control)*/
#undef IOU_SLCR_MIO_PIN_31_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_31_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_31_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_31_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_31_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_31_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (PCIE Reset signal)*/
#undef IOU_SLCR_MIO_PIN_31_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_31_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_31_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_31_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_31_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_31_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[5]- (PMU GPI) 2= test_scan, Input, test_scan_in[31]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[31]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU Ext Tamper)*/
#undef IOU_SLCR_MIO_PIN_31_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_31_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_31_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_31_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_31_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_31_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[5]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[5]- (GPIO bank 1) 1= can
		, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA signa
		) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4= spi0, Input, spi
		_si- (MOSI signal) 5= ttc0, Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial out
		ut) 7= trace, Output, tracedq[9]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_31_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_31_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_31_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_31_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_31_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_31_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rx_clk- (RX RGMII clock)*/
#undef IOU_SLCR_MIO_PIN_32_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_32_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_32_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_32_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_32_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_32_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dqs_in- (NAND Strobe) 1= nand, Output, nfc_dqs_out- (NAND Strobe
		*/
#undef IOU_SLCR_MIO_PIN_32_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_32_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_32_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_32_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_32_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_32_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpo[0]- (PMU GPI) 2= test_scan, Input, test_scan_in[32]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[32]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU Ext Tamper)*/
#undef IOU_SLCR_MIO_PIN_32_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_32_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_32_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_32_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_32_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_32_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[6]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[6]- (GPIO bank 1) 1= can
		, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL signa
		) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4= spi1, Output, spi
		_sclk_out- (SPI Clock) 5= ttc3, Input, ttc3_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= 
		race, Output, tracedq[10]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_32_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_32_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_32_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_32_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_32_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_32_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rxd[0]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_33_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_33_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_33_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_33_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_33_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_33_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (PCIE Reset signal)*/
#undef IOU_SLCR_MIO_PIN_33_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_33_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_33_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_33_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_33_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_33_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpo[1]- (PMU GPI) 2= test_scan, Input, test_scan_in[33]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[33]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU Ext Tamper)*/
#undef IOU_SLCR_MIO_PIN_33_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_33_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_33_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_33_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_33_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_33_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[7]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[7]- (GPIO bank 1) 1= can
		, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA signal
		 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_n_ss_out[2]- (SPI Master Selects) 5= t
		c3, Output, ttc3_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7= trace, Output, traced
		[11]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_33_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_33_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_33_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_33_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_33_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_33_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rxd[1]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_34_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_34_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_34_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_34_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_34_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_34_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (PCIE Reset signal)*/
#undef IOU_SLCR_MIO_PIN_34_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_34_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_34_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_34_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_34_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_34_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpo[2]- (PMU GPI) 2= test_scan, Input, test_scan_in[34]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[34]- (Test Scan Port) 3= dpaux, Input, dp_aux_data_in- (Dp Aux Data) = dpaux, Outp
		t, dp_aux_data_out- (Dp Aux Data)*/
#undef IOU_SLCR_MIO_PIN_34_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_34_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_34_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_34_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_34_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_34_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[8]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[8]- (GPIO bank 1) 1= can
		, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL signal
		 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Master Selects) 5= ttc2
		 Input, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Output, tracedq[12]- (Trace P
		rt Databus)*/
#undef IOU_SLCR_MIO_PIN_34_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_34_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_34_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_34_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_34_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_34_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rxd[2]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_35_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_35_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_35_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_35_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_35_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_35_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (PCIE Reset signal)*/
#undef IOU_SLCR_MIO_PIN_35_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_35_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_35_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_35_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_35_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_35_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpo[3]- (PMU GPI) 2= test_scan, Input, test_scan_in[35]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[35]- (Test Scan Port) 3= dpaux, Input, dp_hot_plug_detect- (Dp Aux Hot Plug)*/
#undef IOU_SLCR_MIO_PIN_35_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_35_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_35_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_35_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_35_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_35_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[9]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[9]- (GPIO bank 1) 1= can
		, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA signa
		) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi1, Input, spi1_n_ss_in- (SPI Master Selects) 4= spi1,
		Output, spi1_n_ss_out[0]- (SPI Master Selects) 5= ttc2, Output, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- 
		UART transmitter serial output) 7= trace, Output, tracedq[13]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_35_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_35_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_35_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_35_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_35_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_35_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rxd[3]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_36_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_36_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_36_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_36_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_36_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_36_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (PCIE Reset signal)*/
#undef IOU_SLCR_MIO_PIN_36_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_36_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_36_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_36_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_36_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_36_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpo[4]- (PMU GPI) 2= test_scan, Input, test_scan_in[36]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[36]- (Test Scan Port) 3= dpaux, Input, dp_aux_data_in- (Dp Aux Data) = dpaux, Outp
		t, dp_aux_data_out- (Dp Aux Data)*/
#undef IOU_SLCR_MIO_PIN_36_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_36_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_36_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_36_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_36_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_36_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[10]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[10]- (GPIO bank 1) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= spi1, Output, spi1
		so- (MISO signal) 5= ttc1, Input, ttc1_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace
		 Output, tracedq[14]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_36_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_36_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_36_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_36_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_36_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_36_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rx_ctl- (RX RGMII control )*/
#undef IOU_SLCR_MIO_PIN_37_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_37_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_37_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_37_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_37_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_37_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (PCIE Reset signal)*/
#undef IOU_SLCR_MIO_PIN_37_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_37_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_37_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_37_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_37_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_37_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpo[5]- (PMU GPI) 2= test_scan, Input, test_scan_in[37]- (Test Sc
		n Port) = test_scan, Output, test_scan_out[37]- (Test Scan Port) 3= dpaux, Input, dp_hot_plug_detect- (Dp Aux Hot Plug)*/
#undef IOU_SLCR_MIO_PIN_37_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_37_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_37_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_37_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_37_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_37_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[11]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[11]- (GPIO bank 1) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal) 4= spi1, Input, sp
		1_si- (MOSI signal) 5= ttc1, Output, ttc1_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input)
		7= trace, Output, tracedq[15]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_37_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_37_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_37_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_37_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_37_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_37_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_tx_clk- (TX RGMII clock)*/
#undef IOU_SLCR_MIO_PIN_38_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_38_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_38_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_38_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_38_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_38_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_38_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_38_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_38_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_38_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_38_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_38_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_clk_out- (SDSDIO clock) 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_38_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_38_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_38_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_38_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_38_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_38_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[12]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[12]- (GPIO bank 1) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= pjtag, Input, pjtag_tck- (PJTAG TCK) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, spi0_sclk_out- (SPI Clo
		k) 5= ttc0, Input, ttc0_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Output, trace_clk-
		(Trace Port Clock)*/
#undef IOU_SLCR_MIO_PIN_38_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_38_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_38_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_38_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_38_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_38_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_txd[0]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_39_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_39_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_39_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_39_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_39_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_39_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_39_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_39_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_39_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_39_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_39_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_39_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_cd_n- (SD card detect from connector) 2= sd1, Input, sd1_data_i
		[4]- (8-bit Data bus) = sd1, Output, sdio1_data_out[4]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_39_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_39_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_39_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_39_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_39_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_39_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[13]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[13]- (GPIO bank 1) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= pjtag, Input, pjtag_tdi- (PJTAG TDI) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5= ttc0, Output, ttc0_wav
		_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial output) 7= trace, Output, trace_ctl- (Trace Port
		Control Signal)*/
#undef IOU_SLCR_MIO_PIN_39_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_39_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_39_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_39_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_39_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_39_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_txd[1]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_40_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_40_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_40_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_40_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_40_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_40_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_40_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_40_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_40_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_40_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_40_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_40_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_cmd_in- (Command Indicator) = sd0, Output, sdio0_cmd_out- (Comman
		 Indicator) 2= sd1, Input, sd1_data_in[5]- (8-bit Data bus) = sd1, Output, sdio1_data_out[5]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_40_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_40_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_40_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_40_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_40_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_40_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[14]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[14]- (GPIO bank 1) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= pjtag, Output, pjtag_tdo- (PJTAG TDO) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= ttc3, Input, ttc3_clk
		in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, Output, tracedq[0]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_40_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_40_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_40_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_40_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_40_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_40_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_txd[2]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_41_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_41_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_41_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_41_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_41_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_41_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_41_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_41_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_41_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_41_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_41_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_41_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[0]- (8-bit Data bus) = sd0, Output, sdio0_data_out[0]- (8
		bit Data bus) 2= sd1, Input, sd1_data_in[6]- (8-bit Data bus) = sd1, Output, sdio1_data_out[6]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_41_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_41_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_41_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_41_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_41_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_41_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[15]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[15]- (GPIO bank 1) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= pjtag, Input, pjtag_tms- (PJTAG TMS) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi0, Output, spi0_n_ss_out[
		]- (SPI Master Selects) 5= ttc3, Output, ttc3_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial in
		ut) 7= trace, Output, tracedq[1]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_41_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_41_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_41_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_41_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_41_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_41_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_txd[3]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_42_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_42_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_42_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_42_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_42_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_42_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_42_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_42_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_42_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_42_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_42_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_42_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[1]- (8-bit Data bus) = sd0, Output, sdio0_data_out[1]- (8
		bit Data bus) 2= sd1, Input, sd1_data_in[7]- (8-bit Data bus) = sd1, Output, sdio1_data_out[7]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_42_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_42_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_42_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_42_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_42_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_42_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[16]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[16]- (GPIO bank 1) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= spi0, Output, spi0_
		o- (MISO signal) 5= ttc2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Outp
		t, tracedq[2]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_42_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_42_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_42_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_42_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_42_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_42_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_tx_ctl- (TX RGMII control)*/
#undef IOU_SLCR_MIO_PIN_43_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_43_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_43_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_43_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_43_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_43_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_43_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_43_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_43_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_43_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_43_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_43_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[2]- (8-bit Data bus) = sd0, Output, sdio0_data_out[2]- (8
		bit Data bus) 2= sd1, Output, sdio1_bus_pow- (SD card bus power) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_43_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_43_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_43_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_43_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_43_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_43_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[17]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[17]- (GPIO bank 1) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4= spi0, Input, s
		i0_si- (MOSI signal) 5= ttc2, Output, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial o
		tput) 7= trace, Output, tracedq[3]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_43_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_43_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_43_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_43_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_43_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_43_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rx_clk- (RX RGMII clock)*/
#undef IOU_SLCR_MIO_PIN_44_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_44_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_44_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_44_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_44_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_44_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_44_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_44_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_44_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_44_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_44_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_44_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[3]- (8-bit Data bus) = sd0, Output, sdio0_data_out[3]- (8
		bit Data bus) 2= sd1, Input, sdio1_wp- (SD card write protect from connector) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_44_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_44_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_44_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_44_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_44_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_44_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[18]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[18]- (GPIO bank 1) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4= spi1, Output, s
		i1_sclk_out- (SPI Clock) 5= ttc1, Input, ttc1_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7
		 Not Used*/
#undef IOU_SLCR_MIO_PIN_44_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_44_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_44_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_44_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_44_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_44_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rxd[0]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_45_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_45_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_45_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_45_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_45_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_45_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_45_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_45_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_45_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_45_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_45_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_45_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[4]- (8-bit Data bus) = sd0, Output, sdio0_data_out[4]- (8
		bit Data bus) 2= sd1, Input, sdio1_cd_n- (SD card detect from connector) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_45_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_45_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_45_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_45_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_45_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_45_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[19]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[19]- (GPIO bank 1) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_n_ss_out[2]- (SPI Master Selects) 5=
		ttc1, Output, ttc1_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_45_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_45_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_45_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_45_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_45_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_45_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rxd[1]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_46_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_46_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_46_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_46_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_46_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_46_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_46_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_46_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_46_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_46_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_46_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_46_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[5]- (8-bit Data bus) = sd0, Output, sdio0_data_out[5]- (8
		bit Data bus) 2= sd1, Input, sd1_data_in[0]- (8-bit Data bus) = sd1, Output, sdio1_data_out[0]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_46_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_46_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_46_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_46_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_46_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_46_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[20]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[20]- (GPIO bank 1) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Master Selects) 5= tt
		0, Input, ttc0_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_46_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_46_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_46_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_46_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_46_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_46_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rxd[2]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_47_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_47_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_47_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_47_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_47_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_47_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_47_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_47_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_47_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_47_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_47_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_47_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[6]- (8-bit Data bus) = sd0, Output, sdio0_data_out[6]- (8
		bit Data bus) 2= sd1, Input, sd1_data_in[1]- (8-bit Data bus) = sd1, Output, sdio1_data_out[1]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_47_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_47_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_47_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_47_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_47_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_47_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[21]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[21]- (GPIO bank 1) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi1, Input, spi1_n_ss_in- (SPI Master Selects) 4= spi
		, Output, spi1_n_ss_out[0]- (SPI Master Selects) 5= ttc0, Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd
		 (UART transmitter serial output) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_47_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_47_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_47_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_47_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_47_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_47_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rxd[3]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_48_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_48_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_48_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_48_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_48_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_48_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_48_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_48_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_48_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_48_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_48_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_48_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[7]- (8-bit Data bus) = sd0, Output, sdio0_data_out[7]- (8
		bit Data bus) 2= sd1, Input, sd1_data_in[2]- (8-bit Data bus) = sd1, Output, sdio1_data_out[2]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_48_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_48_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_48_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_48_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_48_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_48_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[22]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[22]- (GPIO bank 1) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= spi1, Output, spi1
		so- (MISO signal) 5= ttc3, Input, ttc3_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= Not U
		ed*/
#undef IOU_SLCR_MIO_PIN_48_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_48_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_48_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_48_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_48_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_48_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rx_ctl- (RX RGMII control )*/
#undef IOU_SLCR_MIO_PIN_49_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_49_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_49_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_49_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_49_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_49_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_49_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_49_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_49_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_49_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_49_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_49_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_bus_pow- (SD card bus power) 2= sd1, Input, sd1_data_in[3]- (8
		bit Data bus) = sd1, Output, sdio1_data_out[3]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_49_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_49_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_49_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_49_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_49_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_49_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[23]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[23]- (GPIO bank 1) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal) 4= spi1, Input, sp
		1_si- (MOSI signal) 5= ttc3, Output, ttc3_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input)
		7= Not Used*/
#undef IOU_SLCR_MIO_PIN_49_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_49_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_49_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_49_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_49_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_49_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem_tsu, Input, gem_tsu_clk- (TSU clock)*/
#undef IOU_SLCR_MIO_PIN_50_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_50_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_50_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_50_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_50_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_50_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_50_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_50_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_50_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_50_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_50_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_50_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_wp- (SD card write protect from connector) 2= sd1, Input, sd1_c
		d_in- (Command Indicator) = sd1, Output, sdio1_cmd_out- (Command Indicator) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_50_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_50_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_50_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_50_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_50_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_50_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[24]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[24]- (GPIO bank 1) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= mdio1, Output, gem1_mdc- (MDIO Clock) 5= ttc2, Input, ttc2
		clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_50_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_50_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_50_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_50_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_50_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_50_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem_tsu, Input, gem_tsu_clk- (TSU clock)*/
#undef IOU_SLCR_MIO_PIN_51_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_51_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_51_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_51_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_51_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_51_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_51_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_51_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_51_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_51_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_51_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_51_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= sd1, Output, sdio1_clk_out- (SDSDIO clock) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_51_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_51_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_51_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_51_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_51_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_51_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[25]- (GPIO bank 1) 0= gpio1, Output, gpio_1_pin_out[25]- (GPIO bank 1) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= mdio1, Input, gem1_mdio_in- (MDIO Data) 4= mdio1, Outp
		t, gem1_mdio_out- (MDIO Data) 5= ttc2, Output, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter
		serial output) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_51_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_51_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_51_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_51_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_51_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_51_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_tx_clk- (TX RGMII clock)*/
#undef IOU_SLCR_MIO_PIN_52_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_52_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_52_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_52_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_52_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_52_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_clk_in- (ULPI Clock)*/
#undef IOU_SLCR_MIO_PIN_52_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_52_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_52_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_52_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_52_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_52_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_52_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_52_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_52_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_52_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_52_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_52_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[0]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[0]- (GPIO bank 2) 1= can
		, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL signa
		) 3= pjtag, Input, pjtag_tck- (PJTAG TCK) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, spi0_sclk_out- (SPI Cloc
		) 5= ttc1, Input, ttc1_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, Output, trace_
		lk- (Trace Port Clock)*/
#undef IOU_SLCR_MIO_PIN_52_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_52_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_52_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_52_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_52_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_52_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_txd[0]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_53_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_53_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_53_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_53_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_53_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_53_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_dir- (Data bus direction control)*/
#undef IOU_SLCR_MIO_PIN_53_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_53_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_53_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_53_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_53_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_53_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_53_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_53_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_53_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_53_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_53_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_53_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[1]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[1]- (GPIO bank 2) 1= can
		, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA signal
		 3= pjtag, Input, pjtag_tdi- (PJTAG TDI) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5= ttc1, Output, ttc1_wave_o
		t- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7= trace, Output, trace_ctl- (Trace Port Control
		Signal)*/
#undef IOU_SLCR_MIO_PIN_53_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_53_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_53_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_53_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_53_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_53_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_txd[1]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_54_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_54_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_54_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_54_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_54_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_54_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_data[2]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_
		ata[2]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_54_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_54_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_54_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_54_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_54_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_54_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_54_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_54_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_54_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_54_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_54_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_54_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[2]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[2]- (GPIO bank 2) 1= can
		, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL signal
		 3= pjtag, Output, pjtag_tdo- (PJTAG TDO) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= ttc0, Input, ttc0_clk_in
		 (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Output, tracedq[0]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_54_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_54_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_54_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_54_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_54_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_54_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_txd[2]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_55_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_55_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_55_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_55_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_55_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_55_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_nxt- (Data flow control signal from the PHY)*/
#undef IOU_SLCR_MIO_PIN_55_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_55_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_55_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_55_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_55_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_55_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_55_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_55_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_55_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_55_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_55_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_55_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[3]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[3]- (GPIO bank 2) 1= can
		, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA signa
		) 3= pjtag, Input, pjtag_tms- (PJTAG TMS) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi0, Output, spi0_n_ss_out[0
		- (SPI Master Selects) 5= ttc0, Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial
		output) 7= trace, Output, tracedq[1]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_55_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_55_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_55_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_55_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_55_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_55_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_txd[3]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_56_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_56_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_56_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_56_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_56_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_56_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_data[0]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_
		ata[0]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_56_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_56_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_56_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_56_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_56_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_56_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_56_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_56_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_56_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_56_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_56_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_56_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[4]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[4]- (GPIO bank 2) 1= can
		, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL signa
		) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= spi0, Output, spi0_s
		- (MISO signal) 5= ttc3, Input, ttc3_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, 
		utput, tracedq[2]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_56_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_56_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_56_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_56_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_56_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_56_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_tx_ctl- (TX RGMII control)*/
#undef IOU_SLCR_MIO_PIN_57_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_57_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_57_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_57_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_57_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_57_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_data[1]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_
		ata[1]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_57_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_57_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_57_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_57_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_57_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_57_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_57_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_57_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_57_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_57_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_57_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_57_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[5]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[5]- (GPIO bank 2) 1= can
		, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA signal
		 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4= spi0, Input, spi0
		si- (MOSI signal) 5= ttc3, Output, ttc3_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7
		 trace, Output, tracedq[3]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_57_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_57_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_57_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_57_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_57_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_57_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rx_clk- (RX RGMII clock)*/
#undef IOU_SLCR_MIO_PIN_58_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_58_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_58_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_58_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_58_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_58_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Output, usb0_ulpi_stp- (Asserted to end or interrupt transfers)*/
#undef IOU_SLCR_MIO_PIN_58_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_58_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_58_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_58_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_58_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_58_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_58_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_58_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_58_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_58_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_58_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_58_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[6]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[6]- (GPIO bank 2) 1= can
		, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL signal
		 3= pjtag, Input, pjtag_tck- (PJTAG TCK) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4= spi1, Output, spi1_sclk_out- (SPI Clock
		 5= ttc2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Output, tracedq[4]- 
		Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_58_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_58_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_58_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_58_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_58_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_58_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rxd[0]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_59_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_59_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_59_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_59_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_59_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_59_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_data[3]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_
		ata[3]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_59_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_59_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_59_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_59_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_59_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_59_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_59_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_59_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_59_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_59_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_59_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_59_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[7]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[7]- (GPIO bank 2) 1= can
		, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA signa
		) 3= pjtag, Input, pjtag_tdi- (PJTAG TDI) 4= spi1, Output, spi1_n_ss_out[2]- (SPI Master Selects) 5= ttc2, Output, ttc2_wave_
		ut- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial output) 7= trace, Output, tracedq[5]- (Trace Port 
		atabus)*/
#undef IOU_SLCR_MIO_PIN_59_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_59_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_59_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_59_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_59_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_59_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rxd[1]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_60_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_60_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_60_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_60_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_60_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_60_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_data[4]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_
		ata[4]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_60_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_60_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_60_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_60_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_60_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_60_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_60_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_60_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_60_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_60_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_60_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_60_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[8]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[8]- (GPIO bank 2) 1= can
		, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL signa
		) 3= pjtag, Output, pjtag_tdo- (PJTAG TDO) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Master Selects) 5= ttc1, Input, ttc1_clk_i
		- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, Output, tracedq[6]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_60_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_60_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_60_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_60_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_60_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_60_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rxd[2]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_61_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_61_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_61_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_61_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_61_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_61_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_data[5]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_
		ata[5]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_61_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_61_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_61_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_61_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_61_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_61_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_61_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_61_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_61_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_61_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_61_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_61_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[9]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[9]- (GPIO bank 2) 1= can
		, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA signal
		 3= pjtag, Input, pjtag_tms- (PJTAG TMS) 4= spi1, Input, spi1_n_ss_in- (SPI Master Selects) 4= spi1, Output, spi1_n_ss_out[0]
		 (SPI Master Selects) 5= ttc1, Output, ttc1_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial inpu
		) 7= trace, Output, tracedq[7]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_61_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_61_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_61_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_61_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_61_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_61_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rxd[3]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_62_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_62_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_62_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_62_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_62_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_62_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_data[6]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_
		ata[6]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_62_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_62_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_62_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_62_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_62_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_62_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_62_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_62_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_62_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_62_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_62_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_62_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[10]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[10]- (GPIO bank 2) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= spi1, Output, spi1_
		o- (MISO signal) 5= ttc0, Input, ttc0_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Outp
		t, tracedq[8]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_62_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_62_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_62_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_62_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_62_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_62_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rx_ctl- (RX RGMII control )*/
#undef IOU_SLCR_MIO_PIN_63_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_63_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_63_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_63_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_63_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_63_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_data[7]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_
		ata[7]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_63_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_63_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_63_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_63_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_63_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_63_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_63_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_63_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_63_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_63_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_63_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_63_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[11]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[11]- (GPIO bank 2) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal) 4= spi1, Input, s
		i1_si- (MOSI signal) 5= ttc0, Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial o
		tput) 7= trace, Output, tracedq[9]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_63_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_63_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_63_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_63_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_63_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_63_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_tx_clk- (TX RGMII clock)*/
#undef IOU_SLCR_MIO_PIN_64_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_64_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_64_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_64_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_64_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_64_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_clk_in- (ULPI Clock)*/
#undef IOU_SLCR_MIO_PIN_64_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_64_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_64_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_64_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_64_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_64_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_clk_out- (SDSDIO clock) 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_64_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_64_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_64_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_64_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_64_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_64_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[12]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[12]- (GPIO bank 2) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, s
		i0_sclk_out- (SPI Clock) 5= ttc3, Input, ttc3_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7
		 trace, Output, tracedq[10]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_64_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_64_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_64_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_64_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_64_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_64_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_txd[0]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_65_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_65_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_65_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_65_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_65_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_65_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_dir- (Data bus direction control)*/
#undef IOU_SLCR_MIO_PIN_65_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_65_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_65_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_65_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_65_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_65_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_cd_n- (SD card detect from connector) 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_65_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_65_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_65_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_65_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_65_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_65_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[13]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[13]- (GPIO bank 2) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5=
		ttc3, Output, ttc3_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7= trace, Output, trac
		dq[11]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_65_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_65_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_65_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_65_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_65_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_65_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_txd[1]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_66_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_66_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_66_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_66_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_66_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_66_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_data[2]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_
		ata[2]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_66_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_66_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_66_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_66_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_66_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_66_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_cmd_in- (Command Indicator) = sd0, Output, sdio0_cmd_out- (Comman
		 Indicator) 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_66_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_66_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_66_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_66_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_66_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_66_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[14]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[14]- (GPIO bank 2) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= tt
		2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Output, tracedq[12]- (Trace
		Port Databus)*/
#undef IOU_SLCR_MIO_PIN_66_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_66_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_66_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_66_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_66_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_66_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_txd[2]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_67_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_67_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_67_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_67_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_67_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_67_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_nxt- (Data flow control signal from the PHY)*/
#undef IOU_SLCR_MIO_PIN_67_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_67_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_67_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_67_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_67_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_67_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[0]- (8-bit Data bus) = sd0, Output, sdio0_data_out[0]- (8
		bit Data bus) 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_67_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_67_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_67_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_67_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_67_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_67_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[15]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[15]- (GPIO bank 2) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi
		, Output, spi0_n_ss_out[0]- (SPI Master Selects) 5= ttc2, Output, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd
		 (UART transmitter serial output) 7= trace, Output, tracedq[13]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_67_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_67_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_67_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_67_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_67_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_67_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_txd[3]- (TX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_68_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_68_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_68_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_68_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_68_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_68_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_data[0]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_
		ata[0]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_68_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_68_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_68_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_68_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_68_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_68_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[1]- (8-bit Data bus) = sd0, Output, sdio0_data_out[1]- (8
		bit Data bus) 2= Not Used 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_68_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_68_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_68_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_68_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_68_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_68_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[16]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[16]- (GPIO bank 2) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= spi0, Output, spi0
		so- (MISO signal) 5= ttc1, Input, ttc1_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace
		 Output, tracedq[14]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_68_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_68_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_68_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_68_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_68_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_68_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_tx_ctl- (TX RGMII control)*/
#undef IOU_SLCR_MIO_PIN_69_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_69_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_69_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_69_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_69_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_69_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_data[1]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_
		ata[1]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_69_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_69_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_69_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_69_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_69_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_69_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[2]- (8-bit Data bus) = sd0, Output, sdio0_data_out[2]- (8
		bit Data bus) 2= sd1, Input, sdio1_wp- (SD card write protect from connector) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_69_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_69_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_69_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_69_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_69_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_69_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[17]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[17]- (GPIO bank 2) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4= spi0, Input, sp
		0_si- (MOSI signal) 5= ttc1, Output, ttc1_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input)
		7= trace, Output, tracedq[15]- (Trace Port Databus)*/
#undef IOU_SLCR_MIO_PIN_69_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_69_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_69_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_69_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_69_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_69_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rx_clk- (RX RGMII clock)*/
#undef IOU_SLCR_MIO_PIN_70_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_70_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_70_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_70_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_70_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_70_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Output, usb1_ulpi_stp- (Asserted to end or interrupt transfers)*/
#undef IOU_SLCR_MIO_PIN_70_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_70_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_70_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_70_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_70_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_70_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[3]- (8-bit Data bus) = sd0, Output, sdio0_data_out[3]- (8
		bit Data bus) 2= sd1, Output, sdio1_bus_pow- (SD card bus power) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_70_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_70_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_70_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_70_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_70_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_70_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[18]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[18]- (GPIO bank 2) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4= spi1, Output, sp
		1_sclk_out- (SPI Clock) 5= ttc0, Input, ttc0_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= Not 
		sed*/
#undef IOU_SLCR_MIO_PIN_70_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_70_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_70_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_70_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_70_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_70_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rxd[0]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_71_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_71_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_71_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_71_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_71_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_71_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_data[3]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_
		ata[3]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_71_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_71_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_71_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_71_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_71_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_71_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[4]- (8-bit Data bus) = sd0, Output, sdio0_data_out[4]- (8
		bit Data bus) 2= sd1, Input, sd1_data_in[0]- (8-bit Data bus) = sd1, Output, sdio1_data_out[0]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_71_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_71_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_71_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_71_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_71_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_71_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[19]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[19]- (GPIO bank 2) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_n_ss_out[2]- (SPI Master Selects) 5
		 ttc0, Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial output) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_71_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_71_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_71_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_71_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_71_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_71_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rxd[1]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_72_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_72_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_72_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_72_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_72_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_72_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_data[4]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_
		ata[4]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_72_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_72_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_72_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_72_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_72_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_72_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[5]- (8-bit Data bus) = sd0, Output, sdio0_data_out[5]- (8
		bit Data bus) 2= sd1, Input, sd1_data_in[1]- (8-bit Data bus) = sd1, Output, sdio1_data_out[1]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_72_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_72_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_72_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_72_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_72_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_72_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[20]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[20]- (GPIO bank 2) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= swdt1, Input, swdt1_clk_in- (Watch Dog Timer Input clock) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Master Selects) 5= N
		t Used 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_72_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_72_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_72_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_72_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_72_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_72_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rxd[2]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_73_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_73_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_73_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_73_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_73_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_73_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_data[5]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_
		ata[5]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_73_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_73_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_73_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_73_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_73_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_73_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[6]- (8-bit Data bus) = sd0, Output, sdio0_data_out[6]- (8
		bit Data bus) 2= sd1, Input, sd1_data_in[2]- (8-bit Data bus) = sd1, Output, sdio1_data_out[2]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_73_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_73_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_73_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_73_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_73_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_73_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[21]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[21]- (GPIO bank 2) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= swdt1, Output, swdt1_rst_out- (Watch Dog Timer Output clock) 4= spi1, Input, spi1_n_ss_in- (SPI Master Selects) 4= spi1
		 Output, spi1_n_ss_out[0]- (SPI Master Selects) 5= Not Used 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_73_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_73_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_73_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_73_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_73_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_73_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rxd[3]- (RX RGMII data)*/
#undef IOU_SLCR_MIO_PIN_74_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_74_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_74_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_74_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_74_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_74_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_data[6]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_
		ata[6]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_74_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_74_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_74_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_74_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_74_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_74_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[7]- (8-bit Data bus) = sd0, Output, sdio0_data_out[7]- (8
		bit Data bus) 2= sd1, Input, sd1_data_in[3]- (8-bit Data bus) = sd1, Output, sdio1_data_out[3]- (8-bit Data bus) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_74_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_74_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_74_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_74_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_74_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_74_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[22]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[22]- (GPIO bank 2) 1= c
		n0, Input, can0_phy_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0, Output, i2c0_scl_out- (SCL sign
		l) 3= swdt0, Input, swdt0_clk_in- (Watch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= spi1, Output, spi1_
		o- (MISO signal) 5= Not Used 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_74_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_74_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_74_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_74_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_74_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_74_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rx_ctl- (RX RGMII control )*/
#undef IOU_SLCR_MIO_PIN_75_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_75_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_75_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_75_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_75_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_75_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_data[7]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_
		ata[7]- (ULPI data bus)*/
#undef IOU_SLCR_MIO_PIN_75_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_75_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_75_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_75_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_75_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_75_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_bus_pow- (SD card bus power) 2= sd1, Input, sd1_cmd_in- (Comma
		d Indicator) = sd1, Output, sdio1_cmd_out- (Command Indicator) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_75_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_75_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_75_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_75_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_75_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_75_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[23]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[23]- (GPIO bank 2) 1= c
		n0, Output, can0_phy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c0, Output, i2c0_sda_out- (SDA sig
		al) 3= swdt0, Output, swdt0_rst_out- (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal) 4= spi1, Input, s
		i1_si- (MOSI signal) 5= Not Used 6= ua0, Output, ua0_txd- (UART transmitter serial output) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_75_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_75_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_75_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_75_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_75_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_75_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_76_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_76_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_76_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_76_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_76_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_76_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_76_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_76_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_76_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_76_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_76_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_76_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_wp- (SD card write protect from connector) 2= sd1, Output, sdio
		_clk_out- (SDSDIO clock) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_76_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_76_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_76_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_76_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_76_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_76_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[24]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[24]- (GPIO bank 2) 1= c
		n1, Output, can1_phy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c1, Output, i2c1_scl_out- (SCL sig
		al) 3= mdio0, Output, gem0_mdc- (MDIO Clock) 4= mdio1, Output, gem1_mdc- (MDIO Clock) 5= mdio2, Output, gem2_mdc- (MDIO Clock
		 6= mdio3, Output, gem3_mdc- (MDIO Clock) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_76_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_76_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_76_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_76_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_76_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_76_L3_SEL_MASK                                            0x000000E0U

/*Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_77_L0_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_77_L0_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_77_L0_SEL_MASK 
#define IOU_SLCR_MIO_PIN_77_L0_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_77_L0_SEL_SHIFT                                           1
#define IOU_SLCR_MIO_PIN_77_L0_SEL_MASK                                            0x00000002U

/*Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used*/
#undef IOU_SLCR_MIO_PIN_77_L1_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_77_L1_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_77_L1_SEL_MASK 
#define IOU_SLCR_MIO_PIN_77_L1_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_77_L1_SEL_SHIFT                                           2
#define IOU_SLCR_MIO_PIN_77_L1_SEL_MASK                                            0x00000004U

/*Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= sd1, Input, sdio1_cd_n- (SD card detect from connector) 3= Not Used*/
#undef IOU_SLCR_MIO_PIN_77_L2_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_77_L2_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_77_L2_SEL_MASK 
#define IOU_SLCR_MIO_PIN_77_L2_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_77_L2_SEL_SHIFT                                           3
#define IOU_SLCR_MIO_PIN_77_L2_SEL_MASK                                            0x00000018U

/*Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[25]- (GPIO bank 2) 0= gpio2, Output, gpio_2_pin_out[25]- (GPIO bank 2) 1= c
		n1, Input, can1_phy_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1, Output, i2c1_sda_out- (SDA sign
		l) 3= mdio0, Input, gem0_mdio_in- (MDIO Data) 3= mdio0, Output, gem0_mdio_out- (MDIO Data) 4= mdio1, Input, gem1_mdio_in- (MD
		O Data) 4= mdio1, Output, gem1_mdio_out- (MDIO Data) 5= mdio2, Input, gem2_mdio_in- (MDIO Data) 5= mdio2, Output, gem2_mdio_o
		t- (MDIO Data) 6= mdio3, Input, gem3_mdio_in- (MDIO Data) 6= mdio3, Output, gem3_mdio_out- (MDIO Data) 7= Not Used*/
#undef IOU_SLCR_MIO_PIN_77_L3_SEL_DEFVAL 
#undef IOU_SLCR_MIO_PIN_77_L3_SEL_SHIFT 
#undef IOU_SLCR_MIO_PIN_77_L3_SEL_MASK 
#define IOU_SLCR_MIO_PIN_77_L3_SEL_DEFVAL                                          0x00000000
#define IOU_SLCR_MIO_PIN_77_L3_SEL_SHIFT                                           5
#define IOU_SLCR_MIO_PIN_77_L3_SEL_MASK                                            0x000000E0U

/*Master Tri-state Enable for pin 0, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_00_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_00_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_00_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_00_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_00_TRI_SHIFT                                     0
#define IOU_SLCR_MIO_MST_TRI0_PIN_00_TRI_MASK                                      0x00000001U

/*Master Tri-state Enable for pin 1, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_01_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_01_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_01_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_01_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_01_TRI_SHIFT                                     1
#define IOU_SLCR_MIO_MST_TRI0_PIN_01_TRI_MASK                                      0x00000002U

/*Master Tri-state Enable for pin 2, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_02_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_02_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_02_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_02_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_02_TRI_SHIFT                                     2
#define IOU_SLCR_MIO_MST_TRI0_PIN_02_TRI_MASK                                      0x00000004U

/*Master Tri-state Enable for pin 3, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_03_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_03_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_03_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_03_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_03_TRI_SHIFT                                     3
#define IOU_SLCR_MIO_MST_TRI0_PIN_03_TRI_MASK                                      0x00000008U

/*Master Tri-state Enable for pin 4, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_04_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_04_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_04_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_04_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_04_TRI_SHIFT                                     4
#define IOU_SLCR_MIO_MST_TRI0_PIN_04_TRI_MASK                                      0x00000010U

/*Master Tri-state Enable for pin 5, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_05_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_05_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_05_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_05_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_05_TRI_SHIFT                                     5
#define IOU_SLCR_MIO_MST_TRI0_PIN_05_TRI_MASK                                      0x00000020U

/*Master Tri-state Enable for pin 6, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_06_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_06_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_06_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_06_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_06_TRI_SHIFT                                     6
#define IOU_SLCR_MIO_MST_TRI0_PIN_06_TRI_MASK                                      0x00000040U

/*Master Tri-state Enable for pin 7, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_07_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_07_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_07_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_07_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_07_TRI_SHIFT                                     7
#define IOU_SLCR_MIO_MST_TRI0_PIN_07_TRI_MASK                                      0x00000080U

/*Master Tri-state Enable for pin 8, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_08_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_08_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_08_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_08_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_08_TRI_SHIFT                                     8
#define IOU_SLCR_MIO_MST_TRI0_PIN_08_TRI_MASK                                      0x00000100U

/*Master Tri-state Enable for pin 9, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_09_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_09_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_09_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_09_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_09_TRI_SHIFT                                     9
#define IOU_SLCR_MIO_MST_TRI0_PIN_09_TRI_MASK                                      0x00000200U

/*Master Tri-state Enable for pin 10, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_10_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_10_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_10_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_10_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_10_TRI_SHIFT                                     10
#define IOU_SLCR_MIO_MST_TRI0_PIN_10_TRI_MASK                                      0x00000400U

/*Master Tri-state Enable for pin 11, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_11_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_11_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_11_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_11_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_11_TRI_SHIFT                                     11
#define IOU_SLCR_MIO_MST_TRI0_PIN_11_TRI_MASK                                      0x00000800U

/*Master Tri-state Enable for pin 12, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_12_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_12_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_12_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_12_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_12_TRI_SHIFT                                     12
#define IOU_SLCR_MIO_MST_TRI0_PIN_12_TRI_MASK                                      0x00001000U

/*Master Tri-state Enable for pin 13, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_13_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_13_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_13_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_13_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_13_TRI_SHIFT                                     13
#define IOU_SLCR_MIO_MST_TRI0_PIN_13_TRI_MASK                                      0x00002000U

/*Master Tri-state Enable for pin 14, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_14_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_14_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_14_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_14_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_14_TRI_SHIFT                                     14
#define IOU_SLCR_MIO_MST_TRI0_PIN_14_TRI_MASK                                      0x00004000U

/*Master Tri-state Enable for pin 15, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_15_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_15_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_15_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_15_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_15_TRI_SHIFT                                     15
#define IOU_SLCR_MIO_MST_TRI0_PIN_15_TRI_MASK                                      0x00008000U

/*Master Tri-state Enable for pin 16, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_16_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_16_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_16_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_16_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_16_TRI_SHIFT                                     16
#define IOU_SLCR_MIO_MST_TRI0_PIN_16_TRI_MASK                                      0x00010000U

/*Master Tri-state Enable for pin 17, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_17_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_17_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_17_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_17_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_17_TRI_SHIFT                                     17
#define IOU_SLCR_MIO_MST_TRI0_PIN_17_TRI_MASK                                      0x00020000U

/*Master Tri-state Enable for pin 18, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_18_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_18_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_18_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_18_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_18_TRI_SHIFT                                     18
#define IOU_SLCR_MIO_MST_TRI0_PIN_18_TRI_MASK                                      0x00040000U

/*Master Tri-state Enable for pin 19, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_19_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_19_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_19_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_19_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_19_TRI_SHIFT                                     19
#define IOU_SLCR_MIO_MST_TRI0_PIN_19_TRI_MASK                                      0x00080000U

/*Master Tri-state Enable for pin 20, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_20_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_20_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_20_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_20_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_20_TRI_SHIFT                                     20
#define IOU_SLCR_MIO_MST_TRI0_PIN_20_TRI_MASK                                      0x00100000U

/*Master Tri-state Enable for pin 21, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_21_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_21_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_21_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_21_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_21_TRI_SHIFT                                     21
#define IOU_SLCR_MIO_MST_TRI0_PIN_21_TRI_MASK                                      0x00200000U

/*Master Tri-state Enable for pin 22, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_22_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_22_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_22_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_22_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_22_TRI_SHIFT                                     22
#define IOU_SLCR_MIO_MST_TRI0_PIN_22_TRI_MASK                                      0x00400000U

/*Master Tri-state Enable for pin 23, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_23_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_23_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_23_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_23_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_23_TRI_SHIFT                                     23
#define IOU_SLCR_MIO_MST_TRI0_PIN_23_TRI_MASK                                      0x00800000U

/*Master Tri-state Enable for pin 24, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_24_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_24_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_24_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_24_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_24_TRI_SHIFT                                     24
#define IOU_SLCR_MIO_MST_TRI0_PIN_24_TRI_MASK                                      0x01000000U

/*Master Tri-state Enable for pin 25, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_25_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_25_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_25_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_25_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_25_TRI_SHIFT                                     25
#define IOU_SLCR_MIO_MST_TRI0_PIN_25_TRI_MASK                                      0x02000000U

/*Master Tri-state Enable for pin 26, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_26_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_26_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_26_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_26_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_26_TRI_SHIFT                                     26
#define IOU_SLCR_MIO_MST_TRI0_PIN_26_TRI_MASK                                      0x04000000U

/*Master Tri-state Enable for pin 27, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_27_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_27_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_27_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_27_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_27_TRI_SHIFT                                     27
#define IOU_SLCR_MIO_MST_TRI0_PIN_27_TRI_MASK                                      0x08000000U

/*Master Tri-state Enable for pin 28, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_28_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_28_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_28_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_28_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_28_TRI_SHIFT                                     28
#define IOU_SLCR_MIO_MST_TRI0_PIN_28_TRI_MASK                                      0x10000000U

/*Master Tri-state Enable for pin 29, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_29_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_29_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_29_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_29_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_29_TRI_SHIFT                                     29
#define IOU_SLCR_MIO_MST_TRI0_PIN_29_TRI_MASK                                      0x20000000U

/*Master Tri-state Enable for pin 30, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_30_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_30_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_30_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_30_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_30_TRI_SHIFT                                     30
#define IOU_SLCR_MIO_MST_TRI0_PIN_30_TRI_MASK                                      0x40000000U

/*Master Tri-state Enable for pin 31, active high*/
#undef IOU_SLCR_MIO_MST_TRI0_PIN_31_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_31_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI0_PIN_31_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI0_PIN_31_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI0_PIN_31_TRI_SHIFT                                     31
#define IOU_SLCR_MIO_MST_TRI0_PIN_31_TRI_MASK                                      0x80000000U

/*Master Tri-state Enable for pin 32, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_32_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_32_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_32_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_32_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_32_TRI_SHIFT                                     0
#define IOU_SLCR_MIO_MST_TRI1_PIN_32_TRI_MASK                                      0x00000001U

/*Master Tri-state Enable for pin 33, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_33_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_33_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_33_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_33_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_33_TRI_SHIFT                                     1
#define IOU_SLCR_MIO_MST_TRI1_PIN_33_TRI_MASK                                      0x00000002U

/*Master Tri-state Enable for pin 34, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_34_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_34_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_34_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_34_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_34_TRI_SHIFT                                     2
#define IOU_SLCR_MIO_MST_TRI1_PIN_34_TRI_MASK                                      0x00000004U

/*Master Tri-state Enable for pin 35, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_35_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_35_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_35_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_35_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_35_TRI_SHIFT                                     3
#define IOU_SLCR_MIO_MST_TRI1_PIN_35_TRI_MASK                                      0x00000008U

/*Master Tri-state Enable for pin 36, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_36_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_36_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_36_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_36_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_36_TRI_SHIFT                                     4
#define IOU_SLCR_MIO_MST_TRI1_PIN_36_TRI_MASK                                      0x00000010U

/*Master Tri-state Enable for pin 37, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_37_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_37_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_37_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_37_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_37_TRI_SHIFT                                     5
#define IOU_SLCR_MIO_MST_TRI1_PIN_37_TRI_MASK                                      0x00000020U

/*Master Tri-state Enable for pin 38, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_38_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_38_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_38_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_38_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_38_TRI_SHIFT                                     6
#define IOU_SLCR_MIO_MST_TRI1_PIN_38_TRI_MASK                                      0x00000040U

/*Master Tri-state Enable for pin 39, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_39_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_39_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_39_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_39_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_39_TRI_SHIFT                                     7
#define IOU_SLCR_MIO_MST_TRI1_PIN_39_TRI_MASK                                      0x00000080U

/*Master Tri-state Enable for pin 40, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_40_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_40_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_40_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_40_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_40_TRI_SHIFT                                     8
#define IOU_SLCR_MIO_MST_TRI1_PIN_40_TRI_MASK                                      0x00000100U

/*Master Tri-state Enable for pin 41, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_41_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_41_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_41_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_41_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_41_TRI_SHIFT                                     9
#define IOU_SLCR_MIO_MST_TRI1_PIN_41_TRI_MASK                                      0x00000200U

/*Master Tri-state Enable for pin 42, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_42_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_42_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_42_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_42_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_42_TRI_SHIFT                                     10
#define IOU_SLCR_MIO_MST_TRI1_PIN_42_TRI_MASK                                      0x00000400U

/*Master Tri-state Enable for pin 43, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_43_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_43_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_43_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_43_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_43_TRI_SHIFT                                     11
#define IOU_SLCR_MIO_MST_TRI1_PIN_43_TRI_MASK                                      0x00000800U

/*Master Tri-state Enable for pin 44, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_44_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_44_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_44_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_44_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_44_TRI_SHIFT                                     12
#define IOU_SLCR_MIO_MST_TRI1_PIN_44_TRI_MASK                                      0x00001000U

/*Master Tri-state Enable for pin 45, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_45_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_45_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_45_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_45_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_45_TRI_SHIFT                                     13
#define IOU_SLCR_MIO_MST_TRI1_PIN_45_TRI_MASK                                      0x00002000U

/*Master Tri-state Enable for pin 46, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_46_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_46_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_46_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_46_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_46_TRI_SHIFT                                     14
#define IOU_SLCR_MIO_MST_TRI1_PIN_46_TRI_MASK                                      0x00004000U

/*Master Tri-state Enable for pin 47, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_47_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_47_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_47_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_47_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_47_TRI_SHIFT                                     15
#define IOU_SLCR_MIO_MST_TRI1_PIN_47_TRI_MASK                                      0x00008000U

/*Master Tri-state Enable for pin 48, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_48_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_48_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_48_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_48_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_48_TRI_SHIFT                                     16
#define IOU_SLCR_MIO_MST_TRI1_PIN_48_TRI_MASK                                      0x00010000U

/*Master Tri-state Enable for pin 49, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_49_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_49_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_49_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_49_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_49_TRI_SHIFT                                     17
#define IOU_SLCR_MIO_MST_TRI1_PIN_49_TRI_MASK                                      0x00020000U

/*Master Tri-state Enable for pin 50, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_50_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_50_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_50_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_50_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_50_TRI_SHIFT                                     18
#define IOU_SLCR_MIO_MST_TRI1_PIN_50_TRI_MASK                                      0x00040000U

/*Master Tri-state Enable for pin 51, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_51_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_51_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_51_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_51_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_51_TRI_SHIFT                                     19
#define IOU_SLCR_MIO_MST_TRI1_PIN_51_TRI_MASK                                      0x00080000U

/*Master Tri-state Enable for pin 52, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_52_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_52_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_52_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_52_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_52_TRI_SHIFT                                     20
#define IOU_SLCR_MIO_MST_TRI1_PIN_52_TRI_MASK                                      0x00100000U

/*Master Tri-state Enable for pin 53, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_53_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_53_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_53_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_53_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_53_TRI_SHIFT                                     21
#define IOU_SLCR_MIO_MST_TRI1_PIN_53_TRI_MASK                                      0x00200000U

/*Master Tri-state Enable for pin 54, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_54_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_54_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_54_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_54_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_54_TRI_SHIFT                                     22
#define IOU_SLCR_MIO_MST_TRI1_PIN_54_TRI_MASK                                      0x00400000U

/*Master Tri-state Enable for pin 55, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_55_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_55_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_55_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_55_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_55_TRI_SHIFT                                     23
#define IOU_SLCR_MIO_MST_TRI1_PIN_55_TRI_MASK                                      0x00800000U

/*Master Tri-state Enable for pin 56, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_56_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_56_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_56_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_56_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_56_TRI_SHIFT                                     24
#define IOU_SLCR_MIO_MST_TRI1_PIN_56_TRI_MASK                                      0x01000000U

/*Master Tri-state Enable for pin 57, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_57_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_57_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_57_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_57_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_57_TRI_SHIFT                                     25
#define IOU_SLCR_MIO_MST_TRI1_PIN_57_TRI_MASK                                      0x02000000U

/*Master Tri-state Enable for pin 58, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_58_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_58_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_58_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_58_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_58_TRI_SHIFT                                     26
#define IOU_SLCR_MIO_MST_TRI1_PIN_58_TRI_MASK                                      0x04000000U

/*Master Tri-state Enable for pin 59, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_59_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_59_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_59_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_59_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_59_TRI_SHIFT                                     27
#define IOU_SLCR_MIO_MST_TRI1_PIN_59_TRI_MASK                                      0x08000000U

/*Master Tri-state Enable for pin 60, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_60_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_60_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_60_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_60_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_60_TRI_SHIFT                                     28
#define IOU_SLCR_MIO_MST_TRI1_PIN_60_TRI_MASK                                      0x10000000U

/*Master Tri-state Enable for pin 61, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_61_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_61_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_61_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_61_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_61_TRI_SHIFT                                     29
#define IOU_SLCR_MIO_MST_TRI1_PIN_61_TRI_MASK                                      0x20000000U

/*Master Tri-state Enable for pin 62, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_62_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_62_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_62_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_62_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_62_TRI_SHIFT                                     30
#define IOU_SLCR_MIO_MST_TRI1_PIN_62_TRI_MASK                                      0x40000000U

/*Master Tri-state Enable for pin 63, active high*/
#undef IOU_SLCR_MIO_MST_TRI1_PIN_63_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_63_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI1_PIN_63_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI1_PIN_63_TRI_DEFVAL                                    0xFFFFFFFF
#define IOU_SLCR_MIO_MST_TRI1_PIN_63_TRI_SHIFT                                     31
#define IOU_SLCR_MIO_MST_TRI1_PIN_63_TRI_MASK                                      0x80000000U

/*Master Tri-state Enable for pin 64, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_64_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_64_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_64_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_64_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_64_TRI_SHIFT                                     0
#define IOU_SLCR_MIO_MST_TRI2_PIN_64_TRI_MASK                                      0x00000001U

/*Master Tri-state Enable for pin 65, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_65_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_65_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_65_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_65_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_65_TRI_SHIFT                                     1
#define IOU_SLCR_MIO_MST_TRI2_PIN_65_TRI_MASK                                      0x00000002U

/*Master Tri-state Enable for pin 66, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_66_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_66_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_66_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_66_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_66_TRI_SHIFT                                     2
#define IOU_SLCR_MIO_MST_TRI2_PIN_66_TRI_MASK                                      0x00000004U

/*Master Tri-state Enable for pin 67, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_67_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_67_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_67_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_67_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_67_TRI_SHIFT                                     3
#define IOU_SLCR_MIO_MST_TRI2_PIN_67_TRI_MASK                                      0x00000008U

/*Master Tri-state Enable for pin 68, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_68_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_68_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_68_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_68_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_68_TRI_SHIFT                                     4
#define IOU_SLCR_MIO_MST_TRI2_PIN_68_TRI_MASK                                      0x00000010U

/*Master Tri-state Enable for pin 69, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_69_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_69_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_69_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_69_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_69_TRI_SHIFT                                     5
#define IOU_SLCR_MIO_MST_TRI2_PIN_69_TRI_MASK                                      0x00000020U

/*Master Tri-state Enable for pin 70, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_70_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_70_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_70_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_70_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_70_TRI_SHIFT                                     6
#define IOU_SLCR_MIO_MST_TRI2_PIN_70_TRI_MASK                                      0x00000040U

/*Master Tri-state Enable for pin 71, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_71_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_71_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_71_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_71_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_71_TRI_SHIFT                                     7
#define IOU_SLCR_MIO_MST_TRI2_PIN_71_TRI_MASK                                      0x00000080U

/*Master Tri-state Enable for pin 72, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_72_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_72_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_72_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_72_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_72_TRI_SHIFT                                     8
#define IOU_SLCR_MIO_MST_TRI2_PIN_72_TRI_MASK                                      0x00000100U

/*Master Tri-state Enable for pin 73, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_73_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_73_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_73_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_73_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_73_TRI_SHIFT                                     9
#define IOU_SLCR_MIO_MST_TRI2_PIN_73_TRI_MASK                                      0x00000200U

/*Master Tri-state Enable for pin 74, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_74_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_74_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_74_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_74_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_74_TRI_SHIFT                                     10
#define IOU_SLCR_MIO_MST_TRI2_PIN_74_TRI_MASK                                      0x00000400U

/*Master Tri-state Enable for pin 75, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_75_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_75_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_75_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_75_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_75_TRI_SHIFT                                     11
#define IOU_SLCR_MIO_MST_TRI2_PIN_75_TRI_MASK                                      0x00000800U

/*Master Tri-state Enable for pin 76, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_76_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_76_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_76_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_76_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_76_TRI_SHIFT                                     12
#define IOU_SLCR_MIO_MST_TRI2_PIN_76_TRI_MASK                                      0x00001000U

/*Master Tri-state Enable for pin 77, active high*/
#undef IOU_SLCR_MIO_MST_TRI2_PIN_77_TRI_DEFVAL 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_77_TRI_SHIFT 
#undef IOU_SLCR_MIO_MST_TRI2_PIN_77_TRI_MASK 
#define IOU_SLCR_MIO_MST_TRI2_PIN_77_TRI_DEFVAL                                    0x00003FFF
#define IOU_SLCR_MIO_MST_TRI2_PIN_77_TRI_SHIFT                                     13
#define IOU_SLCR_MIO_MST_TRI2_PIN_77_TRI_MASK                                      0x00002000U

/*I2C Loopback Control. 0 = Connect I2C inputs according to MIO mapping. 1 = Loop I2C 0 outputs to I2C 1 inputs, and I2C 1 outp
		ts to I2C 0 inputs.*/
#undef IOU_SLCR_MIO_LOOPBACK_I2C0_LOOP_I2C1_DEFVAL 
#undef IOU_SLCR_MIO_LOOPBACK_I2C0_LOOP_I2C1_SHIFT 
#undef IOU_SLCR_MIO_LOOPBACK_I2C0_LOOP_I2C1_MASK 
#define IOU_SLCR_MIO_LOOPBACK_I2C0_LOOP_I2C1_DEFVAL                                0x00000000
#define IOU_SLCR_MIO_LOOPBACK_I2C0_LOOP_I2C1_SHIFT                                 3
#define IOU_SLCR_MIO_LOOPBACK_I2C0_LOOP_I2C1_MASK                                  0x00000008U

/*CAN Loopback Control. 0 = Connect CAN inputs according to MIO mapping. 1 = Loop CAN 0 Tx to CAN 1 Rx, and CAN 1 Tx to CAN 0 R
		.*/
#undef IOU_SLCR_MIO_LOOPBACK_CAN0_LOOP_CAN1_DEFVAL 
#undef IOU_SLCR_MIO_LOOPBACK_CAN0_LOOP_CAN1_SHIFT 
#undef IOU_SLCR_MIO_LOOPBACK_CAN0_LOOP_CAN1_MASK 
#define IOU_SLCR_MIO_LOOPBACK_CAN0_LOOP_CAN1_DEFVAL                                0x00000000
#define IOU_SLCR_MIO_LOOPBACK_CAN0_LOOP_CAN1_SHIFT                                 2
#define IOU_SLCR_MIO_LOOPBACK_CAN0_LOOP_CAN1_MASK                                  0x00000004U

/*UART Loopback Control. 0 = Connect UART inputs according to MIO mapping. 1 = Loop UART 0 outputs to UART 1 inputs, and UART 1
		outputs to UART 0 inputs. RXD/TXD cross-connected. RTS/CTS cross-connected. DSR, DTR, DCD and RI not used.*/
#undef IOU_SLCR_MIO_LOOPBACK_UA0_LOOP_UA1_DEFVAL 
#undef IOU_SLCR_MIO_LOOPBACK_UA0_LOOP_UA1_SHIFT 
#undef IOU_SLCR_MIO_LOOPBACK_UA0_LOOP_UA1_MASK 
#define IOU_SLCR_MIO_LOOPBACK_UA0_LOOP_UA1_DEFVAL                                  0x00000000
#define IOU_SLCR_MIO_LOOPBACK_UA0_LOOP_UA1_SHIFT                                   1
#define IOU_SLCR_MIO_LOOPBACK_UA0_LOOP_UA1_MASK                                    0x00000002U

/*SPI Loopback Control. 0 = Connect SPI inputs according to MIO mapping. 1 = Loop SPI 0 outputs to SPI 1 inputs, and SPI 1 outp
		ts to SPI 0 inputs. The other SPI core will appear on the LS Slave Select.*/
#undef IOU_SLCR_MIO_LOOPBACK_SPI0_LOOP_SPI1_DEFVAL 
#undef IOU_SLCR_MIO_LOOPBACK_SPI0_LOOP_SPI1_SHIFT 
#undef IOU_SLCR_MIO_LOOPBACK_SPI0_LOOP_SPI1_MASK 
#define IOU_SLCR_MIO_LOOPBACK_SPI0_LOOP_SPI1_DEFVAL                                0x00000000
#define IOU_SLCR_MIO_LOOPBACK_SPI0_LOOP_SPI1_SHIFT                                 0
#define IOU_SLCR_MIO_LOOPBACK_SPI0_LOOP_SPI1_MASK                                  0x00000001U
#undef CRL_APB_RST_LPD_IOU0_OFFSET 
#define CRL_APB_RST_LPD_IOU0_OFFSET                                                0XFF5E0230
#undef CRL_APB_RST_LPD_IOU2_OFFSET 
#define CRL_APB_RST_LPD_IOU2_OFFSET                                                0XFF5E0238
#undef CRL_APB_RST_LPD_IOU2_OFFSET 
#define CRL_APB_RST_LPD_IOU2_OFFSET                                                0XFF5E0238
#undef CRL_APB_RST_LPD_TOP_OFFSET 
#define CRL_APB_RST_LPD_TOP_OFFSET                                                 0XFF5E023C
#undef CRL_APB_RST_LPD_IOU2_OFFSET 
#define CRL_APB_RST_LPD_IOU2_OFFSET                                                0XFF5E0238
#undef IOU_SLCR_CTRL_REG_SD_OFFSET 
#define IOU_SLCR_CTRL_REG_SD_OFFSET                                                0XFF180310
#undef IOU_SLCR_SD_CONFIG_REG2_OFFSET 
#define IOU_SLCR_SD_CONFIG_REG2_OFFSET                                             0XFF180320
#undef CRL_APB_RST_LPD_IOU2_OFFSET 
#define CRL_APB_RST_LPD_IOU2_OFFSET                                                0XFF5E0238
#undef CRL_APB_RST_LPD_IOU2_OFFSET 
#define CRL_APB_RST_LPD_IOU2_OFFSET                                                0XFF5E0238
#undef CRL_APB_RST_LPD_IOU2_OFFSET 
#define CRL_APB_RST_LPD_IOU2_OFFSET                                                0XFF5E0238
#undef CRL_APB_RST_LPD_IOU2_OFFSET 
#define CRL_APB_RST_LPD_IOU2_OFFSET                                                0XFF5E0238
#undef CRL_APB_RST_LPD_IOU2_OFFSET 
#define CRL_APB_RST_LPD_IOU2_OFFSET                                                0XFF5E0238
#undef UART0_BAUD_RATE_DIVIDER_REG0_OFFSET 
#define UART0_BAUD_RATE_DIVIDER_REG0_OFFSET                                        0XFF000034
#undef UART0_BAUD_RATE_GEN_REG0_OFFSET 
#define UART0_BAUD_RATE_GEN_REG0_OFFSET                                            0XFF000018
#undef UART0_CONTROL_REG0_OFFSET 
#define UART0_CONTROL_REG0_OFFSET                                                  0XFF000000
#undef UART0_MODE_REG0_OFFSET 
#define UART0_MODE_REG0_OFFSET                                                     0XFF000004
#undef UART1_BAUD_RATE_DIVIDER_REG0_OFFSET 
#define UART1_BAUD_RATE_DIVIDER_REG0_OFFSET                                        0XFF010034
#undef UART1_BAUD_RATE_GEN_REG0_OFFSET 
#define UART1_BAUD_RATE_GEN_REG0_OFFSET                                            0XFF010018
#undef UART1_CONTROL_REG0_OFFSET 
#define UART1_CONTROL_REG0_OFFSET                                                  0XFF010000
#undef UART1_MODE_REG0_OFFSET 
#define UART1_MODE_REG0_OFFSET                                                     0XFF010004
#undef LPD_SLCR_SECURE_SLCR_ADMA_OFFSET 
#define LPD_SLCR_SECURE_SLCR_ADMA_OFFSET                                           0XFF4B0024
#undef CSU_TAMPER_STATUS_OFFSET 
#define CSU_TAMPER_STATUS_OFFSET                                                   0XFFCA5000

/*GEM 0 reset*/
#undef CRL_APB_RST_LPD_IOU0_GEM0_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU0_GEM0_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU0_GEM0_RESET_MASK 
#define CRL_APB_RST_LPD_IOU0_GEM0_RESET_DEFVAL                                     0x0000000F
#define CRL_APB_RST_LPD_IOU0_GEM0_RESET_SHIFT                                      0
#define CRL_APB_RST_LPD_IOU0_GEM0_RESET_MASK                                       0x00000001U

/*GEM 1 reset*/
#undef CRL_APB_RST_LPD_IOU0_GEM1_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU0_GEM1_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU0_GEM1_RESET_MASK 
#define CRL_APB_RST_LPD_IOU0_GEM1_RESET_DEFVAL                                     0x0000000F
#define CRL_APB_RST_LPD_IOU0_GEM1_RESET_SHIFT                                      1
#define CRL_APB_RST_LPD_IOU0_GEM1_RESET_MASK                                       0x00000002U

/*GEM 2 reset*/
#undef CRL_APB_RST_LPD_IOU0_GEM2_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU0_GEM2_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU0_GEM2_RESET_MASK 
#define CRL_APB_RST_LPD_IOU0_GEM2_RESET_DEFVAL                                     0x0000000F
#define CRL_APB_RST_LPD_IOU0_GEM2_RESET_SHIFT                                      2
#define CRL_APB_RST_LPD_IOU0_GEM2_RESET_MASK                                       0x00000004U

/*GEM 3 reset*/
#undef CRL_APB_RST_LPD_IOU0_GEM3_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU0_GEM3_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU0_GEM3_RESET_MASK 
#define CRL_APB_RST_LPD_IOU0_GEM3_RESET_DEFVAL                                     0x0000000F
#define CRL_APB_RST_LPD_IOU0_GEM3_RESET_SHIFT                                      3
#define CRL_APB_RST_LPD_IOU0_GEM3_RESET_MASK                                       0x00000008U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_QSPI_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_QSPI_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_QSPI_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_QSPI_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_QSPI_RESET_SHIFT                                      0
#define CRL_APB_RST_LPD_IOU2_QSPI_RESET_MASK                                       0x00000001U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_NAND_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_NAND_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_NAND_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_NAND_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_NAND_RESET_SHIFT                                      16
#define CRL_APB_RST_LPD_IOU2_NAND_RESET_MASK                                       0x00010000U

/*USB 0 reset for control registers*/
#undef CRL_APB_RST_LPD_TOP_USB0_APB_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_TOP_USB0_APB_RESET_SHIFT 
#undef CRL_APB_RST_LPD_TOP_USB0_APB_RESET_MASK 
#define CRL_APB_RST_LPD_TOP_USB0_APB_RESET_DEFVAL                                  0x00188FDF
#define CRL_APB_RST_LPD_TOP_USB0_APB_RESET_SHIFT                                   10
#define CRL_APB_RST_LPD_TOP_USB0_APB_RESET_MASK                                    0x00000400U

/*USB 0 sleep circuit reset*/
#undef CRL_APB_RST_LPD_TOP_USB0_HIBERRESET_DEFVAL 
#undef CRL_APB_RST_LPD_TOP_USB0_HIBERRESET_SHIFT 
#undef CRL_APB_RST_LPD_TOP_USB0_HIBERRESET_MASK 
#define CRL_APB_RST_LPD_TOP_USB0_HIBERRESET_DEFVAL                                 0x00188FDF
#define CRL_APB_RST_LPD_TOP_USB0_HIBERRESET_SHIFT                                  8
#define CRL_APB_RST_LPD_TOP_USB0_HIBERRESET_MASK                                   0x00000100U

/*USB 0 reset*/
#undef CRL_APB_RST_LPD_TOP_USB0_CORERESET_DEFVAL 
#undef CRL_APB_RST_LPD_TOP_USB0_CORERESET_SHIFT 
#undef CRL_APB_RST_LPD_TOP_USB0_CORERESET_MASK 
#define CRL_APB_RST_LPD_TOP_USB0_CORERESET_DEFVAL                                  0x00188FDF
#define CRL_APB_RST_LPD_TOP_USB0_CORERESET_SHIFT                                   6
#define CRL_APB_RST_LPD_TOP_USB0_CORERESET_MASK                                    0x00000040U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_SDIO0_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_SDIO0_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_SDIO0_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_SDIO0_RESET_DEFVAL                                    0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_SDIO0_RESET_SHIFT                                     5
#define CRL_APB_RST_LPD_IOU2_SDIO0_RESET_MASK                                      0x00000020U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_SDIO1_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_SDIO1_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_SDIO1_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_SDIO1_RESET_DEFVAL                                    0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_SDIO1_RESET_SHIFT                                     6
#define CRL_APB_RST_LPD_IOU2_SDIO1_RESET_MASK                                      0x00000040U

/*SD or eMMC selection on SDIO0 0: SD enabled 1: eMMC enabled*/
#undef IOU_SLCR_CTRL_REG_SD_SD0_EMMC_SEL_DEFVAL 
#undef IOU_SLCR_CTRL_REG_SD_SD0_EMMC_SEL_SHIFT 
#undef IOU_SLCR_CTRL_REG_SD_SD0_EMMC_SEL_MASK 
#define IOU_SLCR_CTRL_REG_SD_SD0_EMMC_SEL_DEFVAL                                   0x00000000
#define IOU_SLCR_CTRL_REG_SD_SD0_EMMC_SEL_SHIFT                                    0
#define IOU_SLCR_CTRL_REG_SD_SD0_EMMC_SEL_MASK                                     0x00000001U

/*SD or eMMC selection on SDIO1 0: SD enabled 1: eMMC enabled*/
#undef IOU_SLCR_CTRL_REG_SD_SD1_EMMC_SEL_DEFVAL 
#undef IOU_SLCR_CTRL_REG_SD_SD1_EMMC_SEL_SHIFT 
#undef IOU_SLCR_CTRL_REG_SD_SD1_EMMC_SEL_MASK 
#define IOU_SLCR_CTRL_REG_SD_SD1_EMMC_SEL_DEFVAL                                   0x00000000
#define IOU_SLCR_CTRL_REG_SD_SD1_EMMC_SEL_SHIFT                                    15
#define IOU_SLCR_CTRL_REG_SD_SD1_EMMC_SEL_MASK                                     0x00008000U

/*Should be set based on the final product usage 00 - Removable SCard Slot 01 - Embedded Slot for One Device 10 - Shared Bus Sl
		t 11 - Reserved*/
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_SLOTTYPE_DEFVAL 
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_SLOTTYPE_SHIFT 
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_SLOTTYPE_MASK 
#define IOU_SLCR_SD_CONFIG_REG2_SD0_SLOTTYPE_DEFVAL                                0x0FFC0FFC
#define IOU_SLCR_SD_CONFIG_REG2_SD0_SLOTTYPE_SHIFT                                 12
#define IOU_SLCR_SD_CONFIG_REG2_SD0_SLOTTYPE_MASK                                  0x00003000U

/*Should be set based on the final product usage 00 - Removable SCard Slot 01 - Embedded Slot for One Device 10 - Shared Bus Sl
		t 11 - Reserved*/
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_SLOTTYPE_DEFVAL 
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_SLOTTYPE_SHIFT 
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_SLOTTYPE_MASK 
#define IOU_SLCR_SD_CONFIG_REG2_SD1_SLOTTYPE_DEFVAL                                0x0FFC0FFC
#define IOU_SLCR_SD_CONFIG_REG2_SD1_SLOTTYPE_SHIFT                                 28
#define IOU_SLCR_SD_CONFIG_REG2_SD1_SLOTTYPE_MASK                                  0x30000000U

/*1.8V Support 1: 1.8V supported 0: 1.8V not supported support*/
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_1P8V_DEFVAL 
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_1P8V_SHIFT 
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_1P8V_MASK 
#define IOU_SLCR_SD_CONFIG_REG2_SD0_1P8V_DEFVAL                                    0x0FFC0FFC
#define IOU_SLCR_SD_CONFIG_REG2_SD0_1P8V_SHIFT                                     9
#define IOU_SLCR_SD_CONFIG_REG2_SD0_1P8V_MASK                                      0x00000200U

/*3.0V Support 1: 3.0V supported 0: 3.0V not supported support*/
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_3P0V_DEFVAL 
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_3P0V_SHIFT 
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_3P0V_MASK 
#define IOU_SLCR_SD_CONFIG_REG2_SD0_3P0V_DEFVAL                                    0x0FFC0FFC
#define IOU_SLCR_SD_CONFIG_REG2_SD0_3P0V_SHIFT                                     8
#define IOU_SLCR_SD_CONFIG_REG2_SD0_3P0V_MASK                                      0x00000100U

/*3.3V Support 1: 3.3V supported 0: 3.3V not supported support*/
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_3P3V_DEFVAL 
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_3P3V_SHIFT 
#undef IOU_SLCR_SD_CONFIG_REG2_SD0_3P3V_MASK 
#define IOU_SLCR_SD_CONFIG_REG2_SD0_3P3V_DEFVAL                                    0x0FFC0FFC
#define IOU_SLCR_SD_CONFIG_REG2_SD0_3P3V_SHIFT                                     7
#define IOU_SLCR_SD_CONFIG_REG2_SD0_3P3V_MASK                                      0x00000080U

/*1.8V Support 1: 1.8V supported 0: 1.8V not supported support*/
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_1P8V_DEFVAL 
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_1P8V_SHIFT 
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_1P8V_MASK 
#define IOU_SLCR_SD_CONFIG_REG2_SD1_1P8V_DEFVAL                                    0x0FFC0FFC
#define IOU_SLCR_SD_CONFIG_REG2_SD1_1P8V_SHIFT                                     25
#define IOU_SLCR_SD_CONFIG_REG2_SD1_1P8V_MASK                                      0x02000000U

/*3.0V Support 1: 3.0V supported 0: 3.0V not supported support*/
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_3P0V_DEFVAL 
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_3P0V_SHIFT 
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_3P0V_MASK 
#define IOU_SLCR_SD_CONFIG_REG2_SD1_3P0V_DEFVAL                                    0x0FFC0FFC
#define IOU_SLCR_SD_CONFIG_REG2_SD1_3P0V_SHIFT                                     24
#define IOU_SLCR_SD_CONFIG_REG2_SD1_3P0V_MASK                                      0x01000000U

/*3.3V Support 1: 3.3V supported 0: 3.3V not supported support*/
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_3P3V_DEFVAL 
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_3P3V_SHIFT 
#undef IOU_SLCR_SD_CONFIG_REG2_SD1_3P3V_MASK 
#define IOU_SLCR_SD_CONFIG_REG2_SD1_3P3V_DEFVAL                                    0x0FFC0FFC
#define IOU_SLCR_SD_CONFIG_REG2_SD1_3P3V_SHIFT                                     23
#define IOU_SLCR_SD_CONFIG_REG2_SD1_3P3V_MASK                                      0x00800000U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_CAN0_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_CAN0_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_CAN0_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_CAN0_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_CAN0_RESET_SHIFT                                      7
#define CRL_APB_RST_LPD_IOU2_CAN0_RESET_MASK                                       0x00000080U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_CAN1_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_CAN1_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_CAN1_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_CAN1_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_CAN1_RESET_SHIFT                                      8
#define CRL_APB_RST_LPD_IOU2_CAN1_RESET_MASK                                       0x00000100U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_I2C0_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_I2C0_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_I2C0_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_I2C0_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_I2C0_RESET_SHIFT                                      9
#define CRL_APB_RST_LPD_IOU2_I2C0_RESET_MASK                                       0x00000200U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_I2C1_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_I2C1_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_I2C1_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_I2C1_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_I2C1_RESET_SHIFT                                      10
#define CRL_APB_RST_LPD_IOU2_I2C1_RESET_MASK                                       0x00000400U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_SPI0_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_SPI0_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_SPI0_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_SPI0_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_SPI0_RESET_SHIFT                                      3
#define CRL_APB_RST_LPD_IOU2_SPI0_RESET_MASK                                       0x00000008U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_SPI1_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_SPI1_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_SPI1_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_SPI1_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_SPI1_RESET_SHIFT                                      4
#define CRL_APB_RST_LPD_IOU2_SPI1_RESET_MASK                                       0x00000010U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_TTC0_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_TTC0_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_TTC0_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_TTC0_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_TTC0_RESET_SHIFT                                      11
#define CRL_APB_RST_LPD_IOU2_TTC0_RESET_MASK                                       0x00000800U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_TTC1_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_TTC1_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_TTC1_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_TTC1_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_TTC1_RESET_SHIFT                                      12
#define CRL_APB_RST_LPD_IOU2_TTC1_RESET_MASK                                       0x00001000U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_TTC2_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_TTC2_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_TTC2_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_TTC2_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_TTC2_RESET_SHIFT                                      13
#define CRL_APB_RST_LPD_IOU2_TTC2_RESET_MASK                                       0x00002000U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_TTC3_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_TTC3_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_TTC3_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_TTC3_RESET_DEFVAL                                     0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_TTC3_RESET_SHIFT                                      14
#define CRL_APB_RST_LPD_IOU2_TTC3_RESET_MASK                                       0x00004000U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_UART0_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_UART0_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_UART0_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_UART0_RESET_DEFVAL                                    0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_UART0_RESET_SHIFT                                     1
#define CRL_APB_RST_LPD_IOU2_UART0_RESET_MASK                                      0x00000002U

/*Block level reset*/
#undef CRL_APB_RST_LPD_IOU2_UART1_RESET_DEFVAL 
#undef CRL_APB_RST_LPD_IOU2_UART1_RESET_SHIFT 
#undef CRL_APB_RST_LPD_IOU2_UART1_RESET_MASK 
#define CRL_APB_RST_LPD_IOU2_UART1_RESET_DEFVAL                                    0x0017FFFF
#define CRL_APB_RST_LPD_IOU2_UART1_RESET_SHIFT                                     2
#define CRL_APB_RST_LPD_IOU2_UART1_RESET_MASK                                      0x00000004U

/*Baud rate divider value: 0 - 3: ignored 4 - 255: Baud rate*/
#undef UART0_BAUD_RATE_DIVIDER_REG0_BDIV_DEFVAL 
#undef UART0_BAUD_RATE_DIVIDER_REG0_BDIV_SHIFT 
#undef UART0_BAUD_RATE_DIVIDER_REG0_BDIV_MASK 
#define UART0_BAUD_RATE_DIVIDER_REG0_BDIV_DEFVAL                                   0x0000000F
#define UART0_BAUD_RATE_DIVIDER_REG0_BDIV_SHIFT                                    0
#define UART0_BAUD_RATE_DIVIDER_REG0_BDIV_MASK                                     0x000000FFU

/*Baud Rate Clock Divisor Value: 0: Disables baud_sample 1: Clock divisor bypass (baud_sample = sel_clk) 2 - 65535: baud_sample*/
#undef UART0_BAUD_RATE_GEN_REG0_CD_DEFVAL 
#undef UART0_BAUD_RATE_GEN_REG0_CD_SHIFT 
#undef UART0_BAUD_RATE_GEN_REG0_CD_MASK 
#define UART0_BAUD_RATE_GEN_REG0_CD_DEFVAL                                         0x0000028B
#define UART0_BAUD_RATE_GEN_REG0_CD_SHIFT                                          0
#define UART0_BAUD_RATE_GEN_REG0_CD_MASK                                           0x0000FFFFU

/*Stop transmitter break: 0: no affect 1: stop transmission of the break after a minimum of one character length and transmit a
		high level during 12 bit periods. It can be set regardless of the value of STTBRK.*/
#undef UART0_CONTROL_REG0_STPBRK_DEFVAL 
#undef UART0_CONTROL_REG0_STPBRK_SHIFT 
#undef UART0_CONTROL_REG0_STPBRK_MASK 
#define UART0_CONTROL_REG0_STPBRK_DEFVAL                                           0x00000128
#define UART0_CONTROL_REG0_STPBRK_SHIFT                                            8
#define UART0_CONTROL_REG0_STPBRK_MASK                                             0x00000100U

/*Start transmitter break: 0: no affect 1: start to transmit a break after the characters currently present in the FIFO and the
		transmit shift register have been transmitted. It can only be set if STPBRK (Stop transmitter break) is not high.*/
#undef UART0_CONTROL_REG0_STTBRK_DEFVAL 
#undef UART0_CONTROL_REG0_STTBRK_SHIFT 
#undef UART0_CONTROL_REG0_STTBRK_MASK 
#define UART0_CONTROL_REG0_STTBRK_DEFVAL                                           0x00000128
#define UART0_CONTROL_REG0_STTBRK_SHIFT                                            7
#define UART0_CONTROL_REG0_STTBRK_MASK                                             0x00000080U

/*Restart receiver timeout counter: 1: receiver timeout counter is restarted. This bit is self clearing once the restart has co
		pleted.*/
#undef UART0_CONTROL_REG0_RSTTO_DEFVAL 
#undef UART0_CONTROL_REG0_RSTTO_SHIFT 
#undef UART0_CONTROL_REG0_RSTTO_MASK 
#define UART0_CONTROL_REG0_RSTTO_DEFVAL                                            0x00000128
#define UART0_CONTROL_REG0_RSTTO_SHIFT                                             6
#define UART0_CONTROL_REG0_RSTTO_MASK                                              0x00000040U

/*Transmit disable: 0: enable transmitter 1: disable transmitter*/
#undef UART0_CONTROL_REG0_TXDIS_DEFVAL 
#undef UART0_CONTROL_REG0_TXDIS_SHIFT 
#undef UART0_CONTROL_REG0_TXDIS_MASK 
#define UART0_CONTROL_REG0_TXDIS_DEFVAL                                            0x00000128
#define UART0_CONTROL_REG0_TXDIS_SHIFT                                             5
#define UART0_CONTROL_REG0_TXDIS_MASK                                              0x00000020U

/*Transmit enable: 0: disable transmitter 1: enable transmitter, provided the TXDIS field is set to 0.*/
#undef UART0_CONTROL_REG0_TXEN_DEFVAL 
#undef UART0_CONTROL_REG0_TXEN_SHIFT 
#undef UART0_CONTROL_REG0_TXEN_MASK 
#define UART0_CONTROL_REG0_TXEN_DEFVAL                                             0x00000128
#define UART0_CONTROL_REG0_TXEN_SHIFT                                              4
#define UART0_CONTROL_REG0_TXEN_MASK                                               0x00000010U

/*Receive disable: 0: enable 1: disable, regardless of the value of RXEN*/
#undef UART0_CONTROL_REG0_RXDIS_DEFVAL 
#undef UART0_CONTROL_REG0_RXDIS_SHIFT 
#undef UART0_CONTROL_REG0_RXDIS_MASK 
#define UART0_CONTROL_REG0_RXDIS_DEFVAL                                            0x00000128
#define UART0_CONTROL_REG0_RXDIS_SHIFT                                             3
#define UART0_CONTROL_REG0_RXDIS_MASK                                              0x00000008U

/*Receive enable: 0: disable 1: enable When set to one, the receiver logic is enabled, provided the RXDIS field is set to zero.*/
#undef UART0_CONTROL_REG0_RXEN_DEFVAL 
#undef UART0_CONTROL_REG0_RXEN_SHIFT 
#undef UART0_CONTROL_REG0_RXEN_MASK 
#define UART0_CONTROL_REG0_RXEN_DEFVAL                                             0x00000128
#define UART0_CONTROL_REG0_RXEN_SHIFT                                              2
#define UART0_CONTROL_REG0_RXEN_MASK                                               0x00000004U

/*Software reset for Tx data path: 0: no affect 1: transmitter logic is reset and all pending transmitter data is discarded Thi
		 bit is self clearing once the reset has completed.*/
#undef UART0_CONTROL_REG0_TXRES_DEFVAL 
#undef UART0_CONTROL_REG0_TXRES_SHIFT 
#undef UART0_CONTROL_REG0_TXRES_MASK 
#define UART0_CONTROL_REG0_TXRES_DEFVAL                                            0x00000128
#define UART0_CONTROL_REG0_TXRES_SHIFT                                             1
#define UART0_CONTROL_REG0_TXRES_MASK                                              0x00000002U

/*Software reset for Rx data path: 0: no affect 1: receiver logic is reset and all pending receiver data is discarded. This bit
		is self clearing once the reset has completed.*/
#undef UART0_CONTROL_REG0_RXRES_DEFVAL 
#undef UART0_CONTROL_REG0_RXRES_SHIFT 
#undef UART0_CONTROL_REG0_RXRES_MASK 
#define UART0_CONTROL_REG0_RXRES_DEFVAL                                            0x00000128
#define UART0_CONTROL_REG0_RXRES_SHIFT                                             0
#define UART0_CONTROL_REG0_RXRES_MASK                                              0x00000001U

/*Channel mode: Defines the mode of operation of the UART. 00: normal 01: automatic echo 10: local loopback 11: remote loopback*/
#undef UART0_MODE_REG0_CHMODE_DEFVAL 
#undef UART0_MODE_REG0_CHMODE_SHIFT 
#undef UART0_MODE_REG0_CHMODE_MASK 
#define UART0_MODE_REG0_CHMODE_DEFVAL                                              0x00000000
#define UART0_MODE_REG0_CHMODE_SHIFT                                               8
#define UART0_MODE_REG0_CHMODE_MASK                                                0x00000300U

/*Number of stop bits: Defines the number of stop bits to detect on receive and to generate on transmit. 00: 1 stop bit 01: 1.5
		stop bits 10: 2 stop bits 11: reserved*/
#undef UART0_MODE_REG0_NBSTOP_DEFVAL 
#undef UART0_MODE_REG0_NBSTOP_SHIFT 
#undef UART0_MODE_REG0_NBSTOP_MASK 
#define UART0_MODE_REG0_NBSTOP_DEFVAL                                              0x00000000
#define UART0_MODE_REG0_NBSTOP_SHIFT                                               6
#define UART0_MODE_REG0_NBSTOP_MASK                                                0x000000C0U

/*Parity type select: Defines the expected parity to check on receive and the parity to generate on transmit. 000: even parity 
		01: odd parity 010: forced to 0 parity (space) 011: forced to 1 parity (mark) 1xx: no parity*/
#undef UART0_MODE_REG0_PAR_DEFVAL 
#undef UART0_MODE_REG0_PAR_SHIFT 
#undef UART0_MODE_REG0_PAR_MASK 
#define UART0_MODE_REG0_PAR_DEFVAL                                                 0x00000000
#define UART0_MODE_REG0_PAR_SHIFT                                                  3
#define UART0_MODE_REG0_PAR_MASK                                                   0x00000038U

/*Character length select: Defines the number of bits in each character. 11: 6 bits 10: 7 bits 0x: 8 bits*/
#undef UART0_MODE_REG0_CHRL_DEFVAL 
#undef UART0_MODE_REG0_CHRL_SHIFT 
#undef UART0_MODE_REG0_CHRL_MASK 
#define UART0_MODE_REG0_CHRL_DEFVAL                                                0x00000000
#define UART0_MODE_REG0_CHRL_SHIFT                                                 1
#define UART0_MODE_REG0_CHRL_MASK                                                  0x00000006U

/*Clock source select: This field defines whether a pre-scalar of 8 is applied to the baud rate generator input clock. 0: clock
		source is uart_ref_clk 1: clock source is uart_ref_clk/8*/
#undef UART0_MODE_REG0_CLKS_DEFVAL 
#undef UART0_MODE_REG0_CLKS_SHIFT 
#undef UART0_MODE_REG0_CLKS_MASK 
#define UART0_MODE_REG0_CLKS_DEFVAL                                                0x00000000
#define UART0_MODE_REG0_CLKS_SHIFT                                                 0
#define UART0_MODE_REG0_CLKS_MASK                                                  0x00000001U

/*Baud rate divider value: 0 - 3: ignored 4 - 255: Baud rate*/
#undef UART1_BAUD_RATE_DIVIDER_REG0_BDIV_DEFVAL 
#undef UART1_BAUD_RATE_DIVIDER_REG0_BDIV_SHIFT 
#undef UART1_BAUD_RATE_DIVIDER_REG0_BDIV_MASK 
#define UART1_BAUD_RATE_DIVIDER_REG0_BDIV_DEFVAL                                   0x0000000F
#define UART1_BAUD_RATE_DIVIDER_REG0_BDIV_SHIFT                                    0
#define UART1_BAUD_RATE_DIVIDER_REG0_BDIV_MASK                                     0x000000FFU

/*Baud Rate Clock Divisor Value: 0: Disables baud_sample 1: Clock divisor bypass (baud_sample = sel_clk) 2 - 65535: baud_sample*/
#undef UART1_BAUD_RATE_GEN_REG0_CD_DEFVAL 
#undef UART1_BAUD_RATE_GEN_REG0_CD_SHIFT 
#undef UART1_BAUD_RATE_GEN_REG0_CD_MASK 
#define UART1_BAUD_RATE_GEN_REG0_CD_DEFVAL                                         0x0000028B
#define UART1_BAUD_RATE_GEN_REG0_CD_SHIFT                                          0
#define UART1_BAUD_RATE_GEN_REG0_CD_MASK                                           0x0000FFFFU

/*Stop transmitter break: 0: no affect 1: stop transmission of the break after a minimum of one character length and transmit a
		high level during 12 bit periods. It can be set regardless of the value of STTBRK.*/
#undef UART1_CONTROL_REG0_STPBRK_DEFVAL 
#undef UART1_CONTROL_REG0_STPBRK_SHIFT 
#undef UART1_CONTROL_REG0_STPBRK_MASK 
#define UART1_CONTROL_REG0_STPBRK_DEFVAL                                           0x00000128
#define UART1_CONTROL_REG0_STPBRK_SHIFT                                            8
#define UART1_CONTROL_REG0_STPBRK_MASK                                             0x00000100U

/*Start transmitter break: 0: no affect 1: start to transmit a break after the characters currently present in the FIFO and the
		transmit shift register have been transmitted. It can only be set if STPBRK (Stop transmitter break) is not high.*/
#undef UART1_CONTROL_REG0_STTBRK_DEFVAL 
#undef UART1_CONTROL_REG0_STTBRK_SHIFT 
#undef UART1_CONTROL_REG0_STTBRK_MASK 
#define UART1_CONTROL_REG0_STTBRK_DEFVAL                                           0x00000128
#define UART1_CONTROL_REG0_STTBRK_SHIFT                                            7
#define UART1_CONTROL_REG0_STTBRK_MASK                                             0x00000080U

/*Restart receiver timeout counter: 1: receiver timeout counter is restarted. This bit is self clearing once the restart has co
		pleted.*/
#undef UART1_CONTROL_REG0_RSTTO_DEFVAL 
#undef UART1_CONTROL_REG0_RSTTO_SHIFT 
#undef UART1_CONTROL_REG0_RSTTO_MASK 
#define UART1_CONTROL_REG0_RSTTO_DEFVAL                                            0x00000128
#define UART1_CONTROL_REG0_RSTTO_SHIFT                                             6
#define UART1_CONTROL_REG0_RSTTO_MASK                                              0x00000040U

/*Transmit disable: 0: enable transmitter 1: disable transmitter*/
#undef UART1_CONTROL_REG0_TXDIS_DEFVAL 
#undef UART1_CONTROL_REG0_TXDIS_SHIFT 
#undef UART1_CONTROL_REG0_TXDIS_MASK 
#define UART1_CONTROL_REG0_TXDIS_DEFVAL                                            0x00000128
#define UART1_CONTROL_REG0_TXDIS_SHIFT                                             5
#define UART1_CONTROL_REG0_TXDIS_MASK                                              0x00000020U

/*Transmit enable: 0: disable transmitter 1: enable transmitter, provided the TXDIS field is set to 0.*/
#undef UART1_CONTROL_REG0_TXEN_DEFVAL 
#undef UART1_CONTROL_REG0_TXEN_SHIFT 
#undef UART1_CONTROL_REG0_TXEN_MASK 
#define UART1_CONTROL_REG0_TXEN_DEFVAL                                             0x00000128
#define UART1_CONTROL_REG0_TXEN_SHIFT                                              4
#define UART1_CONTROL_REG0_TXEN_MASK                                               0x00000010U

/*Receive disable: 0: enable 1: disable, regardless of the value of RXEN*/
#undef UART1_CONTROL_REG0_RXDIS_DEFVAL 
#undef UART1_CONTROL_REG0_RXDIS_SHIFT 
#undef UART1_CONTROL_REG0_RXDIS_MASK 
#define UART1_CONTROL_REG0_RXDIS_DEFVAL                                            0x00000128
#define UART1_CONTROL_REG0_RXDIS_SHIFT                                             3
#define UART1_CONTROL_REG0_RXDIS_MASK                                              0x00000008U

/*Receive enable: 0: disable 1: enable When set to one, the receiver logic is enabled, provided the RXDIS field is set to zero.*/
#undef UART1_CONTROL_REG0_RXEN_DEFVAL 
#undef UART1_CONTROL_REG0_RXEN_SHIFT 
#undef UART1_CONTROL_REG0_RXEN_MASK 
#define UART1_CONTROL_REG0_RXEN_DEFVAL                                             0x00000128
#define UART1_CONTROL_REG0_RXEN_SHIFT                                              2
#define UART1_CONTROL_REG0_RXEN_MASK                                               0x00000004U

/*Software reset for Tx data path: 0: no affect 1: transmitter logic is reset and all pending transmitter data is discarded Thi
		 bit is self clearing once the reset has completed.*/
#undef UART1_CONTROL_REG0_TXRES_DEFVAL 
#undef UART1_CONTROL_REG0_TXRES_SHIFT 
#undef UART1_CONTROL_REG0_TXRES_MASK 
#define UART1_CONTROL_REG0_TXRES_DEFVAL                                            0x00000128
#define UART1_CONTROL_REG0_TXRES_SHIFT                                             1
#define UART1_CONTROL_REG0_TXRES_MASK                                              0x00000002U

/*Software reset for Rx data path: 0: no affect 1: receiver logic is reset and all pending receiver data is discarded. This bit
		is self clearing once the reset has completed.*/
#undef UART1_CONTROL_REG0_RXRES_DEFVAL 
#undef UART1_CONTROL_REG0_RXRES_SHIFT 
#undef UART1_CONTROL_REG0_RXRES_MASK 
#define UART1_CONTROL_REG0_RXRES_DEFVAL                                            0x00000128
#define UART1_CONTROL_REG0_RXRES_SHIFT                                             0
#define UART1_CONTROL_REG0_RXRES_MASK                                              0x00000001U

/*Channel mode: Defines the mode of operation of the UART. 00: normal 01: automatic echo 10: local loopback 11: remote loopback*/
#undef UART1_MODE_REG0_CHMODE_DEFVAL 
#undef UART1_MODE_REG0_CHMODE_SHIFT 
#undef UART1_MODE_REG0_CHMODE_MASK 
#define UART1_MODE_REG0_CHMODE_DEFVAL                                              0x00000000
#define UART1_MODE_REG0_CHMODE_SHIFT                                               8
#define UART1_MODE_REG0_CHMODE_MASK                                                0x00000300U

/*Number of stop bits: Defines the number of stop bits to detect on receive and to generate on transmit. 00: 1 stop bit 01: 1.5
		stop bits 10: 2 stop bits 11: reserved*/
#undef UART1_MODE_REG0_NBSTOP_DEFVAL 
#undef UART1_MODE_REG0_NBSTOP_SHIFT 
#undef UART1_MODE_REG0_NBSTOP_MASK 
#define UART1_MODE_REG0_NBSTOP_DEFVAL                                              0x00000000
#define UART1_MODE_REG0_NBSTOP_SHIFT                                               6
#define UART1_MODE_REG0_NBSTOP_MASK                                                0x000000C0U

/*Parity type select: Defines the expected parity to check on receive and the parity to generate on transmit. 000: even parity 
		01: odd parity 010: forced to 0 parity (space) 011: forced to 1 parity (mark) 1xx: no parity*/
#undef UART1_MODE_REG0_PAR_DEFVAL 
#undef UART1_MODE_REG0_PAR_SHIFT 
#undef UART1_MODE_REG0_PAR_MASK 
#define UART1_MODE_REG0_PAR_DEFVAL                                                 0x00000000
#define UART1_MODE_REG0_PAR_SHIFT                                                  3
#define UART1_MODE_REG0_PAR_MASK                                                   0x00000038U

/*Character length select: Defines the number of bits in each character. 11: 6 bits 10: 7 bits 0x: 8 bits*/
#undef UART1_MODE_REG0_CHRL_DEFVAL 
#undef UART1_MODE_REG0_CHRL_SHIFT 
#undef UART1_MODE_REG0_CHRL_MASK 
#define UART1_MODE_REG0_CHRL_DEFVAL                                                0x00000000
#define UART1_MODE_REG0_CHRL_SHIFT                                                 1
#define UART1_MODE_REG0_CHRL_MASK                                                  0x00000006U

/*Clock source select: This field defines whether a pre-scalar of 8 is applied to the baud rate generator input clock. 0: clock
		source is uart_ref_clk 1: clock source is uart_ref_clk/8*/
#undef UART1_MODE_REG0_CLKS_DEFVAL 
#undef UART1_MODE_REG0_CLKS_SHIFT 
#undef UART1_MODE_REG0_CLKS_MASK 
#define UART1_MODE_REG0_CLKS_DEFVAL                                                0x00000000
#define UART1_MODE_REG0_CLKS_SHIFT                                                 0
#define UART1_MODE_REG0_CLKS_MASK                                                  0x00000001U

/*TrustZone Classification for ADMA*/
#undef LPD_SLCR_SECURE_SLCR_ADMA_TZ_DEFVAL 
#undef LPD_SLCR_SECURE_SLCR_ADMA_TZ_SHIFT 
#undef LPD_SLCR_SECURE_SLCR_ADMA_TZ_MASK 
#define LPD_SLCR_SECURE_SLCR_ADMA_TZ_DEFVAL                                        
#define LPD_SLCR_SECURE_SLCR_ADMA_TZ_SHIFT                                         0
#define LPD_SLCR_SECURE_SLCR_ADMA_TZ_MASK                                          0x000000FFU

/*CSU regsiter*/
#undef CSU_TAMPER_STATUS_TAMPER_0_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_0_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_0_MASK 
#define CSU_TAMPER_STATUS_TAMPER_0_DEFVAL                                          0x00000000
#define CSU_TAMPER_STATUS_TAMPER_0_SHIFT                                           0
#define CSU_TAMPER_STATUS_TAMPER_0_MASK                                            0x00000001U

/*External MIO*/
#undef CSU_TAMPER_STATUS_TAMPER_1_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_1_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_1_MASK 
#define CSU_TAMPER_STATUS_TAMPER_1_DEFVAL                                          0x00000000
#define CSU_TAMPER_STATUS_TAMPER_1_SHIFT                                           1
#define CSU_TAMPER_STATUS_TAMPER_1_MASK                                            0x00000002U

/*JTAG toggle detect*/
#undef CSU_TAMPER_STATUS_TAMPER_2_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_2_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_2_MASK 
#define CSU_TAMPER_STATUS_TAMPER_2_DEFVAL                                          0x00000000
#define CSU_TAMPER_STATUS_TAMPER_2_SHIFT                                           2
#define CSU_TAMPER_STATUS_TAMPER_2_MASK                                            0x00000004U

/*PL SEU error*/
#undef CSU_TAMPER_STATUS_TAMPER_3_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_3_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_3_MASK 
#define CSU_TAMPER_STATUS_TAMPER_3_DEFVAL                                          0x00000000
#define CSU_TAMPER_STATUS_TAMPER_3_SHIFT                                           3
#define CSU_TAMPER_STATUS_TAMPER_3_MASK                                            0x00000008U

/*AMS over temperature alarm for LPD*/
#undef CSU_TAMPER_STATUS_TAMPER_4_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_4_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_4_MASK 
#define CSU_TAMPER_STATUS_TAMPER_4_DEFVAL                                          0x00000000
#define CSU_TAMPER_STATUS_TAMPER_4_SHIFT                                           4
#define CSU_TAMPER_STATUS_TAMPER_4_MASK                                            0x00000010U

/*AMS over temperature alarm for APU*/
#undef CSU_TAMPER_STATUS_TAMPER_5_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_5_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_5_MASK 
#define CSU_TAMPER_STATUS_TAMPER_5_DEFVAL                                          0x00000000
#define CSU_TAMPER_STATUS_TAMPER_5_SHIFT                                           5
#define CSU_TAMPER_STATUS_TAMPER_5_MASK                                            0x00000020U

/*AMS voltage alarm for VCCPINT_FPD*/
#undef CSU_TAMPER_STATUS_TAMPER_6_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_6_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_6_MASK 
#define CSU_TAMPER_STATUS_TAMPER_6_DEFVAL                                          0x00000000
#define CSU_TAMPER_STATUS_TAMPER_6_SHIFT                                           6
#define CSU_TAMPER_STATUS_TAMPER_6_MASK                                            0x00000040U

/*AMS voltage alarm for VCCPINT_LPD*/
#undef CSU_TAMPER_STATUS_TAMPER_7_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_7_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_7_MASK 
#define CSU_TAMPER_STATUS_TAMPER_7_DEFVAL                                          0x00000000
#define CSU_TAMPER_STATUS_TAMPER_7_SHIFT                                           7
#define CSU_TAMPER_STATUS_TAMPER_7_MASK                                            0x00000080U

/*AMS voltage alarm for VCCPAUX*/
#undef CSU_TAMPER_STATUS_TAMPER_8_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_8_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_8_MASK 
#define CSU_TAMPER_STATUS_TAMPER_8_DEFVAL                                          0x00000000
#define CSU_TAMPER_STATUS_TAMPER_8_SHIFT                                           8
#define CSU_TAMPER_STATUS_TAMPER_8_MASK                                            0x00000100U

/*AMS voltage alarm for DDRPHY*/
#undef CSU_TAMPER_STATUS_TAMPER_9_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_9_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_9_MASK 
#define CSU_TAMPER_STATUS_TAMPER_9_DEFVAL                                          0x00000000
#define CSU_TAMPER_STATUS_TAMPER_9_SHIFT                                           9
#define CSU_TAMPER_STATUS_TAMPER_9_MASK                                            0x00000200U

/*AMS voltage alarm for PSIO bank 0/1/2*/
#undef CSU_TAMPER_STATUS_TAMPER_10_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_10_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_10_MASK 
#define CSU_TAMPER_STATUS_TAMPER_10_DEFVAL                                         0x00000000
#define CSU_TAMPER_STATUS_TAMPER_10_SHIFT                                          10
#define CSU_TAMPER_STATUS_TAMPER_10_MASK                                           0x00000400U

/*AMS voltage alarm for PSIO bank 3 (dedicated pins)*/
#undef CSU_TAMPER_STATUS_TAMPER_11_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_11_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_11_MASK 
#define CSU_TAMPER_STATUS_TAMPER_11_DEFVAL                                         0x00000000
#define CSU_TAMPER_STATUS_TAMPER_11_SHIFT                                          11
#define CSU_TAMPER_STATUS_TAMPER_11_MASK                                           0x00000800U

/*AMS voltaage alarm for GT*/
#undef CSU_TAMPER_STATUS_TAMPER_12_DEFVAL 
#undef CSU_TAMPER_STATUS_TAMPER_12_SHIFT 
#undef CSU_TAMPER_STATUS_TAMPER_12_MASK 
#define CSU_TAMPER_STATUS_TAMPER_12_DEFVAL                                         0x00000000
#define CSU_TAMPER_STATUS_TAMPER_12_SHIFT                                          12
#define CSU_TAMPER_STATUS_TAMPER_12_MASK                                           0x00001000U
#undef LPD_XPPU_CFG_MASTER_ID00_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID00_OFFSET                                            0XFF980100
#undef LPD_XPPU_CFG_MASTER_ID01_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID01_OFFSET                                            0XFF980104
#undef LPD_XPPU_CFG_MASTER_ID02_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID02_OFFSET                                            0XFF980108
#undef LPD_XPPU_CFG_MASTER_ID03_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID03_OFFSET                                            0XFF98010C
#undef LPD_XPPU_CFG_MASTER_ID04_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID04_OFFSET                                            0XFF980110
#undef LPD_XPPU_CFG_MASTER_ID05_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID05_OFFSET                                            0XFF980114
#undef LPD_XPPU_CFG_MASTER_ID06_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID06_OFFSET                                            0XFF980118
#undef LPD_XPPU_CFG_MASTER_ID07_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID07_OFFSET                                            0XFF98011C
#undef LPD_XPPU_CFG_MASTER_ID08_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID08_OFFSET                                            0XFF980120
#undef LPD_XPPU_CFG_MASTER_ID09_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID09_OFFSET                                            0XFF980124
#undef LPD_XPPU_CFG_MASTER_ID10_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID10_OFFSET                                            0XFF980128
#undef LPD_XPPU_CFG_MASTER_ID11_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID11_OFFSET                                            0XFF98012C
#undef LPD_XPPU_CFG_MASTER_ID12_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID12_OFFSET                                            0XFF980130
#undef LPD_XPPU_CFG_MASTER_ID13_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID13_OFFSET                                            0XFF980134
#undef LPD_XPPU_CFG_MASTER_ID14_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID14_OFFSET                                            0XFF980138
#undef LPD_XPPU_CFG_MASTER_ID15_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID15_OFFSET                                            0XFF98013C
#undef LPD_XPPU_CFG_MASTER_ID16_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID16_OFFSET                                            0XFF980140
#undef LPD_XPPU_CFG_MASTER_ID17_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID17_OFFSET                                            0XFF980144
#undef LPD_XPPU_CFG_MASTER_ID18_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID18_OFFSET                                            0XFF980148
#undef LPD_XPPU_CFG_MASTER_ID19_OFFSET 
#define LPD_XPPU_CFG_MASTER_ID19_OFFSET                                            0XFF98014C

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID00_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID00_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID00_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID00_MIDP_DEFVAL                                       0x83FF0040
#define LPD_XPPU_CFG_MASTER_ID00_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID00_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID00_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID00_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID00_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID00_MIDR_DEFVAL                                       0x83FF0040
#define LPD_XPPU_CFG_MASTER_ID00_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID00_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID00_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID00_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID00_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID00_MIDM_DEFVAL                                       0x83FF0040
#define LPD_XPPU_CFG_MASTER_ID00_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID00_MIDM_MASK                                         0x03FF0000U

/*Predefined Master ID for PMU*/
#undef LPD_XPPU_CFG_MASTER_ID00_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID00_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID00_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID00_MID_DEFVAL                                        0x83FF0040
#define LPD_XPPU_CFG_MASTER_ID00_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID00_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID01_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID01_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID01_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID01_MIDP_DEFVAL                                       0x03F00000
#define LPD_XPPU_CFG_MASTER_ID01_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID01_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID01_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID01_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID01_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID01_MIDR_DEFVAL                                       0x03F00000
#define LPD_XPPU_CFG_MASTER_ID01_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID01_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID01_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID01_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID01_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID01_MIDM_DEFVAL                                       0x03F00000
#define LPD_XPPU_CFG_MASTER_ID01_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID01_MIDM_MASK                                         0x03FF0000U

/*Predefined Master ID for RPU0*/
#undef LPD_XPPU_CFG_MASTER_ID01_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID01_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID01_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID01_MID_DEFVAL                                        0x03F00000
#define LPD_XPPU_CFG_MASTER_ID01_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID01_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID02_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID02_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID02_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID02_MIDP_DEFVAL                                       0x83F00010
#define LPD_XPPU_CFG_MASTER_ID02_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID02_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID02_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID02_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID02_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID02_MIDR_DEFVAL                                       0x83F00010
#define LPD_XPPU_CFG_MASTER_ID02_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID02_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID02_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID02_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID02_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID02_MIDM_DEFVAL                                       0x83F00010
#define LPD_XPPU_CFG_MASTER_ID02_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID02_MIDM_MASK                                         0x03FF0000U

/*Predefined Master ID for RPU1*/
#undef LPD_XPPU_CFG_MASTER_ID02_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID02_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID02_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID02_MID_DEFVAL                                        0x83F00010
#define LPD_XPPU_CFG_MASTER_ID02_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID02_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID03_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID03_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID03_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID03_MIDP_DEFVAL                                       0x83C00080
#define LPD_XPPU_CFG_MASTER_ID03_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID03_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID03_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID03_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID03_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID03_MIDR_DEFVAL                                       0x83C00080
#define LPD_XPPU_CFG_MASTER_ID03_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID03_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID03_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID03_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID03_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID03_MIDM_DEFVAL                                       0x83C00080
#define LPD_XPPU_CFG_MASTER_ID03_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID03_MIDM_MASK                                         0x03FF0000U

/*Predefined Master ID for APU*/
#undef LPD_XPPU_CFG_MASTER_ID03_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID03_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID03_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID03_MID_DEFVAL                                        0x83C00080
#define LPD_XPPU_CFG_MASTER_ID03_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID03_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID04_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID04_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID04_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID04_MIDP_DEFVAL                                       0x83C30080
#define LPD_XPPU_CFG_MASTER_ID04_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID04_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID04_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID04_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID04_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID04_MIDR_DEFVAL                                       0x83C30080
#define LPD_XPPU_CFG_MASTER_ID04_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID04_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID04_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID04_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID04_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID04_MIDM_DEFVAL                                       0x83C30080
#define LPD_XPPU_CFG_MASTER_ID04_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID04_MIDM_MASK                                         0x03FF0000U

/*Predefined Master ID for A53 Core 0*/
#undef LPD_XPPU_CFG_MASTER_ID04_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID04_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID04_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID04_MID_DEFVAL                                        0x83C30080
#define LPD_XPPU_CFG_MASTER_ID04_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID04_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID05_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID05_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID05_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID05_MIDP_DEFVAL                                       0x03C30081
#define LPD_XPPU_CFG_MASTER_ID05_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID05_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID05_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID05_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID05_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID05_MIDR_DEFVAL                                       0x03C30081
#define LPD_XPPU_CFG_MASTER_ID05_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID05_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID05_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID05_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID05_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID05_MIDM_DEFVAL                                       0x03C30081
#define LPD_XPPU_CFG_MASTER_ID05_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID05_MIDM_MASK                                         0x03FF0000U

/*Predefined Master ID for A53 Core 1*/
#undef LPD_XPPU_CFG_MASTER_ID05_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID05_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID05_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID05_MID_DEFVAL                                        0x03C30081
#define LPD_XPPU_CFG_MASTER_ID05_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID05_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID06_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID06_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID06_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID06_MIDP_DEFVAL                                       0x03C30082
#define LPD_XPPU_CFG_MASTER_ID06_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID06_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID06_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID06_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID06_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID06_MIDR_DEFVAL                                       0x03C30082
#define LPD_XPPU_CFG_MASTER_ID06_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID06_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID06_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID06_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID06_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID06_MIDM_DEFVAL                                       0x03C30082
#define LPD_XPPU_CFG_MASTER_ID06_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID06_MIDM_MASK                                         0x03FF0000U

/*Predefined Master ID for A53 Core 2*/
#undef LPD_XPPU_CFG_MASTER_ID06_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID06_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID06_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID06_MID_DEFVAL                                        0x03C30082
#define LPD_XPPU_CFG_MASTER_ID06_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID06_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID07_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID07_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID07_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID07_MIDP_DEFVAL                                       0x83C30083
#define LPD_XPPU_CFG_MASTER_ID07_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID07_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID07_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID07_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID07_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID07_MIDR_DEFVAL                                       0x83C30083
#define LPD_XPPU_CFG_MASTER_ID07_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID07_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID07_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID07_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID07_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID07_MIDM_DEFVAL                                       0x83C30083
#define LPD_XPPU_CFG_MASTER_ID07_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID07_MIDM_MASK                                         0x03FF0000U

/*Predefined Master ID for A53 Core 3*/
#undef LPD_XPPU_CFG_MASTER_ID07_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID07_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID07_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID07_MID_DEFVAL                                        0x83C30083
#define LPD_XPPU_CFG_MASTER_ID07_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID07_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID08_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID08_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID08_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID08_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID08_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID08_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID08_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID08_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID08_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID08_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID08_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID08_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID08_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID08_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID08_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID08_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID08_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID08_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID08_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID08_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID08_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID08_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID08_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID08_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID09_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID09_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID09_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID09_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID09_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID09_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID09_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID09_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID09_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID09_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID09_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID09_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID09_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID09_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID09_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID09_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID09_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID09_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID09_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID09_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID09_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID09_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID09_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID09_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID10_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID10_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID10_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID10_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID10_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID10_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID10_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID10_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID10_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID10_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID10_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID10_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID10_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID10_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID10_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID10_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID10_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID10_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID10_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID10_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID10_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID10_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID10_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID10_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID11_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID11_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID11_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID11_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID11_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID11_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID11_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID11_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID11_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID11_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID11_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID11_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID11_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID11_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID11_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID11_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID11_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID11_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID11_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID11_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID11_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID11_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID11_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID11_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID12_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID12_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID12_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID12_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID12_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID12_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID12_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID12_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID12_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID12_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID12_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID12_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID12_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID12_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID12_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID12_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID12_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID12_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID12_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID12_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID12_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID12_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID12_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID12_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID13_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID13_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID13_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID13_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID13_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID13_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID13_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID13_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID13_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID13_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID13_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID13_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID13_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID13_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID13_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID13_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID13_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID13_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID13_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID13_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID13_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID13_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID13_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID13_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID14_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID14_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID14_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID14_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID14_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID14_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID14_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID14_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID14_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID14_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID14_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID14_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID14_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID14_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID14_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID14_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID14_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID14_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID14_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID14_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID14_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID14_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID14_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID14_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID15_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID15_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID15_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID15_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID15_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID15_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID15_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID15_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID15_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID15_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID15_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID15_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID15_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID15_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID15_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID15_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID15_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID15_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID15_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID15_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID15_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID15_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID15_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID15_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID16_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID16_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID16_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID16_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID16_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID16_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID16_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID16_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID16_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID16_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID16_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID16_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID16_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID16_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID16_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID16_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID16_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID16_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID16_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID16_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID16_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID16_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID16_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID16_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID17_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID17_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID17_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID17_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID17_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID17_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID17_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID17_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID17_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID17_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID17_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID17_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID17_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID17_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID17_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID17_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID17_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID17_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID17_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID17_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID17_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID17_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID17_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID17_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID18_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID18_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID18_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID18_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID18_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID18_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID18_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID18_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID18_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID18_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID18_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID18_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID18_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID18_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID18_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID18_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID18_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID18_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID18_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID18_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID18_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID18_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID18_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID18_MID_MASK                                          0x000003FFU

/*Parity of all non-reserved fields (i.e. MIDR, MIDM, MID)*/
#undef LPD_XPPU_CFG_MASTER_ID19_MIDP_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID19_MIDP_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID19_MIDP_MASK 
#define LPD_XPPU_CFG_MASTER_ID19_MIDP_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID19_MIDP_SHIFT                                        31
#define LPD_XPPU_CFG_MASTER_ID19_MIDP_MASK                                         0x80000000U

/*If set, only read transactions are allowed for the masters matching this register*/
#undef LPD_XPPU_CFG_MASTER_ID19_MIDR_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID19_MIDR_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID19_MIDR_MASK 
#define LPD_XPPU_CFG_MASTER_ID19_MIDR_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID19_MIDR_SHIFT                                        30
#define LPD_XPPU_CFG_MASTER_ID19_MIDR_MASK                                         0x40000000U

/*Mask to be applied before comparing*/
#undef LPD_XPPU_CFG_MASTER_ID19_MIDM_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID19_MIDM_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID19_MIDM_MASK 
#define LPD_XPPU_CFG_MASTER_ID19_MIDM_DEFVAL                                       0x00000000
#define LPD_XPPU_CFG_MASTER_ID19_MIDM_SHIFT                                        16
#define LPD_XPPU_CFG_MASTER_ID19_MIDM_MASK                                         0x03FF0000U

/*Programmable Master ID*/
#undef LPD_XPPU_CFG_MASTER_ID19_MID_DEFVAL 
#undef LPD_XPPU_CFG_MASTER_ID19_MID_SHIFT 
#undef LPD_XPPU_CFG_MASTER_ID19_MID_MASK 
#define LPD_XPPU_CFG_MASTER_ID19_MID_DEFVAL                                        0x00000000
#define LPD_XPPU_CFG_MASTER_ID19_MID_SHIFT                                         0
#define LPD_XPPU_CFG_MASTER_ID19_MID_MASK                                          0x000003FFU
#ifdef __cplusplus
extern "C" {
#endif
 int psu_int (); 
#ifdef __cplusplus
}
#endif
