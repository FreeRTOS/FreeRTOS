/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Interface for Real Time Clock calibration (RTC) .
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

const RTC_PPMLookup PPM_Lookup[] =
{
  /* Tmp  PPM  Neg Hi  Correction */
	{-40, -168 ,0, 1 ,22 },
	{-39, -163 ,0, 1 ,23 },
	{-38, -158 ,0, 1 ,24 },
	{-37, -153 ,0, 1 ,25 },
	{-36, -148 ,0, 1 ,25 },
	{-35, -143 ,0, 1 ,26 },
	{-34, -138 ,0, 1 ,27 },
	{-33, -134 ,0, 1 ,28 },
	{-32, -129 ,0, 1 ,29 },
	{-31, -124 ,0, 1 ,31 },
	{-30, -120 ,0, 1 ,32 },
	{-29, -116 ,0, 1 ,33 },
	{-28, -111 ,0, 1 ,34 },
	{-27, -107 ,0, 1 ,36 },
	{-26, -103 ,0, 1 ,37 },
	{-25, -99,  0, 1 ,38 },
	{-24, -95,  0, 1 ,40 },
	{-23, -91,  0, 1 ,42 },
	{-22, -87,  0, 1 ,44 },
	{-21, -84,  0, 1 ,45 },
	{-20, -80,  0, 1 ,48 },
	{-19, -76,  0, 1 ,50 },
	{-18, -73,  0, 1 ,53 },
	{-17, -70,  0, 1 ,55 },
	{-16, -66,  0, 1 ,58 },
	{-15, -63,  0, 1 ,61 },
	{-14, -60,  0, 1 ,64 },
	{-13, -57,  0, 1 ,68 },
	{-12, -54,  0, 1 ,71 },
	{-11, -51,  0, 1 ,76 },
	{-10, -48,  0, 1 ,80 },
	{-9 ,-45 ,  0, 1 ,86 },
	{-8 ,-43 ,  0, 1 ,90 },
	{-7 ,-40 ,  0, 1 ,97 },
	{-6 ,-37 ,  0, 1 ,105},
	{-5 ,-35 ,  0, 1 ,111},
	{-4 ,-33 ,  0, 1 ,117},
	{-3 ,-30 ,  0, 0 ,6  },
	{-2 ,-28 ,  0, 0 ,6  },
	{-1 ,-26 ,  0, 0 ,7  },
	{0 ,-24 ,   0, 0 ,7  },
	{1 ,-22 ,   0, 0 ,8  },
	{2 ,-20 ,   0, 0 ,9  },
	{3 ,-18 ,   0, 0 ,10 },
	{4 ,-17 ,   0, 0 ,10 },
	{5 ,-15 ,   0, 0 ,12 },
	{6 ,-13 ,   0, 0 ,14 },
	{7 ,-12 ,   0, 0 ,15 },
	{8 ,-11 ,   0, 0 ,17 },
	{9 ,-9 ,    0, 0 ,21 },
	{10 ,-8 ,   0, 0 ,23 },
	{11 ,-7 ,   0, 0 ,27 },
	{12 ,-6 ,   0, 0 ,32 },
	{13 ,-5 ,   0, 0 ,38 },
	{14 ,-4 ,   0, 0 ,48 },
	{15 ,-3 ,   0, 0 ,64 },
	{16 ,-2 ,   0, 0 ,97 },
	{17 ,-2 ,   0, 0 ,97 },
	{18 ,-1 ,   0, 0 ,127},
	{19 ,0,     1, 0 ,0  },
	{20 ,0,     1, 0 ,0  },
	{21 ,0,     1, 0 ,0  },
	{22 ,1,     1, 0 ,127},
	{23 ,1,     1, 0 ,127},
	{24 ,1,     1, 0 ,127},
	{25 ,1,     1, 0 ,127},
	{26 ,1,     1, 0 ,127},
	{27 ,1,     1, 0 ,127},
	{28 ,1,     1, 0 ,127},
	{29 ,0,     1, 0 ,0  },
	{30 ,0,     1, 0 ,0  },
	{31 ,0,     1, 0 ,0  },
	{32 ,-1,    0, 0 ,127},
	{33 ,-2,    0, 0 ,97 },
	{34 ,-2,    0, 0 ,97 },
	{35 ,-3,    0, 0 ,64 },
	{36 ,-4,    0, 0 ,48 },
	{37 ,-5,    0, 0 ,38 },
	{38 ,-6,    0, 0 ,32 },
	{39 ,-7,    0, 0 ,27 },
	{40 ,-8,    0, 0 ,23 },
	{41 ,-9,    0, 0 ,21 },
	{42 ,-11 ,  0, 0 ,17 },
	{43 ,-12 ,  0, 0 ,15 },
	{44 ,-13 ,  0, 0 ,14 },
	{45 ,-15 ,  0, 0 ,12 },
	{46 ,-17 ,  0, 0 ,10 },
	{47 ,-18 ,  0, 0 ,10 },
	{48 ,-20 ,  0, 0 ,9  },
	{49 ,-22 ,  0, 0 ,8  },
	{50 ,-24 ,  0, 0 ,7  },
	{51 ,-26 ,  0, 0 ,7  },
	{52 ,-28 ,  0, 0 ,6  },
	{53 ,-30 ,  0, 0 ,6  },
	{54 ,-33 ,  0, 1 ,117},
	{55 ,-35 ,  0, 1 ,111},
	{56 ,-37 ,  0, 1 ,105},
	{57 ,-40 ,  0, 1 ,97 },
	{58 ,-43 ,  0, 1 ,90 },
	{59 ,-45 ,  0, 1 ,86 },
	{60 ,-48 ,  0, 1 ,80 },
	{61 ,-51 ,  0, 1 ,76 },
	{62 ,-54 ,  0, 1 ,71 },
	{63 ,-57 ,  0, 1 ,68 },
	{64 ,-60 ,  0, 1 ,64 },
	{65 ,-63 ,  0, 1 ,61 },
	{66 ,-66 ,  0, 1 ,58 },
	{67 ,-70 ,  0, 1 ,55 },
	{68 ,-73 ,  0, 1 ,53 },
	{69 ,-76 ,  0, 1 ,50 },
	{70 ,-80 ,  0, 1 ,48 },
	{71 ,-84 ,  0, 1 ,45 },
	{72 ,-87 ,  0, 1 ,44 },
	{73 ,-91 ,  0, 1 ,42 },
	{74 ,-95 ,  0, 1 ,40 },
	{75 ,-99 ,  0, 1 ,38 },
	{76 ,-103 , 0, 1 ,37 },
	{77 ,-107 , 0, 1 ,36 },
	{78 ,-111 , 0, 1 ,34 },
	{79 ,-116 , 0, 1 ,33 },
	{80 ,-120 , 0, 1 ,32 },
	{81 ,-124 , 0, 1 ,31 },
	{82 ,-129 , 0, 1 ,29 },
	{83 ,-134 , 0, 1 ,28 },
	{84 ,-138 , 0, 1 ,27 },
	{85 ,-143 , 0, 1 ,26 }
};

/**
 * \brief RTC calibration for Temperature or PPM drift
 */
extern void RTC_ClockCalibration( Rtc* pRtc, int32_t CurrentTempr)
{
	uint16_t i;
	uint32_t MR_Reg, Size;
  
	Size = sizeof(PPM_Lookup);
  
	MR_Reg = 0;
	for(i=0; i< Size; i++) {
		if(PPM_Lookup[i].Tempr == CurrentTempr) {
			MR_Reg |= RTC_MR_CORRECTION(PPM_Lookup[i].CORRECTION);
			MR_Reg |= (PPM_Lookup[i].HIGHPPM << 15);
			MR_Reg |= (PPM_Lookup[i].NEGPPM << 4);
			pRtc->RTC_MR = MR_Reg;    // update the calibration value
			break;
		}
	}
}
