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
 * Implementation WM8904 driver.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

/*----------------------------------------------------------------------------
 *        Type
 *----------------------------------------------------------------------------*/
typedef struct {
				uint16_t value;
				uint8_t address;
		}WM8904_PARA;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Read data from WM8904 Register.
 *
 * \param pTwid   Pointer to twi driver structure
 * \param device  Twi slave address.
 * \param regAddr Register address to read.
 * \return value in the given register.
 */
uint16_t WM8904_Read(Twid *pTwid,
		uint32_t device,
		uint32_t regAddr)
{
	uint16_t bitsDataRegister;
	uint8_t Tdata[2]={0,0};

	TWID_Read(pTwid, device, regAddr, 1, Tdata, 2, 0);
	bitsDataRegister = (Tdata[0] << 8) | Tdata[1];
	return bitsDataRegister;
}

/**
 * \brief  Write data to WM8904 Register.
 *
 * \param pTwid   Pointer to twi driver structure
 * \param device  Twi slave address.
 * \param regAddr Register address to read.
 * \param data    Data to write
 */
void WM8904_Write(Twid *pTwid,
		uint32_t device,
		uint32_t regAddr,
		uint16_t data)
{
	uint8_t tmpData[2];

	tmpData[0] = (data & 0xff00) >> 8;
	tmpData[1] = data & 0xff;
	TWID_Write(pTwid, device, regAddr, 1, tmpData, 2, 0);
}

static WM8904_PARA wm8904_access_slow[]=
{ 
	{ 0x0000, 0},         /** R0   - SW Reset and ID */ 
	{ 0x001A, 4},         /** R4   - Bias Control 0 */ 
	{ 0x0047, 5},         /** R5   - VMID Control 0 */     /*insert_delay_ms 5*/

	{ 0x0043, 5},         /** R5   - VMID Control 0 */ 
	{ 0x000B, 4},         /** R4   - Bias Control 0 */ 

	{ 0x0003, 0x0C},      /** R12  - Power Management 0 CC */ 

	{ 0x0003, 0x0E},      /** R14  - Power Management 2 */ 
	{ 0x000C, 0x12},      /** R18  - Power Management 6 */
	{ 0x0000, 0x21},      /** R33  - DAC Digital 1 */ 
	{ 0x0000, 0x3D},      /** R61  - Analogue OUT12 ZC */ 
	{ 0x0001, 0x62},      /** R98  - Charge Pump 0 */ 
	{ 0x0005, 0x68},     /** R104 - Class W 0 */ 

	//FLL setting,32.768KHZ MCLK input,12.288M output.
	{ 0x0000, 0x74},     /** R116 - FLL Control 1 */ 
	{ 0x0704, 0x75},     /** R117 - FLL Control 2 */ 
	{ 0x8000, 0x76},     /** R118 - FLL Control 3 */ 
	{ 0x1760, 0x77},     /** R119 - FLL Control 4 */ 
	{ 0x0005, 0x74},     /** R116 - FLL Control 1 */     /*insert_delay_ms 5*/

	{ 0x0C05, 0x15},      /** R21  - Clock Rates 1 */ 
	{ 0x845E, 0x14},      /** R20  - Clock Rates 0 */     
	{ 0x4006, 0x16},      /** R22  - Clock Rates 2 */

	//WM8904 IIS master
	//BCLK=12.288MHz/8=1.536MHz
	//LRCK=1.536MHz/32=48KHz
	//{ 0x0042, 0x18},    /** R24  - Audio Interface 0 */ 
	{ 0x0042, 0x19},      /** R25  - Audio Interface 1 */ 
	{ 0x00E8, 0x1A},      /** R26  - Audio Interface 2 */ 
	{ 0x0820, 0x1B},      /** R27  - Audio Interface 3 */ 
	////////////////ADC

	{ 0x0003, 0x0C},      /** R12  - Power Management 0 */ 
	{ 0x000F, 0x12},      /** R18  - Power Management 6 */     /*insert_delay_ms 5*/

	{ 0x0010, 0x2C},      /** R44  - Analogue Left Input 0 */ 
	{ 0x0010, 0x2D},      /** R45  - Analogue Right Input 0 */ 
	{ 0x0044, 0x2E},      /** R46  - Analogue Left Input 1 */ 
	{ 0x0044, 0x2F},      /** R47  - Analogue Right Input 1 */

	{ 0x0011, 0x5A},      /** R90  - Analogue HP 0 */ 
	{ 0x0033, 0x5A},      /** R90  - Analogue HP 0 */ 

	{ 0x000F, 0x43},      /** R67  - DC Servo 0 */ 
	{ 0x00F0, 0x44},      /** R68  - DC Servo 1 */     /*insert_delay_ms 100*/

	{ 0x0077, 0x5A},      /** R90  - Analogue HP 0 */ 
	{ 0x00FF, 0x5A},      /** R90  - Analogue HP 0 */ 
	{ 0x00B9, 0x39},      /** R57  - Analogue OUT1 Left */ 
	{ 0x00B9, 0x3A},      /** R58  - Analogue OUT1 Right */  
};

static WM8904_PARA wm8904_access_main[] = 
{ 
	//{ 0x8904, 0}, /** R0   - SW Reset and ID */ 
	//{ 0x0000, 1}, /** R1   - Revision */ 
	//{ 0x0000, 2}, /** R2 */ 
	//{ 0x0000, 3}, /** R3 */ 
	{ 0x0019, 4},   /** R4   - Bias Control 0 */ 
	{ 0x0043, 5},   /** R5   - VMID Control 0 */ 
	//{ 0x0003, 6},   /** R6   - Mic Bias Control 0 */ 
	//{ 0xC000, 7},   /** R7   - Mic Bias Control 1 */ 
	//{ 0x001E, 8},   /** R8   - Analogue DAC 0 */ 
	//{ 0xFFFF, 9},   /** R9   - mic Filter Control */ 
	//{ 0x0001, 10},  /** R10  - Analogue ADC 0 */ 
	//{ 0x0000, 11},  /** R11 */ 
	{ 0x0003, 12},  /** R12  - Power Management 0 */ 
	//{ 0x0000, 13},  /** R13 */ 
	{ 0x0003, 14},  /** R14  - Power Management 2 */ 
	//{ 0x0003, 15},  /** R15  - Power Management 3 */ 
	//{ 0x0000, 16},  /** R16 */ 
	//{ 0x0000, 17},  /** R17 */ 
	{ 0x000F, 18},  /** R18  - Power Management 6 */ 
	//{ 0x0000, 19},  /** R19 */ 
	{ 0x845E, 20},  /** R20  - Clock Rates 0 */ 
	//{ 0x3C07, 21},  /** R21  - Clock Rates 1 */ 
	{ 0x0006, 22},  /** R22  - Clock Rates 2 */ 
	//{ 0x0000, 23},  /** R23 */ 
	//{ 0x1FFF, 24},  /** R24  - Audio Interface 0 */ 
	{ 0x404A, 25},  /** R25  - Audio Interface 1 */ 
	//{ 0x0004, 26},  /** R26  - Audio Interface 2 */ 
	{ 0x0840, 27},  /** R27  - Audio Interface 3 */ 
	//{ 0x0000, 28},  /** R28 */ 
	//{ 0x0000, 29},  /** R29 */ 
	//{ 0x00FF, 30},  /** R30  - DAC Digital Volume Left */ 
	//{ 0x00FF, 31},  /** R31  - DAC Digital Volume Right */ 
	//{ 0x0FFF, 32},  /** R32  - DAC Digital 0 */ 
	{ 0x0000, 33},  /** R33  - DAC Digital 1 */ 
	//{ 0x0000, 34},  /** R34 */ 
	//{ 0x0000, 35},  /** R35 */ 
	//{ 0x00FF, 36},  /** R36  - ADC Digital Volume Left */ 
	//{ 0x00FF, 37},  /** R37  - ADC Digital Volume Right */ 
	//{ 0x0073, 38},  /** R38  - ADC Digital 0 */ 
	//{ 0x1800, 39},  /** R39  - Digital Microphone 0 */ 
	//{ 0xDFEF, 40},  /** R40  - DRC 0 */ 
	//{ 0xFFFF, 41},  /** R41  - DRC 1 */ 
	//{ 0x003F, 42},  /** R42  - DRC 2 */ 
	//{ 0x07FF, 43},  /** R43  - DRC 3 */ 
	{ 0x0005, 44},  /** R44  - Analogue Left Input 0 */ 
	{ 0x0005, 45},  /** R45  - Analogue Right Input 0 */ 
	{ 0x0000, 46},  /** R46  - Analogue Left Input 1 */ 
	{ 0x0000, 47},  /** R47  - Analogue Right Input 1 */ 
	//{ 0x0000, 48},  /** R48 */ 
	//{ 0x0000, 49},  /** R49 */ 
	//{ 0x0000, 50},  /** R50 */ 
	//{ 0x0000, 51},  /** R51 */ 
	//{ 0x0000, 52},  /** R52 */ 
	//{ 0x0000, 53},  /** R53 */ 
	//{ 0x0000, 54},  /** R54 */ 
	//{ 0x0000, 55},  /** R55 */ 
	//{ 0x0000, 56},  /** R56 */ 
	//{ 0x017F, 57},  /** R57  - Analogue OUT1 Left */ 
	{ 0x00AD, 58},  /** R58  - Analogue OUT1 Right */ 
	//{ 0x017F, 59},  /** R59  - Analogue OUT2 Left */ 
	//{ 0x017F, 60},  /** R60  - Analogue OUT2 Right */ 
	//{ 0x000F, 61},  /** R61  - Analogue OUT12 ZC */ 
	//{ 0x0000, 62},  /** R62 */ 
	//{ 0x0000, 63},  /** R63 */ 
	//{ 0x0000, 64},  /** R64 */ 
	//{ 0x0000, 65},  /** R65 */ 
	//{ 0x0000, 66},  /** R66 */ 
	{ 0x0003, 67},  /** R67  - DC Servo 0 */ 
	//{ 0xFFFF, 68},  /** R68  - DC Servo 1 */ 
	//{ 0x0F0F, 69},  /** R69  - DC Servo 2 */ 
	//{ 0x0000, 70},  /** R70 */ 
	//{ 0x007F, 71},  /** R71  - DC Servo 4 */ 
	//{ 0x007F, 72},  /** R72  - DC Servo 5 */ 
	//{ 0x00FF, 73},  /** R73  - DC Servo 6 */ 
	//{ 0x00FF, 74},  /** R74  - DC Servo 7 */ 
	//{ 0x00FF, 75},  /** R75  - DC Servo 8 */ 
	//{ 0x00FF, 76},  /** R76  - DC Servo 9 */ 
	//{ 0x0FFF, 77},  /** R77  - DC Servo Readback 0 */ 
	//{ 0x0000, 78},  /** R78 */ 
	//{ 0x0000, 79},  /** R79 */ 
	//{ 0x0000, 80},  /** R80 */ 
	//{ 0x0000, 81},  /** R81 */ 
	//{ 0x0000, 82},  /** R82 */ 
	//{ 0x0000, 83},  /** R83 */ 
	//{ 0x0000, 84},  /** R84 */ 
	//{ 0x0000, 85},  /** R85 */ 
	//{ 0x0000, 86},  /** R86 */ 
	//{ 0x0000, 87},  /** R87 */ 
	//{ 0x0000, 88},  /** R88 */ 
	//{ 0x0000, 89},  /** R89 */ 
	{ 0x00FF, 90},  /** R90  - Analogue HP 0 */ 
	//{ 0x0000, 91},  /** R91 */ 
	//{ 0x0000, 92},  /** R92 */ 
	//{ 0x0000, 93},  /** R93 */ 
	//{ 0x00FF, 94},  /** R94  - Analogue Lineout 0 */ 
	//{ 0x0000, 95},  /** R95 */ 
	//{ 0x0000, 96},  /** R96 */ 
	//{ 0x0000, 97},  /** R97 */ 
	{ 0x0001, 98},  /** R98  - Charge Pump 0 */ 
	//{ 0x0000, 99},  /** R99 */ 
	//{ 0x0000, 100}, /** R100 */
	//{ 0x0000, 101}, /** R101 */ 
	//{ 0x0000, 102}, /** R102 */ 
	//{ 0x0000, 103}, /** R103 */ 
	{ 0x0005, 104}, /** R104 - Class W 0 */ 
	//{ 0x0000, 105}, /** R105 */ 
	//{ 0x0000, 106}, /** R106 */ 
	//{ 0x0000, 107}, /** R107 */ 
	//{ 0x011F, 108}, /** R108 - Write Sequencer 0 */ 
	//{ 0x7FFF, 109}, /** R109 - Write Sequencer 1 */ 
	//{ 0x4FFF, 110}, /** R110 - Write Sequencer 2 */ 
	//{ 0x003F, 111}, /** R111 - Write Sequencer 3 */ 
	//{ 0x03F1, 112}, /** R112 - Write Sequencer 4 */ 
	//{ 0x0000, 113}, /** R113 */ 
	//{ 0x0000, 114}, /** R114 */ 
	//{ 0x0000, 115}, /** R115 */ 
	{ 0x0004, 116}, /** R116 - FLL Control 1 */ 
	{ 0x0704, 117}, /** R117 - FLL Control 2 */ 
	{ 0x8000, 118}, /** R118 - FLL Control 3 */ 
	{ 0x1760, 119}, /** R119 - FLL Control 4 */ 
	//{ 0x001B, 120}, /** R120 - FLL Control 5 */ 
	//{ 0x0014, 121}, /** R121 - GPIO Control 1 */ 
	//{ 0x0010, 122}, /** R122 - GPIO Control 2 */ 
	//{ 0x0010, 123}, /** R123 - GPIO Control 3 */ 
	//{ 0x0000, 124}, /** R124 - GPIO Control 4 */ 
	//{ 0x0000, 125}, /** R125 */ 
	//{ 0x000A, 126}, /** R126 - Digital Pulls */ 
	//{ 0x07FF, 127}, /** R127 - Interrupt Status */ 
	//{ 0x03FF, 128}, /** R128 - Interrupt Status Mask */ 
	//{ 0x03FF, 129}, /** R129 - Interrupt Polarity */ 
	//{ 0x03FF, 130}, /** R130 - Interrupt Debounce */
	//{ 0x0000, 131}, /** R131 */ 
	//{ 0x0000, 132}, /** R132 */ 
	//{ 0x0000, 133}, /** R133 */ 
	//{ 0x0001, 134}, /** R134 - EQ1 */ 
	//{ 0x001F, 135}, /** R135 - EQ2 */ 
	//{ 0x001F, 136}, /** R136 - EQ3 */ 
	//{ 0x001F, 137}, /** R137 - EQ4 */ 
	//{ 0x001F, 138}, /** R138 - EQ5 */ 
	//{ 0x001F, 139}, /** R139 - EQ6 */ 
	//{ 0xFFFF, 140}, /** R140 - EQ7 */ 
	//{ 0xFFFF, 141}, /** R141 - EQ8 */ 
	//{ 0xFFFF, 142}, /** R142 - EQ9 */ 
	//{ 0xFFFF, 143}, /** R143 - EQ10 */ 
	//{ 0xFFFF, 144}, /** R144 - EQ11 */ 
	//{ 0xFFFF, 145}, /** R145 - EQ12 */ 
	//{ 0xFFFF, 146}, /** R146 - EQ13 */ 
	//{ 0xFFFF, 147}, /** R147 - EQ14 */ 
	//{ 0xFFFF, 148}, /** R148 - EQ15 */ 
	//{ 0xFFFF, 149}, /** R149 - EQ16 */ 
	//{ 0xFFFF, 150}, /** R150 - EQ17 */ 
	//{ 0xFFFF, 151}, /** R151wm8523_dai - EQ18 */ 
	//{ 0xFFFF, 152}, /** R152 - EQ19 */ 
	//{ 0xFFFF, 153}, /** R153 - EQ20 */ 
	//{ 0xFFFF, 154}, /** R154 - EQ21 */ 
	//{ 0xFFFF, 155}, /** R155 - EQ22 */ 
	//{ 0xFFFF, 156}, /** R156 - EQ23 */ 
	//{ 0xFFFF, 157}, /** R157 - EQ24 */ 
	//{ 0x0000, 158}, /** R158 */ 
	//{ 0x0000, 159}, /** R159 */ 
	//{ 0x0000, 160}, /** R160 */ 
	//{ 0x0002, 161}, /** R161 - Control Interface Test 1 */ 
	//{ 0x0000, 162}, /** R162 */ 
	//{ 0x0000, 163}, /** R163 */ 
	//{ 0x0000, 164}, /** R164 */ 
	//{ 0x0000, 165}, /** R165 */ 
	//{ 0x0000, 166}, /** R166 */ 
	//{ 0x0000, 167}, /** R167 */ 
	//{ 0x0000, 168}, /** R168 */ 
	//{ 0x0000, 169}, /** R169 */ 
	//{ 0x0000, 170}, /** R170 */ 
	//{ 0x0000, 171}, /** R171 */ 
	//{ 0x0000, 172}, /** R172 */ 
	//{ 0x0000, 173}, /** R173 */ 
	//{ 0x0000, 174}, /** R174 */ 
	//{ 0x0000, 175}, /** R175 */ 
	//{ 0x0000, 176}, /** R176 */ 
	//{ 0x0000, 177}, /** R177 */ 
	//{ 0x0000, 178}, /** R178 */ 
	//{ 0x0000, 179}, /** R179 */ 
	//{ 0x0000, 180}, /** R180 */ 
	//{ 0x0000, 181}, /** R181 */ 
	//{ 0x0000, 182}, /** R182 */ 
	//{ 0x0000, 183}, /** R183 */ 
	//{ 0x0000, 184}, /** R184 */ 
	//{ 0x0000, 185}, /** R185 */ 
	//{ 0x0000, 186}, /** R186 */ 
	//{ 0x0000, 187}, /** R187 */ 
	//{ 0x0000, 188}, /** R188 */ 
	//{ 0x0000, 189}, /** R189 */ 
	//{ 0x0000, 190}, /** R190 */ 
	//{ 0x0000, 191}, /** R191 */ 
	//{ 0x0000, 192}, /** R192 */ 
	//{ 0x0000, 193}, /** R193 */ 
	//{ 0x0000, 194}, /** R194 */ 
	//{ 0x0000, 195}, /** R195 */ 
	//{ 0x0000, 196}, /** R196 */ 
	//{ 0x0000, 197}, /** R197 */ 
	//{ 0x0000, 198}, /** R198 */ 
	//{ 0x0000, 199}, /** R199 */ 
	//{ 0x0000, 200}, /** R200 */ 
	//{ 0x0000, 201}, /** R201 */ 
	//{ 0x0000, 202}, /** R202 */ 
	//{ 0x0000, 203}, /** R203 */ 
	//{ 0x0070, 204}, /** R204 - Analogue Output Bias 0 */ 
	//{ 0x0000, 205}, /** R205 */ 
	//{ 0x0000, 206}, /** R206 */ 
	//{ 0x0000, 207}, /** R207 */ 
	//{ 0x0000, 208}, /** R208 */ 
	//{ 0x0000, 209}, /** R209 */ 
	//{ 0x0000, 210}, /** R210 */ 
	//{ 0x0000, 211}, /** R211 */ 
	//{ 0x0000, 212}, /** R212 */ 
	//{ 0x0000, 213}, /** R213 */ 
	//{ 0x0000, 214}, /** R214 */ 
	//{ 0x0000, 215}, /** R215 */ 
	//{ 0x0000, 216}, /** R216 */ 
	//{ 0x0000, 217}, /** R217 */ 
	//{ 0x0000, 218}, /** R218 */ 
	//{ 0x0000, 219}, /** R219 */ 
	//{ 0x0000, 220}, /** R220 */ 
	//{ 0x0000, 221}, /** R221 */ 
	//{ 0x0000, 222}, /** R222 */ 
	//{ 0x0000, 223}, /** R223 */ 
	//{ 0x0000, 224}, /** R224 */ 
	//{ 0x0000, 225}, /** R225 */ 
	//{ 0x0000, 226}, /** R226 */ 
	//{ 0x0000, 227}, /** R227 */ 
	//{ 0x0000, 228}, /** R228 */ 
	//{ 0x0000, 229}, /** R229 */ 
	//{ 0x0000, 230}, /** R230 */ 
	//{ 0x0000, 231}, /** R231 */ 
	//{ 0x0000, 232}, /** R232 */ 
	//{ 0x0000, 233}, /** R233 */ 
	//{ 0x0000, 234}, /** R234 */ 
	//{ 0x0000, 235}, /** R235 */ 
	//{ 0x0000, 236}, /** R236 */ 
	//{ 0x0000, 237}, /** R237 */ 
	//{ 0x0000, 238}, /** R238 */ 
	//{ 0x0000, 239}, /** R239 */ 
	//{ 0x0000, 240}, /** R240 */ 
	//{ 0x0000, 241}, /** R241 */ 
	//{ 0x0000, 242}, /** R242 */ 
	//{ 0x0000, 243}, /** R243 */ 
	//{ 0x0000, 244}, /** R244 */ 
	//{ 0x0000, 245}, /** R245 */ 
	//{ 0x0000, 246}, /** R246 */ 
	//{ 0x0000, 247}, /** R247 - FLL NCO Test 0 */ 
	//{ 0x0019, 248}, /** R248 - FLL NCO Test 1 */ 
	{ 0x55AA, 255}  /** end */ 
};

uint8_t WM8904_Init(Twid *pTwid, uint32_t device,  uint32_t PCK)
{
	uint8_t count, size;
	uint16_t data = 0;

	// Reset (write Reg@0x0 to reset)
	WM8904_Write(pTwid, device, 0, 0xFFFF);

	for(data=0;data<1000;data++);
	//wait ready    
	while(data!=0x8904)
		data=WM8904_Read(pTwid, device, 0);

	if (PMC_MCKR_CSS_SLOW_CLK == PCK) {
		size = sizeof(wm8904_access_slow) / 4 + 1;
		for(count=0; count<size; count++) {
			WM8904_Write(pTwid, device, wm8904_access_slow[count].address,
							wm8904_access_slow[count].value);
			if(((wm8904_access_slow[count].address==0x05)
							&&(wm8904_access_slow[count].value==0x0047))
					||((wm8904_access_slow[count].address==0x74)
							&&(wm8904_access_slow[count].value==0x0005))
					||((wm8904_access_slow[count].address==0x12)
							&&(wm8904_access_slow[count].value==0x000F))) {
				Wait(5);
			}
			if (((wm8904_access_slow[count].address==0x44)
							&&(wm8904_access_slow[count].value==0x00F0))
					||((wm8904_access_slow[count].address==0x3A)
							&&(wm8904_access_slow[count].value==0x00B9))) {
				Wait(100);
			}
		} 
	}
	else if (PMC_MCKR_CSS_MAIN_CLK == PCK) {
		for(count = 0; count < 255; count++) {
			if(wm8904_access_main[count].address < 255) {
				WM8904_Write(pTwid, device, wm8904_access_main[count].address, 
								wm8904_access_main[count].value);
			} else {
				break;
			}
		}
	} else {
		printf("W: PCK not supported! \n\r");
		while(1);
	}
	return 0;
}

void WM8904_IN2R_IN1L(Twid *pTwid, uint32_t device)
{
	//{ 0x0005, 44},  /** R44  - Analogue Left Input 0 */ 
	//{ 0x0005, 45},  /** R45  - Analogue Right Input 0 */ 
	//{ 0x0000, 46},  /** R46  - Analogue Left Input 1 */ 
	//{ 0x0010, 47},  /** R47  - Analogue Right Input 1 */
	WM8904_Write(pTwid, device, 0x2C, 0x0008);
	WM8904_Write(pTwid, device, 0x2D, 0x0005);
	WM8904_Write(pTwid, device, 0x2E, 0x0000);
	WM8904_Write(pTwid, device, 0x2F, 0x0010);
}
