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
 * Check stack-overflow exception
 */

Name(z178, 178)

Method(m0fc, 1, Serialized)
{
	Name(ts, "m0fc")

	Name(i000, 0)
	Name(i001, 0)

	// 0 - 99

	Method(m000) { CH03(ts, z178, 0x000, __LINE__, 0) Add(i000,   0, i000) m001() }
	Method(m001) { CH03(ts, z178, 0x001, __LINE__, 0) Add(i000,   1, i000) m002() }
	Method(m002) { CH03(ts, z178, 0x002, __LINE__, 0) Add(i000,   2, i000) m003() }
	Method(m003) { CH03(ts, z178, 0x003, __LINE__, 0) Add(i000,   3, i000) m004() }
	Method(m004) { CH03(ts, z178, 0x004, __LINE__, 0) Add(i000,   4, i000) m005() }
	Method(m005) { CH03(ts, z178, 0x005, __LINE__, 0) Add(i000,   5, i000) m006() }
	Method(m006) { CH03(ts, z178, 0x006, __LINE__, 0) Add(i000,   6, i000) m007() }
	Method(m007) { CH03(ts, z178, 0x007, __LINE__, 0) Add(i000,   7, i000) m008() }
	Method(m008) { CH03(ts, z178, 0x008, __LINE__, 0) Add(i000,   8, i000) m009() }
	Method(m009) { CH03(ts, z178, 0x009, __LINE__, 0) Add(i000,   9, i000) m010() }

	Method(m010) { CH03(ts, z178, 0x010, __LINE__, 0) Add(i000,  10, i000) m011() }
	Method(m011) { CH03(ts, z178, 0x011, __LINE__, 0) Add(i000,  11, i000) m012() }
	Method(m012) { CH03(ts, z178, 0x012, __LINE__, 0) Add(i000,  12, i000) m013() }
	Method(m013) { CH03(ts, z178, 0x013, __LINE__, 0) Add(i000,  13, i000) m014() }
	Method(m014) { CH03(ts, z178, 0x014, __LINE__, 0) Add(i000,  14, i000) m015() }
	Method(m015) { CH03(ts, z178, 0x015, __LINE__, 0) Add(i000,  15, i000) m016() }
	Method(m016) { CH03(ts, z178, 0x016, __LINE__, 0) Add(i000,  16, i000) m017() }
	Method(m017) { CH03(ts, z178, 0x017, __LINE__, 0) Add(i000,  17, i000) m018() }
	Method(m018) { CH03(ts, z178, 0x018, __LINE__, 0) Add(i000,  18, i000) m019() }
	Method(m019) { CH03(ts, z178, 0x019, __LINE__, 0) Add(i000,  19, i000) m020() }

	Method(m020) { CH03(ts, z178, 0x020, __LINE__, 0) Add(i000,  20, i000) m021() }
	Method(m021) { CH03(ts, z178, 0x021, __LINE__, 0) Add(i000,  21, i000) m022() }
	Method(m022) { CH03(ts, z178, 0x022, __LINE__, 0) Add(i000,  22, i000) m023() }
	Method(m023) { CH03(ts, z178, 0x023, __LINE__, 0) Add(i000,  23, i000) m024() }
	Method(m024) { CH03(ts, z178, 0x024, __LINE__, 0) Add(i000,  24, i000) m025() }
	Method(m025) { CH03(ts, z178, 0x025, __LINE__, 0) Add(i000,  25, i000) m026() }
	Method(m026) { CH03(ts, z178, 0x026, __LINE__, 0) Add(i000,  26, i000) m027() }
	Method(m027) { CH03(ts, z178, 0x027, __LINE__, 0) Add(i000,  27, i000) m028() }
	Method(m028) { CH03(ts, z178, 0x028, __LINE__, 0) Add(i000,  28, i000) m029() }
	Method(m029) { CH03(ts, z178, 0x029, __LINE__, 0) Add(i000,  29, i000) m030() }

	Method(m030) { CH03(ts, z178, 0x030, __LINE__, 0) Add(i000,  30, i000) m031() }
	Method(m031) { CH03(ts, z178, 0x031, __LINE__, 0) Add(i000,  31, i000) m032() }
	Method(m032) { CH03(ts, z178, 0x032, __LINE__, 0) Add(i000,  32, i000) m033() }
	Method(m033) { CH03(ts, z178, 0x033, __LINE__, 0) Add(i000,  33, i000) m034() }
	Method(m034) { CH03(ts, z178, 0x034, __LINE__, 0) Add(i000,  34, i000) m035() }
	Method(m035) { CH03(ts, z178, 0x035, __LINE__, 0) Add(i000,  35, i000) m036() }
	Method(m036) { CH03(ts, z178, 0x036, __LINE__, 0) Add(i000,  36, i000) m037() }
	Method(m037) { CH03(ts, z178, 0x037, __LINE__, 0) Add(i000,  37, i000) m038() }
	Method(m038) { CH03(ts, z178, 0x038, __LINE__, 0) Add(i000,  38, i000) m039() }
	Method(m039) { CH03(ts, z178, 0x039, __LINE__, 0) Add(i000,  39, i000) m040() }

	Method(m040) { CH03(ts, z178, 0x040, __LINE__, 0) Add(i000,  40, i000) m041() }
	Method(m041) { CH03(ts, z178, 0x041, __LINE__, 0) Add(i000,  41, i000) m042() }
	Method(m042) { CH03(ts, z178, 0x042, __LINE__, 0) Add(i000,  42, i000) m043() }
	Method(m043) { CH03(ts, z178, 0x043, __LINE__, 0) Add(i000,  43, i000) m044() }
	Method(m044) { CH03(ts, z178, 0x044, __LINE__, 0) Add(i000,  44, i000) m045() }
	Method(m045) { CH03(ts, z178, 0x045, __LINE__, 0) Add(i000,  45, i000) m046() }
	Method(m046) { CH03(ts, z178, 0x046, __LINE__, 0) Add(i000,  46, i000) m047() }
	Method(m047) { CH03(ts, z178, 0x047, __LINE__, 0) Add(i000,  47, i000) m048() }
	Method(m048) { CH03(ts, z178, 0x048, __LINE__, 0) Add(i000,  48, i000) m049() }
	Method(m049) { CH03(ts, z178, 0x049, __LINE__, 0) Add(i000,  49, i000) m050() }

	Method(m050) { CH03(ts, z178, 0x050, __LINE__, 0) Add(i000,  50, i000) m051() }
	Method(m051) { CH03(ts, z178, 0x051, __LINE__, 0) Add(i000,  51, i000) m052() }
	Method(m052) { CH03(ts, z178, 0x052, __LINE__, 0) Add(i000,  52, i000) m053() }
	Method(m053) { CH03(ts, z178, 0x053, __LINE__, 0) Add(i000,  53, i000) m054() }
	Method(m054) { CH03(ts, z178, 0x054, __LINE__, 0) Add(i000,  54, i000) m055() }
	Method(m055) { CH03(ts, z178, 0x055, __LINE__, 0) Add(i000,  55, i000) m056() }
	Method(m056) { CH03(ts, z178, 0x056, __LINE__, 0) Add(i000,  56, i000) m057() }
	Method(m057) { CH03(ts, z178, 0x057, __LINE__, 0) Add(i000,  57, i000) m058() }
	Method(m058) { CH03(ts, z178, 0x058, __LINE__, 0) Add(i000,  58, i000) m059() }
	Method(m059) { CH03(ts, z178, 0x059, __LINE__, 0) Add(i000,  59, i000) m060() }

	Method(m060) { CH03(ts, z178, 0x060, __LINE__, 0) Add(i000,  60, i000) m061() }
	Method(m061) { CH03(ts, z178, 0x061, __LINE__, 0) Add(i000,  61, i000) m062() }
	Method(m062) { CH03(ts, z178, 0x062, __LINE__, 0) Add(i000,  62, i000) m063() }
	Method(m063) { CH03(ts, z178, 0x063, __LINE__, 0) Add(i000,  63, i000) m064() }
	Method(m064) { CH03(ts, z178, 0x064, __LINE__, 0) Add(i000,  64, i000) m065() }
	Method(m065) { CH03(ts, z178, 0x065, __LINE__, 0) Add(i000,  65, i000) m066() }
	Method(m066) { CH03(ts, z178, 0x066, __LINE__, 0) Add(i000,  66, i000) m067() }
	Method(m067) { CH03(ts, z178, 0x067, __LINE__, 0) Add(i000,  67, i000) m068() }
	Method(m068) { CH03(ts, z178, 0x068, __LINE__, 0) Add(i000,  68, i000) m069() }
	Method(m069) { CH03(ts, z178, 0x069, __LINE__, 0) Add(i000,  69, i000) m070() }

	Method(m070) { CH03(ts, z178, 0x070, __LINE__, 0) Add(i000,  70, i000) m071() }
	Method(m071) { CH03(ts, z178, 0x071, __LINE__, 0) Add(i000,  71, i000) m072() }
	Method(m072) { CH03(ts, z178, 0x072, __LINE__, 0) Add(i000,  72, i000) m073() }
	Method(m073) { CH03(ts, z178, 0x073, __LINE__, 0) Add(i000,  73, i000) m074() }
	Method(m074) { CH03(ts, z178, 0x074, __LINE__, 0) Add(i000,  74, i000) m075() }
	Method(m075) { CH03(ts, z178, 0x075, __LINE__, 0) Add(i000,  75, i000) m076() }
	Method(m076) { CH03(ts, z178, 0x076, __LINE__, 0) Add(i000,  76, i000) m077() }
	Method(m077) { CH03(ts, z178, 0x077, __LINE__, 0) Add(i000,  77, i000) m078() }
	Method(m078) { CH03(ts, z178, 0x078, __LINE__, 0) Add(i000,  78, i000) m079() }
	Method(m079) { CH03(ts, z178, 0x079, __LINE__, 0) Add(i000,  79, i000) m080() }

	Method(m080) { CH03(ts, z178, 0x080, __LINE__, 0) Add(i000,  80, i000) m081() }
	Method(m081) { CH03(ts, z178, 0x081, __LINE__, 0) Add(i000,  81, i000) m082() }
	Method(m082) { CH03(ts, z178, 0x082, __LINE__, 0) Add(i000,  82, i000) m083() }
	Method(m083) { CH03(ts, z178, 0x083, __LINE__, 0) Add(i000,  83, i000) m084() }
	Method(m084) { CH03(ts, z178, 0x084, __LINE__, 0) Add(i000,  84, i000) m085() }
	Method(m085) { CH03(ts, z178, 0x085, __LINE__, 0) Add(i000,  85, i000) m086() }
	Method(m086) { CH03(ts, z178, 0x086, __LINE__, 0) Add(i000,  86, i000) m087() }
	Method(m087) { CH03(ts, z178, 0x087, __LINE__, 0) Add(i000,  87, i000) m088() }
	Method(m088) { CH03(ts, z178, 0x088, __LINE__, 0) Add(i000,  88, i000) m089() }
	Method(m089) { CH03(ts, z178, 0x089, __LINE__, 0) Add(i000,  89, i000) m090() }

	Method(m090) { CH03(ts, z178, 0x090, __LINE__, 0) Add(i000,  90, i000) m091() }
	Method(m091) { CH03(ts, z178, 0x091, __LINE__, 0) Add(i000,  91, i000) m092() }
	Method(m092) { CH03(ts, z178, 0x092, __LINE__, 0) Add(i000,  92, i000) m093() }
	Method(m093) { CH03(ts, z178, 0x093, __LINE__, 0) Add(i000,  93, i000) m094() }
	Method(m094) { CH03(ts, z178, 0x094, __LINE__, 0) Add(i000,  94, i000) m095() }
	Method(m095) { CH03(ts, z178, 0x095, __LINE__, 0) Add(i000,  95, i000) m096() }
	Method(m096) { CH03(ts, z178, 0x096, __LINE__, 0) Add(i000,  96, i000) m097() }
	Method(m097) { CH03(ts, z178, 0x097, __LINE__, 0) Add(i000,  97, i000) m098() }
	Method(m098) { CH03(ts, z178, 0x098, __LINE__, 0) Add(i000,  98, i000) m099() }
	Method(m099) { CH03(ts, z178, 0x099, __LINE__, 0) Add(i000,  99, i000) m100() }


	// 100 - 199

	Method(m100) { CH03(ts, z178, 0x100, __LINE__, 0) Add(i000, 100, i000) m101() }
	Method(m101) { CH03(ts, z178, 0x101, __LINE__, 0) Add(i000, 101, i000) m102() }
	Method(m102) { CH03(ts, z178, 0x102, __LINE__, 0) Add(i000, 102, i000) m103() }
	Method(m103) { CH03(ts, z178, 0x103, __LINE__, 0) Add(i000, 103, i000) m104() }
	Method(m104) { CH03(ts, z178, 0x104, __LINE__, 0) Add(i000, 104, i000) m105() }
	Method(m105) { CH03(ts, z178, 0x105, __LINE__, 0) Add(i000, 105, i000) m106() }
	Method(m106) { CH03(ts, z178, 0x106, __LINE__, 0) Add(i000, 106, i000) m107() }
	Method(m107) { CH03(ts, z178, 0x107, __LINE__, 0) Add(i000, 107, i000) m108() }
	Method(m108) { CH03(ts, z178, 0x108, __LINE__, 0) Add(i000, 108, i000) m109() }
	Method(m109) { CH03(ts, z178, 0x109, __LINE__, 0) Add(i000, 109, i000) m110() }

	Method(m110) { CH03(ts, z178, 0x110, __LINE__, 0) Add(i000, 110, i000) m111() }
	Method(m111) { CH03(ts, z178, 0x111, __LINE__, 0) Add(i000, 111, i000) m112() }
	Method(m112) { CH03(ts, z178, 0x112, __LINE__, 0) Add(i000, 112, i000) m113() }
	Method(m113) { CH03(ts, z178, 0x113, __LINE__, 0) Add(i000, 113, i000) m114() }
	Method(m114) { CH03(ts, z178, 0x114, __LINE__, 0) Add(i000, 114, i000) m115() }
	Method(m115) { CH03(ts, z178, 0x115, __LINE__, 0) Add(i000, 115, i000) m116() }
	Method(m116) { CH03(ts, z178, 0x116, __LINE__, 0) Add(i000, 116, i000) m117() }
	Method(m117) { CH03(ts, z178, 0x117, __LINE__, 0) Add(i000, 117, i000) m118() }
	Method(m118) { CH03(ts, z178, 0x118, __LINE__, 0) Add(i000, 118, i000) m119() }
	Method(m119) { CH03(ts, z178, 0x119, __LINE__, 0) Add(i000, 119, i000) m120() }

	Method(m120) { CH03(ts, z178, 0x120, __LINE__, 0) Add(i000, 120, i000) m121() }
	Method(m121) { CH03(ts, z178, 0x121, __LINE__, 0) Add(i000, 121, i000) m122() }
	Method(m122) { CH03(ts, z178, 0x122, __LINE__, 0) Add(i000, 122, i000) m123() }
	Method(m123) { CH03(ts, z178, 0x123, __LINE__, 0) Add(i000, 123, i000) m124() }
	Method(m124) { CH03(ts, z178, 0x124, __LINE__, 0) Add(i000, 124, i000) m125() }
	Method(m125) { CH03(ts, z178, 0x125, __LINE__, 0) Add(i000, 125, i000) m126() }
	Method(m126) { CH03(ts, z178, 0x126, __LINE__, 0) Add(i000, 126, i000) m127() }
	Method(m127) { CH03(ts, z178, 0x127, __LINE__, 0) Add(i000, 127, i000) m128() }
	Method(m128) { CH03(ts, z178, 0x128, __LINE__, 0) Add(i000, 128, i000) m129() }
	Method(m129) { CH03(ts, z178, 0x129, __LINE__, 0) Add(i000, 129, i000) m130() }

	Method(m130) { CH03(ts, z178, 0x130, __LINE__, 0) Add(i000, 130, i000) m131() }
	Method(m131) { CH03(ts, z178, 0x131, __LINE__, 0) Add(i000, 131, i000) m132() }
	Method(m132) { CH03(ts, z178, 0x132, __LINE__, 0) Add(i000, 132, i000) m133() }
	Method(m133) { CH03(ts, z178, 0x133, __LINE__, 0) Add(i000, 133, i000) m134() }
	Method(m134) { CH03(ts, z178, 0x134, __LINE__, 0) Add(i000, 134, i000) m135() }
	Method(m135) { CH03(ts, z178, 0x135, __LINE__, 0) Add(i000, 135, i000) m136() }
	Method(m136) { CH03(ts, z178, 0x136, __LINE__, 0) Add(i000, 136, i000) m137() }
	Method(m137) { CH03(ts, z178, 0x137, __LINE__, 0) Add(i000, 137, i000) m138() }
	Method(m138) { CH03(ts, z178, 0x138, __LINE__, 0) Add(i000, 138, i000) m139() }
	Method(m139) { CH03(ts, z178, 0x139, __LINE__, 0) Add(i000, 139, i000) m140() }

	Method(m140) { CH03(ts, z178, 0x140, __LINE__, 0) Add(i000, 140, i000) m141() }
	Method(m141) { CH03(ts, z178, 0x141, __LINE__, 0) Add(i000, 141, i000) m142() }
	Method(m142) { CH03(ts, z178, 0x142, __LINE__, 0) Add(i000, 142, i000) m143() }
	Method(m143) { CH03(ts, z178, 0x143, __LINE__, 0) Add(i000, 143, i000) m144() }
	Method(m144) { CH03(ts, z178, 0x144, __LINE__, 0) Add(i000, 144, i000) m145() }
	Method(m145) { CH03(ts, z178, 0x145, __LINE__, 0) Add(i000, 145, i000) m146() }
	Method(m146) { CH03(ts, z178, 0x146, __LINE__, 0) Add(i000, 146, i000) m147() }
	Method(m147) { CH03(ts, z178, 0x147, __LINE__, 0) Add(i000, 147, i000) m148() }
	Method(m148) { CH03(ts, z178, 0x148, __LINE__, 0) Add(i000, 148, i000) m149() }
	Method(m149) { CH03(ts, z178, 0x149, __LINE__, 0) Add(i000, 149, i000) m150() }

	Method(m150) { CH03(ts, z178, 0x150, __LINE__, 0) Add(i000, 150, i000) m151() }
	Method(m151) { CH03(ts, z178, 0x151, __LINE__, 0) Add(i000, 151, i000) m152() }
	Method(m152) { CH03(ts, z178, 0x152, __LINE__, 0) Add(i000, 152, i000) m153() }
	Method(m153) { CH03(ts, z178, 0x153, __LINE__, 0) Add(i000, 153, i000) m154() }
	Method(m154) { CH03(ts, z178, 0x154, __LINE__, 0) Add(i000, 154, i000) m155() }
	Method(m155) { CH03(ts, z178, 0x155, __LINE__, 0) Add(i000, 155, i000) m156() }
	Method(m156) { CH03(ts, z178, 0x156, __LINE__, 0) Add(i000, 156, i000) m157() }
	Method(m157) { CH03(ts, z178, 0x157, __LINE__, 0) Add(i000, 157, i000) m158() }
	Method(m158) { CH03(ts, z178, 0x158, __LINE__, 0) Add(i000, 158, i000) m159() }
	Method(m159) { CH03(ts, z178, 0x159, __LINE__, 0) Add(i000, 159, i000) m160() }

	Method(m160) { CH03(ts, z178, 0x160, __LINE__, 0) Add(i000, 160, i000) m161() }
	Method(m161) { CH03(ts, z178, 0x161, __LINE__, 0) Add(i000, 161, i000) m162() }
	Method(m162) { CH03(ts, z178, 0x162, __LINE__, 0) Add(i000, 162, i000) m163() }
	Method(m163) { CH03(ts, z178, 0x163, __LINE__, 0) Add(i000, 163, i000) m164() }
	Method(m164) { CH03(ts, z178, 0x164, __LINE__, 0) Add(i000, 164, i000) m165() }
	Method(m165) { CH03(ts, z178, 0x165, __LINE__, 0) Add(i000, 165, i000) m166() }
	Method(m166) { CH03(ts, z178, 0x166, __LINE__, 0) Add(i000, 166, i000) m167() }
	Method(m167) { CH03(ts, z178, 0x167, __LINE__, 0) Add(i000, 167, i000) m168() }
	Method(m168) { CH03(ts, z178, 0x168, __LINE__, 0) Add(i000, 168, i000) m169() }
	Method(m169) { CH03(ts, z178, 0x169, __LINE__, 0) Add(i000, 169, i000) m170() }

	Method(m170) { CH03(ts, z178, 0x170, __LINE__, 0) Add(i000, 170, i000) m171() }
	Method(m171) { CH03(ts, z178, 0x171, __LINE__, 0) Add(i000, 171, i000) m172() }
	Method(m172) { CH03(ts, z178, 0x172, __LINE__, 0) Add(i000, 172, i000) m173() }
	Method(m173) { CH03(ts, z178, 0x173, __LINE__, 0) Add(i000, 173, i000) m174() }
	Method(m174) { CH03(ts, z178, 0x174, __LINE__, 0) Add(i000, 174, i000) m175() }
	Method(m175) { CH03(ts, z178, 0x175, __LINE__, 0) Add(i000, 175, i000) m176() }
	Method(m176) { CH03(ts, z178, 0x176, __LINE__, 0) Add(i000, 176, i000) m177() }
	Method(m177) { CH03(ts, z178, 0x177, __LINE__, 0) Add(i000, 177, i000) m178() }
	Method(m178) { CH03(ts, z178, 0x178, __LINE__, 0) Add(i000, 178, i000) m179() }
	Method(m179) { CH03(ts, z178, 0x179, __LINE__, 0) Add(i000, 179, i000) m180() }

	Method(m180) { CH03(ts, z178, 0x180, __LINE__, 0) Add(i000, 180, i000) m181() }
	Method(m181) { CH03(ts, z178, 0x181, __LINE__, 0) Add(i000, 181, i000) m182() }
	Method(m182) { CH03(ts, z178, 0x182, __LINE__, 0) Add(i000, 182, i000) m183() }
	Method(m183) { CH03(ts, z178, 0x183, __LINE__, 0) Add(i000, 183, i000) m184() }
	Method(m184) { CH03(ts, z178, 0x184, __LINE__, 0) Add(i000, 184, i000) m185() }
	Method(m185) { CH03(ts, z178, 0x185, __LINE__, 0) Add(i000, 185, i000) m186() }
	Method(m186) { CH03(ts, z178, 0x186, __LINE__, 0) Add(i000, 186, i000) m187() }
	Method(m187) { CH03(ts, z178, 0x187, __LINE__, 0) Add(i000, 187, i000) m188() }
	Method(m188) { CH03(ts, z178, 0x188, __LINE__, 0) Add(i000, 188, i000) m189() }
	Method(m189) { CH03(ts, z178, 0x189, __LINE__, 0) Add(i000, 189, i000) m190() }

	Method(m190) { CH03(ts, z178, 0x190, __LINE__, 0) Add(i000, 190, i000) m191() }
	Method(m191) { CH03(ts, z178, 0x191, __LINE__, 0) Add(i000, 191, i000) m192() }
	Method(m192) { CH03(ts, z178, 0x192, __LINE__, 0) Add(i000, 192, i000) m193() }
	Method(m193) { CH03(ts, z178, 0x193, __LINE__, 0) Add(i000, 193, i000) m194() }
	Method(m194) { CH03(ts, z178, 0x194, __LINE__, 0) Add(i000, 194, i000) m195() }
	Method(m195) { CH03(ts, z178, 0x195, __LINE__, 0) Add(i000, 195, i000) m196() }
	Method(m196) { CH03(ts, z178, 0x196, __LINE__, 0) Add(i000, 196, i000) m197() }
	Method(m197) { CH03(ts, z178, 0x197, __LINE__, 0) Add(i000, 197, i000) m198() }
	Method(m198) { CH03(ts, z178, 0x198, __LINE__, 0) Add(i000, 198, i000) m199() }
	Method(m199) { CH03(ts, z178, 0x199, __LINE__, 0) Add(i000, 199, i000) m200() }


	// 200 - 299

	Method(m200) { CH03(ts, z178, 0x200, __LINE__, 0) Add(i000, 200, i000) m201() }
	Method(m201) { CH03(ts, z178, 0x201, __LINE__, 0) Add(i000, 201, i000) m202() }
	Method(m202) { CH03(ts, z178, 0x202, __LINE__, 0) Add(i000, 202, i000) m203() }
	Method(m203) { CH03(ts, z178, 0x203, __LINE__, 0) Add(i000, 203, i000) m204() }
	Method(m204) { CH03(ts, z178, 0x204, __LINE__, 0) Add(i000, 204, i000) m205() }
	Method(m205) { CH03(ts, z178, 0x205, __LINE__, 0) Add(i000, 205, i000) m206() }
	Method(m206) { CH03(ts, z178, 0x206, __LINE__, 0) Add(i000, 206, i000) m207() }
	Method(m207) { CH03(ts, z178, 0x207, __LINE__, 0) Add(i000, 207, i000) m208() }
	Method(m208) { CH03(ts, z178, 0x208, __LINE__, 0) Add(i000, 208, i000) m209() }
	Method(m209) { CH03(ts, z178, 0x209, __LINE__, 0) Add(i000, 209, i000) m210() }

	Method(m210) { CH03(ts, z178, 0x210, __LINE__, 0) Add(i000, 210, i000) m211() }
	Method(m211) { CH03(ts, z178, 0x211, __LINE__, 0) Add(i000, 211, i000) m212() }
	Method(m212) { CH03(ts, z178, 0x212, __LINE__, 0) Add(i000, 212, i000) m213() }
	Method(m213) { CH03(ts, z178, 0x213, __LINE__, 0) Add(i000, 213, i000) m214() }
	Method(m214) { CH03(ts, z178, 0x214, __LINE__, 0) Add(i000, 214, i000) m215() }
	Method(m215) { CH03(ts, z178, 0x215, __LINE__, 0) Add(i000, 215, i000) m216() }
	Method(m216) { CH03(ts, z178, 0x216, __LINE__, 0) Add(i000, 216, i000) m217() }
	Method(m217) { CH03(ts, z178, 0x217, __LINE__, 0) Add(i000, 217, i000) m218() }
	Method(m218) { CH03(ts, z178, 0x218, __LINE__, 0) Add(i000, 218, i000) m219() }
	Method(m219) { CH03(ts, z178, 0x219, __LINE__, 0) Add(i000, 219, i000) m220() }

	Method(m220) { CH03(ts, z178, 0x220, __LINE__, 0) Add(i000, 220, i000) m221() }
	Method(m221) { CH03(ts, z178, 0x221, __LINE__, 0) Add(i000, 221, i000) m222() }
	Method(m222) { CH03(ts, z178, 0x222, __LINE__, 0) Add(i000, 222, i000) m223() }
	Method(m223) { CH03(ts, z178, 0x223, __LINE__, 0) Add(i000, 223, i000) m224() }
	Method(m224) { CH03(ts, z178, 0x224, __LINE__, 0) Add(i000, 224, i000) m225() }
	Method(m225) { CH03(ts, z178, 0x225, __LINE__, 0) Add(i000, 225, i000) m226() }
	Method(m226) { CH03(ts, z178, 0x226, __LINE__, 0) Add(i000, 226, i000) m227() }
	Method(m227) { CH03(ts, z178, 0x227, __LINE__, 0) Add(i000, 227, i000) m228() }
	Method(m228) { CH03(ts, z178, 0x228, __LINE__, 0) Add(i000, 228, i000) m229() }
	Method(m229) { CH03(ts, z178, 0x229, __LINE__, 0) Add(i000, 229, i000) m230() }

	Method(m230) { CH03(ts, z178, 0x230, __LINE__, 0) Add(i000, 230, i000) m231() }
	Method(m231) { CH03(ts, z178, 0x231, __LINE__, 0) Add(i000, 231, i000) m232() }
	Method(m232) { CH03(ts, z178, 0x232, __LINE__, 0) Add(i000, 232, i000) m233() }
	Method(m233) { CH03(ts, z178, 0x233, __LINE__, 0) Add(i000, 233, i000) m234() }
	Method(m234) { CH03(ts, z178, 0x234, __LINE__, 0) Add(i000, 234, i000) m235() }
	Method(m235) { CH03(ts, z178, 0x235, __LINE__, 0) Add(i000, 235, i000) m236() }
	Method(m236) { CH03(ts, z178, 0x236, __LINE__, 0) Add(i000, 236, i000) m237() }
	Method(m237) { CH03(ts, z178, 0x237, __LINE__, 0) Add(i000, 237, i000) m238() }
	Method(m238) { CH03(ts, z178, 0x238, __LINE__, 0) Add(i000, 238, i000) m239() }
	Method(m239) { CH03(ts, z178, 0x239, __LINE__, 0) Add(i000, 239, i000) m240() }

	Method(m240) { CH03(ts, z178, 0x240, __LINE__, 0) Add(i000, 240, i000) m241() }
	Method(m241) { CH03(ts, z178, 0x241, __LINE__, 0) Add(i000, 241, i000) m242() }
	Method(m242) { CH03(ts, z178, 0x242, __LINE__, 0) Add(i000, 242, i000) m243() }
	Method(m243) { CH03(ts, z178, 0x243, __LINE__, 0) Add(i000, 243, i000) m244() }
	Method(m244) { CH03(ts, z178, 0x244, __LINE__, 0) Add(i000, 244, i000) m245() }
	Method(m245) { CH03(ts, z178, 0x245, __LINE__, 0) Add(i000, 245, i000) m246() }

	/*
	 * We should take into account there how many method
	 * calls precede invocation of this test method m0fc.
	 * So, when we run MN00 or MN01 (but not immediately MAIN)
	 * the number of preceding method calls is greater by 1.
	 * So, in that case, the number of calls in m0fc should
	 * be less by 1.
	 */

	Method(m246)
	{
		CH03(ts, z178, 0x246, __LINE__, 0)
		Add(i000, 246, i000)

		if (LNot(MLVL)) {
			m247()
		} elseif (i001) {
			// To cause AE_AML_METHOD_LIMIT exception
			m247()
		}
	}
	Method(m247)
	{
		CH03(ts, z178, 0x247, __LINE__, 0)
		Add(i000, 247, i000)
		if (i001) {
			// To cause AE_AML_METHOD_LIMIT exception
			m248()
		}
	}
	Method(m248) { CH03(ts, z178, 0x248, __LINE__, 0) Add(i000, 248, i000) }


	CH03(ts, z178, 0x300, __LINE__, 0)

	Store(arg0, i001)

	m000()

	if (arg0) {
		CH04(ts, 0, 86, z178, __LINE__, 0, 0)	// AE_OWNER_ID_LIMIT
	} else {
		CH03(ts, z178, 0x302, __LINE__, 0)
		if (MLVL) {
			Store(0x76AD, Local0)
		} else {
			Store(0x77A4, Local0)
		}
		if (LNotEqual(i000, Local0)) {
			err(ts, z178, __LINE__, 0, 0, i000, Local0)
		}
	}
}

Method(m0fe, 1, Serialized)
{
	Name(ts, "m0fe")

	Name(i000, 0)
	Name(i001, 0)

	Name(max0, 246)

	Method(m000) {

		CH03(ts, z178, 0x400, __LINE__, 0)

		Store(max0, Local0)
		if (i001) {
			Increment(Local0)
		}

		Increment(i000)
		if (LLessEqual(i000, Local0)) {
			m000()
		}
	}

	CH03(ts, z178, 0x401, __LINE__, 0)

	Store(arg0, i001)

	m000()

	if (arg0) {
		CH04(ts, 0, 84, z178, __LINE__, 0, 0)	// AE_AML_METHOD_LIMIT
	} else {
		CH03(ts, z178, 0x403, __LINE__, 0)
		if (LNotEqual(i000, 0xf7)) {
			err(ts, z178, __LINE__, 0, 0, i000, 0xf7)
		}
	}
}


Method(m0fd)
{
/*
SRMT("m0fe-0")
m0fe(0)
return
*/


	SRMT("m0fc-0")
	m0fc(0)

	SRMT("m0fc-1")
	if (y527) {
		m0fc(1)
	} else {
		BLCK()
	}

	SRMT("m0fe-0")
	m0fe(0)

	SRMT("m0fe-1")
	if (y200) {
		m0fe(1)
	} else {
		BLCK()
	}


	CH03("m0fd", z178, 0x405, __LINE__, 0)
}
