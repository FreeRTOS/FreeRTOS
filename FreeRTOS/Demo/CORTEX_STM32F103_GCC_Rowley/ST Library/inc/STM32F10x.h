// Copyright (c) 2009 Rowley Associates Limited.
//
// This file may be distributed under the terms of the License Agreement
// provided with this software.
//
// THIS FILE IS PROVIDED AS IS WITH NO WARRANTY OF ANY KIND, INCLUDING THE
// WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.

#ifndef __STM32F10x_H__
#define __STM32F10x_H__

#define STM32F101C4 0x10114
#define STM32F101C6 0x10116
#define STM32F101C8 0x10118
#define STM32F101CB 0x1011B

#define STM32F101R4 0x10124
#define STM32F101R6 0x10126
#define STM32F101R8 0x10128
#define STM32F101RB 0x1012B
#define STM32F101RC 0x1012C
#define STM32F101RD 0x1012D
#define STM32F101RE 0x1012E

#define STM32F101T4 0x10134
#define STM32F101T6 0x10136
#define STM32F101T8 0x10138

#define STM32F101V8 0x10148
#define STM32F101VB 0x1014B
#define STM32F101VC 0x1014C
#define STM32F101VD 0x1014D
#define STM32F101VE 0x1014E

#define STM32F101ZC 0x1015C
#define STM32F101ZD 0x1015D
#define STM32F101ZE 0x1015E

#define STM32F102C4 0x10214
#define STM32F102C6 0x10216
#define STM32F102C8 0x10218
#define STM32F102CB 0x1021B

#define STM32F102R4 0x10228
#define STM32F102R6 0x1022B
#define STM32F102R8 0x10228
#define STM32F102RB 0x1022B

#define STM32F103C4 0x10314
#define STM32F103C6 0x10316
#define STM32F103C8 0x10318
#define STM32F103CB 0x1031B

#define STM32F103R4 0x10324
#define STM32F103R6 0x10326
#define STM32F103R8 0x10328
#define STM32F103RB 0x1032B
#define STM32F103RC 0x1032C
#define STM32F103RD 0x1032D
#define STM32F103RE 0x1032E

#define STM32F103T4 0x10334
#define STM32F103T6 0x10336
#define STM32F103T8 0x10338
#define STM32F103TB 0x1033B

#define STM32F103V8 0x10348
#define STM32F103VB 0x1034B
#define STM32F103VC 0x1034C
#define STM32F103VD 0x1034D
#define STM32F103VE 0x1034E

#define STM32F103ZC 0x1035C
#define STM32F103ZD 0x1035D
#define STM32F103ZE 0x1035E

#define STM32F105R8 0x10528
#define STM32F105RB 0x1052B
#define STM32F105RC 0x1052C

#define STM32F105V8 0x10548
#define STM32F105VB 0x1054B
#define STM32F105VC 0x1054C

#define STM32F107RB 0x1072B
#define STM32F107RC 0x1072C

#define STM32F107VB 0x1074B
#define STM32F107VC 0x1074C

#if (__TARGET_PROCESSOR == STM32F101C4)
#include <targets/STM32F101C4.h>
#elif (__TARGET_PROCESSOR == STM32F101C6)
#include <targets/STM32F101C6.h>
#elif (__TARGET_PROCESSOR == STM32F101C8)
#include <targets/STM32F101C6.h>
#elif (__TARGET_PROCESSOR == STM32F101CB)
#include <targets/STM32F101C8.h>
#elif (__TARGET_PROCESSOR == STM32F101R4)
#include <targets/STM32F101R4.h>
#elif (__TARGET_PROCESSOR == STM32F101R6)
#include <targets/STM32F101R6.h>
#elif (__TARGET_PROCESSOR == STM32F101R8)
#include <targets/STM32F101R8.h>
#elif (__TARGET_PROCESSOR == STM32F101RB)
#include <targets/STM32F101RB.h>
#elif (__TARGET_PROCESSOR == STM32F101RC)
#include <targets/STM32F101RC.h>
#elif (__TARGET_PROCESSOR == STM32F101RD)
#include <targets/STM32F101RD.h>
#elif (__TARGET_PROCESSOR == STM32F101RE)
#include <targets/STM32F101RE.h>
#elif (__TARGET_PROCESSOR == STM32F101T4)
#include <targets/STM32F101T4.h>
#elif (__TARGET_PROCESSOR == STM32F101T6)
#include <targets/STM32F101T6.h>
#elif (__TARGET_PROCESSOR == STM32F101T8)
#include <targets/STM32F101T8.h>
#elif (__TARGET_PROCESSOR == STM32F101V8)
#include <targets/STM32F101V8.h>
#elif (__TARGET_PROCESSOR == STM32F101VB)
#include <targets/STM32F101VB.h>
#elif (__TARGET_PROCESSOR == STM32F101VC)
#include <targets/STM32F101VC.h>
#elif (__TARGET_PROCESSOR == STM32F101VD)
#include <targets/STM32F101VD.h>
#elif (__TARGET_PROCESSOR == STM32F101VE)
#include <targets/STM32F101VE.h>
#elif (__TARGET_PROCESSOR == STM32F101ZC)
#include <targets/STM32F101ZC.h>
#elif (__TARGET_PROCESSOR == STM32F101ZD)
#include <targets/STM32F101ZD.h>
#elif (__TARGET_PROCESSOR == STM32F101ZE)
#include <targets/STM32F101ZE.h>
#elif (__TARGET_PROCESSOR == STM32F102C4)
#include <targets/STM32F102C4.h>
#elif (__TARGET_PROCESSOR == STM32F102C6)
#include <targets/STM32F102C6.h>
#elif (__TARGET_PROCESSOR == STM32F102C8)
#include <targets/STM32F102C8.h>
#elif (__TARGET_PROCESSOR == STM32F102CB)
#include <targets/STM32F102CB.h>
#elif (__TARGET_PROCESSOR == STM32F102R4)
#include <targets/STM32F102R4.h>
#elif (__TARGET_PROCESSOR == STM32F102R6)
#include <targets/STM32F102R6.h>
#elif (__TARGET_PROCESSOR == STM32F102R8)
#include <targets/STM32F102R8.h>
#elif (__TARGET_PROCESSOR == STM32F102RB)
#include <targets/STM32F102RB.h>
#elif (__TARGET_PROCESSOR == STM32F103C4)
#include <targets/STM32F103C4.h>
#elif (__TARGET_PROCESSOR == STM32F103C6)
#include <targets/STM32F103C6.h>
#elif (__TARGET_PROCESSOR == STM32F103C8)
#include <targets/STM32F103C8.h>
#elif (__TARGET_PROCESSOR == STM32F103CB)
#include <targets/STM32F103CB.h>
#elif (__TARGET_PROCESSOR == STM32F103R4)
#include <targets/STM32F103R4.h>
#elif (__TARGET_PROCESSOR == STM32F103R6)
#include <targets/STM32F103R6.h>
#elif (__TARGET_PROCESSOR == STM32F103R8)
#include <targets/STM32F101C6.h>
#elif (__TARGET_PROCESSOR == STM32F103RB)
#include <targets/STM32F103RB.h>
#elif (__TARGET_PROCESSOR == STM32F103RC)
#include <targets/STM32F103RC.h>
#elif (__TARGET_PROCESSOR == STM32F103RD)
#include <targets/STM32F103RD.h>
#elif (__TARGET_PROCESSOR == STM32F103RE)
#include <targets/STM32F103RE.h>
#elif (__TARGET_PROCESSOR == STM32F103T4)
#include <targets/STM32F103T4.h>
#elif (__TARGET_PROCESSOR == STM32F103T6)
#include <targets/STM32F103T6.h>
#elif (__TARGET_PROCESSOR == STM32F103T8)
#include <targets/STM32F103T8.h>
#elif (__TARGET_PROCESSOR == STM32F103TB)
#include <targets/STM32F103TB.h>
#elif (__TARGET_PROCESSOR == STM32F103V8)
#include <targets/STM32F103V8.h>
#elif (__TARGET_PROCESSOR == STM32F103VB)
#include <targets/STM32F103VB.h>
#elif (__TARGET_PROCESSOR == STM32F103VC)
#include <targets/STM32F103VC.h>
#elif (__TARGET_PROCESSOR == STM32F103VD)
#include <targets/STM32F103VD.h>
#elif (__TARGET_PROCESSOR == STM32F103VE)
#include <targets/STM32F103VE.h>
#elif (__TARGET_PROCESSOR == STM32F103ZC)
#include <targets/STM32F103ZC.h>
#elif (__TARGET_PROCESSOR == STM32F103ZD)
#include <targets/STM32F103ZD.h>
#elif (__TARGET_PROCESSOR == STM32F103ZE)
#include <targets/STM32F103ZE.h>
#elif (__TARGET_PROCESSOR == STM32F105R8)
#include <targets/STM32F105R8.h>
#elif (__TARGET_PROCESSOR == STM32F105RB)
#include <targets/STM32F105RB.h>
#elif (__TARGET_PROCESSOR == STM32F105RC)
#include <targets/STM32F105RC.h>
#elif (__TARGET_PROCESSOR == STM32F105V8)
#include <targets/STM32F105V8.h>
#elif (__TARGET_PROCESSOR == STM32F105VB)
#include <targets/STM32F105VB.h>
#elif (__TARGET_PROCESSOR == STM32F105VC)
#include <targets/STM32F105VC.h>
#elif (__TARGET_PROCESSOR == STM32F107RB)
#include <targets/STM32F107RB.h>
#elif (__TARGET_PROCESSOR == STM32F107RC)
#include <targets/STM32F107RC.h>
#elif (__TARGET_PROCESSOR == STM32F107VB)
#include <targets/STM32F107VB.h>
#elif (__TARGET_PROCESSOR == STM32F107VC)
#include <targets/STM32F107VC.h>
#else
#error bad __TARGET_PROCESSOR
#endif

#endif