//*****************************************************************************
// To configure the same pin 1 of port 0, write 
// Control_P0_1(mode, drivestrength); where the mode is INPUT, INPUT_PD ... 
// OUTPUT_PP_GP ... OUTPUT_ODAF4. (see definitions below)
// and drivestrength is WEAK, MEDIUM, STRONG or VERYSTRONG
//
// To toggle reset or set a pin you need to call the macro and put in brackets 
// the name of the port pin. 
// Example: you want to toggle, reset and set pin 1 of port: 
// Toggle(P0_1);
// Reset(P0_1);
// Set(P0_1);
//*****************************************************************************

#ifndef __GPIO_H__
#define __GPIO_H__

#include <XMC4500.h>

#define INPUT           0x00
#define INPUT_PD        0x01
#define INPUT_PU        0x02
#define INPUT_PPS       0x03
#define INPUT_INV       0x04
#define INPUT_INV_PD    0x05
#define INPUT_INV_PU    0x06
#define INPUT_INV_PPS   0x07
#define OUTPUT_PP_GP    0x10
#define OUTPUT_PP_AF1   0x11
#define OUTPUT_PP_AF2   0x12
#define OUTPUT_PP_AF3   0x13
#define OUTPUT_PP_AF4   0x14
#define OUTPUT_OD_GP    0x18
#define OUTPUT_OD_AF1   0x19
#define OUTPUT_OD_AF2   0x1A
#define OUTPUT_OD_AF3   0x1B
#define OUTPUT_OD_AF4   0X1C

#define WEAK            0x7
#define MEDIUM          0x4
#define STRONG          0x2
#define VERYSTRONG      0x0

#define Set(PinName) SET_##PinName
#define Reset(PinName) RESET_##PinName
#define Toggle(PinName) TOGGLE_##PinName

#define SET_P0_0       PORT0->OMR = 0x00000001
#define SET_P0_1       PORT0->OMR = 0x00000002
#define SET_P0_2       PORT0->OMR = 0x00000004
#define SET_P0_3       PORT0->OMR = 0x00000008
#define SET_P0_4       PORT0->OMR = 0x00000010
#define SET_P0_5       PORT0->OMR = 0x00000020
#define SET_P0_6       PORT0->OMR = 0x00000040
#define SET_P0_7       PORT0->OMR = 0x00000080
#define SET_P0_8       PORT0->OMR = 0x00000100
#define SET_P0_9       PORT0->OMR = 0x00000200
#define SET_P0_10       PORT0->OMR = 0x00000400
#define SET_P0_11       PORT0->OMR = 0x00000800
#define SET_P0_12       PORT0->OMR = 0x00001000
#define SET_P0_13       PORT0->OMR = 0x00002000
#define SET_P0_14       PORT0->OMR = 0x00004000
#define SET_P0_15       PORT0->OMR = 0x00008000

#define RESET_P0_0       PORT0->OMR = 0x00010000
#define RESET_P0_1       PORT0->OMR = 0x00020000
#define RESET_P0_2       PORT0->OMR = 0x00040000
#define RESET_P0_3       PORT0->OMR = 0x00080000
#define RESET_P0_4       PORT0->OMR = 0x00100000
#define RESET_P0_5       PORT0->OMR = 0x00200000
#define RESET_P0_6       PORT0->OMR = 0x00400000
#define RESET_P0_7       PORT0->OMR = 0x00800000
#define RESET_P0_8       PORT0->OMR = 0x01000000
#define RESET_P0_9       PORT0->OMR = 0x02000000
#define RESET_P0_10       PORT0->OMR = 0x04000000
#define RESET_P0_11       PORT0->OMR= 0x08000000
#define RESET_P0_12       PORT0->OMR = 0x10000000
#define RESET_P0_13       PORT0->OMR = 0x20000000
#define RESET_P0_14       PORT0->OMR = 0x40000000
#define RESET_P0_15       PORT0->OMR = 0x80000000

#define TOGGLE_P0_0       PORT0->OMR = 0x00010001
#define TOGGLE_P0_1       PORT0->OMR = 0x00020002
#define TOGGLE_P0_2       PORT0->OMR = 0x00040004
#define TOGGLE_P0_3       PORT0->OMR = 0x00080008
#define TOGGLE_P0_4       PORT0->OMR = 0x00100010
#define TOGGLE_P0_5       PORT0->OMR = 0x00200020
#define TOGGLE_P0_6       PORT0->OMR = 0x00400040
#define TOGGLE_P0_7       PORT0->OMR = 0x00800080
#define TOGGLE_P0_8       PORT0->OMR = 0x01000100
#define TOGGLE_P0_9       PORT0->OMR = 0x02000200
#define TOGGLE_P0_10       PORT0->OMR = 0x04000400
#define TOGGLE_P0_11       PORT0->OMR = 0x08000800
#define TOGGLE_P0_12       PORT0->OMR = 0x10001000
#define TOGGLE_P0_13       PORT0->OMR = 0x20002000
#define TOGGLE_P0_14       PORT0->OMR = 0x40004000
#define TOGGLE_P0_15       PORT0->OMR = 0x80008000

#define Control_P0_0(Mode, DriveStrength)       PORT0->IOCR0 = (PORT0->IOCR0 & ~0x000000F8) | (Mode << 3); PORT0->PDR0 = (PORT0->PDR0 & ~0x00000007) | (DriveStrength)
#define Control_P0_1(Mode, DriveStrength)       PORT0->IOCR0 = (PORT0->IOCR0 & ~0x0000F800) | (Mode << 11); PORT0->PDR0 = (PORT0->PDR0 & ~0x00000070) | (DriveStrength << 4)
#define Control_P0_2(Mode, DriveStrength)       PORT0->IOCR0 = (PORT0->IOCR0 & ~0x00F80000) | (Mode << 19); PORT0->PDR0 = (PORT0->PDR0 & ~0x00000700) | (DriveStrength << 8)
#define Control_P0_3(Mode, DriveStrength)       PORT0->IOCR0 = (PORT0->IOCR0 & ~0xF8000000) | (Mode << 27); PORT0->PDR0 = (PORT0->PDR0 & ~0x00007000) | (DriveStrength << 12)
#define Control_P0_4(Mode, DriveStrength)       PORT0->IOCR4 = (PORT0->IOCR4 & ~0x000000F8) | (Mode << 3); PORT0->PDR0 = (PORT0->PDR0 & ~0x00070000) | (DriveStrength << 16)
#define Control_P0_5(Mode, DriveStrength)       PORT0->IOCR4 = (PORT0->IOCR4 & ~0x0000F800) | (Mode << 11); PORT0->PDR0 = (PORT0->PDR0 & ~0x00700000) | (DriveStrength << 20)
#define Control_P0_6(Mode, DriveStrength)       PORT0->IOCR4 = (PORT0->IOCR4 & ~0x00F80000) | (Mode << 19); PORT0->PDR0 = (PORT0->PDR0 & ~0x07000000) | (DriveStrength << 24)
#define Control_P0_7(Mode, DriveStrength)       PORT0->IOCR4 = (PORT0->IOCR4 & ~0xF8000000) | (Mode << 27); PORT0->PDR0 = (PORT0->PDR0 & ~0x70000000) | (DriveStrength << 28)
#define Control_P0_8(Mode, DriveStrength)       PORT0->IOCR8 = (PORT0->IOCR8 & ~0x000000F8) | (Mode << 3); PORT0->PDR1 = (PORT0->PDR1 & ~0x00000007) | (DriveStrength)
#define Control_P0_9(Mode, DriveStrength)       PORT0->IOCR8 = (PORT0->IOCR8 & ~0x0000F800) | (Mode << 11); PORT0->PDR1 = (PORT0->PDR1 & ~0x00000070) | (DriveStrength << 4)
#define Control_P0_10(Mode, DriveStrength)      PORT0->IOCR8 = (PORT0->IOCR8 & ~0x00F80000) | (Mode << 19); PORT0->PDR1 = (PORT0->PDR1 & ~0x00000700) | (DriveStrength << 8)
#define Control_P0_11(Mode, DriveStrength)      PORT0->IOCR8 = (PORT0->IOCR8 & ~0xF8000000) | (Mode << 27); PORT0->PDR1 = (PORT0->PDR1 & ~0x00007000) | (DriveStrength << 12)
#define Control_P0_12(Mode, DriveStrength)      PORT0->IOCR12 = (PORT0->IOCR12 & ~0x000000F8) | (Mode << 3); PORT0->PDR1 = (PORT0->PDR1 & ~0x00070000) | (DriveStrength << 16)
#define Control_P0_13(Mode, DriveStrength)      PORT0->IOCR12 = (PORT0->IOCR12 & ~0x0000F800) | (Mode << 11); PORT0->PDR1 = (PORT0->PDR1 & ~0x00700000) | (DriveStrength << 20)
#define Control_P0_14(Mode, DriveStrength)      PORT0->IOCR12 = (PORT0->IOCR12 & ~0x00F80000) | (Mode << 19); PORT0->PDR1 = (PORT0->PDR1 & ~0x07000000) | (DriveStrength << 24)
#define Control_P0_15(Mode, DriveStrength)      PORT0->IOCR12 = (PORT0->IOCR12 & ~0xF8000000) | (Mode << 27); PORT0->PDR1 = (PORT0->PDR1 & ~0x70000000) | (DriveStrength << 28)

//********************************************

#define SET_P1_0       PORT1->OMR = 0x00000001
#define SET_P1_1       PORT1->OMR = 0x00000002
#define SET_P1_2       PORT1->OMR = 0x00000004
#define SET_P1_3       PORT1->OMR = 0x00000008
#define SET_P1_4       PORT1->OMR = 0x00000010
#define SET_P1_5       PORT1->OMR = 0x00000020
#define SET_P1_6       PORT1->OMR = 0x00000040
#define SET_P1_7       PORT1->OMR = 0x00000080
#define SET_P1_8       PORT1->OMR = 0x00000100
#define SET_P1_9       PORT1->OMR = 0x00000200
#define SET_P1_10       PORT1->OMR = 0x00000400
#define SET_P1_11       PORT1->OMR = 0x00000800
#define SET_P1_12       PORT1->OMR = 0x00001000
#define SET_P1_13       PORT1->OMR = 0x00002000
#define SET_P1_14       PORT1->OMR = 0x00004000
#define SET_P1_15       PORT1->OMR = 0x00008000

#define RESET_P1_0       PORT1->OMR = 0x00010000
#define RESET_P1_1       PORT1->OMR = 0x00020000
#define RESET_P1_2       PORT1->OMR = 0x00040000
#define RESET_P1_3       PORT1->OMR = 0x00080000
#define RESET_P1_4       PORT1->OMR = 0x00100000
#define RESET_P1_5       PORT1->OMR = 0x00200000
#define RESET_P1_6       PORT1->OMR = 0x00400000
#define RESET_P1_7       PORT1->OMR = 0x00800000
#define RESET_P1_8       PORT1->OMR = 0x01000000
#define RESET_P1_9       PORT1->OMR = 0x02000000
#define RESET_P1_10       PORT1->OMR = 0x04000000
#define RESET_P1_11       PORT1->OMR= 0x08000000
#define RESET_P1_12       PORT1->OMR = 0x10000000
#define RESET_P1_13       PORT1->OMR = 0x20000000
#define RESET_P1_14       PORT1->OMR = 0x40000000
#define RESET_P1_15       PORT1->OMR = 0x80000000

#define TOGGLE_P1_0       PORT1->OMR = 0x00010001
#define TOGGLE_P1_1       PORT1->OMR = 0x00020002
#define TOGGLE_P1_2       PORT1->OMR = 0x00040004
#define TOGGLE_P1_3       PORT1->OMR = 0x00080008
#define TOGGLE_P1_4       PORT1->OMR = 0x00100010
#define TOGGLE_P1_5       PORT1->OMR = 0x00200020
#define TOGGLE_P1_6       PORT1->OMR = 0x00400040
#define TOGGLE_P1_7       PORT1->OMR = 0x00800080
#define TOGGLE_P1_8       PORT1->OMR = 0x01000100
#define TOGGLE_P1_9       PORT1->OMR = 0x02000200
#define TOGGLE_P1_10       PORT1->OMR = 0x04000400
#define TOGGLE_P1_11       PORT1->OMR = 0x08000800
#define TOGGLE_P1_12       PORT1->OMR = 0x10001000
#define TOGGLE_P1_13       PORT1->OMR = 0x20002000
#define TOGGLE_P1_14       PORT1->OMR = 0x40004000
#define TOGGLE_P1_15       PORT1->OMR = 0x80008000

#define Control_P1_0(Mode, DriveStrength)       PORT1->IOCR0 = (PORT1->IOCR0 & ~0x000000F8) | (Mode << 3); PORT1->PDR0 = (PORT1->PDR0 & ~0x00000007) | (DriveStrength)
#define Control_P1_1(Mode, DriveStrength)       PORT1->IOCR0 = (PORT1->IOCR0 & ~0x0000F800) | (Mode << 11); PORT1->PDR0 = (PORT1->PDR0 & ~0x00000070) | (DriveStrength << 4)
#define Control_P1_2(Mode, DriveStrength)       PORT1->IOCR0 = (PORT1->IOCR0 & ~0x00F80000) | (Mode << 19); PORT1->PDR0 = (PORT1->PDR0 & ~0x00000700) | (DriveStrength << 8)
#define Control_P1_3(Mode, DriveStrength)       PORT1->IOCR0 = (PORT1->IOCR0 & ~0xF8000000) | (Mode << 27); PORT1->PDR0 = (PORT1->PDR0 & ~0x00007000) | (DriveStrength << 12)
#define Control_P1_4(Mode, DriveStrength)       PORT1->IOCR4 = (PORT1->IOCR4 & ~0x000000F8) | (Mode << 3); PORT1->PDR0 = (PORT1->PDR0 & ~0x00070000) | (DriveStrength << 16)
#define Control_P1_5(Mode, DriveStrength)       PORT1->IOCR4 = (PORT1->IOCR4 & ~0x0000F800) | (Mode << 11); PORT1->PDR0 = (PORT1->PDR0 & ~0x00700000) | (DriveStrength << 20)
#define Control_P1_6(Mode, DriveStrength)       PORT1->IOCR4 = (PORT1->IOCR4 & ~0x00F80000) | (Mode << 19); PORT1->PDR0 = (PORT1->PDR0 & ~0x07000000) | (DriveStrength << 24)
#define Control_P1_7(Mode, DriveStrength)       PORT1->IOCR4 = (PORT1->IOCR4 & ~0xF8000000) | (Mode << 27); PORT1->PDR0 = (PORT1->PDR0 & ~0x70000000) | (DriveStrength << 28)
#define Control_P1_8(Mode, DriveStrength)       PORT1->IOCR8 = (PORT1->IOCR8 & ~0x000000F8) | (Mode << 3); PORT1->PDR1 = (PORT1->PDR1 & ~0x00000007) | (DriveStrength)
#define Control_P1_9(Mode, DriveStrength)       PORT1->IOCR8 = (PORT1->IOCR8 & ~0x0000F800) | (Mode << 11); PORT1->PDR1 = (PORT1->PDR1 & ~0x00000070) | (DriveStrength << 4)
#define Control_P1_10(Mode, DriveStrength)      PORT1->IOCR8 = (PORT1->IOCR8 & ~0x00F80000) | (Mode << 19); PORT1->PDR1 = (PORT1->PDR1 & ~0x00000700) | (DriveStrength << 8)
#define Control_P1_11(Mode, DriveStrength)      PORT1->IOCR8 = (PORT1->IOCR8 & ~0xF8000000) | (Mode << 27); PORT1->PDR1 = (PORT1->PDR1 & ~0x00007000) | (DriveStrength << 12)
#define Control_P1_12(Mode, DriveStrength)      PORT1->IOCR12 = (PORT1->IOCR12 & ~0x000000F8) | (Mode << 3); PORT1->PDR1 = (PORT1->PDR1 & ~0x00070000) | (DriveStrength << 16)
#define Control_P1_13(Mode, DriveStrength)      PORT1->IOCR12 = (PORT1->IOCR12 & ~0x0000F800) | (Mode << 11); PORT1->PDR1 = (PORT1->PDR1 & ~0x00700000) | (DriveStrength << 20)
#define Control_P1_14(Mode, DriveStrength)      PORT1->IOCR12 = (PORT1->IOCR12 & ~0x00F80000) | (Mode << 19); PORT1->PDR1 = (PORT1->PDR1 & ~0x07000000) | (DriveStrength << 24)
#define Control_P1_15(Mode, DriveStrength)      PORT1->IOCR12 = (PORT1->IOCR12 & ~0xF8000000) | (Mode << 27); PORT1->PDR1 = (PORT1->PDR1 & ~0x70000000) | (DriveStrength << 28)

//********************************************

#define SET_P2_0       PORT2->OMR = 0x00000001
#define SET_P2_1       PORT2->OMR = 0x00000002
#define SET_P2_2       PORT2->OMR = 0x00000004
#define SET_P2_3       PORT2->OMR = 0x00000008
#define SET_P2_4       PORT2->OMR = 0x00000010
#define SET_P2_5       PORT2->OMR = 0x00000020
#define SET_P2_6       PORT2->OMR = 0x00000040
#define SET_P2_7       PORT2->OMR = 0x00000080
#define SET_P2_8       PORT2->OMR = 0x00000100
#define SET_P2_9       PORT2->OMR = 0x00000200
#define SET_P2_10       PORT2->OMR = 0x00000400
#define SET_P2_11       PORT2->OMR = 0x00000800
#define SET_P2_12       PORT2->OMR = 0x00001000
#define SET_P2_13       PORT2->OMR = 0x00002000
#define SET_P2_14       PORT2->OMR = 0x00004000
#define SET_P2_15       PORT2->OMR = 0x00008000

#define RESET_P2_0       PORT2->OMR = 0x00010000
#define RESET_P2_1       PORT2->OMR = 0x00020000
#define RESET_P2_2       PORT2->OMR = 0x00040000
#define RESET_P2_3       PORT2->OMR = 0x00080000
#define RESET_P2_4       PORT2->OMR = 0x00100000
#define RESET_P2_5       PORT2->OMR = 0x00200000
#define RESET_P2_6       PORT2->OMR = 0x00400000
#define RESET_P2_7       PORT2->OMR = 0x00800000
#define RESET_P2_8       PORT2->OMR = 0x01000000
#define RESET_P2_9       PORT2->OMR = 0x02000000
#define RESET_P2_10       PORT2->OMR = 0x04000000
#define RESET_P2_11       PORT2->OMR= 0x08000000
#define RESET_P2_12       PORT2->OMR = 0x10000000
#define RESET_P2_13       PORT2->OMR = 0x20000000
#define RESET_P2_14       PORT2->OMR = 0x40000000
#define RESET_P2_15       PORT2->OMR = 0x80000000

#define TOGGLE_P2_0       PORT2->OMR = 0x00010001
#define TOGGLE_P2_1       PORT2->OMR = 0x00020002
#define TOGGLE_P2_2       PORT2->OMR = 0x00040004
#define TOGGLE_P2_3       PORT2->OMR = 0x00080008
#define TOGGLE_P2_4       PORT2->OMR = 0x00100010
#define TOGGLE_P2_5       PORT2->OMR = 0x00200020
#define TOGGLE_P2_6       PORT2->OMR = 0x00400040
#define TOGGLE_P2_7       PORT2->OMR = 0x00800080
#define TOGGLE_P2_8       PORT2->OMR = 0x01000100
#define TOGGLE_P2_9       PORT2->OMR = 0x02000200
#define TOGGLE_P2_10       PORT2->OMR = 0x04000400
#define TOGGLE_P2_11       PORT2->OMR = 0x08000800
#define TOGGLE_P2_12       PORT2->OMR = 0x10001000
#define TOGGLE_P2_13       PORT2->OMR = 0x20002000
#define TOGGLE_P2_14       PORT2->OMR = 0x40004000
#define TOGGLE_P2_15       PORT2->OMR = 0x80008000

#define Control_P2_0(Mode, DriveStrength)       PORT2->IOCR0 = (PORT2->IOCR0 & ~0x000000F8) | (Mode << 3); PORT2->PDR0 = (PORT2->PDR0 & ~0x00000007) | (DriveStrength)
#define Control_P2_1(Mode, DriveStrength)       PORT2->IOCR0 = (PORT2->IOCR0 & ~0x0000F800) | (Mode << 11); PORT2->PDR0 = (PORT2->PDR0 & ~0x00000070) | (DriveStrength << 4)
#define Control_P2_2(Mode, DriveStrength)       PORT2->IOCR0 = (PORT2->IOCR0 & ~0x00F80000) | (Mode << 19); PORT2->PDR0 = (PORT2->PDR0 & ~0x00000700) | (DriveStrength << 8)
#define Control_P2_3(Mode, DriveStrength)       PORT2->IOCR0 = (PORT2->IOCR0 & ~0xF8000000) | (Mode << 27); PORT2->PDR0 = (PORT2->PDR0 & ~0x00007000) | (DriveStrength << 12)
#define Control_P2_4(Mode, DriveStrength)       PORT2->IOCR4 = (PORT2->IOCR4 & ~0x000000F8) | (Mode << 3); PORT2->PDR0 = (PORT2->PDR0 & ~0x00070000) | (DriveStrength << 16)
#define Control_P2_5(Mode, DriveStrength)       PORT2->IOCR4 = (PORT2->IOCR4 & ~0x0000F800) | (Mode << 11); PORT2->PDR0 = (PORT2->PDR0 & ~0x00700000) | (DriveStrength << 20)
#define Control_P2_6(Mode, DriveStrength)       PORT2->IOCR4 = (PORT2->IOCR4 & ~0x00F80000) | (Mode << 19); PORT2->PDR0 = (PORT2->PDR0 & ~0x07000000) | (DriveStrength << 24)
#define Control_P2_7(Mode, DriveStrength)       PORT2->IOCR4 = (PORT2->IOCR4 & ~0xF8000000) | (Mode << 27); PORT2->PDR0 = (PORT2->PDR0 & ~0x70000000) | (DriveStrength << 28)
#define Control_P2_8(Mode, DriveStrength)       PORT2->IOCR8 = (PORT2->IOCR8 & ~0x000000F8) | (Mode << 3); PORT2->PDR1 = (PORT2->PDR1 & ~0x00000007) | (DriveStrength)
#define Control_P2_9(Mode, DriveStrength)       PORT2->IOCR8 = (PORT2->IOCR8 & ~0x0000F800) | (Mode << 11); PORT2->PDR1 = (PORT2->PDR1 & ~0x00000070) | (DriveStrength << 4)
#define Control_P2_10(Mode, DriveStrength)      PORT2->IOCR8 = (PORT2->IOCR8 & ~0x00F80000) | (Mode << 19); PORT2->PDR1 = (PORT2->PDR1 & ~0x00000700) | (DriveStrength << 8)
#define Control_P2_11(Mode, DriveStrength)      PORT2->IOCR8 = (PORT2->IOCR8 & ~0xF8000000) | (Mode << 27); PORT2->PDR1 = (PORT2->PDR1 & ~0x00007000) | (DriveStrength << 12)
#define Control_P2_12(Mode, DriveStrength)      PORT2->IOCR12 = (PORT2->IOCR12 & ~0x000000F8) | (Mode << 3); PORT2->PDR1 = (PORT2->PDR1 & ~0x00070000) | (DriveStrength << 16)
#define Control_P2_13(Mode, DriveStrength)      PORT2->IOCR12 = (PORT2->IOCR12 & ~0x0000F800) | (Mode << 11); PORT2->PDR1 = (PORT2->PDR1 & ~0x00700000) | (DriveStrength << 20)
#define Control_P2_14(Mode, DriveStrength)      PORT2->IOCR12 = (PORT2->IOCR12 & ~0x00F80000) | (Mode << 19); PORT2->PDR1 = (PORT2->PDR1 & ~0x07000000) | (DriveStrength << 24)
#define Control_P2_15(Mode, DriveStrength)      PORT2->IOCR12 = (PORT2->IOCR12 & ~0xF8000000) | (Mode << 27); PORT2->PDR1 = (PORT2->PDR1 & ~0x70000000) | (DriveStrength << 28)

//********************************************

#define SET_P3_0       PORT3->OMR = 0x00000001
#define SET_P3_1       PORT3->OMR = 0x00000002
#define SET_P3_2       PORT3->OMR = 0x00000004
#define SET_P3_3       PORT3->OMR = 0x00000008
#define SET_P3_4       PORT3->OMR = 0x00000010
#define SET_P3_5       PORT3->OMR = 0x00000020
#define SET_P3_6       PORT3->OMR = 0x00000040
#define SET_P3_7       PORT3->OMR = 0x00000080
#define SET_P3_8       PORT3->OMR = 0x00000100
#define SET_P3_9       PORT3->OMR = 0x00000200
#define SET_P3_10       PORT3->OMR = 0x00000400
#define SET_P3_11       PORT3->OMR = 0x00000800
#define SET_P3_12       PORT3->OMR = 0x00001000
#define SET_P3_13       PORT3->OMR = 0x00002000
#define SET_P3_14       PORT3->OMR = 0x00004000
#define SET_P3_15       PORT3->OMR = 0x00008000

#define RESET_P3_0       PORT3->OMR = 0x00010000
#define RESET_P3_1       PORT3->OMR = 0x00020000
#define RESET_P3_2       PORT3->OMR = 0x00040000
#define RESET_P3_3       PORT3->OMR = 0x00080000
#define RESET_P3_4       PORT3->OMR = 0x00100000
#define RESET_P3_5       PORT3->OMR = 0x00200000
#define RESET_P3_6       PORT3->OMR = 0x00400000
#define RESET_P3_7       PORT3->OMR = 0x00800000
#define RESET_P3_8       PORT3->OMR = 0x01000000
#define RESET_P3_9       PORT3->OMR = 0x02000000
#define RESET_P3_10       PORT3->OMR = 0x04000000
#define RESET_P3_11       PORT3->OMR= 0x08000000
#define RESET_P3_12       PORT3->OMR = 0x10000000
#define RESET_P3_13       PORT3->OMR = 0x20000000
#define RESET_P3_14       PORT3->OMR = 0x40000000
#define RESET_P3_15       PORT3->OMR = 0x80000000

#define TOGGLE_P3_0       PORT3->OMR = 0x00010001
#define TOGGLE_P3_1       PORT3->OMR = 0x00020002
#define TOGGLE_P3_2       PORT3->OMR = 0x00040004
#define TOGGLE_P3_3       PORT3->OMR = 0x00080008
#define TOGGLE_P3_4       PORT3->OMR = 0x00100010
#define TOGGLE_P3_5       PORT3->OMR = 0x00200020
#define TOGGLE_P3_6       PORT3->OMR = 0x00400040
#define TOGGLE_P3_7       PORT3->OMR = 0x00800080
#define TOGGLE_P3_8       PORT3->OMR = 0x01000100
#define TOGGLE_P3_9       PORT3->OMR = 0x02000200
#define TOGGLE_P3_10       PORT3->OMR = 0x04000400
#define TOGGLE_P3_11       PORT3->OMR = 0x08000800
#define TOGGLE_P3_12       PORT3->OMR = 0x10001000
#define TOGGLE_P3_13       PORT3->OMR = 0x20002000
#define TOGGLE_P3_14       PORT3->OMR = 0x40004000
#define TOGGLE_P3_15       PORT3->OMR = 0x80008000

#define Control_P3_0(Mode, DriveStrength)       PORT3->IOCR0 = (PORT3->IOCR0 & ~0x000000F8) | (Mode << 3); PORT3->PDR0 = (PORT3->PDR0 & ~0x00000007) | (DriveStrength)
#define Control_P3_1(Mode, DriveStrength)       PORT3->IOCR0 = (PORT3->IOCR0 & ~0x0000F800) | (Mode << 11); PORT3->PDR0 = (PORT3->PDR0 & ~0x00000070) | (DriveStrength << 4)
#define Control_P3_2(Mode, DriveStrength)       PORT3->IOCR0 = (PORT3->IOCR0 & ~0x00F80000) | (Mode << 19); PORT3->PDR0 = (PORT3->PDR0 & ~0x00000700) | (DriveStrength << 8)
#define Control_P3_3(Mode, DriveStrength)       PORT3->IOCR0 = (PORT3->IOCR0 & ~0xF8000000) | (Mode << 27); PORT3->PDR0 = (PORT3->PDR0 & ~0x00007000) | (DriveStrength << 12)
#define Control_P3_4(Mode, DriveStrength)       PORT3->IOCR4 = (PORT3->IOCR4 & ~0x000000F8) | (Mode << 3); PORT3->PDR0 = (PORT3->PDR0 & ~0x00070000) | (DriveStrength << 16)
#define Control_P3_5(Mode, DriveStrength)       PORT3->IOCR4 = (PORT3->IOCR4 & ~0x0000F800) | (Mode << 11); PORT3->PDR0 = (PORT3->PDR0 & ~0x00700000) | (DriveStrength << 20)
#define Control_P3_6(Mode, DriveStrength)       PORT3->IOCR4 = (PORT3->IOCR4 & ~0x00F80000) | (Mode << 19); PORT3->PDR0 = (PORT3->PDR0 & ~0x07000000) | (DriveStrength << 24)
#define Control_P3_7(Mode, DriveStrength)       PORT3->IOCR4 = (PORT3->IOCR4 & ~0xF8000000) | (Mode << 27); PORT3->PDR0 = (PORT3->PDR0 & ~0x70000000) | (DriveStrength << 28)
#define Control_P3_8(Mode, DriveStrength)       PORT3->IOCR8 = (PORT3->IOCR8 & ~0x000000F8) | (Mode << 3); PORT3->PDR1 = (PORT3->PDR1 & ~0x00000007) | (DriveStrength)
#define Control_P3_9(Mode, DriveStrength)       PORT3->IOCR8 = (PORT3->IOCR8 & ~0x0000F800) | (Mode << 11); PORT3->PDR1 = (PORT3->PDR1 & ~0x00000070) | (DriveStrength << 4)
#define Control_P3_10(Mode, DriveStrength)      PORT3->IOCR8 = (PORT3->IOCR8 & ~0x00F80000) | (Mode << 19); PORT3->PDR1 = (PORT3->PDR1 & ~0x00000700) | (DriveStrength << 8)
#define Control_P3_11(Mode, DriveStrength)      PORT3->IOCR8 = (PORT3->IOCR8 & ~0xF8000000) | (Mode << 27); PORT3->PDR1 = (PORT3->PDR1 & ~0x00007000) | (DriveStrength << 12)
#define Control_P3_12(Mode, DriveStrength)      PORT3->IOCR12 = (PORT3->IOCR12 & ~0x000000F8) | (Mode << 3); PORT3->PDR1 = (PORT3->PDR1 & ~0x00070000) | (DriveStrength << 16)
#define Control_P3_13(Mode, DriveStrength)      PORT3->IOCR12 = (PORT3->IOCR12 & ~0x0000F800) | (Mode << 11); PORT3->PDR1 = (PORT3->PDR1 & ~0x00700000) | (DriveStrength << 20)
#define Control_P3_14(Mode, DriveStrength)      PORT3->IOCR12 = (PORT3->IOCR12 & ~0x00F80000) | (Mode << 19); PORT3->PDR1 = (PORT3->PDR1 & ~0x07000000) | (DriveStrength << 24)
#define Control_P3_15(Mode, DriveStrength)      PORT3->IOCR12 = (PORT3->IOCR12 & ~0xF8000000) | (Mode << 27); PORT3->PDR1 = (PORT3->PDR1 & ~0x70000000) | (DriveStrength << 28)

//********************************************

#define SET_P4_0       PORT4->OMR = 0x00000001
#define SET_P4_1       PORT4->OMR = 0x00000002
#define SET_P4_2       PORT4->OMR = 0x00000004
#define SET_P4_3       PORT4->OMR = 0x00000008
#define SET_P4_4       PORT4->OMR = 0x00000010
#define SET_P4_5       PORT4->OMR = 0x00000020
#define SET_P4_6       PORT4->OMR = 0x00000040
#define SET_P4_7       PORT4->OMR = 0x00000080

#define RESET_P4_0       PORT4->OMR = 0x00010000
#define RESET_P4_1       PORT4->OMR = 0x00020000
#define RESET_P4_2       PORT4->OMR = 0x00040000
#define RESET_P4_3       PORT4->OMR = 0x00080000
#define RESET_P4_4       PORT4->OMR = 0x00100000
#define RESET_P4_5       PORT4->OMR = 0x00200000
#define RESET_P4_6       PORT4->OMR = 0x00400000
#define RESET_P4_7       PORT4->OMR = 0x00800000

#define TOGGLE_P4_0       PORT4->OMR = 0x00010001
#define TOGGLE_P4_1       PORT4->OMR = 0x00020002
#define TOGGLE_P4_2       PORT4->OMR = 0x00040004
#define TOGGLE_P4_3       PORT4->OMR = 0x00080008
#define TOGGLE_P4_4       PORT4->OMR = 0x00100010
#define TOGGLE_P4_5       PORT4->OMR = 0x00200020
#define TOGGLE_P4_6       PORT4->OMR = 0x00400040
#define TOGGLE_P4_7       PORT4->OMR = 0x00800080

#define Control_P4_0(Mode, DriveStrength)       PORT4->IOCR0 = (PORT4->IOCR0 & ~0x000000F8) | (Mode << 3); PORT4->PDR0 = (PORT4->PDR0 & ~0x00000007) | (DriveStrength)
#define Control_P4_1(Mode, DriveStrength)       PORT4->IOCR0 = (PORT4->IOCR0 & ~0x0000F800) | (Mode << 11); PORT4->PDR0 = (PORT4->PDR0 & ~0x00000070) | (DriveStrength << 4)
#define Control_P4_2(Mode, DriveStrength)       PORT4->IOCR0 = (PORT4->IOCR0 & ~0x00F80000) | (Mode << 19); PORT4->PDR0 = (PORT4->PDR0 & ~0x00000700) | (DriveStrength << 8)
#define Control_P4_3(Mode, DriveStrength)       PORT4->IOCR0 = (PORT4->IOCR0 & ~0xF8000000) | (Mode << 27); PORT4->PDR0 = (PORT4->PDR0 & ~0x00007000) | (DriveStrength << 12)
#define Control_P4_4(Mode, DriveStrength)       PORT4->IOCR4 = (PORT4->IOCR4 & ~0x000000F8) | (Mode << 3); PORT4->PDR0 = (PORT4->PDR0 & ~0x00070000) | (DriveStrength << 16)
#define Control_P4_5(Mode, DriveStrength)       PORT4->IOCR4 = (PORT4->IOCR4 & ~0x0000F800) | (Mode << 11); PORT4->PDR0 = (PORT4->PDR0 & ~0x00700000) | (DriveStrength << 20)
#define Control_P4_6(Mode, DriveStrength)       PORT4->IOCR4 = (PORT4->IOCR4 & ~0x00F80000) | (Mode << 19); PORT4->PDR0 = (PORT4->PDR0 & ~0x07000000) | (DriveStrength << 24)
#define Control_P4_7(Mode, DriveStrength)       PORT4->IOCR4 = (PORT4->IOCR4 & ~0xF8000000) | (Mode << 27); PORT4->PDR0 = (PORT4->PDR0 & ~0x70000000) | (DriveStrength << 28)

//********************************************

#define SET_P5_0       PORT5->OMR = 0x00000001
#define SET_P5_1       PORT5->OMR = 0x00000002
#define SET_P5_2       PORT5->OMR = 0x00000004
#define SET_P5_3       PORT5->OMR = 0x00000008
#define SET_P5_4       PORT5->OMR = 0x00000010
#define SET_P5_5       PORT5->OMR = 0x00000020
#define SET_P5_6       PORT5->OMR = 0x00000040
#define SET_P5_7       PORT5->OMR = 0x00000080
#define SET_P5_8       PORT5->OMR = 0x00000100
#define SET_P5_9       PORT5->OMR = 0x00000200
#define SET_P5_10       PORT5->OMR = 0x00000400
#define SET_P5_11       PORT5->OMR = 0x00000800
#define SET_P5_12       PORT5->OMR = 0x00001000
#define SET_P5_13       PORT5->OMR = 0x00002000
#define SET_P5_14       PORT5->OMR = 0x00004000
#define SET_P5_15       PORT5->OMR = 0x00008000

#define RESET_P5_0       PORT5->OMR = 0x00010000
#define RESET_P5_1       PORT5->OMR = 0x00020000
#define RESET_P5_2       PORT5->OMR = 0x00040000
#define RESET_P5_3       PORT5->OMR = 0x00080000
#define RESET_P5_4       PORT5->OMR = 0x00100000
#define RESET_P5_5       PORT5->OMR = 0x00200000
#define RESET_P5_6       PORT5->OMR = 0x00400000
#define RESET_P5_7       PORT5->OMR = 0x00800000
#define RESET_P5_8       PORT5->OMR = 0x01000000
#define RESET_P5_9       PORT5->OMR = 0x02000000
#define RESET_P5_10       PORT5->OMR = 0x04000000
#define RESET_P5_11       PORT5->OMR= 0x08000000
#define RESET_P5_12       PORT5->OMR = 0x10000000
#define RESET_P5_13       PORT5->OMR = 0x20000000
#define RESET_P5_14       PORT5->OMR = 0x40000000
#define RESET_P5_15       PORT5->OMR = 0x80000000

#define TOGGLE_P5_0       PORT5->OMR = 0x00010001
#define TOGGLE_P5_1       PORT5->OMR = 0x00020002
#define TOGGLE_P5_2       PORT5->OMR = 0x00040004
#define TOGGLE_P5_3       PORT5->OMR = 0x00080008
#define TOGGLE_P5_4       PORT5->OMR = 0x00100010
#define TOGGLE_P5_5       PORT5->OMR = 0x00200020
#define TOGGLE_P5_6       PORT5->OMR = 0x00400040
#define TOGGLE_P5_7       PORT5->OMR = 0x00800080
#define TOGGLE_P5_8       PORT5->OMR = 0x01000100
#define TOGGLE_P5_9       PORT5->OMR = 0x02000200
#define TOGGLE_P5_10       PORT5->OMR = 0x04000400
#define TOGGLE_P5_11       PORT5->OMR = 0x08000800
#define TOGGLE_P5_12       PORT5->OMR = 0x10001000
#define TOGGLE_P5_13       PORT5->OMR = 0x20002000
#define TOGGLE_P5_14       PORT5->OMR = 0x40004000
#define TOGGLE_P5_15       PORT5->OMR = 0x80008000

#define Control_P5_0(Mode, DriveStrength)       PORT5->IOCR0 = (PORT5->IOCR0 & ~0x000000F8) | (Mode << 3); PORT5->PDR0 = (PORT5->PDR0 & ~0x00000007) | (DriveStrength)
#define Control_P5_1(Mode, DriveStrength)       PORT5->IOCR0 = (PORT5->IOCR0 & ~0x0000F800) | (Mode << 11); PORT5->PDR0 = (PORT5->PDR0 & ~0x00000070) | (DriveStrength << 4)
#define Control_P5_2(Mode, DriveStrength)       PORT5->IOCR0 = (PORT5->IOCR0 & ~0x00F80000) | (Mode << 19); PORT5->PDR0 = (PORT5->PDR0 & ~0x00000700) | (DriveStrength << 8)
#define Control_P5_3(Mode, DriveStrength)       PORT5->IOCR0 = (PORT5->IOCR0 & ~0xF8000000) | (Mode << 27); PORT5->PDR0 = (PORT5->PDR0 & ~0x00007000) | (DriveStrength << 12)
#define Control_P5_4(Mode, DriveStrength)       PORT5->IOCR4 = (PORT5->IOCR4 & ~0x000000F8) | (Mode << 3); PORT5->PDR0 = (PORT5->PDR0 & ~0x00070000) | (DriveStrength << 16)
#define Control_P5_5(Mode, DriveStrength)       PORT5->IOCR4 = (PORT5->IOCR4 & ~0x0000F800) | (Mode << 11); PORT5->PDR0 = (PORT5->PDR0 & ~0x00700000) | (DriveStrength << 20)
#define Control_P5_6(Mode, DriveStrength)       PORT5->IOCR4 = (PORT5->IOCR4 & ~0x00F80000) | (Mode << 19); PORT5->PDR0 = (PORT5->PDR0 & ~0x07000000) | (DriveStrength << 24)
#define Control_P5_7(Mode, DriveStrength)       PORT5->IOCR4 = (PORT5->IOCR4 & ~0xF8000000) | (Mode << 27); PORT5->PDR0 = (PORT5->PDR0 & ~0x70000000) | (DriveStrength << 28)
#define Control_P5_8(Mode, DriveStrength)       PORT5->IOCR8 = (PORT5->IOCR8 & ~0x000000F8) | (Mode << 3); PORT5->PDR1 = (PORT5->PDR1 & ~0x00000007) | (DriveStrength)
#define Control_P5_9(Mode, DriveStrength)       PORT5->IOCR8 = (PORT5->IOCR8 & ~0x0000F800) | (Mode << 11); PORT5->PDR1 = (PORT5->PDR1 & ~0x00000070) | (DriveStrength << 4)
#define Control_P5_10(Mode, DriveStrength)      PORT5->IOCR8 = (PORT5->IOCR8 & ~0x00F80000) | (Mode << 19); PORT5->PDR1 = (PORT5->PDR1 & ~0x00000700) | (DriveStrength << 8)
#define Control_P5_11(Mode, DriveStrength)      PORT5->IOCR8 = (PORT5->IOCR8 & ~0xF8000000) | (Mode << 27); PORT5->PDR1 = (PORT5->PDR1 & ~0x00007000) | (DriveStrength << 12)
#define Control_P5_12(Mode, DriveStrength)      PORT5->IOCR12 = (PORT5->IOCR12 & ~0x000000F8) | (Mode << 3); PORT5->PDR1 = (PORT5->PDR1 & ~0x00070000) | (DriveStrength << 16)
#define Control_P5_13(Mode, DriveStrength)      PORT5->IOCR12 = (PORT5->IOCR12 & ~0x0000F800) | (Mode << 11); PORT5->PDR1 = (PORT5->PDR1 & ~0x00700000) | (DriveStrength << 20)
#define Control_P5_14(Mode, DriveStrength)      PORT5->IOCR12 = (PORT5->IOCR12 & ~0x00F80000) | (Mode << 19); PORT5->PDR1 = (PORT5->PDR1 & ~0x07000000) | (DriveStrength << 24)
#define Control_P5_15(Mode, DriveStrength)      PORT5->IOCR12 = (PORT5->IOCR12 & ~0xF8000000) | (Mode << 27); PORT5->PDR1 = (PORT5->PDR1 & ~0x70000000) | (DriveStrength << 28)

//********************************************

#define SET_P6_0       PORT6->OMR = 0x00000001
#define SET_P6_1       PORT6->OMR = 0x00000002
#define SET_P6_2       PORT6->OMR = 0x00000004
#define SET_P6_3       PORT6->OMR = 0x00000008
#define SET_P6_4       PORT6->OMR = 0x00000010
#define SET_P6_5       PORT6->OMR = 0x00000020
#define SET_P6_6       PORT6->OMR = 0x00000040
#define SET_P6_7       PORT6->OMR = 0x00000080
#define SET_P6_8       PORT6->OMR = 0x00000100
#define SET_P6_9       PORT6->OMR = 0x00000200
#define SET_P6_10       PORT6->OMR = 0x00000400
#define SET_P6_11       PORT6->OMR = 0x00000800
#define SET_P6_12       PORT6->OMR = 0x00001000
#define SET_P6_13       PORT6->OMR = 0x00002000
#define SET_P6_14       PORT6->OMR = 0x00004000
#define SET_P6_15       PORT6->OMR = 0x00008000

#define RESET_P6_0       PORT6->OMR = 0x00010000
#define RESET_P6_1       PORT6->OMR = 0x00020000
#define RESET_P6_2       PORT6->OMR = 0x00040000
#define RESET_P6_3       PORT6->OMR = 0x00080000
#define RESET_P6_4       PORT6->OMR = 0x00100000
#define RESET_P6_5       PORT6->OMR = 0x00200000
#define RESET_P6_6       PORT6->OMR = 0x00400000

#define TOGGLE_P6_0       PORT6->OMR = 0x00010001
#define TOGGLE_P6_1       PORT6->OMR = 0x00020002
#define TOGGLE_P6_2       PORT6->OMR = 0x00040004
#define TOGGLE_P6_3       PORT6->OMR = 0x00080008
#define TOGGLE_P6_4       PORT6->OMR = 0x00100010
#define TOGGLE_P6_5       PORT6->OMR = 0x00200020
#define TOGGLE_P6_6       PORT6->OMR = 0x00400040

#define Control_P6_0(Mode, DriveStrength)       PORT6->IOCR0 = (PORT6->IOCR0 & ~0x000000F8) | (Mode << 3); PORT6->PDR0 = (PORT6->PDR0 & ~0x00000007) | (DriveStrength)
#define Control_P6_1(Mode, DriveStrength)       PORT6->IOCR0 = (PORT6->IOCR0 & ~0x0000F800) | (Mode << 11); PORT6->PDR0 = (PORT6->PDR0 & ~0x00000070) | (DriveStrength << 4)
#define Control_P6_2(Mode, DriveStrength)       PORT6->IOCR0 = (PORT6->IOCR0 & ~0x00F80000) | (Mode << 19); PORT6->PDR0 = (PORT6->PDR0 & ~0x00000700) | (DriveStrength << 8)
#define Control_P6_3(Mode, DriveStrength)       PORT6->IOCR0 = (PORT6->IOCR0 & ~0xF8000000) | (Mode << 27); PORT6->PDR0 = (PORT6->PDR0 & ~0x00007000) | (DriveStrength << 12)
#define Control_P6_4(Mode, DriveStrength)       PORT6->IOCR4 = (PORT6->IOCR4 & ~0x000000F8) | (Mode << 3); PORT6->PDR0 = (PORT6->PDR0 & ~0x00070000) | (DriveStrength << 16)
#define Control_P6_5(Mode, DriveStrength)       PORT6->IOCR4 = (PORT6->IOCR4 & ~0x0000F800) | (Mode << 11); PORT6->PDR0 = (PORT6->PDR0 & ~0x00700000) | (DriveStrength << 20)
#define Control_P6_6(Mode, DriveStrength)       PORT6->IOCR4 = (PORT6->IOCR4 & ~0x00F80000) | (Mode << 19); PORT6->PDR0 = (PORT6->PDR0 & ~0x07000000) | (DriveStrength << 24)

//********************************************

#endif
