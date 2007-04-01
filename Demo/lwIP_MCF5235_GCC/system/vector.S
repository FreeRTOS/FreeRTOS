/*
    FreeRTOS MCF5235 port - Copyright (C) 2006 Christian Walter.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    FreeRTOS is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with FreeRTOS; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    A special exception to the GPL can be applied should you wish to distribute
    a combined work that includes FreeRTOS, without being obliged to provide
    the source code for any proprietary components.  See the licensing section
    of http://www.FreeRTOS.org for full details of how and when the exception
    can be applied.

    ***************************************************************************
    See http://www.FreeRTOS.org for documentation, latest information, license
    and contact details.  Please ensure to read the configuration and relevant
    port sections of the online documentation.

	Also see http://www.SafeRTOS.com for an IEC 61508 compliant version along
	with commercial development and support options.
    ***************************************************************************
*/

  .extern __stack
  .extern start
  .extern fec_handler
  .extern fec_if
  .extern decrement_timers
  .global __RAMVEC
  .global __ROMVEC

  .equ    MCF_PIT_PCSR0, IPSBAR + 0x150000
  .equ    MCF_PIT_PCSR_PIF, 0x0004

  .section  .vector_rom, "x"
__ROMVEC:
  .long   __stack               /* Reset: Initial Stack Pointer */
  .long   start                 /* Reset: Initial Program Counter */
  .long   VecDefault            /* Bus Error */
  .long   VecDefault            /* Address Error */
  .long   VecDefault            /* Illegal Instruction */
  .long   VecDefault            /* Zero Divison */
  .space  4                     /* reserved */
  .space  4                     /* reserved */
  .long   VecDefault            /* Privilege Violation */
  .long   VecDefault            /* Trace */
  .long   VecDefault            /* Unimplemented line-a opcode */
  .long   VecDefault            /* Unimplemented line-b opcode */
  .long   VecDefault            /* Non-PC breakpoint debug interrupt */
  .long   VecDefault            /* PC breakpoint debug interrupt */
  .long   VecDefault            /* Format Error */
  .long   VecDefault            /* Uninitialized Interrupt */
  .org    0x60
  .long   IRQSpurious           /* Spurious Interrupt */
  .long   IRQDefault            /* Level 1 Interrupt */
  .long   IRQDefault            /* Level 2 Interrupt */
  .long   IRQDefault            /* Level 3 Interrupt */
  .long   IRQDefault            /* Level 4 Interrupt */
  .long   IRQDefault            /* Level 5 Interrupt */
  .long   IRQDefault            /* Level 6 Interrupt */
  .long   IRQDefault            /* Level 7 Interrupt */
  .org    0x80
  .long   TrapDefault           /* TRAP 0 */
  .long   TrapDefault           /* TRAP 1 */
  .long   TrapDefault           /* TRAP 2 */
  .long   TrapDefault           /* TRAP 3 */
  .long   TrapDefault           /* TRAP 4 */
  .long   TrapDefault           /* TRAP 5 */
  .long   TrapDefault           /* TRAP 6 */
  .long   TrapDefault           /* TRAP 7 */
  .long   TrapDefault           /* TRAP 8 */
  .long   TrapDefault           /* TRAP 9 */
  .long   TrapDefault           /* TRAP 10 */
  .long   TrapDefault           /* TRAP 11 */
  .long   TrapDefault           /* TRAP 12 */
  .long   TrapDefault           /* TRAP 13 */
  .long   TrapDefault           /* TRAP 14 */
  .long   TrapDefault           /* TRAP 15 */
  .org    0x100
  .long   IRQDefault            /* User-Defined Interrupt 0 */
  .long   IRQDefault            /* User-Defined Interrupt 1 */
  .long   IRQDefault            /* User-Defined Interrupt 2 */
  .long   IRQDefault            /* User-Defined Interrupt 3 */
  .long   IRQDefault            /* User-Defined Interrupt 4 */
  .long   IRQDefault            /* User-Defined Interrupt 5 */
  .long   IRQDefault            /* User-Defined Interrupt 6 */
  .long   IRQDefault            /* User-Defined Interrupt 7 */
  .long   IRQDefault            /* User-Defined Interrupt 8 */
  .long   IRQDefault            /* User-Defined Interrupt 9 */
  .long   IRQDefault            /* User-Defined Interrupt 10 */
  .long   IRQDefault            /* User-Defined Interrupt 11 */
  .long   IRQDefault            /* User-Defined Interrupt 12 */
  .long   IRQDefault            /* User-Defined Interrupt 13 */
  .long   IRQDefault            /* User-Defined Interrupt 14 */
  .long   IRQDefault            /* User-Defined Interrupt 15 */
  .long   IRQDefault            /* User-Defined Interrupt 16 */
  .long   IRQDefault            /* User-Defined Interrupt 17 */
  .long   IRQDefault            /* User-Defined Interrupt 18 */
  .long   IRQDefault            /* User-Defined Interrupt 19 */
  .long   IRQDefault            /* User-Defined Interrupt 20 */
  .long   IRQDefault            /* User-Defined Interrupt 21 */
  .long   IRQDefault            /* User-Defined Interrupt 22 */
  .long   IRQDefault            /* Transmit frame interrupt */
  .long   IRQDefault            /* Transmit buffer interrupt */
  .long   IRQDefault            /* Transmit FIFO underrun */
  .long   IRQDefault            /* Collision retry limit */
  .long   IRQDefault            /* Receive frame interrupt */
  .long   IRQDefault            /* Receive buffer interrupt */
  .long   IRQDefault            /* MII interrupt */
  .long   IRQDefault            /* Late collision */
  .long   IRQDefault            /* Heartbeat error */
  .long   IRQDefault            /* Graceful stop complete */
  .long   IRQDefault            /* Ethernet bus error */
  .long   IRQDefault            /* Babbling transmit error */
  .long   IRQDefault            /* Babbling receive error */
  .long   IRQDefault            /* Timer interrupt */
  .long   IRQDefault            /* User-Defined Interrupt 37 */
  .long   IRQDefault            /* User-Defined Interrupt 38 */
  .long   IRQDefault            /* User-Defined Interrupt 39 */
  .long   IRQDefault            /* User-Defined Interrupt 40 */
  .long   IRQDefault            /* User-Defined Interrupt 41 */
  .long   IRQDefault            /* User-Defined Interrupt 42 */
  .long   IRQDefault            /* User-Defined Interrupt 43 */
  .long   IRQDefault            /* User-Defined Interrupt 44 */
  .long   IRQDefault            /* User-Defined Interrupt 45 */
  .long   IRQDefault            /* User-Defined Interrupt 46 */
  .long   IRQDefault            /* User-Defined Interrupt 47 */
  .long   IRQDefault            /* User-Defined Interrupt 48 */
  .long   IRQDefault            /* User-Defined Interrupt 49 */
  .long   IRQDefault            /* User-Defined Interrupt 50 */
  .long   IRQDefault            /* User-Defined Interrupt 51 */
  .long   IRQDefault            /* User-Defined Interrupt 52 */
  .long   IRQDefault            /* User-Defined Interrupt 53 */
  .long   IRQDefault            /* User-Defined Interrupt 54 */
  .long   IRQDefault            /* User-Defined Interrupt 55 */
  .long   IRQDefault            /* User-Defined Interrupt 56 */
  .long   IRQDefault            /* User-Defined Interrupt 57 */
  .long   IRQDefault            /* User-Defined Interrupt 58 */
  .long   IRQDefault            /* User-Defined Interrupt 59 */
  .long   IRQDefault            /* User-Defined Interrupt 60 */
  .long   IRQDefault            /* User-Defined Interrupt 61 */
  .long   IRQDefault            /* User-Defined Interrupt 62 */
  .long   IRQDefault            /* User-Defined Interrupt 63 */
  .long   IRQDefault            /* User-Defined Interrupt 64 */
  .long   IRQDefault            /* User-Defined Interrupt 65 */
  .long   IRQDefault            /* User-Defined Interrupt 66 */
  .long   IRQDefault            /* User-Defined Interrupt 67 */
  .long   IRQDefault            /* User-Defined Interrupt 68 */
  .long   IRQDefault            /* User-Defined Interrupt 69 */
  .long   IRQDefault            /* User-Defined Interrupt 70 */
  .long   IRQDefault            /* User-Defined Interrupt 71 */
  .long   IRQDefault            /* User-Defined Interrupt 72 */
  .long   IRQDefault            /* User-Defined Interrupt 73 */
  .long   IRQDefault            /* User-Defined Interrupt 74 */
  .long   IRQDefault            /* User-Defined Interrupt 75 */
  .long   IRQDefault            /* User-Defined Interrupt 76 */
  .long   IRQDefault            /* User-Defined Interrupt 77 */
  .long   IRQDefault            /* User-Defined Interrupt 78 */
  .long   IRQDefault            /* User-Defined Interrupt 79 */
  .long   IRQDefault            /* User-Defined Interrupt 80 */
  .long   IRQDefault            /* User-Defined Interrupt 81 */
  .long   IRQDefault            /* User-Defined Interrupt 82 */
  .long   IRQDefault            /* User-Defined Interrupt 83 */
  .long   IRQDefault            /* User-Defined Interrupt 84 */
  .long   IRQDefault            /* User-Defined Interrupt 85 */
  .long   IRQDefault            /* User-Defined Interrupt 86 */
  .long   IRQDefault            /* User-Defined Interrupt 87 */
  .long   IRQDefault            /* User-Defined Interrupt 88 */
  .long   IRQDefault            /* User-Defined Interrupt 89 */
  .long   IRQDefault            /* User-Defined Interrupt 90 */
  .long   IRQDefault            /* User-Defined Interrupt 91 */
  .long   IRQDefault            /* User-Defined Interrupt 92 */
  .long   IRQDefault            /* User-Defined Interrupt 93 */
  .long   IRQDefault            /* User-Defined Interrupt 94 */
  .long   IRQDefault            /* User-Defined Interrupt 95 */
  .long   IRQDefault            /* User-Defined Interrupt 96 */
  .long   IRQDefault            /* User-Defined Interrupt 97 */
  .long   IRQDefault            /* User-Defined Interrupt 98 */
  .long   IRQDefault            /* User-Defined Interrupt 99 */
  .long   IRQDefault            /* User-Defined Interrupt 100 */
  .long   IRQDefault            /* User-Defined Interrupt 101 */
  .long   IRQDefault            /* User-Defined Interrupt 102 */
  .long   IRQDefault            /* User-Defined Interrupt 103 */
  .long   IRQDefault            /* User-Defined Interrupt 104 */
  .long   IRQDefault            /* User-Defined Interrupt 105 */
  .long   IRQDefault            /* User-Defined Interrupt 106 */
  .long   IRQDefault            /* User-Defined Interrupt 107 */
  .long   IRQDefault            /* User-Defined Interrupt 108 */
  .long   IRQDefault            /* User-Defined Interrupt 109 */
  .long   IRQDefault            /* User-Defined Interrupt 110 */
  .long   IRQDefault            /* User-Defined Interrupt 111 */
  .long   IRQDefault            /* User-Defined Interrupt 112 */
  .long   IRQDefault            /* User-Defined Interrupt 113 */
  .long   IRQDefault            /* User-Defined Interrupt 114 */
  .long   IRQDefault            /* User-Defined Interrupt 115 */
  .long   IRQDefault            /* User-Defined Interrupt 116 */
  .long   IRQDefault            /* User-Defined Interrupt 117 */
  .long   IRQDefault            /* User-Defined Interrupt 118 */
  .long   IRQDefault            /* User-Defined Interrupt 119 */
  .long   IRQDefault            /* User-Defined Interrupt 120 */
  .long   IRQDefault            /* User-Defined Interrupt 121 */
  .long   IRQDefault            /* User-Defined Interrupt 122 */
  .long   IRQDefault            /* User-Defined Interrupt 123 */
  .long   IRQDefault            /* User-Defined Interrupt 124 */
  .long   IRQDefault            /* User-Defined Interrupt 125 */
  .long   IRQDefault            /* User-Defined Interrupt 126 */
  .long   IRQDefault            /* User-Defined Interrupt 127 */
  .long   IRQDefault            /* User-Defined Interrupt 128 */
  .long   IRQDefault            /* User-Defined Interrupt 129 */
  .long   IRQDefault            /* User-Defined Interrupt 130 */
  .long   IRQDefault            /* User-Defined Interrupt 131 */
  .long   IRQDefault            /* User-Defined Interrupt 132 */
  .long   IRQDefault            /* User-Defined Interrupt 133 */
  .long   IRQDefault            /* User-Defined Interrupt 134 */
  .long   IRQDefault            /* User-Defined Interrupt 135 */
  .long   IRQDefault            /* User-Defined Interrupt 136 */
  .long   IRQDefault            /* User-Defined Interrupt 137 */
  .long   IRQDefault            /* User-Defined Interrupt 138 */
  .long   IRQDefault            /* User-Defined Interrupt 139 */
  .long   IRQDefault            /* User-Defined Interrupt 140 */
  .long   IRQDefault            /* User-Defined Interrupt 141 */
  .long   IRQDefault            /* User-Defined Interrupt 142 */
  .long   IRQDefault            /* User-Defined Interrupt 143 */
  .long   IRQDefault            /* User-Defined Interrupt 144 */
  .long   IRQDefault            /* User-Defined Interrupt 145 */
  .long   IRQDefault            /* User-Defined Interrupt 146 */
  .long   IRQDefault            /* User-Defined Interrupt 147 */
  .long   IRQDefault            /* User-Defined Interrupt 148 */
  .long   IRQDefault            /* User-Defined Interrupt 149 */
  .long   IRQDefault            /* User-Defined Interrupt 150 */
  .long   IRQDefault            /* User-Defined Interrupt 151 */
  .long   IRQDefault            /* User-Defined Interrupt 152 */
  .long   IRQDefault            /* User-Defined Interrupt 153 */
  .long   IRQDefault            /* User-Defined Interrupt 154 */
  .long   IRQDefault            /* User-Defined Interrupt 155 */
  .long   IRQDefault            /* User-Defined Interrupt 156 */
  .long   IRQDefault            /* User-Defined Interrupt 157 */
  .long   IRQDefault            /* User-Defined Interrupt 158 */
  .long   IRQDefault            /* User-Defined Interrupt 159 */
  .long   IRQDefault            /* User-Defined Interrupt 160 */
  .long   IRQDefault            /* User-Defined Interrupt 161 */
  .long   IRQDefault            /* User-Defined Interrupt 162 */
  .long   IRQDefault            /* User-Defined Interrupt 163 */
  .long   IRQDefault            /* User-Defined Interrupt 164 */
  .long   IRQDefault            /* User-Defined Interrupt 165 */
  .long   IRQDefault            /* User-Defined Interrupt 166 */
  .long   IRQDefault            /* User-Defined Interrupt 167 */
  .long   IRQDefault            /* User-Defined Interrupt 168 */
  .long   IRQDefault            /* User-Defined Interrupt 169 */
  .long   IRQDefault            /* User-Defined Interrupt 170 */
  .long   IRQDefault            /* User-Defined Interrupt 171 */
  .long   IRQDefault            /* User-Defined Interrupt 172 */
  .long   IRQDefault            /* User-Defined Interrupt 173 */
  .long   IRQDefault            /* User-Defined Interrupt 174 */
  .long   IRQDefault            /* User-Defined Interrupt 175 */
  .long   IRQDefault            /* User-Defined Interrupt 176 */
  .long   IRQDefault            /* User-Defined Interrupt 177 */
  .long   IRQDefault            /* User-Defined Interrupt 178 */
  .long   IRQDefault            /* User-Defined Interrupt 179 */
  .long   IRQDefault            /* User-Defined Interrupt 180 */
  .long   IRQDefault            /* User-Defined Interrupt 181 */
  .long   IRQDefault            /* User-Defined Interrupt 182 */
  .long   IRQDefault            /* User-Defined Interrupt 183 */
  .long   IRQDefault            /* User-Defined Interrupt 184 */
  .long   IRQDefault            /* User-Defined Interrupt 185 */
  .long   IRQDefault            /* User-Defined Interrupt 186 */
  .long   IRQDefault            /* User-Defined Interrupt 187 */
  .long   IRQDefault            /* User-Defined Interrupt 188 */
  .long   IRQDefault            /* User-Defined Interrupt 189 */
  .long   IRQDefault            /* User-Defined Interrupt 190 */
  .long   IRQDefault            /* User-Defined Interrupt 191 */
  .org    0x00000400

  .section  .vector_ram
__RAMVEC:
  .space  0x400

  .section  .text
VecDefault:
  halt
  bra VecDefault

IRQDefault:
  halt
  bra IRQDefault

IRQSpurious:
  halt
  bra IRQSpurious

TrapDefault:
  halt
  bra TrapDefault
