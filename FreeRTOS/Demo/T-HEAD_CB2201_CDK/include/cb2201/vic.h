/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#define VECTOR_RESET            0
#define VECTOR_MISALIGN         1
#define VECTOR_ACCESS           2
#define VECTOR_DIV_BY_ZERO      3
#define VECTOR_ILLEGAL          4
#define VECTOR_PRIVILEGE        5
#define VECTOR_TRACE            6
#define VECTOR_BREAK            7
#define VECTOR_UNRECOV          8
#define VECTOR_SOFT             9
#define VECTOR_INT              10               /* Used by PIT timer only for OS tick */
#define VECTOR_FINT             11               /* All other controller-based interrupts
                                                    use fast interrupt (FINT) and alternate regs */
#define VECTOR_HW_ACCEL         12

#define VECTOR_TRAP0            16
#define VECTOR_TRAP1            17
#define VECTOR_TRAP2            18
#define VECTOR_TRAP3            19


#define VECTOR_UART0            32
#define VECTOR_TIMER            33

/* INT_CONTROLLER memory locations */

#define VIC_BASE                (0xE000E000)
#define VIC_ICR                 ((volatile uint32_t *) (VIC_BASE + 0x4))
#define VIC_ISER                ((volatile uint32_t *) (VIC_BASE + 0x100))
#define VIC_IWER                ((volatile uint32_t *) (VIC_BASE + 0x140))
#define VIC_ICER                ((volatile uint32_t *) (VIC_BASE + 0x180))
#define VIC_IWDR                ((volatile uint32_t *) (VIC_BASE + 0x1C0))
#define VIC_ISPR                ((volatile uint32_t *) (VIC_BASE + 0x200))
#define VIC_ICPR                ((volatile uint32_t *) (VIC_BASE + 0x280))
#define VIC_ISFR                ((volatile uint32_t *) (VIC_BASE + 0x300))
#define VIC_ISNR                ((volatile uint32_t *) (VIC_BASE + 0x380))

#define VIC_PR                  ((volatile uint32_t *) (VIC_BASE + 0x400))

/*****************************************************************************/

#endif /* __VIC_H_ */
