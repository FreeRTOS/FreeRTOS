/* io 
 * 
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *
 */


#include <stdint.h>
#include <FreeRTOS.h>
#if defined(__x86_64__)
void outb(uint16_t port, uint8_t val)
{                    
    asm volatile("outb %b0, %w1" : : "a"(val), "Nd"(port));
}                        
void outw(uint16_t port, uint16_t val)
{                    
    asm volatile ( "outw %w0, %w1" : : "a"(val), "Nd"(port) );
}                        
void outl(uint16_t port, uint32_t val)
{
    asm volatile ( "out %0, %1" : : "a"(val), "Nd"(port) );
}
uint8_t inb(uint16_t port)        
{                            
    uint8_t value;                
    asm volatile("inb %w1, %b0" : "=a"(value): "Nd"(port));
    return (uint8_t)value;                
}
uint16_t inw(uint16_t port)        
{                            
    uint16_t value;                
    asm volatile("inw %w1, %w0" : "=a"(value): "Nd"(port));
    return (uint16_t)value;                
}
uint32_t inl(uint16_t port)        
{                            
    uint32_t value;                
    asm volatile("in %w1, %0" : "=a"(value): "Nd"(port));
    return (uint32_t)value;                
}
#endif
