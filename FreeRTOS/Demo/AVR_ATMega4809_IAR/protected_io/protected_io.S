/**
 * \file
 *
 * \brief Configuration Change Protection
 *
 (c) 2018 Microchip Technology Inc. and its subsidiaries.

    Subject to your compliance with these terms,you may use this software and 
    any derivatives exclusively with Microchip products.It is your responsibility
    to comply with third party license terms applicable to your use of third party 
    software (including open source software) that may accompany Microchip software.

    THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS". NO WARRANTIES, WHETHER
    EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE, INCLUDING ANY IMPLIED
    WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY, AND FITNESS FOR A
    PARTICULAR PURPOSE.

    IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
    INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
    WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
    BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE. TO THE
    FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL CLAIMS IN
    ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF FEES, IF ANY,
    THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
 *
 */

 
/**
 * \defgroup doc_driver_system_protected_io Protected IO
 * \ingroup doc_driver_system
 *
 * \section doc_driver_protected_io_rev Revision History
 * - v0.0.0.1 Initial Commit
 *
 *@{
 */

//

/*
     * GNU and IAR use different calling conventions. Since this is
     * a very small and simple function to begin with, it's easier
     * to implement it twice than to deal with the differences
     * within a single implementation.
     */


#if defined(__GNUC__)
#include <assembler.h>
        PUBLIC_FUNCTION(protected_write_io)
  
#ifdef RAMPZ
    out     _SFR_IO_ADDR(RAMPZ), r1         // Clear bits 23:16 of Z
#endif
    movw    r30, r24                // Load addr into Z
    out     CCP, r22                // Start CCP handshake
    st      Z, r20                  // Write value to I/O register
    ret                             // Return to caller
    END_FUNC(protected_write_io)
    END_FILE()


#elif defined(__IAR_SYSTEMS_ASM__)
#include <ioavr.h>
        PUBLIC protected_write_io
        RSEG CODE

protected_write_io:

# if !defined(CONFIG_MEMORY_MODEL_TINY) && !defined(CONFIG_MEMORY_MODEL_SMALL) \
                && !defined(CONFIG_MEMORY_MODEL_LARGE)
#  define CONFIG_MEMORY_MODEL_SMALL
# endif
# if defined(CONFIG_MEMORY_MODEL_LARGE)
    ldi     r20, 0
    out     RAMPZ, r20              // Reset bits 23:16 of Z
    movw    r30, r16                // Load addr into Z
# elif defined(CONFIG_MEMORY_MODEL_TINY)
    ldi     r31, 0                  // Reset bits 8:15 of Z
    mov     r30, r16                // Load addr into Z
# else
    movw    r30, r16                // Load addr into Z
# endif
# if defined(CONFIG_MEMORY_MODEL_TINY)
    out     CCP, r17                // Start CCP handshake
    st      Z, r18                  // Write value to I/O register
# elif defined(CONFIG_MEMORY_MODEL_SMALL)
    out     CCP, r18                // Start CCP handshake
    st      Z, r19                  // Write value to I/O register
# elif defined(CONFIG_MEMORY_MODEL_LARGE)
    out     CCP, r19                // Start CCP handshake
    st      Z, r20                  // Write value to I/O register
# else
#  error Unknown memory model in use, no idea how registers should be accessed
# endif
        ret
        END
#else
# error Unknown assembler
#endif

