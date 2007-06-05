//*****************************************************************************
//
// ustdlib.c - Simple standard library functions.
//
// Copyright (c) 2007 Luminary Micro, Inc.  All rights reserved.
//
// Software License Agreement
//
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
//
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  Any use in violation
// of the foregoing restrictions may subject the user to criminal sanctions
// under applicable laws, as well as to civil liability for the breach of the
// terms and conditions of this license.
//
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
//
//*****************************************************************************

#include <stdarg.h>
#include <string.h>
#include "debug.h"

//*****************************************************************************
//
//! \addtogroup utilities_api
//! @{
//
//*****************************************************************************

//*****************************************************************************
//
// A mapping from an integer between 0 and 15 to its ASCII character
// equivalent.
//
//*****************************************************************************
static const char * const g_pcHex = "0123456789abcdef";

//*****************************************************************************
//
//! A simple sprintf function supporting \%c, \%d, \%s, \%u, \%x, and \%X.
//!
//! \param pcBuf is the buffer where the converted string is stored.
//! \param pcString is the format string.
//! \param ... are the optional arguments, which depend on the contents of the
//! format string.
//!
//! This function is very similar to the C library <tt>sprintf()</tt> function.
//! Only the following formatting characters are supported:
//!
//! - \%c to print a character
//! - \%d to print a decimal value
//! - \%s to print a string
//! - \%u to print an unsigned decimal value
//! - \%x to print a hexadecimal value using lower case letters
//! - \%X to print a hexadecimal value using lower case letters (not upper case
//! letters as would typically be used)
//! - \%\% to print out a \% character
//!
//! For \%d, \%u, \%x, and \%X, an optional number may reside between the \%
//! and the format character, which specifies the minimum number of characters
//! to use for that value; if preceeded by a 0 then the extra characters will
//! be filled with zeros instead of spaces.  For example, ``\%8d'' will use
//! eight characters to print the decimal value with spaces added to reach
//! eight; ``\%08d'' will use eight characters as well but will add zeros
//! instead of spaces.
//!
//! The type of the arguments after \b pcString must match the requirements of
//! the format string.  For example, if an integer was passed where a string
//! was expected, an error of some kind will most likely occur.
//!
//! The caller must ensure that the buffer pcBuf is large enough to hold the
//! entire converted string, including the null termination character.
//!
//! \return None.
//
//*****************************************************************************
int
uvsnprintf(char *pcBuf, unsigned long ulSize, const char *pcString,
           va_list vaArgP)
{
    unsigned long ulIdx, ulValue, ulPos, ulCount, ulBase;
    char *pcStr, cFill, *pcOriginalBuf = pcBuf;

    //
    // Check the arguments.
    //
    ASSERT(pcString != 0);
    ASSERT(pcBuf != 0);
    ASSERT(ulSize != 0);

    //
    // Adjust buffer size limit to allow one space for null termination.
    //
    if(ulSize)
    {
        ulSize--;
    }

    //
    // Loop while there are more characters in the string, and
    // there is more room in the destination buffer.
    //
    while(*pcString && ulSize)
    {
        //
        // Find the first non-% character, or the end of the string.
        //
        for(ulIdx = 0; (pcString[ulIdx] != '%') && (pcString[ulIdx] != '\0');
            ulIdx++)
        {
        }

        //
        // Limit the number of characters that can be copied to the
        // space remaining in the buffer.
        //
        if(ulIdx > ulSize)
        {
            ulIdx = ulSize;
        }

        //
        // Write this portion of the string and update the buffer pointer.
        //
        strncpy(pcBuf, pcString, ulIdx);
        pcBuf += ulIdx;

        //
        // Update the size limit, and check to see if the buffer
        // limit is reached.
        //
        ulSize -= ulIdx;
        if(ulSize == 0)
        {
            break;
        }

        //
        // Skip the portion of the string that was written.
        //
        pcString += ulIdx;

        //
        // See if the next character is a %.
        //
        if(*pcString == '%')
        {
            //
            // Skip the %.
            //
            pcString++;

            //
            // Set the digit count to zero, and the fill character to space
            // (i.e. to the defaults).
            //
            ulCount = 0;
            cFill = ' ';

            //
            // It may be necessary to get back here to process more characters.
            // Goto's aren't pretty, but effective.  I feel extremely dirty for
            // using not one but two of the beasts.
            //
again:

            //
            // Determine how to handle the next character.
            //
            switch(*pcString++)
            {
                //
                // Handle the digit characters.
                //
                case '0':
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7':
                case '8':
                case '9':
                {
                    //
                    // If this is a zero, and it is the first digit, then the
                    // fill character is a zero instead of a space.
                    //
                    if((pcString[-1] == '0') && (ulCount == 0))
                    {
                        cFill = '0';
                    }

                    //
                    // Update the digit count.
                    //
                    ulCount *= 10;
                    ulCount += pcString[-1] - '0';

                    //
                    // Get the next character.
                    //
                    goto again;
                }

                //
                // Handle the %c command.
                //
                case 'c':
                {
                    //
                    // Get the value from the varargs.
                    //
                    ulValue = va_arg(vaArgP, unsigned long);

                    //
                    // Print out the character.
                    //
                    *pcBuf++ = (char)ulValue;

                    //
                    // Decrement the buffer limit.
                    //
                    ulSize--;

                    //
                    // This command has been handled.
                    //
                    break;
                }

                //
                // Handle the %d command.
                //
                case 'd':
                {
                    //
                    // Get the value from the varargs.
                    //
                    ulValue = va_arg(vaArgP, unsigned long);

                    //
                    // Reset the buffer position.
                    //
                    ulPos = 0;

                    //
                    // If the value is negative, make it positive and stick a
                    // minus sign in the beginning of the buffer.
                    //
                    if((long)ulValue < 0)
                    {
                        *pcBuf++ = '-';
                        ulPos++;
                        ulValue = -(long)ulValue;

                        //
                        // Decrement the buffer size limit and check
                        // if the limit is reached.
                        //
                        ulSize--;
                        if(ulSize == 0)
                        {
                            break;
                        }
                    }

                    //
                    // Set the base to 10.
                    //
                    ulBase = 10;

                    //
                    // Convert the value to ASCII.
                    //
                    goto convert;
                }

                //
                // Handle the %s command.
                //
                case 's':
                {
                    //
                    // Get the string pointer from the varargs.
                    //
                    pcStr = va_arg(vaArgP, char *);

                    //
                    // Determine the length of the string.
                    //
                    for(ulIdx = 0; pcStr[ulIdx] != '\0'; ulIdx++)
                    {
                    }

                    //
                    // Limit the number of characters that can be copied to the
                    // space remaining in the buffer.
                    //
                    if(ulIdx > ulSize)
                    {
                        ulIdx = ulSize;
                    }

                    //
                    // Write the string and update the buffer pointer.
                    //
                    strncpy(pcBuf, pcStr, ulIdx);
                    pcBuf += ulIdx;

                    //
                    // Decrement the buffer size limit.
                    //
                    ulSize -= ulIdx;

                    //
                    //
                    // This command has been handled.
                    //
                    break;
                }

                //
                // Handle the %u command.
                //
                case 'u':
                {
                    //
                    // Get the value from the varargs.
                    //
                    ulValue = va_arg(vaArgP, unsigned long);

                    //
                    // Reset the buffer position.
                    //
                    ulPos = 0;

                    //
                    // Set the base to 10.
                    //
                    ulBase = 10;

                    //
                    // Convert the value to ASCII.
                    //
                    goto convert;
                }

                //
                // Handle the %x and %X commands.  Note that they are treated
                // identically; i.e. %X will use lower case letters for a-f
                // instead of the upper case letters is should use.
                //
                case 'x':
                case 'X':
                {
                    //
                    // Get the value from the varargs.
                    //
                    ulValue = va_arg(vaArgP, unsigned long);

                    //
                    // Reset the buffer position.
                    //
                    ulPos = 0;

                    //
                    // Set the base to 16.
                    //
                    ulBase = 16;

                    //
                    // Determine the number of digits in the string version of
                    // the value.
                    //
convert:
                    for(ulIdx = 1;
                        (((ulIdx * ulBase) <= ulValue) &&
                         (((ulIdx * ulBase) / ulBase) == ulIdx));
                        ulIdx *= ulBase, ulCount--)
                    {
                    }

                    //
                    // Provide additional padding at the beginning of the
                    // string conversion if needed.
                    //
                    if((ulCount > 1) && (ulCount < 16))
                    {
                        for(ulCount--; ulCount; ulCount--)
                        {
                            *pcBuf++ = cFill;
                            ulPos++;

                            //
                            // Decrement buffer size and check to see if
                            // buffer limit is reached.
                            //
                            ulSize--;
                            if(ulSize == 0)
                            {
                                break;
                            }
                        }
                    }

                    //
                    // Convert the value into a string.
                    //
                    for(; ulIdx; ulIdx /= ulBase)
                    {
                        *pcBuf++ = g_pcHex[(ulValue / ulIdx) % ulBase];
                        ulPos++;

                        //
                        // Decrement buffer size and check to see if
                        // buffer limit is reached.
                        //
                        ulSize--;
                        if(ulSize == 0)
                        {
                            break;
                        }
                    }

                    //
                    // This command has been handled.
                    //
                    break;
                }

                //
                // Handle the %% command.
                //
                case '%':
                {
                    //
                    // Simply write a single %.
                    //
                    *pcBuf++ = pcString[-1];
                    ulSize--;

                    //
                    // This command has been handled.
                    //
                    break;
                }

                //
                // Handle all other commands.
                //
                default:
                {
                    //
                    // Indicate an error.
                    //
                    if(ulSize > 5)
                    {
                        strncpy(pcBuf, "ERROR", 5);
                        pcBuf += 5;
                        ulSize -= 5;
                    }

                    //
                    // This command has been handled.
                    //
                    break;
                }
            }
        }
    }

    //
    // Null terminate the string in the buffer.
    //
    *pcBuf = 0;
	return ( int ) pcBuf - ( int ) pcOriginalBuf;
}

//*****************************************************************************
//
//! A simple sprintf function supporting \%c, \%d, \%s, \%u, \%x, and \%X.
//!
//! \param pcBuf is the buffer where the converted string is stored.
//! \param pcString is the format string.
//! \param ... are the optional arguments, which depend on the contents of the
//! format string.
//!
//! This function is very similar to the C library <tt>sprintf()</tt> function.
//! Only the following formatting characters are supported:
//!
//! - \%c to print a character
//! - \%d to print a decimal value
//! - \%s to print a string
//! - \%u to print an unsigned decimal value
//! - \%x to print a hexadecimal value using lower case letters
//! - \%X to print a hexadecimal value using lower case letters (not upper case
//! letters as would typically be used)
//! - \%\% to print out a \% character
//!
//! For \%d, \%u, \%x, and \%X, an optional number may reside between the \%
//! and the format character, which specifies the minimum number of characters
//! to use for that value; if preceeded by a 0 then the extra characters will
//! be filled with zeros instead of spaces.  For example, ``\%8d'' will use
//! eight characters to print the decimal value with spaces added to reach
//! eight; ``\%08d'' will use eight characters as well but will add zeros
//! instead of spaces.
//!
//! The type of the arguments after \b pcString must match the requirements of
//! the format string.  For example, if an integer was passed where a string
//! was expected, an error of some kind will most likely occur.
//!
//! The caller must ensure that the buffer pcBuf is large enough to hold the
//! entire converted string, including the null termination character.
//!
//! \return None.
//
//*****************************************************************************
void
usprintf(char *pcBuf, const char *pcString, ...)
{
    va_list vaArgP;

    //
    // Start the varargs processing.
    //
    va_start(vaArgP, pcString);

    //
    // Call vsnprintf to perform the conversion.  Use a
    // large number for the buffer size.
    //
    uvsnprintf(pcBuf, 0xffff, pcString, vaArgP);

    //
    // End the varargs processing.
    //
    va_end(vaArgP);
}

//*****************************************************************************
//
//! A simple snprintf function supporting \%c, \%d, \%s, \%u, \%x, and \%X.
//!
//! \param pcBuf is the buffer where the converted string is stored.
//! \param ulSize is the size of the buffer.
//! \param pcString is the format string.
//! \param ... are the optional arguments, which depend on the contents of the
//! format string.
//!
//! This function is very similar to the C library <tt>sprintf()</tt> function.
//! Only the following formatting characters are supported:
//!
//! - \%c to print a character
//! - \%d to print a decimal value
//! - \%s to print a string
//! - \%u to print an unsigned decimal value
//! - \%x to print a hexadecimal value using lower case letters
//! - \%X to print a hexadecimal value using lower case letters (not upper case
//! letters as would typically be used)
//! - \%\% to print out a \% character
//!
//! For \%d, \%u, \%x, and \%X, an optional number may reside between the \%
//! and the format character, which specifies the minimum number of characters
//! to use for that value; if preceeded by a 0 then the extra characters will
//! be filled with zeros instead of spaces.  For example, ``\%8d'' will use
//! eight characters to print the decimal value with spaces added to reach
//! eight; ``\%08d'' will use eight characters as well but will add zeros
//! instead of spaces.
//!
//! The type of the arguments after \b pcString must match the requirements of
//! the format string.  For example, if an integer was passed where a string
//! was expected, an error of some kind will most likely occur.
//!
//! The function will copy at most \b ulSize - 1 characters into the
//! buffer \b pcBuf.  One space is reserved in the buffer for the null
//! termination character.
//!
//! \return None.
//
//*****************************************************************************
int
usnprintf(char *pcBuf, unsigned long ulSize, const char *pcString, ...)
{
int iReturn;

    va_list vaArgP;

    //
    // Start the varargs processing.
    //
    va_start(vaArgP, pcString);

    //
    // Call vsnprintf to perform the conversion.
    //
    iReturn = uvsnprintf(pcBuf, ulSize, pcString, vaArgP);

    //
    // End the varargs processing.
    //
    va_end(vaArgP);

	return iReturn;
}

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
