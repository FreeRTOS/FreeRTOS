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
//! A simple vsnprintf function supporting \%c, \%d, \%s, \%u, \%x, and \%X.
//!
//! \param pcBuf points to the buffer where the converted string is stored.
//! \param ulSize is the size of the buffer.
//! \param pcString is the format string.
//! \param vaArgP is the list of optional arguments, which depend on the
//! contents of the format string.
//!
//! This function is very similar to the C library <tt>vsnprintf()</tt>
//! function. Only the following formatting characters are supported:
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
//! The \b ulSize parameter limits the number of characters that will be
//! stored in the buffer pointed to by \b pcBuf to prevent the possibility
//! of a buffer overflow.  The buffer size should be large enough to hold
//! the expected converted output string, including the null termination
//! character.
//!
//! The function will return the number of characters that would be
//! converted as if there were no limit on the buffer size.  Therefore
//! it is possible for the function to return a count that is greater than
//! the specified buffer size.  If this happens, it means that the output
//! was truncated.
//!
//! \return the number of characters that were to be stored, not including
//! the NULL termination character, regardless of space in the buffer.
//
//*****************************************************************************
int
uvsnprintf(char *pcBuf, unsigned long ulSize, const char *pcString,
           va_list vaArgP)
{
    unsigned long ulIdx, ulValue, ulCount, ulBase;
    char *pcStr, cFill;
    int iConvertCount = 0;

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
    // Initialize the count of characters converted.
    //
    iConvertCount = 0;

    //
    // Loop while there are more characters in the format string.
    //
    while(*pcString)
    {
        //
        // Find the first non-% character, or the end of the string.
        //
        for(ulIdx = 0; (pcString[ulIdx] != '%') && (pcString[ulIdx] != '\0');
            ulIdx++)
        {
        }

        //
        // Write this portion of the string to the output buffer.  If
        // there are more characters to write than there is space in the
        // buffer, then only write as much as will fit in the buffer.
        //
        if(ulIdx > ulSize)
        {
            strncpy(pcBuf, pcString, ulSize);
            pcBuf += ulSize;
            ulSize = 0;
        }
        else
        {
            strncpy(pcBuf, pcString, ulIdx);
            pcBuf += ulIdx;
            ulSize -= ulIdx;
        }

        //
        // Update the conversion count.  This will be the number of
        // characters that should have been written, even if there was
        // not room in the buffer.
        //
        iConvertCount += ulIdx;

        //
        // Skip the portion of the format string that was written.
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
                    // Copy the character to the output buffer, if
                    // there is room.  Update the buffer size remaining.
                    //
                    if(ulSize != 0)
                    {
                        *pcBuf++ = (char)ulValue;
                        ulSize--;
                    }

                    //
                    // Update the conversion count.
                    //
                    iConvertCount++;

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
                    // If the value is negative, make it positive and stick a
                    // minus sign in the beginning of the buffer.
                    //
                    if((long)ulValue < 0)
                    {
                        ulValue = -(long)ulValue;

                        if(ulSize != 0)
                        {
                            *pcBuf++ = '-';
                            ulSize--;
                        }

                        //
                        // Update the conversion count.
                        //
                        iConvertCount++;
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
                    // Copy the string to the output buffer.  Only copy
                    // as much as will fit in the buffer.  Update the
                    // output buffer pointer and the space remaining.
                    //
                    if(ulIdx > ulSize)
                    {
                        strncpy(pcBuf, pcStr, ulSize);
                        pcBuf += ulSize;
                        ulSize = 0;
                    }
                    else
                    {
                        strncpy(pcBuf, pcStr, ulIdx);
                        pcBuf += ulIdx;
                        ulSize -= ulIdx;
                    }

                    //
                    // Update the conversion count.  This will be the number of
                    // characters that should have been written, even if there
                    // was not room in the buffer.
                    //
                    iConvertCount += ulIdx;

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
                            //
                            // Copy the character to the output buffer if
                            // there is room.
                            //
                            if(ulSize != 0)
                            {
                                *pcBuf++ = cFill;
                                ulSize--;
                            }

                            //
                            // Update the conversion count.
                            //
                            iConvertCount++;
                        }
                    }

                    //
                    // Convert the value into a string.
                    //
                    for(; ulIdx; ulIdx /= ulBase)
                    {
                        //
                        // Copy the character to the output buffer if
                        // there is room.
                        //
                        if(ulSize != 0)
                        {
                            *pcBuf++ = g_pcHex[(ulValue / ulIdx) % ulBase];
                            ulSize--;
                        }

                        //
                        // Update the conversion count.
                        //
                        iConvertCount++;
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
                    if(ulSize != 0)
                    {
                        *pcBuf++ = pcString[-1];
                        ulSize--;
                    }

                    //
                    // Update the conversion count.
                    //
                    iConvertCount++;

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
                    if(ulSize >= 5)
                    {
                        strncpy(pcBuf, "ERROR", 5);
                        pcBuf += 5;
                        ulSize -= 5;
                    }
                    else
                    {
                        strncpy(pcBuf, "ERROR", ulSize);
                        pcBuf += ulSize;
                        ulSize = 0;
                    }

                    //
                    // Update the conversion count.
                    //
                    iConvertCount += 5;

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
    return(iConvertCount);
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
//! \return The count of characters that were written to the output buffer,
//! not including the NULL termination character.
//
//*****************************************************************************
int
usprintf(char *pcBuf, const char *pcString, ...)
{
    va_list vaArgP;
    int iRet;

    //
    // Start the varargs processing.
    //
    va_start(vaArgP, pcString);

    //
    // Call vsnprintf to perform the conversion.  Use a
    // large number for the buffer size.
    //
    iRet = uvsnprintf(pcBuf, 0xffff, pcString, vaArgP);

    //
    // End the varargs processing.
    //
    va_end(vaArgP);

    //
    // Return the conversion count.
    //
    return(iRet);
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
//! The function will return the number of characters that would be
//! converted as if there were no limit on the buffer size.  Therefore
//! it is possible for the function to return a count that is greater than
//! the specified buffer size.  If this happens, it means that the output
//! was truncated.
//!
//! \return the number of characters that were to be stored, not including
//! the NULL termination character, regardless of space in the buffer.
//
//*****************************************************************************
int
usnprintf(char *pcBuf, unsigned long ulSize, const char *pcString, ...)
{
int iRet;

    va_list vaArgP;

    //
    // Start the varargs processing.
    //
    va_start(vaArgP, pcString);

    //
    // Call vsnprintf to perform the conversion.
    //
    iRet = uvsnprintf(pcBuf, ulSize, pcString, vaArgP);

    //
    // End the varargs processing.
    //
    va_end(vaArgP);

    //
    // Return the conversion count.
    //
    return(iRet);
}

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
