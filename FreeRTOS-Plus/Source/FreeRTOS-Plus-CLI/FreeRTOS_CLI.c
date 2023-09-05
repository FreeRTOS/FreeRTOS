/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* Standard includes. */
#include <string.h>
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Utils includes. */
#include "FreeRTOS_CLI.h"

/* If the application writer needs to place the buffer used by the CLI at a
 * fixed address then set configAPPLICATION_PROVIDES_cOutputBuffer to 1 in
 * FreeRTOSConfig.h, then declare an array with the following name and size in
 * one of the application files:
 *  char cOutputBuffer[ configCOMMAND_INT_MAX_OUTPUT_SIZE ];
 */
#ifndef configAPPLICATION_PROVIDES_cOutputBuffer
    #define configAPPLICATION_PROVIDES_cOutputBuffer    0
#endif

/*
 * Register the command passed in using the pxCommandToRegister parameter
 * and using pxCliDefinitionListItemBuffer as the memory for command line
 * list items. Registering a command adds the command to the list of
 * commands that are handled by the command interpreter.  Once a command
 * has been registered it can be executed from the command line.
 */
static void prvRegisterCommand( const CLI_Command_Definition_t * const pxCommandToRegister,
                                CLI_Definition_List_Item_t * pxCliDefinitionListItemBuffer );

/*
 * The callback function that is executed when "help" is entered.  This is the
 * only default command that is always present.
 */
static BaseType_t prvHelpCommand( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString );

/*
 * Return the number of parameters that follow the command name.
 */
static int8_t prvGetNumberOfParameters( const char * pcCommandString );

/* The definition of the "help" command.  This command is always at the front
 * of the list of registered commands. */
static const CLI_Command_Definition_t xHelpCommand =
{
    "help",
    "\r\nhelp:\r\n Lists all the registered commands\r\n\r\n",
    prvHelpCommand,
    0
};

/* The definition of the list of commands.  Commands that are registered are
 * added to this list. */
static CLI_Definition_List_Item_t xRegisteredCommands =
{
    &xHelpCommand, /* The first command in the list is always the help command, defined in this file. */
    NULL           /* The next pointer is initialised to NULL, as there are no other registered commands yet. */
};

/* A buffer into which command outputs can be written is declared here, rather
* than in the command console implementation, to allow multiple command consoles
* to share the same buffer.  For example, an application may allow access to the
* command interpreter by UART and by Ethernet.  Sharing a buffer is done purely
* to save RAM.  Note, however, that the command console itself is not re-entrant,
* so only one command interpreter interface can be used at any one time.  For that
* reason, no attempt at providing mutual exclusion to the cOutputBuffer array is
* attempted.
*
* configAPPLICATION_PROVIDES_cOutputBuffer is provided to allow the application
* writer to provide their own cOutputBuffer declaration in cases where the
* buffer needs to be placed at a fixed address (rather than by the linker). */
#if ( configAPPLICATION_PROVIDES_cOutputBuffer == 0 )
    static char cOutputBuffer[ configCOMMAND_INT_MAX_OUTPUT_SIZE ];
#else
    extern char cOutputBuffer[ configCOMMAND_INT_MAX_OUTPUT_SIZE ];
#endif


/*-----------------------------------------------------------*/

#if ( configSUPPORT_DYNAMIC_ALLOCATION == 1 )

    BaseType_t FreeRTOS_CLIRegisterCommand( const CLI_Command_Definition_t * const pxCommandToRegister )
    {
        BaseType_t xReturn = pdFAIL;
        CLI_Definition_List_Item_t * pxNewListItem;

        /* Check the parameter is not NULL. */
        configASSERT( pxCommandToRegister != NULL );

        /* Create a new list item that will reference the command being registered. */
        pxNewListItem = ( CLI_Definition_List_Item_t * ) pvPortMalloc( sizeof( CLI_Definition_List_Item_t ) );
        configASSERT( pxNewListItem != NULL );

        if( pxNewListItem != NULL )
        {
            prvRegisterCommand( pxCommandToRegister, pxNewListItem );
            xReturn = pdPASS;
        }

        return xReturn;
    }

#endif /* #if ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) */
/*-----------------------------------------------------------*/

#if ( configSUPPORT_STATIC_ALLOCATION == 1 )

    BaseType_t FreeRTOS_CLIRegisterCommandStatic( const CLI_Command_Definition_t * const pxCommandToRegister,
                                                  CLI_Definition_List_Item_t * pxCliDefinitionListItemBuffer )
    {
        /* Check the parameters are not NULL. */
        configASSERT( pxCommandToRegister != NULL );
        configASSERT( pxCliDefinitionListItemBuffer != NULL );

        prvRegisterCommand( pxCommandToRegister, pxCliDefinitionListItemBuffer );

        return pdPASS;
    }

#endif /* #if ( configSUPPORT_STATIC_ALLOCATION == 1 ) */
/*-----------------------------------------------------------*/

BaseType_t FreeRTOS_CLIProcessCommand( const char * const pcCommandInput,
                                       char * pcWriteBuffer,
                                       size_t xWriteBufferLen )
{
    static const CLI_Definition_List_Item_t * pxCommand = NULL;
    BaseType_t xReturn = pdTRUE;
    const char * pcRegisteredCommandString;
    size_t xCommandStringLength;

    /* Note:  This function is not re-entrant.  It must not be called from more
     * thank one task. */

    if( pxCommand == NULL )
    {
        /* Search for the command string in the list of registered commands. */
        for( pxCommand = &xRegisteredCommands; pxCommand != NULL; pxCommand = pxCommand->pxNext )
        {
            pcRegisteredCommandString = pxCommand->pxCommandLineDefinition->pcCommand;
            xCommandStringLength = strlen( pcRegisteredCommandString );

            /* To ensure the string lengths match exactly, so as not to pick up
             * a sub-string of a longer command, check the byte after the expected
             * end of the string is either the end of the string or a space before
             * a parameter. */
            if( strncmp( pcCommandInput, pcRegisteredCommandString, xCommandStringLength ) == 0 )
            {
                if( ( pcCommandInput[ xCommandStringLength ] == ' ' ) || ( pcCommandInput[ xCommandStringLength ] == 0x00 ) )
                {
                    /* The command has been found.  Check it has the expected
                     * number of parameters.  If cExpectedNumberOfParameters is -1,
                     * then there could be a variable number of parameters and no
                     * check is made. */
                    if( pxCommand->pxCommandLineDefinition->cExpectedNumberOfParameters >= 0 )
                    {
                        if( prvGetNumberOfParameters( pcCommandInput ) != pxCommand->pxCommandLineDefinition->cExpectedNumberOfParameters )
                        {
                            xReturn = pdFALSE;
                        }
                    }

                    break;
                }
            }
        }
    }

    if( ( pxCommand != NULL ) && ( xReturn == pdFALSE ) )
    {
        /* The command was found, but the number of parameters with the command
         * was incorrect. */
        strncpy( pcWriteBuffer, "Incorrect command parameter(s).  Enter \"help\" to view a list of available commands.\r\n\r\n", xWriteBufferLen );
        pxCommand = NULL;
    }
    else if( pxCommand != NULL )
    {
        /* Call the callback function that is registered to this command. */
        xReturn = pxCommand->pxCommandLineDefinition->pxCommandInterpreter( pcWriteBuffer, xWriteBufferLen, pcCommandInput );

        /* If xReturn is pdFALSE, then no further strings will be returned
         * after this one, and	pxCommand can be reset to NULL ready to search
         * for the next entered command. */
        if( xReturn == pdFALSE )
        {
            pxCommand = NULL;
        }
    }
    else
    {
        /* pxCommand was NULL, the command was not found. */
        strncpy( pcWriteBuffer, "Command not recognised.  Enter 'help' to view a list of available commands.\r\n\r\n", xWriteBufferLen );
        xReturn = pdFALSE;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

char * FreeRTOS_CLIGetOutputBuffer( void )
{
    return cOutputBuffer;
}
/*-----------------------------------------------------------*/

const char * FreeRTOS_CLIGetParameter( const char * pcCommandString,
                                       UBaseType_t uxWantedParameter,
                                       BaseType_t * pxParameterStringLength )
{
    UBaseType_t uxParametersFound = 0;
    const char * pcReturn = NULL;

    *pxParameterStringLength = 0;

    while( uxParametersFound < uxWantedParameter )
    {
        /* Index the character pointer past the current word.  If this is the start
         * of the command string then the first word is the command itself. */
        while( ( ( *pcCommandString ) != 0x00 ) && ( ( *pcCommandString ) != ' ' ) )
        {
            pcCommandString++;
        }

        /* Find the start of the next string. */
        while( ( ( *pcCommandString ) != 0x00 ) && ( ( *pcCommandString ) == ' ' ) )
        {
            pcCommandString++;
        }

        /* Was a string found? */
        if( *pcCommandString != 0x00 )
        {
            /* Is this the start of the required parameter? */
            uxParametersFound++;

            if( uxParametersFound == uxWantedParameter )
            {
                /* How long is the parameter? */
                pcReturn = pcCommandString;

                while( ( ( *pcCommandString ) != 0x00 ) && ( ( *pcCommandString ) != ' ' ) )
                {
                    ( *pxParameterStringLength )++;
                    pcCommandString++;
                }

                if( *pxParameterStringLength == 0 )
                {
                    pcReturn = NULL;
                }

                break;
            }
        }
        else
        {
            break;
        }
    }

    return pcReturn;
}
/*-----------------------------------------------------------*/

static void prvRegisterCommand( const CLI_Command_Definition_t * const pxCommandToRegister,
                                CLI_Definition_List_Item_t * pxCliDefinitionListItemBuffer )
{
    static CLI_Definition_List_Item_t * pxLastCommandInList = &xRegisteredCommands;

    /* Check the parameters are not NULL. */
    configASSERT( pxCommandToRegister != NULL );
    configASSERT( pxCliDefinitionListItemBuffer != NULL );

    taskENTER_CRITICAL();
    {
        /* Reference the command being registered from the newly created
         * list item. */
        pxCliDefinitionListItemBuffer->pxCommandLineDefinition = pxCommandToRegister;

        /* The new list item will get added to the end of the list, so
         * pxNext has nowhere to point. */
        pxCliDefinitionListItemBuffer->pxNext = NULL;

        /* Add the newly created list item to the end of the already existing
         * list. */
        pxLastCommandInList->pxNext = pxCliDefinitionListItemBuffer;

        /* Set the end of list marker to the new list item. */
        pxLastCommandInList = pxCliDefinitionListItemBuffer;
    }
    taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

static BaseType_t prvHelpCommand( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{
    static const CLI_Definition_List_Item_t * pxCommand = NULL;
    BaseType_t xReturn;

    ( void ) pcCommandString;

    if( pxCommand == NULL )
    {
        /* Reset the pxCommand pointer back to the start of the list. */
        pxCommand = &xRegisteredCommands;
    }

    /* Return the next command help string, before moving the pointer on to
     * the next command in the list. */
    strncpy( pcWriteBuffer, pxCommand->pxCommandLineDefinition->pcHelpString, xWriteBufferLen );
    pxCommand = pxCommand->pxNext;

    if( pxCommand == NULL )
    {
        /* There are no more commands in the list, so there will be no more
         *  strings to return after this one and pdFALSE should be returned. */
        xReturn = pdFALSE;
    }
    else
    {
        xReturn = pdTRUE;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static int8_t prvGetNumberOfParameters( const char * pcCommandString )
{
    int8_t cParameters = 0;
    BaseType_t xLastCharacterWasSpace = pdFALSE;

    /* Count the number of space delimited words in pcCommandString. */
    while( *pcCommandString != 0x00 )
    {
        if( ( *pcCommandString ) == ' ' )
        {
            if( xLastCharacterWasSpace != pdTRUE )
            {
                cParameters++;
                xLastCharacterWasSpace = pdTRUE;
            }
        }
        else
        {
            xLastCharacterWasSpace = pdFALSE;
        }

        pcCommandString++;
    }

    /* If the command string ended with spaces, then there will have been too
     * many parameters counted. */
    if( xLastCharacterWasSpace == pdTRUE )
    {
        cParameters--;
    }

    /* The value returned is one less than the number of space delimited words,
     * as the first word should be the command itself. */
    return cParameters;
}
/*-----------------------------------------------------------*/
