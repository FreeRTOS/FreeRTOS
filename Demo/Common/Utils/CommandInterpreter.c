/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/* Standard includes. */
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Utils includes. */
#include "CommandInterpreter.h"

typedef struct xCOMMAND_INPUT_LIST
{
	const xCommandLineInput *pxCommandLineDefinition;
	struct xCOMMAND_INPUT_LIST *pxNext;
} xCommandLineInputListItem;

/*
 * The callback function that is executed when "help" is entered.  This is the
 * only default command that is always present.
 */
static portBASE_TYPE prvHelpCommand( signed char *pcWriteBuffer, size_t xWriteBufferLen, const signed char *pcCommandString );

/*
 * Return the number of parameters that follow the command name.
 */
static signed char prvGetNumberOfParameters( const signed char * pcCommandString );

/* The definition of the "help" command.  This command is always at the front
of the list of registered commands. */
static const xCommandLineInput xHelpCommand = 
{
	( const signed char * const ) "help",
	( const signed char * const ) "help: Lists all the registered commands\r\n",
	prvHelpCommand,
	0
};

/* The definition of the list of commands.  Commands that are registered are
added to this list. */
static xCommandLineInputListItem xRegisteredCommands =
{	
	&xHelpCommand,	/* The first command in the list is always the help command, defined in this file. */
	NULL			/* The next pointer is initialised to NULL, as there are no other registered commands yet. */
};

/* A buffer into which command outputs can be written is declared here, rather
than in the command console implementation, to allow multiple command consoles
to share the same buffer.  For example, an application may allow access to the
command interpreter by UART and by Ethernet.  Sharing a buffer is done purely
to save RAM.  Note, however, that the command console itself is not re-entrant,
so only one command interpreter interface can be used at any one time.  For that
reason, no attempt at providing mutual exclusion to the cOutputBuffer array is
attempted. */
static signed char cOutputBuffer[ configCOMMAND_INT_MAX_OUTPUT_SIZE ];

/*-----------------------------------------------------------*/

portBASE_TYPE xCmdIntRegisterCommand( const xCommandLineInput * const pxCommandToRegister )
{
static xCommandLineInputListItem *pxLastCommandInList = &xRegisteredCommands;
xCommandLineInputListItem *pxNewListItem;
portBASE_TYPE xReturn = pdFAIL;

	/* Check the parameter is not NULL. */
	configASSERT( pxCommandToRegister );

	/* Create a new list item that will reference the command being registered. */
	pxNewListItem = ( xCommandLineInputListItem * ) pvPortMalloc( sizeof( xCommandLineInputListItem ) );
	configASSERT( pxNewListItem );

	if( pxNewListItem != NULL )
	{
		taskENTER_CRITICAL();
		{
			/* Reference the command being registered from the newly created 
			list item. */
			pxNewListItem->pxCommandLineDefinition = pxCommandToRegister;

			/* The new list item will get added to the end of the list, so 
			pxNext has nowhere to point. */
			pxNewListItem->pxNext = NULL;

			/* Add the newly created list item to the end of the already existing
			list. */
			pxLastCommandInList->pxNext = pxNewListItem;

			/* Set the end of list marker to the new list item. */
			pxLastCommandInList = pxNewListItem;
		}
		taskEXIT_CRITICAL();
		
		xReturn = pdPASS;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xCmdIntProcessCommand( const signed char * const pcCommandInput, signed char * pcWriteBuffer, size_t xWriteBufferLen  )
{
static const xCommandLineInputListItem *pxCommand = NULL;
portBASE_TYPE xReturn = pdTRUE;
const signed char *pcRegisteredCommandString;

	/* Note:  This function is not re-entrant.  It must not be called from more
	thank one task. */

	if( pxCommand == NULL )
	{
		/* Search for the command string in the list of registered commands. */
		for( pxCommand = &xRegisteredCommands; pxCommand != NULL; pxCommand = pxCommand->pxNext )
		{
			pcRegisteredCommandString = pxCommand->pxCommandLineDefinition->pcCommand;
			if( strncmp( ( const char * ) pcCommandInput, ( const char * ) pcRegisteredCommandString, strlen( ( const char * ) pcRegisteredCommandString ) ) == 0 )
			{
				/* The command has been found.  Check it has the expected
				number of parameters.  If cExpectedNumberOfParameters is -1,
				then there could be a variable number of parameters and no
				check is made. */
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

	if( ( pxCommand != NULL ) && ( xReturn == pdFALSE ) )
	{
		/* The command was found, but the number of parameters with the command
		was incorrect. */
		strncpy( ( char * ) pcWriteBuffer, "Incorrect command parameter(s).  Enter \"help\" to view a list of available commands.\r\n\r\n", xWriteBufferLen );
		pxCommand = NULL;
	}
	else if( pxCommand != NULL )
	{
		/* Call the callback function that is registered to this command. */
		xReturn = pxCommand->pxCommandLineDefinition->pxCommandInterpreter( pcWriteBuffer, xWriteBufferLen, pcCommandInput );

		/* If xReturn is pdFALSE, then no further strings will be returned
		after this one, and	pxCommand can be reset to NULL ready to search 
		for the next entered command. */
		if( xReturn == pdFALSE )
		{
			pxCommand = NULL;
		}
	}
	else
	{
		/* pxCommand was NULL, the command was not found. */
		strncpy( ( char * ) pcWriteBuffer, ( const char * const ) "Command not recognised.  Enter \"help\" to view a list of available commands.\r\n\r\n", xWriteBufferLen );
		xReturn = pdFALSE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

signed char *pcCmdIntGetOutputBuffer( void )
{
	return cOutputBuffer;
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxCmdIntGetOutputBufferSizeBytes( void )
{
	return configCOMMAND_INT_MAX_OUTPUT_SIZE;
}
/*-----------------------------------------------------------*/

const signed char *pcCmdIntGetParameter( const signed char *pcCommandString, unsigned portBASE_TYPE uxWantedParameter, portBASE_TYPE *pxParameterStringLength )
{
unsigned portBASE_TYPE uxParametersFound = 0;
const signed char *pcReturn = NULL;

	*pxParameterStringLength = 0;

	while( uxParametersFound < uxWantedParameter )
	{
		/* Index the character pointer past the current word.  If this is the start
		of the command string then the first word is the command itself. */
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

static portBASE_TYPE prvHelpCommand( signed char *pcWriteBuffer, size_t xWriteBufferLen, const signed char *pcCommandString )
{
static const xCommandLineInputListItem * pxCommand = NULL;
signed portBASE_TYPE xReturn;

	( void ) pcCommandString;

	if( pxCommand == NULL )
	{
		/* Reset the pxCommand pointer back to the start of the list. */
		pxCommand = &xRegisteredCommands;
	}

	/* Return the next command help string, before moving the pointer on to
	the next command in the list. */
	strncpy( ( char * ) pcWriteBuffer, ( const char * ) pxCommand->pxCommandLineDefinition->pcHelpString, xWriteBufferLen );
	pxCommand = pxCommand->pxNext;

	if( pxCommand == NULL )
	{
		/* There are no more commands in the list, so there will be no more
		strings to return after this one and pdFALSE should be returned. */
		xReturn = pdFALSE;
	}
	else
	{
		xReturn = pdTRUE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static signed char prvGetNumberOfParameters( const signed char * pcCommandString )
{
signed char cParameters = 0;
portBASE_TYPE xLastCharacterWasSpace = pdFALSE;

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

	/* The value returned is one less than the number of space delimited words,
	as the first word should be the command itself. */
	return cParameters;
}

