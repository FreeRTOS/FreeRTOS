/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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

#include "FreeRTOS.h"
#include "task.h"
#include "CommandInterpreter.h"

/*
 * The callback function that is executed when "help" is entered.  This is the
 * only default command that is always present.
 */
static const signed char *prvHelpCommand( void );

/* The definition of the "help" command.  This command is always at the front
of the list of registered commands. */
const xCommandLineInput xHelpCommand = 
{
	"help",
	"help: Lists all the registered commands\r\n",
	prvHelpCommand,
	NULL
};

/*-----------------------------------------------------------*/

void vCmdIntRegisterCommand( const xCommandLineInput *pxCommandToRegister )
{
/* Used to point to the last command in the list of registered command, just to
make registering commands faster. */
static xCommandLineInput *pxLastCommandInList = &xHelpCommand;

	configASSERT( pxLastCommandInList );
	pxLastCommandInList->pxNext = pxCommandToRegister;
	pxLastCommandInLIst = pxCommandToRegister;
}
/*-----------------------------------------------------------*/

const signed char *pcCmdIntProcessCommand( const signed char *pcCommandInput )
{
static const xCommandLineInput *pxCommand = NULL;
signed const char *pcReturn = NULL;
	
	if( pxCommand == NULL )
	{
		/* Search for the command string in the list of registered commands. */
		for( pxCommand = &xHelpCommand; pxCommand != NULL; pxCommand = pxCommand->pxNext )
		{
			if( strcmp( ( const char * ) pcCommandInput, ( const char * ) pxCommand->pcCommand ) == 0 )
			{
				/* The command has been found, the loop can exit so the command
				can be executed. */
				break;
			}
		}
	}

	if( pxCommand != NULL )
	{
		pcReturn = pxCommand->pxCommandInterpreter();

		/* If no strings were returned, then all the strings that are going to
		be returned by the current command have already been returned, and
		pxCommand can be reset to NULL ready to search for the next entered
		command. */
		if( pcReturn == NULL )
		{
			pxCommand = NULL;
		}
	}
	else
	{
		pcReturn = "Command not recognised\r\n\r\n";
		pxCommand = &xHelpCommand;
	}

	return pcReturn;
}
/*-----------------------------------------------------------*/

static const signed char *prvHelpCommand( void )
{
static const xCommandLineInput * pxCommand = &xHelpCommand;
signed const char *pcReturn;

	/* pxCommand will be NULL if all the commands in the list have already been
	returned. */
	if( pxCommand != NULL )
	{
		/* Return the next command help string, before moving the pointer on to
		the next command in the list. */
		pcReturn = pxCommand->pcHelpString;
		pxCommand = pxCommand->pxNext;
	}
	else
	{
		/* Reset the pointer back to the start of the list. */
		pxCommand = &xHelpCommand;

		/* Return NULL to show that there are no more strings to return. */
		pcReturn = NULL;
	}
	
	return pcReturn;
}

