/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Example includes. */
#include "FreeRTOS_CLI.h"
#include "portmacro.h"
#include "serial.h"
#include "UARTCommandConsole.h"

/* Dimensions the buffer into which input characters are placed. */
#define cmdMAX_INPUT_SIZE               ( 128 )

/* The maximum time in ticks to wait for the UART access mutex. */
#define cmdMAX_MUTEX_WAIT               ( 200 / portTICK_PERIOD_MS )

/* Characters are only ever received slowly on the CLI so it is ok to pass
received characters from the UART interrupt to the task on a queue.  This sets
the length of the queue used for that purpose. */
#define cmdRXED_CHARS_QUEUE_LENGTH      ( 10 )

/* DEL acts as a backspace. */
#define cmdASCII_DEL                    ( 0x7F )

#define comNO_BLOCK                     ( ( TickType_t ) 0 )
#define com_WAIT                        ( ( TickType_t ) 1 )
/*-----------------------------------------------------------*/

/* The task that implements the command console processing. */
static void prvUARTCommandConsoleTask( void *pvParameters );

/* Register the 'standard' sample CLI commands with FreeRTOS+CLI. */
extern void vRegisterSampleCLICommands( void );

/* Baud rate used by the serial port tasks. */
#define mainCOM_TEST_BAUD_RATE      ( ( unsigned long ) 230400 )
/*-----------------------------------------------------------*/

/* Const messages output by the command console. */
const char * const pcWelcomeMessage = "\r\n\r\nFreeRTOS command server.\r\nType Help to view a list of registered commands.\r\n\r\n>";
const char * const pcEndOfOutputMessage = "\r\n[Press ENTER to execute the previous command again]\r\n>";
const char * const pcNewLine = "\r\n";

/*-----------------------------------------------------------*/

void vUARTCommandConsoleStart( uint16_t usStackSize, unsigned portBASE_TYPE uxPriority )
{
    vRegisterSampleCLICommands();

    /* Create that task that handles the console itself. */
    xTaskCreate(    prvUARTCommandConsoleTask,          /* The task that implements the command console. */
                    "CLI",                              /* Text name assigned to the task.  This is just to assist debugging.  The kernel does not use this name itself. */
                    usStackSize,                        /* The size of the stack allocated to the task. */
                    NULL,                               /* The parameter is not used, so NULL is passed. */
                    uxPriority,                         /* The priority allocated to the task. */
                    NULL );                             /* A handle is not required, so just pass NULL. */
}
/*-----------------------------------------------------------*/

static void prvUARTCommandConsoleTask( void *pvParameters )
{
char cRxedChar, *pcOutputString;
uint8_t ucInputIndex = 0;
static char cInputString[ cmdMAX_INPUT_SIZE ], cLastInputString[ cmdMAX_INPUT_SIZE ];
portBASE_TYPE xReturned;
xComPortHandle xCDCUsart = NULL; /* Static so it doesn't take up too much stack. */

    ( void ) pvParameters;

    xSerialPortInitMinimal( mainCOM_TEST_BAUD_RATE, cmdMAX_INPUT_SIZE);

    /* Obtain the address of the output buffer.  Note there is no mutual
    exclusion on this buffer as it is assumed only one command console
    interface will be used at any one time. */
    pcOutputString = FreeRTOS_CLIGetOutputBuffer();
     
    /* Send the welcome message. */
    vSerialPutString( xCDCUsart, pcWelcomeMessage, strlen( pcWelcomeMessage ) );
   
    for( ;; )
    {
        /* Wait for the next character to arrive. 
         * TODO: non-blocking   */
        if (xSerialGetChar( xCDCUsart , (signed char *) &cRxedChar , comNO_BLOCK ) == pdTRUE)
        {
              /* Echo the character back. */
            xSerialPutChar(xCDCUsart , cRxedChar , comNO_BLOCK );

            /* Was it the end of the line? */
            if( cRxedChar == '\n' || cRxedChar == '\r' )
            {
                /* Just to space the output from the input. */
                vSerialPutString( xCDCUsart, pcNewLine, strlen( pcNewLine ) );

                /* See if the command is empty, indicating that the last command is
                to be executed again. */
                if( ucInputIndex == 0 )
                {
                    /* Copy the last command back into the input string. */
                    strcpy( cInputString, cLastInputString );
                }

                /* Pass the received command to the command interpreter.  The
                command interpreter is called repeatedly until it returns pdFALSE
                (indicating there is no more output) as it might generate more than
                one string. */
                do
                {
                    /* Get the next output string from the command interpreter. */
                    xReturned = FreeRTOS_CLIProcessCommand( cInputString, pcOutputString, configCOMMAND_INT_MAX_OUTPUT_SIZE );

                    /* Write the generated string to the UART. */
                    vSerialPutString( xCDCUsart, pcOutputString, strlen( pcOutputString ) );

                } while( xReturned != pdFALSE );

                /* All the strings generated by the input command have been sent.
                Clear the input string ready to receive the next command.  Remember
                the command that was just processed first in case it is to be
                processed again. */
                strcpy( cLastInputString, cInputString );
                ucInputIndex = 0;
                memset( cInputString, 0x00, cmdMAX_INPUT_SIZE );

                vSerialPutString( xCDCUsart, pcEndOfOutputMessage, strlen( pcEndOfOutputMessage ) );
            }
            else
            {
                if( cRxedChar == '\r' )
                {
                    /* Ignore the character. */
                }
                else if( ( cRxedChar == '\b' ) || ( cRxedChar == cmdASCII_DEL ) )
                {
                    /* Backspace was pressed.  Erase the last character in the
                    string - if any. */
                    if( ucInputIndex > 0 )
                    {
                        ucInputIndex--;
                        cInputString[ ucInputIndex ] = '\0';
                    }
                }
                else
                {
                    /* A character was entered.  Add it to the string
                    entered so far.  When a \n is entered the complete
                    string will be passed to the command interpreter. */
                    if( ( cRxedChar >= ' ' ) && ( cRxedChar <= '~' ) )
                    {
                        if( ucInputIndex < cmdMAX_INPUT_SIZE )
                        {
                            cInputString[ ucInputIndex ] = cRxedChar;
                            ucInputIndex++;
                        }
                    }
                }
            }
        }
        else
        {
          vTaskDelay(1);
        }
    }
}
/*-----------------------------------------------------------*/
