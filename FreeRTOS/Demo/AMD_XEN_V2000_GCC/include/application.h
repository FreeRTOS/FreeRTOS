#ifndef _APPLICATION_H_
#define _APPLICATION_H_
#include "FreeRTOS.h"

/* Application main function. This is called by main before starting scheduler */
void app_main(void);

/* Function that application needs to implement to add application specific cli command */
void register_application_cli_commands(void);
#endif
