#ifndef _BOARD_SUPPORT_LIBRARY_H
#define _BOARD_SUPPORT_LIBRARY_H

#include <stddef.h>

extern void BSL_Init(void);
extern int BSL_ToggleLED(void);
extern int BSL_Write(char *buffer, size_t len);

#endif