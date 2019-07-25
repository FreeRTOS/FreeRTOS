
/*
 * Temporary file for use only during development when there are no library or
 * header files.
 */

#ifndef STRING_H
#define STRING_H

//typedef unsigned long size_t;

/*
 *  Extremely crude standard library implementations in lieu of having a C
 *  library.
 */
unsigned long strlen( const char* pcString );
int strcmp( const char *pcString1, const char *pcString2 );
void *memset( void *pvDest, int iValue, unsigned long ulBytes );
void *memcpy( void *pvDest, const void *pvSource, unsigned long ulBytes );
int memcmp( const void *pvMem1, const void *pvMem2, unsigned long ulBytes );
#endif /* string_h */
