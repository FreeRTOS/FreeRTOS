/*
 * Temporary file for use only during development when there are no library or
 * header files.
 */


#ifndef STDLIB_H
#define STDLIB_H


/*
 *  Extremely crude standard library implementations in lieu of having a C
 *  library.
 */
void *memset( void *pvDest, int iValue, unsigned long ulBytes );
void *memcpy( void *pvDest, const void *pvSource, unsigned long ulBytes );
int memcmp( const void *pvMem1, const void *pvMem2, unsigned long ulBytes );

#endif /* STDLIB_H */

