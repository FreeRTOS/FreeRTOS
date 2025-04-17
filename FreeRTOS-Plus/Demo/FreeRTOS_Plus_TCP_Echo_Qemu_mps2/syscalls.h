#ifndef SYSCALLS_H
#define SYSCALLS_H

void uart_init( void );
int _fstat( int file );
int _read( int file,
           char * buf,
           int len );
int _write( int file,
            char * buf,
            int len );

void * _sbrk( int incr );

#endif /* SYSCALLS_H */
