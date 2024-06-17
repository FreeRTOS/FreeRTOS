#include <stdio.h>
#include <stdlib.h>

int main( int argc, char * argv[] )
{
    setvbuf( stdout, NULL, _IONBF, 0 );
    FILE * fp;
    char path[ 256 ];
    char cmd[ 256 ];

    /* Open the command for reading. */
    fp = popen("find . -name RTOSDemo.out", "r");
        /* Read the output a line at a time - output it. */
    while( fgets( path, sizeof( path ), fp ) != NULL )
    {
        printf( "Path: %s\n", path );
    }

    sprintf(cmd, "qemu-system-arm -machine mps2-an385 -monitor null -semihosting --semihosting-config enable=on,target=native -serial stdio -nographic -kernel %s", path);
    printf("cmd= %s\n", cmd);
    fp = popen( cmd, "r" );
    if( fp == NULL )
    {
        printf( "Failed to run command\n" );
        exit( 1 );
    }

    /* Read the output a line at a time - output it. */
    while( fgets( path, sizeof( path ), fp ) != NULL )
    {
        printf( "%s", path );
    }

    /* close */
    pclose( fp );

    return 0;
}
