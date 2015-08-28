/* main.c
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/settings.h>

#if defined(CYASSL_MICROCHIP_PIC32MZ)
    #define MICROCHIP_PIC32
    #include <xc.h>
    #pragma config ICESEL = ICS_PGx2        
            /* ICE/ICD Comm Channel Select (Communicate on PGEC2/PGED2) */
    #include <stdio.h>
    #include <stdlib.h>
    #include "PIC32MZ-serial.h"
    #define  SYSTEMConfigPerformance /* void out SYSTEMConfigPerformance(); */
#else
    #define PIC32_STARTER_KIT
    #include <stdio.h>
    #include <stdlib.h>
    #include <p32xxxx.h>
    #include <plib.h>
    #include <sys/appio.h>
    #define init_serial()  /* void out init_serial() */
#endif

/* func_args from test.h, so don't have to pull in other junk */
typedef struct func_args {
    int    argc;
    char** argv;
    int    return_code;
} func_args;

/*
 * Main driver for CTaoCrypt tests.
 */
int main(int argc, char** argv) {
    int i ;

    init_serial() ;  /* initialize PIC32MZ serial I/O */
    SYSTEMConfigPerformance(80000000);
    DBINIT();
    printf("CTaoCrypt Test:\n");
    func_args args;

    args.argc = argc;
    args.argv = argv;

    ctaocrypt_test(&args);

    if (args.return_code == 0) {
        printf("All tests passed!\n");
    }
    
    return 0;
}

