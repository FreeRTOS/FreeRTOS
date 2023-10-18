/*
 * Copyright (c) 2002 Todd C. Miller <Todd.Miller@courtesan.com>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 * Sponsored in part by the Defense Advanced Research Projects
 * Agency (DARPA) and Air Force Research Laboratory, Air Force
 * Materiel Command, USAF, under agreement number F39502-99-1-0512.
 */

/*-
 * Copyright (c) 2000 The NetBSD Foundation, Inc.
 * All rights reserved.
 *
 * This code is derived from software contributed to The NetBSD Foundation
 * by Dieter Baron and Thomas Klausner.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE NETBSD FOUNDATION, INC. AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE FOUNDATION OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

/** @file
 *  @brief Implementations of getopt() and getopt_long() work-alike functions.
 *
 *  This code was taken from FreeBSD and slightly modified, mostly to rename
 *  symbols with external linkage to avoid naming conflicts in systems where
 *  there are real getopt()/getopt_long() implementations, and for portability.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <redfs.h>
#include <redgetopt.h>
#include <redtestutils.h>
#include <rederrno.h>


int32_t red_opterr = 1;   /* if error message should be printed */
int32_t red_optind = 1;   /* index into parent argv vector */
int32_t red_optopt = '?'; /* character checked for validity */
int32_t red_optreset;     /* reset RedGetopt */
const char * red_optarg;  /* argument associated with option */

#define PRINT_ERROR      ( ( red_opterr ) && ( *options != ':' ) )

#define FLAG_PERMUTE     0x01   /* permute non-options to the end of argv */
#define FLAG_ALLARGS     0x02   /* treat non-options as args to option "-1" */
#define FLAG_LONGONLY    0x04   /* operate as RedGetoptLongOnly */

/* return values */
#define BADCH            ( int ) '?'
#define BADARG           ( ( *options == ':' ) ? ( int ) ':' : ( int ) '?' )
#define INORDER          ( int ) 1

#define EMSG             ""

#define NO_PREFIX        ( -1 )
#define D_PREFIX         0
#define DD_PREFIX        1
#define W_PREFIX         2

static int gcd( int a,
                int b );
static void permute_args( int panonopt_start,
                          int panonopt_end,
                          int opt_end,
                          char * const * nargv );
static int parse_long_options( char * const * nargv,
                               const char * options,
                               const REDOPTION * long_options,
                               int32_t * idx,
                               int short_too,
                               int flags );
static int getopt_internal( int nargc,
                            char * const * nargv,
                            const char * options,
                            const REDOPTION * long_options,
                            int32_t * idx,
                            int flags );

static const char * place = EMSG; /* option letter processing */

/* XXX: set red_optreset to 1 rather than these two */
static int nonopt_start = -1; /* first non option argument (for permute) */
static int nonopt_end = -1;   /* first option after non options (for permute) */

/* Error messages */
static const char recargchar[] = "option requires an argument -- %c\n";
static const char illoptchar[] = "illegal option -- %c\n"; /* From P1003.2 */
static int dash_prefix = NO_PREFIX;
static const char gnuoptchar[] = "invalid option -- %c\n";

static const char recargstring[] = "option `%s%s' requires an argument\n";
static const char ambig[] = "option `%s%s' is ambiguous\n";
static const char noarg[] = "option `%s%s' doesn't allow an argument\n";
static const char illoptstring[] = "unrecognized option `%s%s'\n";

/*
 * Compute the greatest common divisor of a and b.
 */
static int gcd( int a,
                int b )
{
    int c;

    c = a % b;

    while( c != 0 )
    {
        a = b;
        b = c;
        c = a % b;
    }

    return( b );
}

/*
 * Exchange the block from nonopt_start to nonopt_end with the block
 * from nonopt_end to opt_end (keeping the same order of arguments
 * in each block).
 */
static void permute_args( int panonopt_start,
                          int panonopt_end,
                          int opt_end,
                          char * const * nargv )
{
    int cstart, cyclelen, i, j, ncycle, nnonopts, nopts, pos;
    char * swap;

    /*
     * compute lengths of blocks and number and size of cycles
     */
    nnonopts = panonopt_end - panonopt_start;
    nopts = opt_end - panonopt_end;
    ncycle = gcd( nnonopts, nopts );
    cyclelen = ( opt_end - panonopt_start ) / ncycle;

    for( i = 0; i < ncycle; i++ )
    {
        cstart = panonopt_end + i;
        pos = cstart;

        for( j = 0; j < cyclelen; j++ )
        {
            if( pos >= panonopt_end )
            {
                pos -= nnonopts;
            }
            else
            {
                pos += nopts;
            }

            swap = nargv[ pos ];
            ( ( char ** ) nargv )[ pos ] = nargv[ cstart ];
            ( ( char ** ) nargv )[ cstart ] = swap;
        }
    }
}

/*
 * parse_long_options --
 *  Parse long options in argc/argv argument vector.
 * Returns -1 if short_too is set and the option does not match long_options.
 */
static int parse_long_options( char * const * nargv,
                               const char * options,
                               const REDOPTION * long_options,
                               int32_t * idx,
                               int short_too,
                               int flags )
{
    const char * current_argv, * has_equal, * current_dash;
    size_t current_argv_len;
    int i, match, exact_match, second_partial_match;

    current_argv = place;

    switch( dash_prefix )
    {
        case D_PREFIX:
            current_dash = "-";
            break;

        case DD_PREFIX:
            current_dash = "--";
            break;

        case W_PREFIX:
            current_dash = "-W ";
            break;

        default:
            current_dash = "";
            break;
    }

    match = -1;
    exact_match = 0;
    second_partial_match = 0;

    red_optind++;

    if( ( has_equal = strchr( current_argv, '=' ) ) != NULL )
    {
        /* argument found (--option=arg) */
        current_argv_len = has_equal - current_argv;
        has_equal++;
    }
    else
    {
        current_argv_len = strlen( current_argv );
    }

    for( i = 0; long_options[ i ].name; i++ )
    {
        /* find matching long option */
        if( strncmp( current_argv, long_options[ i ].name,
                     current_argv_len ) )
        {
            continue;
        }

        if( strlen( long_options[ i ].name ) == current_argv_len )
        {
            /* exact match */
            match = i;
            exact_match = 1;
            break;
        }

        /*
         * If this is a known short option, don't allow
         * a partial match of a single character.
         */
        if( short_too && ( current_argv_len == 1 ) )
        {
            continue;
        }

        if( match == -1 ) /* first partial match */
        {
            match = i;
        }
        else if( ( flags & FLAG_LONGONLY ) ||
                 ( long_options[ i ].has_arg !=
                   long_options[ match ].has_arg ) ||
                 ( long_options[ i ].flag != long_options[ match ].flag ) ||
                 ( long_options[ i ].val != long_options[ match ].val ) )
        {
            second_partial_match = 1;
        }
    }

    if( !exact_match && second_partial_match )
    {
        /* ambiguous abbreviation */
        if( PRINT_ERROR )
        {
            fprintf( stderr,
                     ambig,
                     current_dash,
                     current_argv );
        }

        red_optopt = 0;
        return( BADCH );
    }

    if( match != -1 ) /* option found */
    {
        if( ( long_options[ match ].has_arg == red_no_argument ) &&
            has_equal )
        {
            if( PRINT_ERROR )
            {
                fprintf( stderr,
                         noarg,
                         current_dash,
                         current_argv );
            }

            /*
             * XXX: GNU sets red_optopt to val regardless of flag
             */
            if( long_options[ match ].flag == NULL )
            {
                red_optopt = long_options[ match ].val;
            }
            else
            {
                red_optopt = 0;
            }

            return( BADCH );
        }

        if( ( long_options[ match ].has_arg == red_required_argument ) ||
            ( long_options[ match ].has_arg == red_optional_argument ) )
        {
            if( has_equal )
            {
                red_optarg = has_equal;
            }
            else if( long_options[ match ].has_arg ==
                     red_required_argument )
            {
                /*
                 * optional argument doesn't use next nargv
                 */
                red_optarg = nargv[ red_optind++ ];
            }
        }

        if( ( long_options[ match ].has_arg == red_required_argument ) &&
            ( red_optarg == NULL ) )
        {
            /*
             * Missing argument; leading ':' indicates no error
             * should be generated.
             */
            if( PRINT_ERROR )
            {
                fprintf( stderr,
                         recargstring,
                         current_dash,
                         current_argv );
            }

            /*
             * XXX: GNU sets red_optopt to val regardless of flag
             */
            if( long_options[ match ].flag == NULL )
            {
                red_optopt = long_options[ match ].val;
            }
            else
            {
                red_optopt = 0;
            }

            --red_optind;
            return( BADARG );
        }
    }
    else /* unknown option */
    {
        if( short_too )
        {
            --red_optind;
            return( -1 );
        }

        if( PRINT_ERROR )
        {
            fprintf( stderr,
                     illoptstring,
                     current_dash,
                     current_argv );
        }

        red_optopt = 0;
        return( BADCH );
    }

    if( idx )
    {
        *idx = match;
    }

    if( long_options[ match ].flag )
    {
        *long_options[ match ].flag = long_options[ match ].val;
        return( 0 );
    }
    else
    {
        return( long_options[ match ].val );
    }
}

/*
 * getopt_internal --
 *  Parse argc/argv argument vector.  Called by user level routines.
 */
static int getopt_internal( int nargc,
                            char * const * nargv,
                            const char * options,
                            const REDOPTION * long_options,
                            int32_t * idx,
                            int flags )
{
    char * oli; /* option letter list index */
    int optchar, short_too;

    if( options == NULL )
    {
        return( -1 );
    }

    /*
     * XXX Some GNU programs (like cvs) set red_optind to 0 instead of
     * XXX using red_optreset.  Work around this braindamage.
     */
    if( red_optind == 0 )
    {
        red_optind = red_optreset = 1;
    }

    /*
     * Disable GNU extensions if options string begins with a '+'.
     */
    if( *options == '-' )
    {
        flags |= FLAG_ALLARGS;
    }
    else if( *options == '+' )
    {
        flags &= ~FLAG_PERMUTE;
    }

    if( ( *options == '+' ) || ( *options == '-' ) )
    {
        options++;
    }

    red_optarg = NULL;

    if( red_optreset )
    {
        nonopt_start = nonopt_end = -1;
    }

start:

    if( red_optreset || !*place ) /* update scanning pointer */
    {
        red_optreset = 0;

        if( red_optind >= nargc ) /* end of argument vector */
        {
            place = EMSG;

            if( nonopt_end != -1 )
            {
                /* do permutation, if we have to */
                permute_args( nonopt_start, nonopt_end,
                              red_optind, nargv );
                red_optind -= nonopt_end - nonopt_start;
            }
            else if( nonopt_start != -1 )
            {
                /*
                 * If we skipped non-options, set red_optind
                 * to the first of them.
                 */
                red_optind = nonopt_start;
            }

            nonopt_start = nonopt_end = -1;
            return( -1 );
        }

        if( ( *( place = nargv[ red_optind ] ) != '-' ) || ( place[ 1 ] == '\0' ) )
        {
            place = EMSG; /* found non-option */

            if( flags & FLAG_ALLARGS )
            {
                /*
                 * GNU extension:
                 * return non-option as argument to option 1
                 */
                red_optarg = nargv[ red_optind++ ];
                return( INORDER );
            }

            if( !( flags & FLAG_PERMUTE ) )
            {
                /*
                 * If no permutation wanted, stop parsing
                 * at first non-option.
                 */
                return( -1 );
            }

            /* do permutation */
            if( nonopt_start == -1 )
            {
                nonopt_start = red_optind;
            }
            else if( nonopt_end != -1 )
            {
                permute_args( nonopt_start, nonopt_end,
                              red_optind, nargv );
                nonopt_start = red_optind -
                               ( nonopt_end - nonopt_start );
                nonopt_end = -1;
            }

            red_optind++;
            /* process next argument */
            goto start;
        }

        if( ( nonopt_start != -1 ) && ( nonopt_end == -1 ) )
        {
            nonopt_end = red_optind;
        }

        /*
         * If we have "-" do nothing, if "--" we are done.
         */
        if( ( place[ 1 ] != '\0' ) && ( *++place == '-' ) && ( place[ 1 ] == '\0' ) )
        {
            red_optind++;
            place = EMSG;

            /*
             * We found an option (--), so if we skipped
             * non-options, we have to permute.
             */
            if( nonopt_end != -1 )
            {
                permute_args( nonopt_start, nonopt_end,
                              red_optind, nargv );
                red_optind -= nonopt_end - nonopt_start;
            }

            nonopt_start = nonopt_end = -1;
            return( -1 );
        }
    }

    /*
     * Check long options if:
     *  1) we were passed some
     *  2) the arg is not just "-"
     *  3) either the arg starts with -- we are RedGetoptLongOnly()
     */
    if( ( long_options != NULL ) && ( place != nargv[ red_optind ] ) &&
        ( ( *place == '-' ) || ( flags & FLAG_LONGONLY ) ) )
    {
        short_too = 0;
        dash_prefix = D_PREFIX;

        if( *place == '-' )
        {
            place++; /* --foo long option */
            dash_prefix = DD_PREFIX;
        }
        else if( ( *place != ':' ) && ( strchr( options, *place ) != NULL ) )
        {
            short_too = 1; /* could be short option too */
        }

        optchar = parse_long_options( nargv, options, long_options,
                                      idx, short_too, flags );

        if( optchar != -1 )
        {
            place = EMSG;
            return( optchar );
        }
    }

    if( ( ( optchar = ( int ) *place++ ) == ( int ) ':' ) ||
        ( ( optchar == ( int ) '-' ) && ( *place != '\0' ) ) ||
        ( ( oli = strchr( options, optchar ) ) == NULL ) )
    {
        /*
         * If the user specified "-" and  '-' isn't listed in
         * options, return -1 (non-option) as per POSIX.
         * Otherwise, it is an unknown option character (or ':').
         */
        if( ( optchar == ( int ) '-' ) && ( *place == '\0' ) )
        {
            return( -1 );
        }

        if( !*place )
        {
            ++red_optind;
        }

        if( PRINT_ERROR )
        {
            fprintf( stderr, gnuoptchar, optchar );
        }

        red_optopt = optchar;
        return( BADCH );
    }

    if( ( long_options != NULL ) && ( optchar == 'W' ) && ( oli[ 1 ] == ';' ) )
    {
        /* -W long-option */
        if( *place )                     /* no space */
        {                                /* NOTHING */
        }
        else if( ++red_optind >= nargc ) /* no arg */
        {
            place = EMSG;

            if( PRINT_ERROR )
            {
                fprintf( stderr, recargchar, optchar );
            }

            red_optopt = optchar;
            return( BADARG );
        }
        else /* white space */
        {
            place = nargv[ red_optind ];
        }

        dash_prefix = W_PREFIX;
        optchar = parse_long_options( nargv, options, long_options,
                                      idx, 0, flags );
        place = EMSG;
        return( optchar );
    }

    if( *++oli != ':' ) /* doesn't take argument */
    {
        if( !*place )
        {
            ++red_optind;
        }
    }
    else /* takes (optional) argument */
    {
        red_optarg = NULL;

        if( *place ) /* no white space */
        {
            red_optarg = place;
        }
        else if( oli[ 1 ] != ':' )      /* arg not optional */
        {
            if( ++red_optind >= nargc ) /* no arg */
            {
                place = EMSG;

                if( PRINT_ERROR )
                {
                    fprintf( stderr, recargchar, optchar );
                }

                red_optopt = optchar;
                return( BADARG );
            }
            else
            {
                red_optarg = nargv[ red_optind ];
            }
        }

        place = EMSG;
        ++red_optind;
    }

    /* dump back option letter */
    return( optchar );
}


/** @brief Get option character from command line argument list.
 *
 *  For more details, consult the getopt() man pages, since this function is
 *  generally similar.
 *
 *  @param nargc    Number of arguments (argc passed into main()).
 *  @param nargv    Argument vector (argv passed into main()).
 *  @param options  String of option characters.
 *
 *  @return The next known option character in @p options.  If a character not
 *          found in @p options is found or if an option is missing an argument,
 *          it returns '?'.  Returns -1 when the argument list is exhausted.
 */
int32_t RedGetopt( int32_t nargc,
                   char * const * nargv,
                   const char * options )
{
    return getopt_internal( nargc, nargv, options, NULL, NULL, FLAG_PERMUTE );
}


/** @brief Get long options from command line argument list.
 *
 *  For more details, consult the getopt_long() man pages, since this function
 *  is generally similar.
 *
 *  @param nargc        Number of arguments (argc passed into main()).
 *  @param nargv        Argument vector (argv passed into main()).
 *  @param options      String of option characters.
 *  @param long_options The long options; the last element of this array must be
 *                      filled with zeroes.
 *  @param idx          If non-NULL, then populated with the index of the long
 *                      option relative to @p long_options.
 *
 *  @return If the flag field in REDOPTION is NULL, returns the value specified
 *          in the val field, which is usually just the corresponding short
 *          option.  If flag is non-NULL, returns zero and stores val in the
 *          location pointed to by flag.  Returns ':' if an option was missing
 *          its argument, '?' for an unknown option, and -1 when the argument
 *          list is exhausted.
 */
int32_t RedGetoptLong( int32_t nargc,
                       char * const * nargv,
                       const char * options,
                       const REDOPTION * long_options,
                       int32_t * idx )
{
    return getopt_internal( nargc, nargv, options, long_options, idx, FLAG_PERMUTE );
}
