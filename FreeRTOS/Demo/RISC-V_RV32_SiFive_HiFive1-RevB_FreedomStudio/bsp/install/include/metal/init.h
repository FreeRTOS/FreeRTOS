/* Copyright 2019 SiFive Inc. */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL_INIT
#define METAL_INIT

/*!
 * @file init.h
 * API for Metal constructors and destructors
 */

typedef void (*metal_constructor_t)(void);
typedef void (*metal_destructor_t)(void);

#define METAL_INIT_HIGHEST_PRIORITY 0
#define METAL_INIT_DEFAULT_PRIORITY 5000
#define METAL_INIT_LOWEST_PRIORITY 9999

/*! @def METAL_CONSTRUCTOR
 * @brief Define a Metal constructor
 *
 * Functions defined with METAL_CONSTRUCTOR will be added to the list of
 * Metal constructors. By default, these functions are called before main by
 * the metal_init() function.
 */
#define METAL_CONSTRUCTOR(function_name)                                       \
    METAL_CONSTRUCTOR_PRIO(function_name, METAL_INIT_DEFAULT_PRIORITY)

/*! @def METAL_CONSTRUCTOR_PRIO
 * @brief Define a Metal constructor with a given priority
 *
 * The priority argument should be an integer between 0 and 9999, where 0
 * is the highest priority (runs first) and 9999 is the lowest priority
 * (runs last).
 *
 * Functions defined with METAL_CONSTRUCTOR_PRIO will be added to the list of
 * Metal constructors. By default, these functions are called before main by
 * the metal_init() function.
 */
#define METAL_CONSTRUCTOR_PRIO(function_name, priority)                        \
    __METAL_CONSTRUCTOR_PRIO(function_name, priority)

/* We use this wrapper for METAL_CONSTRUCTOR_PRIORITY so that macros passed
 * as 'priority' are expanded before being stringified by the # operator.
 * If we don't do this, then
 * METAL_CONSTRUCTOR(my_fn_name, METAL_INIT_DEFAULT_PRIORITY)
 * results in .metal.init_array.METAL_INIT_DEFAULT_PRIORITY instead of
 * .metal.init_array.5000 */
#define __METAL_CONSTRUCTOR_PRIO(function_name, priority)                      \
    __attribute__((section(".metal.ctors"))) void function_name(void);         \
    __attribute__((section(".metal.init_array." #priority)))                   \
        metal_constructor_t _##function_name##_ptr = &function_name;           \
    void function_name(void)

/*! @def METAL_DESTRUCTOR
 * @brief Define a Metal destructor
 *
 * Functions defined with METAL_DESTRUCTOR will be added to the list of
 * Metal destructors. By default, these functions are called on exit by
 * the metal_fini() function.
 */
#define METAL_DESTRUCTOR(function_name)                                        \
    METAL_DESTRUCTOR_PRIO(function_name, METAL_INIT_DEFAULT_PRIORITY)

/*! @def METAL_DESTRUCTOR_PRIO
 * @brief Define a Metal destructor with a given priority
 *
 * The priority argument should be an integer between 0 and 9999, where 0
 * is the highest priority (runs first) and 9999 is the lowest priority
 * (runs last).
 *
 * Functions defined with METAL_DESTRUCTOR_PRIO will be added to the list of
 * Metal destructors. By default, these functions are called on exit by
 * the metal_fini() function.
 */
#define METAL_DESTRUCTOR_PRIO(function_name, priority)                         \
    __METAL_DESTRUCTOR_PRIO(function_name, priority)
#define __METAL_DESTRUCTOR_PRIO(function_name, priority)                       \
    __attribute__((section(".metal.dtors"))) void function_name(void);         \
    __attribute__((section(".metal.fini_array." #priority)))                   \
        metal_destructor_t _##function_name##_ptr = &function_name;            \
    void function_name(void)

/*!
 * @brief Call all Metal constructors
 *
 * Devices supported by Metal may define Metal constructors to perform
 * initialization before main. This function iterates over the constructors
 * and calls them in turn.
 *
 * You can add your own constructors to the functions called by metal_init()
 * by defining functions with the METAL_CONSTRUCTOR() macro.
 *
 * This function is called before main by default by metal_init_run().
 */
void metal_init(void);

/*!
 * @brief Call all Metal destructors
 *
 * Devices supported by Metal may define Metal destructors to perform
 * initialization on exit. This function iterates over the destructors
 * and calls them in turn.
 *
 * You can add your own destructors to the functions called by metal_fini()
 * by defining functions with the METAL_DESTRUCTOR() macro.
 *
 * This function is called on exit by default by metal_fini_run().
 */
void metal_fini(void);

/*!
 * @brief Weak function to call metal_init() before main
 *
 * This function calls metal_init() before main by default. If you wish to
 * replace or augment this call to the Metal constructors, you can redefine
 * metal_init_run()
 */
void metal_init_run(void);

/*!
 * @brief Weak function to call metal_fini() before main
 *
 * This function calls metal_fini() at exit by default. If you wish to
 * replace or augment this call to the Metal destructors, you can redefine
 * metal_fini_run()
 */
void metal_fini_run(void);

#endif /* METAL_INIT */
