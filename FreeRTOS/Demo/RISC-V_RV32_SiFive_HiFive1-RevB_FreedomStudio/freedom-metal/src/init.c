/* Copyright 2019 SiFive Inc. */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/init.h>

/*
 * These function pointers are created by the linker script
 * in the .init_array section. The arrays defined by these
 * and end points are the set of functions defined by instances
 * of METAL_CONSTRUCTOR() and METAL_DESTRUCTOR().
 */
extern metal_constructor_t metal_constructors_start;
extern metal_constructor_t metal_constructors_end;
extern metal_destructor_t metal_destructors_start;
extern metal_destructor_t metal_destructors_end;

void metal_init(void) {
    /* Make sure the constructors only run once */
    static int init_done = 0;
    if (init_done) {
        return;
    }
    init_done = 1;

    if (&metal_constructors_end <= &metal_constructors_start) {
        return;
    }

    metal_constructor_t *funcptr = &metal_constructors_start;
    while (funcptr != &metal_constructors_end) {
        metal_constructor_t func = *funcptr;

        func();

        funcptr += 1;
    }
}

void metal_fini(void) {
    /* Make sure the destructors only run once */
    static int fini_done = 0;
    if (fini_done) {
        return;
    }
    fini_done = 1;

    if (&metal_destructors_end <= &metal_destructors_start) {
        return;
    }

    metal_destructor_t *funcptr = &metal_destructors_start;
    while (funcptr != &metal_destructors_end) {
        metal_destructor_t func = *funcptr;

        func();

        funcptr += 1;
    }
}

/*
 * metal_init_run() and metal_fini_run() are marked weak so that users
 * can redefine them for their own purposes, including to no-ops
 * in the case that users don't want the metal constructors or
 * destructors to run.
 */

void metal_init_run(void) __attribute__((weak));
void metal_init_run(void) { metal_init(); }

void metal_fini_run(void) __attribute__((weak));
void metal_fini_run(void) { metal_fini(); }
