/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */
/******************************************************************************
 * @file     _init.c
 * @brief    source file for c++ init & uninit
 * @version  V1.0
 * @date     24. April 2019
 ******************************************************************************/

#include <csi_config.h>
#include <string.h>

#ifndef CPP_WEAK
#define CPP_WEAK    __attribute__((weak))
#endif

extern int __dtor_end__;
extern int __ctor_end__;
extern int __ctor_start__;

typedef void (*func_ptr) (void);

CPP_WEAK void _init(void)
{
    func_ptr *p;
    for (p = (func_ptr *)&__ctor_end__ - 1; p >= (func_ptr *)&__ctor_start__; p--) {
        (*p) ();
    }
}

CPP_WEAK void _fini(void)
{
    func_ptr *p;
    for (p = (func_ptr *)&__ctor_end__; p <= (func_ptr *)&__dtor_end__ - 1; p++) {
        (*p) ();
    }
}
