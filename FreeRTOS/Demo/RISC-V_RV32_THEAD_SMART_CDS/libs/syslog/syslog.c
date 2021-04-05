/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */
/******************************************************************************
 * @file     syslog.c
 * @brief    Syslog const strings and APIs
 * @version  V1.0
 * @date     29. January 2019
 ******************************************************************************/
#include <csi_config.h>

#define LOG_COLOR_RED_YELLO_BACK "\033[1;31;43m"
#define LOG_COLOR_RED            "\033[2;31;49m"
#define LOG_COLOR_YELLOW         "\033[2;33;49m"
#define LOG_COLOR_GREEN          "\033[2;32;49m"
#define LOG_COLOR_BLUE           "\033[2;34;49m"
#define LOG_COLOR_GRAY           "\033[1;30m"
#define LOG_COLOR_WHITE          "\033[2;47;49m"
#define LOG_COLOR_RESET          "\033[0m"

#ifdef CONFIG_SYSLOG_COLORFUL
const char *PFORMAT_D    = LOG_COLOR_GRAY   "[D][%s():%d] " LOG_COLOR_RESET;
const char *PFORMAT_I    = LOG_COLOR_WHITE  "[I][%s():%d] " LOG_COLOR_RESET;
const char *PFORMAT_W    = LOG_COLOR_YELLOW "[W][%s():%d] " LOG_COLOR_RESET;
const char *PFORMAT_E    = LOG_COLOR_RED    "[E][%s():%d] " LOG_COLOR_RESET;
#else
const char *PFORMAT_D    = "[D][%s():%d] ";
const char *PFORMAT_I    = "[I][%s():%d] ";
const char *PFORMAT_W    = "[W][%s():%d] ";
const char *PFORMAT_E    = "[E][%s():%d] ";
#endif
