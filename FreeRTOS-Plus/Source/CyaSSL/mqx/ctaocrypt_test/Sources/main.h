/* main.h */

#ifndef __main_h_
#define __main_h_

#include <mqx.h>
#include <bsp.h>

#include <mfs.h>
#include <fio.h>
#include <sdcard.h>
#include <sdcard_spi.h>
#include <spi.h>
#include <part_mgr.h>

#define MAIN_TASK 1

extern void Main_task(uint_32);

#endif /* __main_h_ */

