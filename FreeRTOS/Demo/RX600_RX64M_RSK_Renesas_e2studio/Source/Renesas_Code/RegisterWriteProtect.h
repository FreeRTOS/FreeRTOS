/*
 * RegisterWriteProtect.h
 *
 *  Created on: 4 Mar 2014
 *      Author: WarnerR
 */

#ifndef REGISTERWRITEPROTECT_H_
#define REGISTERWRITEPROTECT_H_

#include "stdint.h"

#define	PRC0_BIT	0x0001
#define	PRC1_BIT	0x0002
#define	PRC3_BIT	0x0008


extern void EnablePRCR( uint16_t protect );
extern void DisablePRCR( uint16_t protect );


#endif /* REGISTERWRITEPROTECT_H_ */
