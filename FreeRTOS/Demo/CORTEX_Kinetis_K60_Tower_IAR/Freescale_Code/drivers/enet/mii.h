/*!
 * \file    mii.h
 * \brief   Media Independent Interface (MII) driver
 * \version $Revision: 1.2 $
 * \author  Michael Norman
 * 
 * \warning 
 *
 */

#ifndef _MII_H_
#define _MII_H_

/*******************************************************************/

#define MII_TIMEOUT		0x1FFFF
#define MII_LINK_TIMEOUT	0x1FFFF

void
mii_init(int, int);

int
mii_write(int, int, int, int);

int
mii_read(int, int, int, int*);

/*******************************************************************/

#endif /* _MII_H_ */
