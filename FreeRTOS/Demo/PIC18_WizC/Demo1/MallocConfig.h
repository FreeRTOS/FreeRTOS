#ifndef _MALLOC_SETTINGS_H
#define _MALLOC_SETTINGS_H
/*********************************************************************
** Title:		Dynamic memory (de-)allocation library for wizC.
**
** Author:		Marcel van Lieshout
**
** Copyright:	(c) 2005, HMCS, Marcel van Lieshout
**
** License:		This software is released to the public domain and comes
**				without	warranty and/or guarantees of any kind. You have
**				the right to use, copy, modify and/or (re-)distribute the
**				software as long as the reference to the author is
**				maintained in the software and a reference to the author
**				is included in any documentation of each product in which
**				this library (in it's original or in a modified form)
**				is used.
*********************************************************************/

/*********************************************************************
** The model to use
*********************************************************************/
//#define MALLOC_SMALL
#define MALLOC_LARGE

/*********************************************************************
** The size of the heap
*********************************************************************/
#define MALLOC_HEAP_SIZE	(3200)

/*********************************************************************
** Should released memory be scribbled with 0x55 before releasing it?
*********************************************************************/
//#define MALLOC_SCRIBBLE

/********************************************************************
** Enable Debug-mode?
*********************************************************************/
//#define MALLOC_DEBUG

#endif	/* _MALLOC_SETTINGS_H */
