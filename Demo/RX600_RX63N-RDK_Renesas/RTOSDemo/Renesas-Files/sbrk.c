#include <stddef.h>
#include <stdio.h>
#define HEAPSIZE	0x400
signed char *sbrk( size_t size );
union HEAP_TYPE
{
	signed long dummy;
	signed char heap[HEAPSIZE];
};
static union HEAP_TYPE	heap_area;

/* End address allocated by sbrk */
static signed char		*brk = ( signed char * ) &heap_area;
signed char *sbrk( size_t size )
{
	signed char *p;
	if( brk + size > heap_area.heap + HEAPSIZE )
	{
		p = ( signed char * ) - 1;
	}
	else
	{
		p = brk;
		brk += size;
	}

	return p;
}
