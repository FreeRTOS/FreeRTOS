#ifndef UTILS_IO_HEADER
#define UTILS_IO_HEADER

#include <stdint.h>

struct _buffer
{
	uint8_t* data;
	uint32_t size;
};

static inline void writeb(volatile void* reg, uint8_t value)
{
	*(volatile uint8_t*)reg = value;
}

static inline void writehw(volatile void* reg, uint16_t value)
{
	*(volatile uint16_t*)reg = value;
}

static inline void readb(volatile const void* reg, uint8_t* value)
{
	*value = *(volatile const uint8_t*)reg;
}

static inline void readhw(volatile const void* reg, uint16_t* value)
{
	*value = *(volatile const uint16_t*)reg;
}

#endif
