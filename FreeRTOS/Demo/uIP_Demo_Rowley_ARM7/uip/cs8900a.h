#ifndef __CS8900A_H__
#define __CS8900A_H__

#include "uip_arch.h"

void cs8900a_init(void);
void cs8900a_send(void);
u8_t cs8900a_poll(void);

#endif /* __CS8900A_H__ */
