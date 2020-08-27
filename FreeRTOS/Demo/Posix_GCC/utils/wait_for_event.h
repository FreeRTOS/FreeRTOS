#ifndef _WAIT_FOR_EVENT_H_
#define _WAIT_FOR_EVENT_H_

#include <stdbool.h>
#include <time.h>

struct event;

struct event * event_create();
void event_delete( struct event * );
bool event_wait( struct event * ev );
bool event_wait_timed( struct event * ev,
                       time_t ms );
void event_signal( struct event * ev );



#endif /* ifndef _WAIT_FOR_EVENT_H_ */
