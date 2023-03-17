#ifndef LOCAL_PORTABLE_H
#define LOCAL_PORTABLE_H

StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters );

BaseType_t xPortStartScheduler( void );

void vPortEndScheduler( void );
#endif /* LOCAL_PORTABLE_H */
