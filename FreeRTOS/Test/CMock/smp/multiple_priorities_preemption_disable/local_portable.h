#ifndef LOCAL_PORTABLE_H
#define LOCAL_PORTABLE_H

BaseType_t xPortStartScheduler( void );

void vPortEndScheduler( void );

StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters );

StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters );
#endif /* ifndef LOCAL_PORTABLE_H */
