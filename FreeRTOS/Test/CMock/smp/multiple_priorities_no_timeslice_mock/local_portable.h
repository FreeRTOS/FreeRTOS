#ifndef PORTABLE_H
#define PORTABLE_H
void * pvPortMalloc( size_t xSize );
void vPortFree( void * pv );
StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters );
BaseType_t xPortStartScheduler( void );
void vPortEndScheduler( void );
#endif
