/*
Common part of the linker scripts for STR75x devices
Copyright RAISONANCE 2006
You can use, modify and distribute this file freely, but without any waranty.
*/


/* Registers mapping */
FLASHR_BASE     = 0x20100000 ;
FLASHPR_BASE    = 0x2010DFB0 ;
CFG_BASE        = 0x60000000 ;
MRCC_BASE       = 0x60000020 ;
EXTMEM_BASE     = 0x80000000 ;
SMI_BASE        = 0x90000000 ;
DMA_BASE        = 0xFFFFEC00 ;
EIC_BASE        = 0xFFFFF800 ;
APB_BASE        = 0xFFFF8000 ;

PROVIDE( _MRCC  =  MRCC_BASE );
PROVIDE( _CFG   =  CFG_BASE  );
PROVIDE( _SMI   =  SMI_BASE  );
PROVIDE( _DMA   =  DMA_BASE  );
PROVIDE( _EIC   =  EIC_BASE  );

PROVIDE( _ADC   = (APB_BASE + 0x0400) );
PROVIDE( _TB    = (APB_BASE + 0x0800) );
PROVIDE( _TIM0  = (APB_BASE + 0x0C00) );
PROVIDE( _TIM1  = (APB_BASE + 0x1000) );
PROVIDE( _TIM2  = (APB_BASE + 0x1400) );
PROVIDE( _PWM   = (APB_BASE + 0x1800) );
PROVIDE( _USB   = (APB_BASE + 0x2800) ); /* USB registers */
PROVIDE( _WDG   = (APB_BASE + 0x3000) );
PROVIDE( _SSP0  = (APB_BASE + 0x3800) );
PROVIDE( _SSP1  = (APB_BASE + 0x3C00) );
PROVIDE( _CAN   = (APB_BASE + 0x4400) );
PROVIDE( _I2C   = (APB_BASE + 0x4C00) );
PROVIDE( _UART0 = (APB_BASE + 0x5400) );
PROVIDE( _UART1 = (APB_BASE + 0x5800) );
PROVIDE( _UART2 = (APB_BASE + 0x5C00) );
PROVIDE( _GPIO0 = (APB_BASE + 0x6400) );
PROVIDE( _GPIO1 = (APB_BASE + 0x6440) );
PROVIDE( _GPIO2 = (APB_BASE + 0x6480) );
PROVIDE( _RTC   = (APB_BASE + 0x7000) );
PROVIDE( _EXTIT = (APB_BASE + 0x7400) );

/* default stack sizes. 

These are used by the startup in order to allocate stacks for the different modes.
*/

__SVC_Stack_Size = 400 ;
__IRQ_Stack_Size = 400 ;
__USR_Stack_Size = 4 ;
__FIQ_Stack_Size = 4 ;
__ABT_Stack_Size = 0 ;
__UND_Stack_Size = 0 ;

__SVC_Stack_Init = _estack ;
__IRQ_Stack_Init = __SVC_Stack_Init - __SVC_Stack_Size ;
__USR_Stack_Init = __IRQ_Stack_Init - __IRQ_Stack_Size ;
__FIQ_Stack_Init = __USR_Stack_Init - __USR_Stack_Size ;
__ABT_Stack_Init = __FIQ_Stack_Init - __FIQ_Stack_Size ;
__UND_Stack_Init = __ABT_Stack_Init - __ABT_Stack_Size ;

/*"PROVIDE" allows to easily override these values from an object file or the commmand line.*/
PROVIDE ( _SVC_Stack_Init = __SVC_Stack_Init ) ;
PROVIDE ( _IRQ_Stack_Init = __IRQ_Stack_Init ) ;
PROVIDE ( _USR_Stack_Init = __USR_Stack_Init ) ;
PROVIDE ( _FIQ_Stack_Init = __FIQ_Stack_Init ) ;
PROVIDE ( _ABT_Stack_Init = __ABT_Stack_Init ) ;
PROVIDE ( _UND_Stack_Init = __UND_Stack_Init ) ;

/*
the user mode stack is an exception because we want it at the end of the RAM.
therefore, we just check against a minimum.
The value below is the minimum memory required for ALL THE STACKS.
There will be a link error if there is not this amount of RAM free at the end.
*/
_Minimum_Stack_Size = 0xC00 ;



/* default ISR addresses. 

The startup needs these addresses defined from another object file.
In case they are not, these PROVIDEs redirect them to the Reset.

_start must be defined, usually in the startup.
*/

PROVIDE( SWI_Handler = _start );
PROVIDE( Undefined_Handler = _start );
PROVIDE( Prefetch_Handler = _start );
PROVIDE( Abort_Handler = _start );
PROVIDE( IRQ_Handler = _start ); /* <-- needed ? */
PROVIDE( FIQ_Handler = _start );
PROVIDE( WAKUP_IRQHandler = _start );
PROVIDE( TIM2_OC2_IRQHandler = _start );
PROVIDE( TIM2_OC1_IRQHandler = _start );
PROVIDE( TIM2_IC12_IRQHandler = _start );
PROVIDE( TIM2_UP_IRQHandler = _start );
PROVIDE( TIM1_OC2_IRQHandler = _start );
PROVIDE( TIM1_OC1_IRQHandler = _start );
PROVIDE( TIM1_IC12_IRQHandler = _start );
PROVIDE( TIM1_UP_IRQHandler = _start );
PROVIDE( TIM0_OC2_IRQHandler = _start );
PROVIDE( TIM0_OC1_IRQHandler = _start );
PROVIDE( TIM0_IC12_IRQHandler = _start );
PROVIDE( TIM0_UP_IRQHandler = _start );
PROVIDE( PWM_OC123_IRQHandler = _start );
PROVIDE( PWM_EM_IRQHandler = _start );
PROVIDE( PWM_UP_IRQHandler = _start );
PROVIDE( I2C_IRQHandler = _start );
PROVIDE( SSP1_IRQHandler = _start );
PROVIDE( SSP0_IRQHandler = _start );
PROVIDE( UART2_IRQHandler = _start );
PROVIDE( UART1_IRQHandler = _start );
PROVIDE( UART0_IRQHandler = _start );
PROVIDE( CAN_IRQHandler = _start );
PROVIDE( USB_LPI_RQHandler = _start );
PROVIDE( USB_HP_IRQHandler = _start );
PROVIDE( ADC_IRQHandler = _start );
PROVIDE( DMA_IRQHandler = _start );
PROVIDE( EXTIT_IRQHandler = _start );
PROVIDE( MRCC_IRQHandler = _start );
PROVIDE( FLASHSMI_IRQHandler = _start );
PROVIDE( RTC_IRQHandler = _start );
PROVIDE( TB_IRQHandler = _start );
PROVIDE( USB_LP_IRQHandler = _start );
PROVIDE( USB_HP_IRQHandler = _start );
