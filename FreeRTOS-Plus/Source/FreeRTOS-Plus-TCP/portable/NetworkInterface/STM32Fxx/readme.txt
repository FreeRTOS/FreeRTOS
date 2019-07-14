This is a FreeeRTOS+TCP driver that works for both STM32F4xx and STM32F7xx parts.

The code of stm32fxx_hal_eth.c is based on both drivers as provided by ST.

These modules should be included:

    NetworkInterface.c
	stm32fxx_hal_eth.c

It is assumed that one of these words are defined:

	STM32F7xx
	STM32F407xx
	STM32F417xx
	STM32F427xx
	STM32F437xx
	STM32F429xx
	STM32F439xx

The driver has been tested on both Eval and Discovery boards with both STM32F4 and STM32F7.
