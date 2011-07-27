################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
C_SRCS += \
../FreeRTOS_Source/list.c \
../FreeRTOS_Source/queue.c \
../FreeRTOS_Source/tasks.c \
../FreeRTOS_Source/timers.c 

OBJS += \
./FreeRTOS_Source/list.o \
./FreeRTOS_Source/queue.o \
./FreeRTOS_Source/tasks.o \
./FreeRTOS_Source/timers.o 

C_DEPS += \
./FreeRTOS_Source/list.d \
./FreeRTOS_Source/queue.d \
./FreeRTOS_Source/tasks.d \
./FreeRTOS_Source/timers.d 


# Each subdirectory must supply rules for building sources it contributes
FreeRTOS_Source/%.o: ../FreeRTOS_Source/%.c
	@echo Building file: $<
	@echo Invoking: MicroBlaze gcc compiler
	mb-gcc -Wall -O0 -g3 -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_EthernetLite\SDKProjects\RTOSDemoSource" -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_EthernetLite\SDKProjects\RTOSDemoSource\Demo_Source\Common_Demo_Files\include" -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_EthernetLite\SDKProjects\RTOSDemoSource\FreeRTOS_Source\include" -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_EthernetLite\SDKProjects\RTOSDemoSource\FreeRTOS_Source\portable\GCC\MicroBlaze" -c -fmessage-length=0 -I../../RTOSDemoBSP/microblaze_0/include -mlittle-endian -mxl-barrel-shift -mxl-pattern-compare -mno-xl-soft-div -mcpu=v8.10.a -mno-xl-soft-mul -mhard-float -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@:%.o=%.d)" -o"$@" "$<"
	@echo Finished building: $<
	@echo ' '


