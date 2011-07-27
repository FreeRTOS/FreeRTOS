################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
C_SRCS += \
../FreeRTOS_Source/portable/GCC/MicroBlaze/port.c 

S_SRCS += \
../FreeRTOS_Source/portable/GCC/MicroBlaze/portasm.s 

OBJS += \
./FreeRTOS_Source/portable/GCC/MicroBlaze/port.o \
./FreeRTOS_Source/portable/GCC/MicroBlaze/portasm.o 

C_DEPS += \
./FreeRTOS_Source/portable/GCC/MicroBlaze/port.d 


# Each subdirectory must supply rules for building sources it contributes
FreeRTOS_Source/portable/GCC/MicroBlaze/%.o: ../FreeRTOS_Source/portable/GCC/MicroBlaze/%.c
	@echo Building file: $<
	@echo Invoking: MicroBlaze gcc compiler
	mb-gcc -Wall -O0 -g3 -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_EthernetLite\SDKProjects\RTOSDemoSource" -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_EthernetLite\SDKProjects\RTOSDemoSource\Demo_Source\Common_Demo_Files\include" -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_EthernetLite\SDKProjects\RTOSDemoSource\FreeRTOS_Source\include" -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_EthernetLite\SDKProjects\RTOSDemoSource\FreeRTOS_Source\portable\GCC\MicroBlaze" -c -fmessage-length=0 -I../../RTOSDemoBSP/microblaze_0/include -mlittle-endian -mxl-barrel-shift -mxl-pattern-compare -mno-xl-soft-div -mcpu=v8.10.a -mno-xl-soft-mul -mhard-float -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@:%.o=%.d)" -o"$@" "$<"
	@echo Finished building: $<
	@echo ' '

FreeRTOS_Source/portable/GCC/MicroBlaze/%.o: ../FreeRTOS_Source/portable/GCC/MicroBlaze/%.s
	@echo Building file: $<
	@echo Invoking: MicroBlaze gcc assembler
	mb-as -mlittle-endian -o"$@" "$<"
	@echo Finished building: $<
	@echo ' '


