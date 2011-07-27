################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
C_SRCS += \
../src/xemaclite_example_util.c 

LD_SRCS += \
../src/lscript.ld 

OBJS += \
./src/xemaclite_example_util.o 

C_DEPS += \
./src/xemaclite_example_util.d 


# Each subdirectory must supply rules for building sources it contributes
src/%.o: ../src/%.c
	@echo Building file: $<
	@echo Invoking: MicroBlaze gcc compiler
	mb-gcc -Wall -O0 -g3 -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_Ethernet\RTOSDemoSource" -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_Ethernet\RTOSDemoSource\lwIP\lwIP_Apps\apps\httpserver_raw" -I"C:\E\Dev\FreeRTOS\WorkingCopy\Demo\MicroBlaze_Spartan-6_Ethernet\RTOSDemoSource\lwIP\lwIP_Apps" -c -fmessage-length=0 -I../../RTOSDemoBSP/microblaze_0/include -mlittle-endian -mxl-barrel-shift -mxl-pattern-compare -mno-xl-soft-div -mcpu=v8.10.a -mno-xl-soft-mul -mhard-float -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@:%.o=%.d)" -o"$@" "$<"
	@echo Finished building: $<
	@echo ' '


