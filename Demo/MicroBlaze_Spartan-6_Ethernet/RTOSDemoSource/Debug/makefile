################################################################################
# Automatically-generated file. Do not edit!
################################################################################

-include ../makefile.init

RM := rm -rf

# All of the sources participating in the build are defined here
-include sources.mk
-include subdir.mk
-include src/subdir.mk
-include FreeRTOS_Source/subdir.mk
-include FreeRTOS_Source/portable/MemMang/subdir.mk
-include FreeRTOS_Source/portable/GCC/MicroBlaze/subdir.mk
-include objects.mk

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(strip $(C_DEPS)),)
-include $(C_DEPS)
endif
ifneq ($(strip $(S_UPPER_DEPS)),)
-include $(S_UPPER_DEPS)
endif
endif

-include ../makefile.defs

# Add inputs and outputs from these tool invocations to the build variables 
ELFSIZE += \
RTOSDemoSource.elf.size \

ELFCHECK += \
RTOSDemoSource.elf.elfcheck \


# All Target
all: RTOSDemoSource.elf secondary-outputs

# Tool invocations
RTOSDemoSource.elf: $(OBJS) ../src/lscript.ld $(USER_OBJS)
	@echo Building target: $@
	@echo Invoking: MicroBlaze gcc linker
	mb-gcc -Wl,-T -Wl,../src/lscript.ld -L../../RTOSDemoBSP/microblaze_0/lib -mlittle-endian -mxl-barrel-shift -mxl-pattern-compare -mno-xl-soft-div -mcpu=v8.10.a -mno-xl-soft-mul -mhard-float -o"RTOSDemoSource.elf" $(OBJS) $(USER_OBJS) $(LIBS)
	@echo Finished building target: $@
	@echo ' '

RTOSDemoSource.elf.size: RTOSDemoSource.elf
	@echo Invoking: MicroBlaze Print Size
	mb-size RTOSDemoSource.elf  |tee "RTOSDemoSource.elf.size"
	@echo Finished building: $@
	@echo ' '

RTOSDemoSource.elf.elfcheck: RTOSDemoSource.elf
	@echo Invoking: Xilinx ELF Check
	elfcheck RTOSDemoSource.elf -hw ../../HardwareWithEthernetLite/system.xml -pe microblaze_0  |tee "RTOSDemoSource.elf.elfcheck"
	@echo Finished building: $@
	@echo ' '

# Other Targets
clean:
	-$(RM) $(OBJS)$(C_DEPS)$(EXECUTABLES)$(ELFSIZE)$(ELFCHECK)$(S_UPPER_DEPS) RTOSDemoSource.elf
	-@echo ' '

secondary-outputs: $(ELFSIZE) $(ELFCHECK)

.PHONY: all clean dependents
.SECONDARY:

-include ../makefile.targets
