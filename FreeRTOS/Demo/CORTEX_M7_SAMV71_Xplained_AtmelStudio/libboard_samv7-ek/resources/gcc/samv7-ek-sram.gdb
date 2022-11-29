#*************************************************
#
#  Connect to J-Link and debug application in sram.
#

# define 'reset' command
define reset

# Connect to the J-Link gdb server
target remote localhost:2331

# Reset the chip to get to a known state
monitor reset

# Load the program
load

# Reset peripheral  (RSTC_CR)
set *0x400E1800 = 0xA5000004

# Initializing PC and stack pointer
mon reg sp = (0x20400000)
set *0x20400004 = *0x20400004 & 0xFFFFFFFE
mon reg pc=(0x20400004)
info reg

# end of 'reset' command
end
