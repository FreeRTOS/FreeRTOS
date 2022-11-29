# Simulator only:
# Copy ROM-mirror area to bank 0x00

if %EVAL(ROMM_CONFIG & 0x01) == 0x01

set variable ROMM_BANK = %EVAL(ROMM_CONFIG >> 4)
set variable ROMM_SIZE = %EVAL((ROMM_CONFIG >> 1) & 0x03)

print "\n\n>Set ROM-mirror memory map...\n"


if %ROMM_SIZE == 0
set map /read H'00E000..H'00FFFF

if %ROMM_BANK == 0x00
show map
move H'f0e000..H'F0FFFF,H'e000

elseif %ROMM_BANK == 0x01
show map
move H'f1e000..H'F1FFFF,H'e000

elseif %ROMM_BANK == 0x02
show map
move H'f2e000..H'F2FFFF,H'e000

elseif %ROMM_BANK == 0x03
show map
move H'f3e000..H'F3FFFF,H'e000

elseif %ROMM_BANK == 0x04
show map
move H'f4e000..H'F4FFFF,H'e000

elseif %ROMM_BANK == 0x05
show map
move H'f5e000..H'F5FFFF,H'e000

elseif %ROMM_BANK == 0x06
show map
move H'f6e000..H'F6FFFF,H'e000

elseif %ROMM_BANK == 0x07
show map
move H'f7e000..H'F7FFFF,H'e000

elseif %ROMM_BANK == 0x08
show map
move H'f8e000..H'F8FFFF,H'e000

elseif %ROMM_BANK == 0x09
show map
move H'f9e000..H'F9FFFF,H'e000

elseif %ROMM_BANK == 0x0A
show map
move H'fAe000..H'FAFFFF,H'e000

elseif %ROMM_BANK == 0x0B
show map
move H'fBe000..H'FBFFFF,H'e000

elseif %ROMM_BANK == 0x0B
show map
move H'fBe000..H'FBFFFF,H'e000

elseif %ROMM_BANK == 0x0C
show map
move H'fCe000..H'FCFFFF,H'e000

elseif %ROMM_BANK == 0x0D
show map
move H'fde000..H'FDFFFF,H'e000

elseif %ROMM_BANK == 0x0E
show map
move H'fee000..H'FEFFFF,H'e000

elseif %ROMM_BANK == 0x0F
show map
move H'ffe000..H'FFFFFF,H'e000

endif # ROMM_BANK selection

elseif %ROMM_SIZE == 1
set map /read H'00C000..H'00FFFF

if %ROMM_BANK == 0x00
show map
move H'f0c000..H'F0FFFF,H'c000

elseif %ROMM_BANK == 0x01
show map
move H'f1c000..H'F1FFFF,H'c000

elseif %ROMM_BANK == 0x02
show map
move H'f2c000..H'F2FFFF,H'c000

elseif %ROMM_BANK == 0x03
show map
move H'f3c000..H'F3FFFF,H'c000

elseif %ROMM_BANK == 0x04
show map
move H'f4c000..H'F4FFFF,H'c000

elseif %ROMM_BANK == 0x05
show map
move H'f5c000..H'F5FFFF,H'c000

elseif %ROMM_BANK == 0x06
show map
move H'f6c000..H'F6FFFF,H'c000

elseif %ROMM_BANK == 0x07
show map
move H'f7c000..H'F7FFFF,H'c000

elseif %ROMM_BANK == 0x08
show map
move H'f8c000..H'F8FFFF,H'c000

elseif %ROMM_BANK == 0x09
show map
move H'f9c000..H'F9FFFF,H'c000

elseif %ROMM_BANK == 0x0A
show map
move H'fAc000..H'FAFFFF,H'c000

elseif %ROMM_BANK == 0x0B
show map
move H'fBc000..H'FBFFFF,H'c000

elseif %ROMM_BANK == 0x0B
show map
move H'fBc000..H'FBFFFF,H'c000

elseif %ROMM_BANK == 0x0C
show map
move H'fCc000..H'FCFFFF,H'c000

elseif %ROMM_BANK == 0x0D
show map
move H'fdc000..H'FDFFFF,H'c000

elseif %ROMM_BANK == 0x0E
show map
move H'fec000..H'FEFFFF,H'c000

elseif %ROMM_BANK == 0x0F
show map
move H'ffc000..H'FFFFFF,H'c000

endif # ROMM_BANK selection

elseif %ROMM_SIZE == 2
set map /read H'00A000..H'00FFFF

if %ROMM_BANK == 0x00
show map
move H'f0a000..H'F0FFFF,H'a000

elseif %ROMM_BANK == 0x01
show map
move H'f1a000..H'F1FFFF,H'a000

elseif %ROMM_BANK == 0x02
show map
move H'f2a000..H'F2FFFF,H'a000

elseif %ROMM_BANK == 0x03
show map
move H'f3a000..H'F3FFFF,H'a000

elseif %ROMM_BANK == 0x04
show map
move H'f4a000..H'F4FFFF,H'a000

elseif %ROMM_BANK == 0x05
show map
move H'f5a000..H'F5FFFF,H'a000

elseif %ROMM_BANK == 0x06
show map
move H'f6a000..H'F6FFFF,H'a000

elseif %ROMM_BANK == 0x07
show map
move H'f7a000..H'F7FFFF,H'a000

elseif %ROMM_BANK == 0x08
show map
move H'f8a000..H'F8FFFF,H'a000

elseif %ROMM_BANK == 0x09
show map
move H'f9a000..H'F9FFFF,H'a000

elseif %ROMM_BANK == 0x0A
show map
move H'fAa000..H'FAFFFF,H'a000

elseif %ROMM_BANK == 0x0B
show map
move H'fBa000..H'FBFFFF,H'a000

elseif %ROMM_BANK == 0x0B
show map
move H'fBa000..H'FBFFFF,H'a000

elseif %ROMM_BANK == 0x0C
show map
move H'fCa000..H'FCFFFF,H'a000

elseif %ROMM_BANK == 0x0D
show map
move H'fda000..H'FDFFFF,H'a000

elseif %ROMM_BANK == 0x0E
show map
move H'fea000..H'FEFFFF,H'a000

elseif %ROMM_BANK == 0x0F
show map
move H'ffa000..H'FFFFFF,H'a000

endif # ROMM_BANK selection

elseif %ROMM_SIZE == 3
set map /read H'008000..H'00FFFF

if %ROMM_BANK == 0x00
show map
move H'f08000..H'F0FFFF,H'8000

elseif %ROMM_BANK == 0x01
show map
move H'f18000..H'F1FFFF,H'8000

elseif %ROMM_BANK == 0x02
show map
move H'f28000..H'F2FFFF,H'8000

elseif %ROMM_BANK == 0x03
show map
move H'f38000..H'F3FFFF,H'8000

elseif %ROMM_BANK == 0x04
show map
move H'f48000..H'F4FFFF,H'8000

elseif %ROMM_BANK == 0x05
show map
move H'f58000..H'F5FFFF,H'8000

elseif %ROMM_BANK == 0x06
show map
move H'f68000..H'F6FFFF,H'8000

elseif %ROMM_BANK == 0x07
show map
move H'f78000..H'F7FFFF,H'8000

elseif %ROMM_BANK == 0x08
show map
move H'f88000..H'F8FFFF,H'8000

elseif %ROMM_BANK == 0x09
show map
move H'f98000..H'F9FFFF,H'8000

elseif %ROMM_BANK == 0x0A
show map
move H'fA8000..H'FAFFFF,H'8000

elseif %ROMM_BANK == 0x0B
show map
move H'fB8000..H'FBFFFF,H'8000

elseif %ROMM_BANK == 0x0B
show map
move H'fB8000..H'FBFFFF,H'8000

elseif %ROMM_BANK == 0x0C
show map
move H'fC8000..H'FCFFFF,H'8000

elseif %ROMM_BANK == 0x0D
show map
move H'fd8000..H'FDFFFF,H'8000

elseif %ROMM_BANK == 0x0E
show map
move H'fe8000..H'FEFFFF,H'8000

elseif %ROMM_BANK == 0x0F
show map
move H'ff8000..H'FFFFFF,H'8000

endif # ROMM_BANK selection

endif # ROMM_SIZE selection

print ">Copy ROMCONST for simulation..."
print "OK"

print "\n-----------------------------------------------------------"
print "\nUse command \"batch prc\\romconst.prc\" after each download"
print "\n-----------------------------------------------------------"

else

print "\n----------------------"
print "\nROM Mirror disabled!!!"
print "\n----------------------"

endif

print "\n-------------------------------------------------------------------"
print "\nSetting CKMR to 0xF0 to allow for the Clock Wait in that start.asm."
print "\n-------------------------------------------------------------------"

set MEM /byte 0x0403 = 0xF0
