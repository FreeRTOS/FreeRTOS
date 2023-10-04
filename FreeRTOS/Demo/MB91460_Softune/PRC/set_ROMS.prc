# THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU
# MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR
# ELIGIBILITY FOR ANY PURPOSES.                                            
#                 (C) Fujitsu Microelectronics Europe GmbH                 
# set_ROMS.prc
# ===========
#
# Procedurefile for the FR-Emulator - Target : MB91F467D.
# Should be executed before loading any target-file into
# the RAM of the emulator (use the debug settings).
# The procedure checks sets the ROM Select Register to allow
# the emulation of the whole ROM Area of the MB91F467D


SET MEMORY/HALFWORD 0x390 = 0xFF00
