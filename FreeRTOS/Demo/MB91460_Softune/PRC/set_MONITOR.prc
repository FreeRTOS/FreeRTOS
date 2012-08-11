# THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
# MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
# ELIGIBILITY FOR ANY PURPOSES.                                             */
#                 (C) Fujitsu Microelectronics Europe GmbH                  */

# Environment and memory manioulation after program upload


# Settings
SET VARIABLE abortIRQ0 = 0x1
SET VARIABLE intVectorMonitorDebugger = 0x10FFC00




# Disable all Interrupts
SET REGISTER I = 0x0

# Set Table Base Register
SET REGISTER TBR = intVectorMonitorDebugger

# Run to smd_tbr and save TBR of Application
go ,Start91460\smd_tbr
SET VARIABLE intVectorApllication  = %r0
SET REGISTER TBR = intVectorApllication  

# Copy required vector table entries of monitor debugger in vector table of application
MOVE intVectorMonitorDebugger + 0x3C0..intVectorMonitorDebugger + 0x3FF, intVectorApllication + 0x3C0
    
# Prepare Entries for INT0
IF %abortIRQ0 == 1
  MOVE intVectorMonitorDebugger + 0x3C0..intVectorMonitorDebugger + 0x3C3, intVectorApllication + 0x3BC
  SET MEMORY/BYTE 0x32 = 0x3
  SET MEMORY/BYTE 0x30 = 0x0
  SET MEMORY/BYTE 0x31 = 0x1
  SET MEMORY/BYTE 0x440 = 0x10
  SET REGISTER ILM = 0x1E
ENDIF

# Setting indicates software reset, which leads to that the clock settings are not changed.
SET REGISTER R4 = 0x8


# Set TBR to Vector table of application
SET REGISTER TBR = intVectorApllication 


# Run to smd_c and let the CS enabled
go noClockStartup,Start91460\smd_cs
set register r2 = %r2|0x3

# Run to main()
go ,main
