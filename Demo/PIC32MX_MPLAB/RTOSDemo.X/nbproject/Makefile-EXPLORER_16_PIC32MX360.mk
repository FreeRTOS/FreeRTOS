#
# Generated Makefile - do not edit!
#
# Edit the Makefile in the project folder instead (../Makefile). Each target
# has a -pre and a -post target defined where you can add customized code.
#
# This makefile implements configuration specific macros and targets.


# Include project Makefile
include Makefile
# Include makefile containing local settings
ifeq "$(wildcard nbproject/Makefile-local-EXPLORER_16_PIC32MX360.mk)" "nbproject/Makefile-local-EXPLORER_16_PIC32MX360.mk"
include nbproject/Makefile-local-EXPLORER_16_PIC32MX360.mk
endif

# Environment
MKDIR=gnumkdir -p
RM=rm -f 
MV=mv 
CP=cp 

# Macros
CND_CONF=EXPLORER_16_PIC32MX360
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
IMAGE_TYPE=debug
OUTPUT_SUFFIX=elf
DEBUGGABLE_SUFFIX=elf
FINAL_IMAGE=dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}
else
IMAGE_TYPE=production
OUTPUT_SUFFIX=hex
DEBUGGABLE_SUFFIX=elf
FINAL_IMAGE=dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}
endif

# Object Directory
OBJECTDIR=build/${CND_CONF}/${IMAGE_TYPE}

# Distribution Directory
DISTDIR=dist/${CND_CONF}/${IMAGE_TYPE}

# Object Files Quoted if spaced
OBJECTFILES_QUOTED_IF_SPACED=${OBJECTDIR}/_ext/332309696/port.o ${OBJECTDIR}/_ext/332309696/port_asm.o ${OBJECTDIR}/_ext/449926602/queue.o ${OBJECTDIR}/_ext/449926602/tasks.o ${OBJECTDIR}/_ext/449926602/list.o ${OBJECTDIR}/_ext/1884096877/heap_2.o ${OBJECTDIR}/_ext/1163846883/blocktim.o ${OBJECTDIR}/_ext/1163846883/comtest.o ${OBJECTDIR}/_ext/1163846883/semtest.o ${OBJECTDIR}/_ext/1163846883/QPeek.o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ${OBJECTDIR}/_ext/1163846883/GenQTest.o ${OBJECTDIR}/_ext/1472/main.o ${OBJECTDIR}/_ext/809743516/ParTest.o ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o ${OBJECTDIR}/_ext/1472/lcd.o ${OBJECTDIR}/_ext/821501661/serial.o ${OBJECTDIR}/_ext/821501661/serial_isr.o ${OBJECTDIR}/_ext/1472/timertest.o ${OBJECTDIR}/_ext/1472/timertest_isr.o ${OBJECTDIR}/_ext/1472/IntQueueTimer.o ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o ${OBJECTDIR}/_ext/1472/printf-stdarg.o ${OBJECTDIR}/_ext/1163846883/flash_timer.o ${OBJECTDIR}/_ext/1472/main_blinky.o ${OBJECTDIR}/_ext/1472/main_full.o ${OBJECTDIR}/_ext/449926602/timers.o
POSSIBLE_DEPFILES=${OBJECTDIR}/_ext/332309696/port.o.d ${OBJECTDIR}/_ext/332309696/port_asm.o.d ${OBJECTDIR}/_ext/449926602/queue.o.d ${OBJECTDIR}/_ext/449926602/tasks.o.d ${OBJECTDIR}/_ext/449926602/list.o.d ${OBJECTDIR}/_ext/1884096877/heap_2.o.d ${OBJECTDIR}/_ext/1163846883/blocktim.o.d ${OBJECTDIR}/_ext/1163846883/comtest.o.d ${OBJECTDIR}/_ext/1163846883/semtest.o.d ${OBJECTDIR}/_ext/1163846883/QPeek.o.d ${OBJECTDIR}/_ext/1163846883/IntQueue.o.d ${OBJECTDIR}/_ext/1163846883/GenQTest.o.d ${OBJECTDIR}/_ext/1472/main.o.d ${OBJECTDIR}/_ext/809743516/ParTest.o.d ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d ${OBJECTDIR}/_ext/1472/lcd.o.d ${OBJECTDIR}/_ext/821501661/serial.o.d ${OBJECTDIR}/_ext/821501661/serial_isr.o.d ${OBJECTDIR}/_ext/1472/timertest.o.d ${OBJECTDIR}/_ext/1472/timertest_isr.o.d ${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d ${OBJECTDIR}/_ext/1472/printf-stdarg.o.d ${OBJECTDIR}/_ext/1163846883/flash_timer.o.d ${OBJECTDIR}/_ext/1472/main_blinky.o.d ${OBJECTDIR}/_ext/1472/main_full.o.d ${OBJECTDIR}/_ext/449926602/timers.o.d

# Object Files
OBJECTFILES=${OBJECTDIR}/_ext/332309696/port.o ${OBJECTDIR}/_ext/332309696/port_asm.o ${OBJECTDIR}/_ext/449926602/queue.o ${OBJECTDIR}/_ext/449926602/tasks.o ${OBJECTDIR}/_ext/449926602/list.o ${OBJECTDIR}/_ext/1884096877/heap_2.o ${OBJECTDIR}/_ext/1163846883/blocktim.o ${OBJECTDIR}/_ext/1163846883/comtest.o ${OBJECTDIR}/_ext/1163846883/semtest.o ${OBJECTDIR}/_ext/1163846883/QPeek.o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ${OBJECTDIR}/_ext/1163846883/GenQTest.o ${OBJECTDIR}/_ext/1472/main.o ${OBJECTDIR}/_ext/809743516/ParTest.o ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o ${OBJECTDIR}/_ext/1472/lcd.o ${OBJECTDIR}/_ext/821501661/serial.o ${OBJECTDIR}/_ext/821501661/serial_isr.o ${OBJECTDIR}/_ext/1472/timertest.o ${OBJECTDIR}/_ext/1472/timertest_isr.o ${OBJECTDIR}/_ext/1472/IntQueueTimer.o ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o ${OBJECTDIR}/_ext/1472/printf-stdarg.o ${OBJECTDIR}/_ext/1163846883/flash_timer.o ${OBJECTDIR}/_ext/1472/main_blinky.o ${OBJECTDIR}/_ext/1472/main_full.o ${OBJECTDIR}/_ext/449926602/timers.o


CFLAGS=
ASFLAGS=
LDLIBSOPTIONS=

############# Tool locations ##########################################
# If you copy a project from one host to another, the path where the  #
# compiler is installed may be different.                             #
# If you open this project with MPLAB X in the new host, this         #
# makefile will be regenerated and the paths will be corrected.       #
#######################################################################
# fixDeps replaces a bunch of sed/cat/printf statements that slow down the build
FIXDEPS=fixDeps

.build-conf:  ${BUILD_SUBPROJECTS}
	${MAKE}  -f nbproject/Makefile-EXPLORER_16_PIC32MX360.mk dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}

MP_PROCESSOR_OPTION=32MX360F512L
MP_LINKER_FILE_OPTION=
# ------------------------------------------------------------------------------------
# Rules for buildStep: assemble
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
else
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: assembleWithPreprocess
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
${OBJECTDIR}/_ext/332309696/port_asm.o: ../../../Source/portable/MPLAB/PIC32MX/port_asm.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/332309696 
	@${RM} ${OBJECTDIR}/_ext/332309696/port_asm.o.d 
	@${RM} ${OBJECTDIR}/_ext/332309696/port_asm.o.ok ${OBJECTDIR}/_ext/332309696/port_asm.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/332309696/port_asm.o.d" "${OBJECTDIR}/_ext/332309696/port_asm.o.asm.d" -t $(SILENT) -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../" -I"../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/332309696/port_asm.o.d"  -o ${OBJECTDIR}/_ext/332309696/port_asm.o ../../../Source/portable/MPLAB/PIC32MX/port_asm.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/332309696/port_asm.o.asm.d",--defsym=__MPLAB_DEBUG=1,--defsym=__ICD2RAM=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_REAL_ICE=1
	
${OBJECTDIR}/_ext/1472/RegisterTestTasks.o: ../RegisterTestTasks.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d 
	@${RM} ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.ok ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d" "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.asm.d" -t $(SILENT) -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../" -I"../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d"  -o ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o ../RegisterTestTasks.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.asm.d",--defsym=__MPLAB_DEBUG=1,--defsym=__ICD2RAM=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_REAL_ICE=1
	
${OBJECTDIR}/_ext/821501661/serial_isr.o: ../serial/serial_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/821501661 
	@${RM} ${OBJECTDIR}/_ext/821501661/serial_isr.o.d 
	@${RM} ${OBJECTDIR}/_ext/821501661/serial_isr.o.ok ${OBJECTDIR}/_ext/821501661/serial_isr.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/821501661/serial_isr.o.d" "${OBJECTDIR}/_ext/821501661/serial_isr.o.asm.d" -t $(SILENT) -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../" -I"../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/821501661/serial_isr.o.d"  -o ${OBJECTDIR}/_ext/821501661/serial_isr.o ../serial/serial_isr.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/821501661/serial_isr.o.asm.d",--defsym=__MPLAB_DEBUG=1,--defsym=__ICD2RAM=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_REAL_ICE=1
	
${OBJECTDIR}/_ext/1472/timertest_isr.o: ../timertest_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/timertest_isr.o.d 
	@${RM} ${OBJECTDIR}/_ext/1472/timertest_isr.o.ok ${OBJECTDIR}/_ext/1472/timertest_isr.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/timertest_isr.o.d" "${OBJECTDIR}/_ext/1472/timertest_isr.o.asm.d" -t $(SILENT) -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../" -I"../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/timertest_isr.o.d"  -o ${OBJECTDIR}/_ext/1472/timertest_isr.o ../timertest_isr.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/timertest_isr.o.asm.d",--defsym=__MPLAB_DEBUG=1,--defsym=__ICD2RAM=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_REAL_ICE=1
	
${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o: ../IntQueueTimer_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d 
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.ok ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d" "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.asm.d" -t $(SILENT) -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../" -I"../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d"  -o ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o ../IntQueueTimer_isr.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.asm.d",--defsym=__MPLAB_DEBUG=1,--defsym=__ICD2RAM=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_REAL_ICE=1
	
else
${OBJECTDIR}/_ext/332309696/port_asm.o: ../../../Source/portable/MPLAB/PIC32MX/port_asm.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/332309696 
	@${RM} ${OBJECTDIR}/_ext/332309696/port_asm.o.d 
	@${RM} ${OBJECTDIR}/_ext/332309696/port_asm.o.ok ${OBJECTDIR}/_ext/332309696/port_asm.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/332309696/port_asm.o.d" "${OBJECTDIR}/_ext/332309696/port_asm.o.asm.d" -t $(SILENT) -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../" -I"../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/332309696/port_asm.o.d"  -o ${OBJECTDIR}/_ext/332309696/port_asm.o ../../../Source/portable/MPLAB/PIC32MX/port_asm.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/332309696/port_asm.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1472/RegisterTestTasks.o: ../RegisterTestTasks.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d 
	@${RM} ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.ok ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d" "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.asm.d" -t $(SILENT) -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../" -I"../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d"  -o ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o ../RegisterTestTasks.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/821501661/serial_isr.o: ../serial/serial_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/821501661 
	@${RM} ${OBJECTDIR}/_ext/821501661/serial_isr.o.d 
	@${RM} ${OBJECTDIR}/_ext/821501661/serial_isr.o.ok ${OBJECTDIR}/_ext/821501661/serial_isr.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/821501661/serial_isr.o.d" "${OBJECTDIR}/_ext/821501661/serial_isr.o.asm.d" -t $(SILENT) -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../" -I"../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/821501661/serial_isr.o.d"  -o ${OBJECTDIR}/_ext/821501661/serial_isr.o ../serial/serial_isr.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/821501661/serial_isr.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1472/timertest_isr.o: ../timertest_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/timertest_isr.o.d 
	@${RM} ${OBJECTDIR}/_ext/1472/timertest_isr.o.ok ${OBJECTDIR}/_ext/1472/timertest_isr.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/timertest_isr.o.d" "${OBJECTDIR}/_ext/1472/timertest_isr.o.asm.d" -t $(SILENT) -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../" -I"../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/timertest_isr.o.d"  -o ${OBJECTDIR}/_ext/1472/timertest_isr.o ../timertest_isr.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/timertest_isr.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o: ../IntQueueTimer_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d 
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.ok ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d" "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.asm.d" -t $(SILENT) -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../" -I"../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d"  -o ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o ../IntQueueTimer_isr.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.asm.d",--gdwarf-2
	
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: compile
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
${OBJECTDIR}/_ext/332309696/port.o: ../../../Source/portable/MPLAB/PIC32MX/port.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/332309696 
	@${RM} ${OBJECTDIR}/_ext/332309696/port.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/332309696/port.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/332309696/port.o.d" -o ${OBJECTDIR}/_ext/332309696/port.o ../../../Source/portable/MPLAB/PIC32MX/port.c  
	
${OBJECTDIR}/_ext/449926602/queue.o: ../../../Source/queue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/449926602 
	@${RM} ${OBJECTDIR}/_ext/449926602/queue.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/queue.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/449926602/queue.o.d" -o ${OBJECTDIR}/_ext/449926602/queue.o ../../../Source/queue.c  
	
${OBJECTDIR}/_ext/449926602/tasks.o: ../../../Source/tasks.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/449926602 
	@${RM} ${OBJECTDIR}/_ext/449926602/tasks.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/tasks.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/449926602/tasks.o.d" -o ${OBJECTDIR}/_ext/449926602/tasks.o ../../../Source/tasks.c  
	
${OBJECTDIR}/_ext/449926602/list.o: ../../../Source/list.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/449926602 
	@${RM} ${OBJECTDIR}/_ext/449926602/list.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/list.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/449926602/list.o.d" -o ${OBJECTDIR}/_ext/449926602/list.o ../../../Source/list.c  
	
${OBJECTDIR}/_ext/1884096877/heap_2.o: ../../../Source/portable/MemMang/heap_2.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1884096877 
	@${RM} ${OBJECTDIR}/_ext/1884096877/heap_2.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1884096877/heap_2.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1884096877/heap_2.o.d" -o ${OBJECTDIR}/_ext/1884096877/heap_2.o ../../../Source/portable/MemMang/heap_2.c  
	
${OBJECTDIR}/_ext/1163846883/blocktim.o: ../../Common/Minimal/blocktim.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/blocktim.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" -o ${OBJECTDIR}/_ext/1163846883/blocktim.o ../../Common/Minimal/blocktim.c  
	
${OBJECTDIR}/_ext/1163846883/comtest.o: ../../Common/Minimal/comtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/comtest.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/comtest.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/comtest.o.d" -o ${OBJECTDIR}/_ext/1163846883/comtest.o ../../Common/Minimal/comtest.c  
	
${OBJECTDIR}/_ext/1163846883/semtest.o: ../../Common/Minimal/semtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/semtest.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/semtest.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/semtest.o.d" -o ${OBJECTDIR}/_ext/1163846883/semtest.o ../../Common/Minimal/semtest.c  
	
${OBJECTDIR}/_ext/1163846883/QPeek.o: ../../Common/Minimal/QPeek.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/QPeek.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/QPeek.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/QPeek.o.d" -o ${OBJECTDIR}/_ext/1163846883/QPeek.o ../../Common/Minimal/QPeek.c  
	
${OBJECTDIR}/_ext/1163846883/IntQueue.o: ../../Common/Minimal/IntQueue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntQueue.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" -o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ../../Common/Minimal/IntQueue.c  
	
${OBJECTDIR}/_ext/1163846883/GenQTest.o: ../../Common/Minimal/GenQTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/GenQTest.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" -o ${OBJECTDIR}/_ext/1163846883/GenQTest.o ../../Common/Minimal/GenQTest.c  
	
${OBJECTDIR}/_ext/1472/main.o: ../main.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/main.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/main.o.d" -o ${OBJECTDIR}/_ext/1472/main.o ../main.c  
	
${OBJECTDIR}/_ext/809743516/ParTest.o: ../ParTest/ParTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/809743516 
	@${RM} ${OBJECTDIR}/_ext/809743516/ParTest.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/809743516/ParTest.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/809743516/ParTest.o.d" -o ${OBJECTDIR}/_ext/809743516/ParTest.o ../ParTest/ParTest.c  
	
${OBJECTDIR}/_ext/1472/lcd.o: ../lcd.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/lcd.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/lcd.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/lcd.o.d" -o ${OBJECTDIR}/_ext/1472/lcd.o ../lcd.c  
	
${OBJECTDIR}/_ext/821501661/serial.o: ../serial/serial.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/821501661 
	@${RM} ${OBJECTDIR}/_ext/821501661/serial.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/821501661/serial.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/821501661/serial.o.d" -o ${OBJECTDIR}/_ext/821501661/serial.o ../serial/serial.c  
	
${OBJECTDIR}/_ext/1472/timertest.o: ../timertest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/timertest.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/timertest.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/timertest.o.d" -o ${OBJECTDIR}/_ext/1472/timertest.o ../timertest.c  
	
${OBJECTDIR}/_ext/1472/IntQueueTimer.o: ../IntQueueTimer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d" -o ${OBJECTDIR}/_ext/1472/IntQueueTimer.o ../IntQueueTimer.c  
	
${OBJECTDIR}/_ext/1472/printf-stdarg.o: ../printf-stdarg.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/printf-stdarg.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/printf-stdarg.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/printf-stdarg.o.d" -o ${OBJECTDIR}/_ext/1472/printf-stdarg.o ../printf-stdarg.c  
	
${OBJECTDIR}/_ext/1163846883/flash_timer.o: ../../Common/Minimal/flash_timer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/flash_timer.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/flash_timer.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/flash_timer.o.d" -o ${OBJECTDIR}/_ext/1163846883/flash_timer.o ../../Common/Minimal/flash_timer.c  
	
${OBJECTDIR}/_ext/1472/main_blinky.o: ../main_blinky.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/main_blinky.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main_blinky.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/main_blinky.o.d" -o ${OBJECTDIR}/_ext/1472/main_blinky.o ../main_blinky.c  
	
${OBJECTDIR}/_ext/1472/main_full.o: ../main_full.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/main_full.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main_full.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/main_full.o.d" -o ${OBJECTDIR}/_ext/1472/main_full.o ../main_full.c  
	
${OBJECTDIR}/_ext/449926602/timers.o: ../../../Source/timers.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/449926602 
	@${RM} ${OBJECTDIR}/_ext/449926602/timers.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/timers.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_REAL_ICE=1 -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/449926602/timers.o.d" -o ${OBJECTDIR}/_ext/449926602/timers.o ../../../Source/timers.c  
	
else
${OBJECTDIR}/_ext/332309696/port.o: ../../../Source/portable/MPLAB/PIC32MX/port.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/332309696 
	@${RM} ${OBJECTDIR}/_ext/332309696/port.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/332309696/port.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/332309696/port.o.d" -o ${OBJECTDIR}/_ext/332309696/port.o ../../../Source/portable/MPLAB/PIC32MX/port.c  
	
${OBJECTDIR}/_ext/449926602/queue.o: ../../../Source/queue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/449926602 
	@${RM} ${OBJECTDIR}/_ext/449926602/queue.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/queue.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/449926602/queue.o.d" -o ${OBJECTDIR}/_ext/449926602/queue.o ../../../Source/queue.c  
	
${OBJECTDIR}/_ext/449926602/tasks.o: ../../../Source/tasks.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/449926602 
	@${RM} ${OBJECTDIR}/_ext/449926602/tasks.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/tasks.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/449926602/tasks.o.d" -o ${OBJECTDIR}/_ext/449926602/tasks.o ../../../Source/tasks.c  
	
${OBJECTDIR}/_ext/449926602/list.o: ../../../Source/list.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/449926602 
	@${RM} ${OBJECTDIR}/_ext/449926602/list.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/list.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/449926602/list.o.d" -o ${OBJECTDIR}/_ext/449926602/list.o ../../../Source/list.c  
	
${OBJECTDIR}/_ext/1884096877/heap_2.o: ../../../Source/portable/MemMang/heap_2.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1884096877 
	@${RM} ${OBJECTDIR}/_ext/1884096877/heap_2.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1884096877/heap_2.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1884096877/heap_2.o.d" -o ${OBJECTDIR}/_ext/1884096877/heap_2.o ../../../Source/portable/MemMang/heap_2.c  
	
${OBJECTDIR}/_ext/1163846883/blocktim.o: ../../Common/Minimal/blocktim.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/blocktim.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" -o ${OBJECTDIR}/_ext/1163846883/blocktim.o ../../Common/Minimal/blocktim.c  
	
${OBJECTDIR}/_ext/1163846883/comtest.o: ../../Common/Minimal/comtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/comtest.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/comtest.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/comtest.o.d" -o ${OBJECTDIR}/_ext/1163846883/comtest.o ../../Common/Minimal/comtest.c  
	
${OBJECTDIR}/_ext/1163846883/semtest.o: ../../Common/Minimal/semtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/semtest.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/semtest.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/semtest.o.d" -o ${OBJECTDIR}/_ext/1163846883/semtest.o ../../Common/Minimal/semtest.c  
	
${OBJECTDIR}/_ext/1163846883/QPeek.o: ../../Common/Minimal/QPeek.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/QPeek.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/QPeek.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/QPeek.o.d" -o ${OBJECTDIR}/_ext/1163846883/QPeek.o ../../Common/Minimal/QPeek.c  
	
${OBJECTDIR}/_ext/1163846883/IntQueue.o: ../../Common/Minimal/IntQueue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntQueue.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" -o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ../../Common/Minimal/IntQueue.c  
	
${OBJECTDIR}/_ext/1163846883/GenQTest.o: ../../Common/Minimal/GenQTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/GenQTest.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" -o ${OBJECTDIR}/_ext/1163846883/GenQTest.o ../../Common/Minimal/GenQTest.c  
	
${OBJECTDIR}/_ext/1472/main.o: ../main.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/main.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/main.o.d" -o ${OBJECTDIR}/_ext/1472/main.o ../main.c  
	
${OBJECTDIR}/_ext/809743516/ParTest.o: ../ParTest/ParTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/809743516 
	@${RM} ${OBJECTDIR}/_ext/809743516/ParTest.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/809743516/ParTest.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/809743516/ParTest.o.d" -o ${OBJECTDIR}/_ext/809743516/ParTest.o ../ParTest/ParTest.c  
	
${OBJECTDIR}/_ext/1472/lcd.o: ../lcd.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/lcd.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/lcd.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/lcd.o.d" -o ${OBJECTDIR}/_ext/1472/lcd.o ../lcd.c  
	
${OBJECTDIR}/_ext/821501661/serial.o: ../serial/serial.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/821501661 
	@${RM} ${OBJECTDIR}/_ext/821501661/serial.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/821501661/serial.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/821501661/serial.o.d" -o ${OBJECTDIR}/_ext/821501661/serial.o ../serial/serial.c  
	
${OBJECTDIR}/_ext/1472/timertest.o: ../timertest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/timertest.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/timertest.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/timertest.o.d" -o ${OBJECTDIR}/_ext/1472/timertest.o ../timertest.c  
	
${OBJECTDIR}/_ext/1472/IntQueueTimer.o: ../IntQueueTimer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d" -o ${OBJECTDIR}/_ext/1472/IntQueueTimer.o ../IntQueueTimer.c  
	
${OBJECTDIR}/_ext/1472/printf-stdarg.o: ../printf-stdarg.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/printf-stdarg.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/printf-stdarg.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/printf-stdarg.o.d" -o ${OBJECTDIR}/_ext/1472/printf-stdarg.o ../printf-stdarg.c  
	
${OBJECTDIR}/_ext/1163846883/flash_timer.o: ../../Common/Minimal/flash_timer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1163846883 
	@${RM} ${OBJECTDIR}/_ext/1163846883/flash_timer.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/flash_timer.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1163846883/flash_timer.o.d" -o ${OBJECTDIR}/_ext/1163846883/flash_timer.o ../../Common/Minimal/flash_timer.c  
	
${OBJECTDIR}/_ext/1472/main_blinky.o: ../main_blinky.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/main_blinky.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main_blinky.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/main_blinky.o.d" -o ${OBJECTDIR}/_ext/1472/main_blinky.o ../main_blinky.c  
	
${OBJECTDIR}/_ext/1472/main_full.o: ../main_full.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/1472 
	@${RM} ${OBJECTDIR}/_ext/1472/main_full.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main_full.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/1472/main_full.o.d" -o ${OBJECTDIR}/_ext/1472/main_full.o ../main_full.c  
	
${OBJECTDIR}/_ext/449926602/timers.o: ../../../Source/timers.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} ${OBJECTDIR}/_ext/449926602 
	@${RM} ${OBJECTDIR}/_ext/449926602/timers.o.d 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/timers.o.d" $(SILENT) -c ${MP_CC} $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION) -ffunction-sections -I"../" -I"../../Common/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MX" -I"../../../../Source/portable/MPLAB/PIC32MX" -MMD -MF "${OBJECTDIR}/_ext/449926602/timers.o.d" -o ${OBJECTDIR}/_ext/449926602/timers.o ../../../Source/timers.c  
	
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: link
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}: ${OBJECTFILES}  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} dist/${CND_CONF}/${IMAGE_TYPE} 
	${MP_CC} $(MP_EXTRA_LD_PRE)  -mdebugger -D__MPLAB_DEBUGGER_REAL_ICE=1 -mprocessor=$(MP_PROCESSOR_OPTION)  -o dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX} ${OBJECTFILES_QUOTED_IF_SPACED}        -Wl,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_LD_POST)$(MP_LINKER_FILE_OPTION),--defsym=__MPLAB_DEBUG=1,--defsym=__ICD2RAM=1,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_REAL_ICE=1,--gc-sections 
else
dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}: ${OBJECTFILES}  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} dist/${CND_CONF}/${IMAGE_TYPE} 
	${MP_CC} $(MP_EXTRA_LD_PRE)  -mprocessor=$(MP_PROCESSOR_OPTION)  -o dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${DEBUGGABLE_SUFFIX} ${OBJECTFILES_QUOTED_IF_SPACED}        -Wl,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_LD_POST)$(MP_LINKER_FILE_OPTION),--gc-sections
	${MP_CC_DIR}\\xc32-bin2hex dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${DEBUGGABLE_SUFFIX}  
endif


# Subprojects
.build-subprojects:


# Subprojects
.clean-subprojects:

# Clean Targets
.clean-conf: ${CLEAN_SUBPROJECTS}
	${RM} -r build/EXPLORER_16_PIC32MX360
	${RM} -r dist/EXPLORER_16_PIC32MX360

# Enable dependency checking
.dep.inc: .depcheck-impl

DEPFILES=$(shell mplabwildcard ${POSSIBLE_DEPFILES})
ifneq (${DEPFILES},)
include ${DEPFILES}
endif
