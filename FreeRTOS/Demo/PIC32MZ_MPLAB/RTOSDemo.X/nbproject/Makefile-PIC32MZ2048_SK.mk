#
# Generated Makefile - do not edit!
#
# Edit the Makefile in the project folder instead (../Makefile). Each target
# has a -pre and a -post target defined where you can add customized code.
#
# This makefile implements configuration specific macros and targets.


# Include project Makefile
ifeq "${IGNORE_LOCAL}" "TRUE"
# do not include local makefile. User is passing all local related variables already
else
include Makefile
# Include makefile containing local settings
ifeq "$(wildcard nbproject/Makefile-local-PIC32MZ2048_SK.mk)" "nbproject/Makefile-local-PIC32MZ2048_SK.mk"
include nbproject/Makefile-local-PIC32MZ2048_SK.mk
endif
endif

# Environment
MKDIR=gnumkdir -p
RM=rm -f
MV=mv
CP=cp

# Macros
CND_CONF=PIC32MZ2048_SK
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

ifeq ($(COMPARE_BUILD), true)
COMPARISON_BUILD=-mafrlcsj
else
COMPARISON_BUILD=
endif

ifdef SUB_IMAGE_ADDRESS

else
SUB_IMAGE_ADDRESS_COMMAND=
endif

# Object Directory
OBJECTDIR=build/${CND_CONF}/${IMAGE_TYPE}

# Distribution Directory
DISTDIR=dist/${CND_CONF}/${IMAGE_TYPE}

# Source Files Quoted if spaced
SOURCEFILES_QUOTED_IF_SPACED=../../Common/Minimal/GenQTest.c ../../Common/Minimal/QPeek.c ../../Common/Minimal/blocktim.c ../../Common/Minimal/flash_timer.c ../../Common/Minimal/semtest.c ../../Common/Minimal/IntQueue.c ../../Common/Minimal/QueueOverwrite.c ../../Common/Minimal/QueueSet.c ../../Common/Minimal/countsem.c ../../Common/Minimal/dynamic.c ../../Common/Minimal/recmutex.c ../../Common/Minimal/EventGroupsDemo.c ../../../Source/queue.c ../../../Source/tasks.c ../../../Source/list.c ../../../Source/timers.c ../../../Source/portable/MPLAB/PIC32MZ/port.c ../../../Source/portable/MPLAB/PIC32MZ/port_asm.S ../../../Source/portable/MemMang/heap_4.c ../../../Source/event_groups.c ../main.c ../ParTest/ParTest.c ../main_blinky.c ../ConfigPerformance.c ../main_full.c ../RegisterTestTasks.S ../IntQueueTimer.c ../IntQueueTimer_isr.S ../timertest.c ../timertest_isr.S ../ISRTriggeredTask.c ../ISRTriggeredTask_isr.S ../flop_mz.c

# Object Files Quoted if spaced
OBJECTFILES_QUOTED_IF_SPACED=${OBJECTDIR}/_ext/1163846883/GenQTest.o ${OBJECTDIR}/_ext/1163846883/QPeek.o ${OBJECTDIR}/_ext/1163846883/blocktim.o ${OBJECTDIR}/_ext/1163846883/flash_timer.o ${OBJECTDIR}/_ext/1163846883/semtest.o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o ${OBJECTDIR}/_ext/1163846883/QueueSet.o ${OBJECTDIR}/_ext/1163846883/countsem.o ${OBJECTDIR}/_ext/1163846883/dynamic.o ${OBJECTDIR}/_ext/1163846883/recmutex.o ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o ${OBJECTDIR}/_ext/449926602/queue.o ${OBJECTDIR}/_ext/449926602/tasks.o ${OBJECTDIR}/_ext/449926602/list.o ${OBJECTDIR}/_ext/449926602/timers.o ${OBJECTDIR}/_ext/332309698/port.o ${OBJECTDIR}/_ext/332309698/port_asm.o ${OBJECTDIR}/_ext/1884096877/heap_4.o ${OBJECTDIR}/_ext/449926602/event_groups.o ${OBJECTDIR}/_ext/1472/main.o ${OBJECTDIR}/_ext/809743516/ParTest.o ${OBJECTDIR}/_ext/1472/main_blinky.o ${OBJECTDIR}/_ext/1472/ConfigPerformance.o ${OBJECTDIR}/_ext/1472/main_full.o ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o ${OBJECTDIR}/_ext/1472/IntQueueTimer.o ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o ${OBJECTDIR}/_ext/1472/timertest.o ${OBJECTDIR}/_ext/1472/timertest_isr.o ${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o ${OBJECTDIR}/_ext/1472/flop_mz.o
POSSIBLE_DEPFILES=${OBJECTDIR}/_ext/1163846883/GenQTest.o.d ${OBJECTDIR}/_ext/1163846883/QPeek.o.d ${OBJECTDIR}/_ext/1163846883/blocktim.o.d ${OBJECTDIR}/_ext/1163846883/flash_timer.o.d ${OBJECTDIR}/_ext/1163846883/semtest.o.d ${OBJECTDIR}/_ext/1163846883/IntQueue.o.d ${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o.d ${OBJECTDIR}/_ext/1163846883/QueueSet.o.d ${OBJECTDIR}/_ext/1163846883/countsem.o.d ${OBJECTDIR}/_ext/1163846883/dynamic.o.d ${OBJECTDIR}/_ext/1163846883/recmutex.o.d ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d ${OBJECTDIR}/_ext/449926602/queue.o.d ${OBJECTDIR}/_ext/449926602/tasks.o.d ${OBJECTDIR}/_ext/449926602/list.o.d ${OBJECTDIR}/_ext/449926602/timers.o.d ${OBJECTDIR}/_ext/332309698/port.o.d ${OBJECTDIR}/_ext/332309698/port_asm.o.d ${OBJECTDIR}/_ext/1884096877/heap_4.o.d ${OBJECTDIR}/_ext/449926602/event_groups.o.d ${OBJECTDIR}/_ext/1472/main.o.d ${OBJECTDIR}/_ext/809743516/ParTest.o.d ${OBJECTDIR}/_ext/1472/main_blinky.o.d ${OBJECTDIR}/_ext/1472/ConfigPerformance.o.d ${OBJECTDIR}/_ext/1472/main_full.o.d ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d ${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d ${OBJECTDIR}/_ext/1472/timertest.o.d ${OBJECTDIR}/_ext/1472/timertest_isr.o.d ${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o.d ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.d ${OBJECTDIR}/_ext/1472/flop_mz.o.d

# Object Files
OBJECTFILES=${OBJECTDIR}/_ext/1163846883/GenQTest.o ${OBJECTDIR}/_ext/1163846883/QPeek.o ${OBJECTDIR}/_ext/1163846883/blocktim.o ${OBJECTDIR}/_ext/1163846883/flash_timer.o ${OBJECTDIR}/_ext/1163846883/semtest.o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o ${OBJECTDIR}/_ext/1163846883/QueueSet.o ${OBJECTDIR}/_ext/1163846883/countsem.o ${OBJECTDIR}/_ext/1163846883/dynamic.o ${OBJECTDIR}/_ext/1163846883/recmutex.o ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o ${OBJECTDIR}/_ext/449926602/queue.o ${OBJECTDIR}/_ext/449926602/tasks.o ${OBJECTDIR}/_ext/449926602/list.o ${OBJECTDIR}/_ext/449926602/timers.o ${OBJECTDIR}/_ext/332309698/port.o ${OBJECTDIR}/_ext/332309698/port_asm.o ${OBJECTDIR}/_ext/1884096877/heap_4.o ${OBJECTDIR}/_ext/449926602/event_groups.o ${OBJECTDIR}/_ext/1472/main.o ${OBJECTDIR}/_ext/809743516/ParTest.o ${OBJECTDIR}/_ext/1472/main_blinky.o ${OBJECTDIR}/_ext/1472/ConfigPerformance.o ${OBJECTDIR}/_ext/1472/main_full.o ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o ${OBJECTDIR}/_ext/1472/IntQueueTimer.o ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o ${OBJECTDIR}/_ext/1472/timertest.o ${OBJECTDIR}/_ext/1472/timertest_isr.o ${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o ${OBJECTDIR}/_ext/1472/flop_mz.o

# Source Files
SOURCEFILES=../../Common/Minimal/GenQTest.c ../../Common/Minimal/QPeek.c ../../Common/Minimal/blocktim.c ../../Common/Minimal/flash_timer.c ../../Common/Minimal/semtest.c ../../Common/Minimal/IntQueue.c ../../Common/Minimal/QueueOverwrite.c ../../Common/Minimal/QueueSet.c ../../Common/Minimal/countsem.c ../../Common/Minimal/dynamic.c ../../Common/Minimal/recmutex.c ../../Common/Minimal/EventGroupsDemo.c ../../../Source/queue.c ../../../Source/tasks.c ../../../Source/list.c ../../../Source/timers.c ../../../Source/portable/MPLAB/PIC32MZ/port.c ../../../Source/portable/MPLAB/PIC32MZ/port_asm.S ../../../Source/portable/MemMang/heap_4.c ../../../Source/event_groups.c ../main.c ../ParTest/ParTest.c ../main_blinky.c ../ConfigPerformance.c ../main_full.c ../RegisterTestTasks.S ../IntQueueTimer.c ../IntQueueTimer_isr.S ../timertest.c ../timertest_isr.S ../ISRTriggeredTask.c ../ISRTriggeredTask_isr.S ../flop_mz.c


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
ifneq ($(INFORMATION_MESSAGE), )
	@echo $(INFORMATION_MESSAGE)
endif
	${MAKE}  -f nbproject/Makefile-PIC32MZ2048_SK.mk dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}

MP_PROCESSOR_OPTION=32MZ2048ECH144
MP_LINKER_FILE_OPTION=
# ------------------------------------------------------------------------------------
# Rules for buildStep: assemble
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
else
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: assembleWithPreprocess
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
${OBJECTDIR}/_ext/332309698/port_asm.o: ../../../Source/portable/MPLAB/PIC32MZ/port_asm.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/332309698"
	@${RM} ${OBJECTDIR}/_ext/332309698/port_asm.o.d
	@${RM} ${OBJECTDIR}/_ext/332309698/port_asm.o
	@${RM} ${OBJECTDIR}/_ext/332309698/port_asm.o.ok ${OBJECTDIR}/_ext/332309698/port_asm.o.err
	@${FIXDEPS} "${OBJECTDIR}/_ext/332309698/port_asm.o.d" "${OBJECTDIR}/_ext/332309698/port_asm.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -DPKOBSKDEPlatformTool=1 -c -mprocessor=$(MP_PROCESSOR_OPTION)  -MMD -MF "${OBJECTDIR}/_ext/332309698/port_asm.o.d"  -o ${OBJECTDIR}/_ext/332309698/port_asm.o ../../../Source/portable/MPLAB/PIC32MZ/port_asm.S  -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/332309698/port_asm.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=PKOBSKDEPlatformTool=1 -I../../../Source/portable/MPLAB/PIC32MZ -I../

${OBJECTDIR}/_ext/1472/RegisterTestTasks.o: ../RegisterTestTasks.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o
	@${RM} ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.ok ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.err
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d" "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -DPKOBSKDEPlatformTool=1 -c -mprocessor=$(MP_PROCESSOR_OPTION)  -MMD -MF "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d"  -o ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o ../RegisterTestTasks.S  -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=PKOBSKDEPlatformTool=1 -I../../../Source/portable/MPLAB/PIC32MZ -I../

${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o: ../IntQueueTimer_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.ok ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.err
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d" "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -DPKOBSKDEPlatformTool=1 -c -mprocessor=$(MP_PROCESSOR_OPTION)  -MMD -MF "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d"  -o ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o ../IntQueueTimer_isr.S  -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=PKOBSKDEPlatformTool=1 -I../../../Source/portable/MPLAB/PIC32MZ -I../

${OBJECTDIR}/_ext/1472/timertest_isr.o: ../timertest_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/timertest_isr.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/timertest_isr.o
	@${RM} ${OBJECTDIR}/_ext/1472/timertest_isr.o.ok ${OBJECTDIR}/_ext/1472/timertest_isr.o.err
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/timertest_isr.o.d" "${OBJECTDIR}/_ext/1472/timertest_isr.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -DPKOBSKDEPlatformTool=1 -c -mprocessor=$(MP_PROCESSOR_OPTION)  -MMD -MF "${OBJECTDIR}/_ext/1472/timertest_isr.o.d"  -o ${OBJECTDIR}/_ext/1472/timertest_isr.o ../timertest_isr.S  -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/timertest_isr.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=PKOBSKDEPlatformTool=1 -I../../../Source/portable/MPLAB/PIC32MZ -I../

${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o: ../ISRTriggeredTask_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o
	@${RM} ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.ok ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.err
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.d" "${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -DPKOBSKDEPlatformTool=1 -c -mprocessor=$(MP_PROCESSOR_OPTION)  -MMD -MF "${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.d"  -o ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o ../ISRTriggeredTask_isr.S  -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=PKOBSKDEPlatformTool=1 -I../../../Source/portable/MPLAB/PIC32MZ -I../

else
${OBJECTDIR}/_ext/332309698/port_asm.o: ../../../Source/portable/MPLAB/PIC32MZ/port_asm.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/332309698"
	@${RM} ${OBJECTDIR}/_ext/332309698/port_asm.o.d
	@${RM} ${OBJECTDIR}/_ext/332309698/port_asm.o
	@${RM} ${OBJECTDIR}/_ext/332309698/port_asm.o.ok ${OBJECTDIR}/_ext/332309698/port_asm.o.err
	@${FIXDEPS} "${OBJECTDIR}/_ext/332309698/port_asm.o.d" "${OBJECTDIR}/_ext/332309698/port_asm.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION)  -MMD -MF "${OBJECTDIR}/_ext/332309698/port_asm.o.d"  -o ${OBJECTDIR}/_ext/332309698/port_asm.o ../../../Source/portable/MPLAB/PIC32MZ/port_asm.S  -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/332309698/port_asm.o.asm.d",--gdwarf-2 -I../../../Source/portable/MPLAB/PIC32MZ -I../

${OBJECTDIR}/_ext/1472/RegisterTestTasks.o: ../RegisterTestTasks.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o
	@${RM} ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.ok ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.err
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d" "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION)  -MMD -MF "${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.d"  -o ${OBJECTDIR}/_ext/1472/RegisterTestTasks.o ../RegisterTestTasks.S  -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/RegisterTestTasks.o.asm.d",--gdwarf-2 -I../../../Source/portable/MPLAB/PIC32MZ -I../

${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o: ../IntQueueTimer_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.ok ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.err
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d" "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION)  -MMD -MF "${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.d"  -o ${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o ../IntQueueTimer_isr.S  -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/IntQueueTimer_isr.o.asm.d",--gdwarf-2 -I../../../Source/portable/MPLAB/PIC32MZ -I../

${OBJECTDIR}/_ext/1472/timertest_isr.o: ../timertest_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/timertest_isr.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/timertest_isr.o
	@${RM} ${OBJECTDIR}/_ext/1472/timertest_isr.o.ok ${OBJECTDIR}/_ext/1472/timertest_isr.o.err
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/timertest_isr.o.d" "${OBJECTDIR}/_ext/1472/timertest_isr.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION)  -MMD -MF "${OBJECTDIR}/_ext/1472/timertest_isr.o.d"  -o ${OBJECTDIR}/_ext/1472/timertest_isr.o ../timertest_isr.S  -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/timertest_isr.o.asm.d",--gdwarf-2 -I../../../Source/portable/MPLAB/PIC32MZ -I../

${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o: ../ISRTriggeredTask_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o
	@${RM} ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.ok ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.err
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.d" "${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION)  -MMD -MF "${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.d"  -o ${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o ../ISRTriggeredTask_isr.S  -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1472/ISRTriggeredTask_isr.o.asm.d",--gdwarf-2 -I../../../Source/portable/MPLAB/PIC32MZ -I../

endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: compile
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
${OBJECTDIR}/_ext/1163846883/GenQTest.o: ../../Common/Minimal/GenQTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/GenQTest.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/GenQTest.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" -o ${OBJECTDIR}/_ext/1163846883/GenQTest.o ../../Common/Minimal/GenQTest.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/QPeek.o: ../../Common/Minimal/QPeek.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/QPeek.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/QPeek.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/QPeek.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/QPeek.o.d" -o ${OBJECTDIR}/_ext/1163846883/QPeek.o ../../Common/Minimal/QPeek.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/blocktim.o: ../../Common/Minimal/blocktim.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/blocktim.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/blocktim.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" -o ${OBJECTDIR}/_ext/1163846883/blocktim.o ../../Common/Minimal/blocktim.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/flash_timer.o: ../../Common/Minimal/flash_timer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/flash_timer.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/flash_timer.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/flash_timer.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/flash_timer.o.d" -o ${OBJECTDIR}/_ext/1163846883/flash_timer.o ../../Common/Minimal/flash_timer.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/semtest.o: ../../Common/Minimal/semtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/semtest.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/semtest.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/semtest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/semtest.o.d" -o ${OBJECTDIR}/_ext/1163846883/semtest.o ../../Common/Minimal/semtest.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/IntQueue.o: ../../Common/Minimal/IntQueue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntQueue.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntQueue.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" -o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ../../Common/Minimal/IntQueue.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o: ../../Common/Minimal/QueueOverwrite.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o.d" -o ${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o ../../Common/Minimal/QueueOverwrite.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/QueueSet.o: ../../Common/Minimal/QueueSet.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/QueueSet.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/QueueSet.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/QueueSet.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/QueueSet.o.d" -o ${OBJECTDIR}/_ext/1163846883/QueueSet.o ../../Common/Minimal/QueueSet.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/countsem.o: ../../Common/Minimal/countsem.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/countsem.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/countsem.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/countsem.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/countsem.o.d" -o ${OBJECTDIR}/_ext/1163846883/countsem.o ../../Common/Minimal/countsem.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/dynamic.o: ../../Common/Minimal/dynamic.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/dynamic.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/dynamic.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/dynamic.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/dynamic.o.d" -o ${OBJECTDIR}/_ext/1163846883/dynamic.o ../../Common/Minimal/dynamic.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/recmutex.o: ../../Common/Minimal/recmutex.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/recmutex.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/recmutex.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/recmutex.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/recmutex.o.d" -o ${OBJECTDIR}/_ext/1163846883/recmutex.o ../../Common/Minimal/recmutex.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o: ../../Common/Minimal/EventGroupsDemo.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d" -o ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o ../../Common/Minimal/EventGroupsDemo.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/449926602/queue.o: ../../../Source/queue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602"
	@${RM} ${OBJECTDIR}/_ext/449926602/queue.o.d
	@${RM} ${OBJECTDIR}/_ext/449926602/queue.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/queue.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/449926602/queue.o.d" -o ${OBJECTDIR}/_ext/449926602/queue.o ../../../Source/queue.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/449926602/tasks.o: ../../../Source/tasks.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602"
	@${RM} ${OBJECTDIR}/_ext/449926602/tasks.o.d
	@${RM} ${OBJECTDIR}/_ext/449926602/tasks.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/tasks.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/449926602/tasks.o.d" -o ${OBJECTDIR}/_ext/449926602/tasks.o ../../../Source/tasks.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/449926602/list.o: ../../../Source/list.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602"
	@${RM} ${OBJECTDIR}/_ext/449926602/list.o.d
	@${RM} ${OBJECTDIR}/_ext/449926602/list.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/list.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/449926602/list.o.d" -o ${OBJECTDIR}/_ext/449926602/list.o ../../../Source/list.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/449926602/timers.o: ../../../Source/timers.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602"
	@${RM} ${OBJECTDIR}/_ext/449926602/timers.o.d
	@${RM} ${OBJECTDIR}/_ext/449926602/timers.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/timers.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/449926602/timers.o.d" -o ${OBJECTDIR}/_ext/449926602/timers.o ../../../Source/timers.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/332309698/port.o: ../../../Source/portable/MPLAB/PIC32MZ/port.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/332309698"
	@${RM} ${OBJECTDIR}/_ext/332309698/port.o.d
	@${RM} ${OBJECTDIR}/_ext/332309698/port.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/332309698/port.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/332309698/port.o.d" -o ${OBJECTDIR}/_ext/332309698/port.o ../../../Source/portable/MPLAB/PIC32MZ/port.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1884096877/heap_4.o: ../../../Source/portable/MemMang/heap_4.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1884096877"
	@${RM} ${OBJECTDIR}/_ext/1884096877/heap_4.o.d
	@${RM} ${OBJECTDIR}/_ext/1884096877/heap_4.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1884096877/heap_4.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1884096877/heap_4.o.d" -o ${OBJECTDIR}/_ext/1884096877/heap_4.o ../../../Source/portable/MemMang/heap_4.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/449926602/event_groups.o: ../../../Source/event_groups.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602"
	@${RM} ${OBJECTDIR}/_ext/449926602/event_groups.o.d
	@${RM} ${OBJECTDIR}/_ext/449926602/event_groups.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/event_groups.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/449926602/event_groups.o.d" -o ${OBJECTDIR}/_ext/449926602/event_groups.o ../../../Source/event_groups.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/main.o: ../main.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/main.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/main.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/main.o.d" -o ${OBJECTDIR}/_ext/1472/main.o ../main.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/809743516/ParTest.o: ../ParTest/ParTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/809743516"
	@${RM} ${OBJECTDIR}/_ext/809743516/ParTest.o.d
	@${RM} ${OBJECTDIR}/_ext/809743516/ParTest.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/809743516/ParTest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/809743516/ParTest.o.d" -o ${OBJECTDIR}/_ext/809743516/ParTest.o ../ParTest/ParTest.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/main_blinky.o: ../main_blinky.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/main_blinky.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/main_blinky.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main_blinky.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/main_blinky.o.d" -o ${OBJECTDIR}/_ext/1472/main_blinky.o ../main_blinky.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/ConfigPerformance.o: ../ConfigPerformance.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/ConfigPerformance.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/ConfigPerformance.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/ConfigPerformance.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/ConfigPerformance.o.d" -o ${OBJECTDIR}/_ext/1472/ConfigPerformance.o ../ConfigPerformance.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/main_full.o: ../main_full.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/main_full.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/main_full.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main_full.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/main_full.o.d" -o ${OBJECTDIR}/_ext/1472/main_full.o ../main_full.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/IntQueueTimer.o: ../IntQueueTimer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d" -o ${OBJECTDIR}/_ext/1472/IntQueueTimer.o ../IntQueueTimer.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/timertest.o: ../timertest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/timertest.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/timertest.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/timertest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/timertest.o.d" -o ${OBJECTDIR}/_ext/1472/timertest.o ../timertest.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o: ../ISRTriggeredTask.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o.d" -o ${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o ../ISRTriggeredTask.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/flop_mz.o: ../flop_mz.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/flop_mz.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/flop_mz.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/flop_mz.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -DPKOBSKDEPlatformTool=1  -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/flop_mz.o.d" -o ${OBJECTDIR}/_ext/1472/flop_mz.o ../flop_mz.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

else
${OBJECTDIR}/_ext/1163846883/GenQTest.o: ../../Common/Minimal/GenQTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/GenQTest.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/GenQTest.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" -o ${OBJECTDIR}/_ext/1163846883/GenQTest.o ../../Common/Minimal/GenQTest.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/QPeek.o: ../../Common/Minimal/QPeek.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/QPeek.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/QPeek.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/QPeek.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/QPeek.o.d" -o ${OBJECTDIR}/_ext/1163846883/QPeek.o ../../Common/Minimal/QPeek.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/blocktim.o: ../../Common/Minimal/blocktim.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/blocktim.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/blocktim.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" -o ${OBJECTDIR}/_ext/1163846883/blocktim.o ../../Common/Minimal/blocktim.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/flash_timer.o: ../../Common/Minimal/flash_timer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/flash_timer.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/flash_timer.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/flash_timer.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/flash_timer.o.d" -o ${OBJECTDIR}/_ext/1163846883/flash_timer.o ../../Common/Minimal/flash_timer.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/semtest.o: ../../Common/Minimal/semtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/semtest.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/semtest.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/semtest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/semtest.o.d" -o ${OBJECTDIR}/_ext/1163846883/semtest.o ../../Common/Minimal/semtest.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/IntQueue.o: ../../Common/Minimal/IntQueue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntQueue.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntQueue.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" -o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ../../Common/Minimal/IntQueue.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o: ../../Common/Minimal/QueueOverwrite.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o.d" -o ${OBJECTDIR}/_ext/1163846883/QueueOverwrite.o ../../Common/Minimal/QueueOverwrite.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/QueueSet.o: ../../Common/Minimal/QueueSet.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/QueueSet.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/QueueSet.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/QueueSet.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/QueueSet.o.d" -o ${OBJECTDIR}/_ext/1163846883/QueueSet.o ../../Common/Minimal/QueueSet.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/countsem.o: ../../Common/Minimal/countsem.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/countsem.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/countsem.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/countsem.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/countsem.o.d" -o ${OBJECTDIR}/_ext/1163846883/countsem.o ../../Common/Minimal/countsem.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/dynamic.o: ../../Common/Minimal/dynamic.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/dynamic.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/dynamic.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/dynamic.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/dynamic.o.d" -o ${OBJECTDIR}/_ext/1163846883/dynamic.o ../../Common/Minimal/dynamic.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/recmutex.o: ../../Common/Minimal/recmutex.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/recmutex.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/recmutex.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/recmutex.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/recmutex.o.d" -o ${OBJECTDIR}/_ext/1163846883/recmutex.o ../../Common/Minimal/recmutex.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o: ../../Common/Minimal/EventGroupsDemo.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883"
	@${RM} ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d
	@${RM} ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d" -o ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o ../../Common/Minimal/EventGroupsDemo.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/449926602/queue.o: ../../../Source/queue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602"
	@${RM} ${OBJECTDIR}/_ext/449926602/queue.o.d
	@${RM} ${OBJECTDIR}/_ext/449926602/queue.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/queue.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/449926602/queue.o.d" -o ${OBJECTDIR}/_ext/449926602/queue.o ../../../Source/queue.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/449926602/tasks.o: ../../../Source/tasks.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602"
	@${RM} ${OBJECTDIR}/_ext/449926602/tasks.o.d
	@${RM} ${OBJECTDIR}/_ext/449926602/tasks.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/tasks.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/449926602/tasks.o.d" -o ${OBJECTDIR}/_ext/449926602/tasks.o ../../../Source/tasks.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/449926602/list.o: ../../../Source/list.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602"
	@${RM} ${OBJECTDIR}/_ext/449926602/list.o.d
	@${RM} ${OBJECTDIR}/_ext/449926602/list.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/list.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/449926602/list.o.d" -o ${OBJECTDIR}/_ext/449926602/list.o ../../../Source/list.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/449926602/timers.o: ../../../Source/timers.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602"
	@${RM} ${OBJECTDIR}/_ext/449926602/timers.o.d
	@${RM} ${OBJECTDIR}/_ext/449926602/timers.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/timers.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/449926602/timers.o.d" -o ${OBJECTDIR}/_ext/449926602/timers.o ../../../Source/timers.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/332309698/port.o: ../../../Source/portable/MPLAB/PIC32MZ/port.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/332309698"
	@${RM} ${OBJECTDIR}/_ext/332309698/port.o.d
	@${RM} ${OBJECTDIR}/_ext/332309698/port.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/332309698/port.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/332309698/port.o.d" -o ${OBJECTDIR}/_ext/332309698/port.o ../../../Source/portable/MPLAB/PIC32MZ/port.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1884096877/heap_4.o: ../../../Source/portable/MemMang/heap_4.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1884096877"
	@${RM} ${OBJECTDIR}/_ext/1884096877/heap_4.o.d
	@${RM} ${OBJECTDIR}/_ext/1884096877/heap_4.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1884096877/heap_4.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1884096877/heap_4.o.d" -o ${OBJECTDIR}/_ext/1884096877/heap_4.o ../../../Source/portable/MemMang/heap_4.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/449926602/event_groups.o: ../../../Source/event_groups.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602"
	@${RM} ${OBJECTDIR}/_ext/449926602/event_groups.o.d
	@${RM} ${OBJECTDIR}/_ext/449926602/event_groups.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/event_groups.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/449926602/event_groups.o.d" -o ${OBJECTDIR}/_ext/449926602/event_groups.o ../../../Source/event_groups.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/main.o: ../main.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/main.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/main.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/main.o.d" -o ${OBJECTDIR}/_ext/1472/main.o ../main.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/809743516/ParTest.o: ../ParTest/ParTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/809743516"
	@${RM} ${OBJECTDIR}/_ext/809743516/ParTest.o.d
	@${RM} ${OBJECTDIR}/_ext/809743516/ParTest.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/809743516/ParTest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/809743516/ParTest.o.d" -o ${OBJECTDIR}/_ext/809743516/ParTest.o ../ParTest/ParTest.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/main_blinky.o: ../main_blinky.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/main_blinky.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/main_blinky.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main_blinky.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/main_blinky.o.d" -o ${OBJECTDIR}/_ext/1472/main_blinky.o ../main_blinky.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/ConfigPerformance.o: ../ConfigPerformance.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/ConfigPerformance.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/ConfigPerformance.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/ConfigPerformance.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/ConfigPerformance.o.d" -o ${OBJECTDIR}/_ext/1472/ConfigPerformance.o ../ConfigPerformance.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/main_full.o: ../main_full.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/main_full.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/main_full.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/main_full.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/main_full.o.d" -o ${OBJECTDIR}/_ext/1472/main_full.o ../main_full.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/IntQueueTimer.o: ../IntQueueTimer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/IntQueueTimer.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/IntQueueTimer.o.d" -o ${OBJECTDIR}/_ext/1472/IntQueueTimer.o ../IntQueueTimer.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/timertest.o: ../timertest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/timertest.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/timertest.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/timertest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/timertest.o.d" -o ${OBJECTDIR}/_ext/1472/timertest.o ../timertest.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o: ../ISRTriggeredTask.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o.d" -o ${OBJECTDIR}/_ext/1472/ISRTriggeredTask.o ../ISRTriggeredTask.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

${OBJECTDIR}/_ext/1472/flop_mz.o: ../flop_mz.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1472"
	@${RM} ${OBJECTDIR}/_ext/1472/flop_mz.o.d
	@${RM} ${OBJECTDIR}/_ext/1472/flop_mz.o
	@${FIXDEPS} "${OBJECTDIR}/_ext/1472/flop_mz.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MZ" -I"../../Common/include" -I"../" -Wall -MMD -MF "${OBJECTDIR}/_ext/1472/flop_mz.o.d" -o ${OBJECTDIR}/_ext/1472/flop_mz.o ../flop_mz.c    -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wall -Wextra

endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: compileCPP
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
else
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: link
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}: ${OBJECTFILES}  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} dist/${CND_CONF}/${IMAGE_TYPE}
	${MP_CC} $(MP_EXTRA_LD_PRE) -g -mdebugger -DPKOBSKDEPlatformTool=1 -mprocessor=$(MP_PROCESSOR_OPTION)  -o dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX} ${OBJECTFILES_QUOTED_IF_SPACED}          -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)   -mreserve=data@0x0:0x27F   -Wl,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_LD_POST)$(MP_LINKER_FILE_OPTION),--defsym=__MPLAB_DEBUG=1,--defsym=__DEBUG=1,-D=__DEBUG_D,--defsym=PKOBSKDEPlatformTool=1,--defsym=_min_heap_size=0,--no-code-in-dinit,--no-dinit-in-serial-mem,-Map="${DISTDIR}/${PROJECTNAME}.${IMAGE_TYPE}.map",--memorysummary,dist/${CND_CONF}/${IMAGE_TYPE}/memoryfile.xml

else
dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}: ${OBJECTFILES}  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} dist/${CND_CONF}/${IMAGE_TYPE}
	${MP_CC} $(MP_EXTRA_LD_PRE)  -mprocessor=$(MP_PROCESSOR_OPTION)  -o dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${DEBUGGABLE_SUFFIX} ${OBJECTFILES_QUOTED_IF_SPACED}          -DXPRJ_PIC32MZ2048_SK=$(CND_CONF)  -no-legacy-libc  $(COMPARISON_BUILD)  -Wl,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_LD_POST)$(MP_LINKER_FILE_OPTION),--defsym=_min_heap_size=0,--no-code-in-dinit,--no-dinit-in-serial-mem,-Map="${DISTDIR}/${PROJECTNAME}.${IMAGE_TYPE}.map",--memorysummary,dist/${CND_CONF}/${IMAGE_TYPE}/memoryfile.xml
	${MP_CC_DIR}\\xc32-bin2hex dist/${CND_CONF}/${IMAGE_TYPE}/RTOSDemo.X.${IMAGE_TYPE}.${DEBUGGABLE_SUFFIX}
endif


# Subprojects
.build-subprojects:


# Subprojects
.clean-subprojects:

# Clean Targets
.clean-conf: ${CLEAN_SUBPROJECTS}
	${RM} -r build/PIC32MZ2048_SK
	${RM} -r dist/PIC32MZ2048_SK

# Enable dependency checking
.dep.inc: .depcheck-impl

DEPFILES=$(shell mplabwildcard ${POSSIBLE_DEPFILES})
ifneq (${DEPFILES},)
include ${DEPFILES}
endif
