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
ifeq "$(wildcard nbproject/Makefile-local-default.mk)" "nbproject/Makefile-local-default.mk"
include nbproject/Makefile-local-default.mk
endif
endif

# Environment
MKDIR=gnumkdir -p
RM=rm -f 
MV=mv 
CP=cp 

# Macros
CND_CONF=default
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
IMAGE_TYPE=debug
OUTPUT_SUFFIX=elf
DEBUGGABLE_SUFFIX=elf
FINAL_IMAGE=dist/${CND_CONF}/${IMAGE_TYPE}/PIC32MEC14xx_RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}
else
IMAGE_TYPE=production
OUTPUT_SUFFIX=hex
DEBUGGABLE_SUFFIX=elf
FINAL_IMAGE=dist/${CND_CONF}/${IMAGE_TYPE}/PIC32MEC14xx_RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}
endif

# Object Directory
OBJECTDIR=build/${CND_CONF}/${IMAGE_TYPE}

# Distribution Directory
DISTDIR=dist/${CND_CONF}/${IMAGE_TYPE}

# Source Files Quoted if spaced
SOURCEFILES_QUOTED_IF_SPACED=../src/Blinky_Demo/main_blinky.c ../../../Source/portable/MemMang/heap_2.c ../../../Source/portable/MPLAB/PIC32MEC14xx/port.c ../../../Source/portable/MPLAB/PIC32MEC14xx/port_asm.S ../../../Source/event_groups.c ../../../Source/list.c ../../../Source/queue.c ../../../Source/tasks.c ../../../Source/timers.c ../../Common/Minimal/blocktim.c ../../Common/Minimal/countsem.c ../../Common/Minimal/dynamic.c ../../Common/Minimal/EventGroupsDemo.c ../../Common/Minimal/GenQTest.c ../../Common/Minimal/IntQueue.c ../../Common/Minimal/IntSemTest.c ../../Common/Minimal/recmutex.c ../../Common/Minimal/semtest.c ../../Common/Minimal/TaskNotify.c ../../Common/Minimal/TimerDemo.c ../src/Full_Demo/IntQueueTimer.c ../src/Full_Demo/IntQueueTimer_isr.S ../src/Full_Demo/main_full.c ../src/Full_Demo/timertest.c ../src/Full_Demo/RegisterTestTasks.S ../src/MEC14xx/exceptions/MPLAB/general_exception.c ../src/MEC14xx/exceptions/MPLAB/general_exception_ctx.S ../src/MEC14xx/interrupts/girq08.c ../src/MEC14xx/interrupts/girq09.c ../src/MEC14xx/interrupts/girq10.c ../src/MEC14xx/interrupts/girq11.c ../src/MEC14xx/interrupts/girq12.c ../src/MEC14xx/interrupts/girq13.c ../src/MEC14xx/interrupts/girq14.c ../src/MEC14xx/interrupts/girq15.c ../src/MEC14xx/interrupts/girq16.c ../src/MEC14xx/interrupts/girq17.c ../src/MEC14xx/interrupts/girq18.c ../src/MEC14xx/interrupts/girq19.c ../src/MEC14xx/interrupts/girq20.c ../src/MEC14xx/interrupts/girq21.c ../src/MEC14xx/interrupts/girq22.c ../src/MEC14xx/interrupts/girq23.c ../src/MEC14xx/interrupts/girq24.c ../src/MEC14xx/interrupts/girq25.c ../src/MEC14xx/interrupts/girq26.c ../src/MEC14xx/interrupts/girqs.c ../src/MEC14xx/interrupts/girq08d.S ../src/MEC14xx/interrupts/girq09d.S ../src/MEC14xx/interrupts/girq10d.S ../src/MEC14xx/interrupts/girq11d.S ../src/MEC14xx/interrupts/girq12d.S ../src/MEC14xx/interrupts/girq13d.S ../src/MEC14xx/interrupts/girq14d.S ../src/MEC14xx/interrupts/girq15d.S ../src/MEC14xx/interrupts/girq16d.S ../src/MEC14xx/interrupts/girq17d.S ../src/MEC14xx/interrupts/girq18d.S ../src/MEC14xx/interrupts/girq19d.S ../src/MEC14xx/interrupts/girq20d.S ../src/MEC14xx/interrupts/girq21d.S ../src/MEC14xx/interrupts/girq22d.S ../src/MEC14xx/interrupts/girq23d.S ../src/MEC14xx/interrupts/girq24d.S ../src/MEC14xx/interrupts/girq25d.S ../src/MEC14xx/interrupts/girq26d.S ../src/MEC14xx/startup/MPLAB/default-on-bootstrap.c ../src/MEC14xx/startup/MPLAB/on_reset.c ../src/MEC14xx/startup/MPLAB/crt0.S ../src/MEC14xx/startup/MPLAB/crti.S ../src/MEC14xx/startup/MPLAB/crtn.S ../src/MEC14xx/mec14xx_bbled.c ../src/MEC14xx/mec14xx_gpio.c ../src/MEC14xx/mec14xx_jtvic.c ../src/MEC14xx/mec14xx_system.c ../src/MEC14xx/mec14xx_tfdp.c ../src/MEC14xx/mec14xx_timers.c ../src/main.c

# Object Files Quoted if spaced
OBJECTFILES_QUOTED_IF_SPACED=${OBJECTDIR}/_ext/1477011893/main_blinky.o ${OBJECTDIR}/_ext/1884096877/heap_2.o ${OBJECTDIR}/_ext/582319769/port.o ${OBJECTDIR}/_ext/582319769/port_asm.o ${OBJECTDIR}/_ext/449926602/event_groups.o ${OBJECTDIR}/_ext/449926602/list.o ${OBJECTDIR}/_ext/449926602/queue.o ${OBJECTDIR}/_ext/449926602/tasks.o ${OBJECTDIR}/_ext/449926602/timers.o ${OBJECTDIR}/_ext/1163846883/blocktim.o ${OBJECTDIR}/_ext/1163846883/countsem.o ${OBJECTDIR}/_ext/1163846883/dynamic.o ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o ${OBJECTDIR}/_ext/1163846883/GenQTest.o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ${OBJECTDIR}/_ext/1163846883/IntSemTest.o ${OBJECTDIR}/_ext/1163846883/recmutex.o ${OBJECTDIR}/_ext/1163846883/semtest.o ${OBJECTDIR}/_ext/1163846883/TaskNotify.o ${OBJECTDIR}/_ext/1163846883/TimerDemo.o ${OBJECTDIR}/_ext/950458649/IntQueueTimer.o ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o ${OBJECTDIR}/_ext/950458649/main_full.o ${OBJECTDIR}/_ext/950458649/timertest.o ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o ${OBJECTDIR}/_ext/1801383878/general_exception.o ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o ${OBJECTDIR}/_ext/1662639563/girq08.o ${OBJECTDIR}/_ext/1662639563/girq09.o ${OBJECTDIR}/_ext/1662639563/girq10.o ${OBJECTDIR}/_ext/1662639563/girq11.o ${OBJECTDIR}/_ext/1662639563/girq12.o ${OBJECTDIR}/_ext/1662639563/girq13.o ${OBJECTDIR}/_ext/1662639563/girq14.o ${OBJECTDIR}/_ext/1662639563/girq15.o ${OBJECTDIR}/_ext/1662639563/girq16.o ${OBJECTDIR}/_ext/1662639563/girq17.o ${OBJECTDIR}/_ext/1662639563/girq18.o ${OBJECTDIR}/_ext/1662639563/girq19.o ${OBJECTDIR}/_ext/1662639563/girq20.o ${OBJECTDIR}/_ext/1662639563/girq21.o ${OBJECTDIR}/_ext/1662639563/girq22.o ${OBJECTDIR}/_ext/1662639563/girq23.o ${OBJECTDIR}/_ext/1662639563/girq24.o ${OBJECTDIR}/_ext/1662639563/girq25.o ${OBJECTDIR}/_ext/1662639563/girq26.o ${OBJECTDIR}/_ext/1662639563/girqs.o ${OBJECTDIR}/_ext/1662639563/girq08d.o ${OBJECTDIR}/_ext/1662639563/girq09d.o ${OBJECTDIR}/_ext/1662639563/girq10d.o ${OBJECTDIR}/_ext/1662639563/girq11d.o ${OBJECTDIR}/_ext/1662639563/girq12d.o ${OBJECTDIR}/_ext/1662639563/girq13d.o ${OBJECTDIR}/_ext/1662639563/girq14d.o ${OBJECTDIR}/_ext/1662639563/girq15d.o ${OBJECTDIR}/_ext/1662639563/girq16d.o ${OBJECTDIR}/_ext/1662639563/girq17d.o ${OBJECTDIR}/_ext/1662639563/girq18d.o ${OBJECTDIR}/_ext/1662639563/girq19d.o ${OBJECTDIR}/_ext/1662639563/girq20d.o ${OBJECTDIR}/_ext/1662639563/girq21d.o ${OBJECTDIR}/_ext/1662639563/girq22d.o ${OBJECTDIR}/_ext/1662639563/girq23d.o ${OBJECTDIR}/_ext/1662639563/girq24d.o ${OBJECTDIR}/_ext/1662639563/girq25d.o ${OBJECTDIR}/_ext/1662639563/girq26d.o ${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o ${OBJECTDIR}/_ext/1068550557/on_reset.o ${OBJECTDIR}/_ext/1068550557/crt0.o ${OBJECTDIR}/_ext/1068550557/crti.o ${OBJECTDIR}/_ext/1068550557/crtn.o ${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o ${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o ${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o ${OBJECTDIR}/_ext/1376193940/mec14xx_system.o ${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o ${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o ${OBJECTDIR}/_ext/1360937237/main.o
POSSIBLE_DEPFILES=${OBJECTDIR}/_ext/1477011893/main_blinky.o.d ${OBJECTDIR}/_ext/1884096877/heap_2.o.d ${OBJECTDIR}/_ext/582319769/port.o.d ${OBJECTDIR}/_ext/582319769/port_asm.o.d ${OBJECTDIR}/_ext/449926602/event_groups.o.d ${OBJECTDIR}/_ext/449926602/list.o.d ${OBJECTDIR}/_ext/449926602/queue.o.d ${OBJECTDIR}/_ext/449926602/tasks.o.d ${OBJECTDIR}/_ext/449926602/timers.o.d ${OBJECTDIR}/_ext/1163846883/blocktim.o.d ${OBJECTDIR}/_ext/1163846883/countsem.o.d ${OBJECTDIR}/_ext/1163846883/dynamic.o.d ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d ${OBJECTDIR}/_ext/1163846883/GenQTest.o.d ${OBJECTDIR}/_ext/1163846883/IntQueue.o.d ${OBJECTDIR}/_ext/1163846883/IntSemTest.o.d ${OBJECTDIR}/_ext/1163846883/recmutex.o.d ${OBJECTDIR}/_ext/1163846883/semtest.o.d ${OBJECTDIR}/_ext/1163846883/TaskNotify.o.d ${OBJECTDIR}/_ext/1163846883/TimerDemo.o.d ${OBJECTDIR}/_ext/950458649/IntQueueTimer.o.d ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.d ${OBJECTDIR}/_ext/950458649/main_full.o.d ${OBJECTDIR}/_ext/950458649/timertest.o.d ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.d ${OBJECTDIR}/_ext/1801383878/general_exception.o.d ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.d ${OBJECTDIR}/_ext/1662639563/girq08.o.d ${OBJECTDIR}/_ext/1662639563/girq09.o.d ${OBJECTDIR}/_ext/1662639563/girq10.o.d ${OBJECTDIR}/_ext/1662639563/girq11.o.d ${OBJECTDIR}/_ext/1662639563/girq12.o.d ${OBJECTDIR}/_ext/1662639563/girq13.o.d ${OBJECTDIR}/_ext/1662639563/girq14.o.d ${OBJECTDIR}/_ext/1662639563/girq15.o.d ${OBJECTDIR}/_ext/1662639563/girq16.o.d ${OBJECTDIR}/_ext/1662639563/girq17.o.d ${OBJECTDIR}/_ext/1662639563/girq18.o.d ${OBJECTDIR}/_ext/1662639563/girq19.o.d ${OBJECTDIR}/_ext/1662639563/girq20.o.d ${OBJECTDIR}/_ext/1662639563/girq21.o.d ${OBJECTDIR}/_ext/1662639563/girq22.o.d ${OBJECTDIR}/_ext/1662639563/girq23.o.d ${OBJECTDIR}/_ext/1662639563/girq24.o.d ${OBJECTDIR}/_ext/1662639563/girq25.o.d ${OBJECTDIR}/_ext/1662639563/girq26.o.d ${OBJECTDIR}/_ext/1662639563/girqs.o.d ${OBJECTDIR}/_ext/1662639563/girq08d.o.d ${OBJECTDIR}/_ext/1662639563/girq09d.o.d ${OBJECTDIR}/_ext/1662639563/girq10d.o.d ${OBJECTDIR}/_ext/1662639563/girq11d.o.d ${OBJECTDIR}/_ext/1662639563/girq12d.o.d ${OBJECTDIR}/_ext/1662639563/girq13d.o.d ${OBJECTDIR}/_ext/1662639563/girq14d.o.d ${OBJECTDIR}/_ext/1662639563/girq15d.o.d ${OBJECTDIR}/_ext/1662639563/girq16d.o.d ${OBJECTDIR}/_ext/1662639563/girq17d.o.d ${OBJECTDIR}/_ext/1662639563/girq18d.o.d ${OBJECTDIR}/_ext/1662639563/girq19d.o.d ${OBJECTDIR}/_ext/1662639563/girq20d.o.d ${OBJECTDIR}/_ext/1662639563/girq21d.o.d ${OBJECTDIR}/_ext/1662639563/girq22d.o.d ${OBJECTDIR}/_ext/1662639563/girq23d.o.d ${OBJECTDIR}/_ext/1662639563/girq24d.o.d ${OBJECTDIR}/_ext/1662639563/girq25d.o.d ${OBJECTDIR}/_ext/1662639563/girq26d.o.d ${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o.d ${OBJECTDIR}/_ext/1068550557/on_reset.o.d ${OBJECTDIR}/_ext/1068550557/crt0.o.d ${OBJECTDIR}/_ext/1068550557/crti.o.d ${OBJECTDIR}/_ext/1068550557/crtn.o.d ${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o.d ${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o.d ${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o.d ${OBJECTDIR}/_ext/1376193940/mec14xx_system.o.d ${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o.d ${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o.d ${OBJECTDIR}/_ext/1360937237/main.o.d

# Object Files
OBJECTFILES=${OBJECTDIR}/_ext/1477011893/main_blinky.o ${OBJECTDIR}/_ext/1884096877/heap_2.o ${OBJECTDIR}/_ext/582319769/port.o ${OBJECTDIR}/_ext/582319769/port_asm.o ${OBJECTDIR}/_ext/449926602/event_groups.o ${OBJECTDIR}/_ext/449926602/list.o ${OBJECTDIR}/_ext/449926602/queue.o ${OBJECTDIR}/_ext/449926602/tasks.o ${OBJECTDIR}/_ext/449926602/timers.o ${OBJECTDIR}/_ext/1163846883/blocktim.o ${OBJECTDIR}/_ext/1163846883/countsem.o ${OBJECTDIR}/_ext/1163846883/dynamic.o ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o ${OBJECTDIR}/_ext/1163846883/GenQTest.o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ${OBJECTDIR}/_ext/1163846883/IntSemTest.o ${OBJECTDIR}/_ext/1163846883/recmutex.o ${OBJECTDIR}/_ext/1163846883/semtest.o ${OBJECTDIR}/_ext/1163846883/TaskNotify.o ${OBJECTDIR}/_ext/1163846883/TimerDemo.o ${OBJECTDIR}/_ext/950458649/IntQueueTimer.o ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o ${OBJECTDIR}/_ext/950458649/main_full.o ${OBJECTDIR}/_ext/950458649/timertest.o ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o ${OBJECTDIR}/_ext/1801383878/general_exception.o ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o ${OBJECTDIR}/_ext/1662639563/girq08.o ${OBJECTDIR}/_ext/1662639563/girq09.o ${OBJECTDIR}/_ext/1662639563/girq10.o ${OBJECTDIR}/_ext/1662639563/girq11.o ${OBJECTDIR}/_ext/1662639563/girq12.o ${OBJECTDIR}/_ext/1662639563/girq13.o ${OBJECTDIR}/_ext/1662639563/girq14.o ${OBJECTDIR}/_ext/1662639563/girq15.o ${OBJECTDIR}/_ext/1662639563/girq16.o ${OBJECTDIR}/_ext/1662639563/girq17.o ${OBJECTDIR}/_ext/1662639563/girq18.o ${OBJECTDIR}/_ext/1662639563/girq19.o ${OBJECTDIR}/_ext/1662639563/girq20.o ${OBJECTDIR}/_ext/1662639563/girq21.o ${OBJECTDIR}/_ext/1662639563/girq22.o ${OBJECTDIR}/_ext/1662639563/girq23.o ${OBJECTDIR}/_ext/1662639563/girq24.o ${OBJECTDIR}/_ext/1662639563/girq25.o ${OBJECTDIR}/_ext/1662639563/girq26.o ${OBJECTDIR}/_ext/1662639563/girqs.o ${OBJECTDIR}/_ext/1662639563/girq08d.o ${OBJECTDIR}/_ext/1662639563/girq09d.o ${OBJECTDIR}/_ext/1662639563/girq10d.o ${OBJECTDIR}/_ext/1662639563/girq11d.o ${OBJECTDIR}/_ext/1662639563/girq12d.o ${OBJECTDIR}/_ext/1662639563/girq13d.o ${OBJECTDIR}/_ext/1662639563/girq14d.o ${OBJECTDIR}/_ext/1662639563/girq15d.o ${OBJECTDIR}/_ext/1662639563/girq16d.o ${OBJECTDIR}/_ext/1662639563/girq17d.o ${OBJECTDIR}/_ext/1662639563/girq18d.o ${OBJECTDIR}/_ext/1662639563/girq19d.o ${OBJECTDIR}/_ext/1662639563/girq20d.o ${OBJECTDIR}/_ext/1662639563/girq21d.o ${OBJECTDIR}/_ext/1662639563/girq22d.o ${OBJECTDIR}/_ext/1662639563/girq23d.o ${OBJECTDIR}/_ext/1662639563/girq24d.o ${OBJECTDIR}/_ext/1662639563/girq25d.o ${OBJECTDIR}/_ext/1662639563/girq26d.o ${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o ${OBJECTDIR}/_ext/1068550557/on_reset.o ${OBJECTDIR}/_ext/1068550557/crt0.o ${OBJECTDIR}/_ext/1068550557/crti.o ${OBJECTDIR}/_ext/1068550557/crtn.o ${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o ${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o ${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o ${OBJECTDIR}/_ext/1376193940/mec14xx_system.o ${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o ${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o ${OBJECTDIR}/_ext/1360937237/main.o

# Source Files
SOURCEFILES=../src/Blinky_Demo/main_blinky.c ../../../Source/portable/MemMang/heap_2.c ../../../Source/portable/MPLAB/PIC32MEC14xx/port.c ../../../Source/portable/MPLAB/PIC32MEC14xx/port_asm.S ../../../Source/event_groups.c ../../../Source/list.c ../../../Source/queue.c ../../../Source/tasks.c ../../../Source/timers.c ../../Common/Minimal/blocktim.c ../../Common/Minimal/countsem.c ../../Common/Minimal/dynamic.c ../../Common/Minimal/EventGroupsDemo.c ../../Common/Minimal/GenQTest.c ../../Common/Minimal/IntQueue.c ../../Common/Minimal/IntSemTest.c ../../Common/Minimal/recmutex.c ../../Common/Minimal/semtest.c ../../Common/Minimal/TaskNotify.c ../../Common/Minimal/TimerDemo.c ../src/Full_Demo/IntQueueTimer.c ../src/Full_Demo/IntQueueTimer_isr.S ../src/Full_Demo/main_full.c ../src/Full_Demo/timertest.c ../src/Full_Demo/RegisterTestTasks.S ../src/MEC14xx/exceptions/MPLAB/general_exception.c ../src/MEC14xx/exceptions/MPLAB/general_exception_ctx.S ../src/MEC14xx/interrupts/girq08.c ../src/MEC14xx/interrupts/girq09.c ../src/MEC14xx/interrupts/girq10.c ../src/MEC14xx/interrupts/girq11.c ../src/MEC14xx/interrupts/girq12.c ../src/MEC14xx/interrupts/girq13.c ../src/MEC14xx/interrupts/girq14.c ../src/MEC14xx/interrupts/girq15.c ../src/MEC14xx/interrupts/girq16.c ../src/MEC14xx/interrupts/girq17.c ../src/MEC14xx/interrupts/girq18.c ../src/MEC14xx/interrupts/girq19.c ../src/MEC14xx/interrupts/girq20.c ../src/MEC14xx/interrupts/girq21.c ../src/MEC14xx/interrupts/girq22.c ../src/MEC14xx/interrupts/girq23.c ../src/MEC14xx/interrupts/girq24.c ../src/MEC14xx/interrupts/girq25.c ../src/MEC14xx/interrupts/girq26.c ../src/MEC14xx/interrupts/girqs.c ../src/MEC14xx/interrupts/girq08d.S ../src/MEC14xx/interrupts/girq09d.S ../src/MEC14xx/interrupts/girq10d.S ../src/MEC14xx/interrupts/girq11d.S ../src/MEC14xx/interrupts/girq12d.S ../src/MEC14xx/interrupts/girq13d.S ../src/MEC14xx/interrupts/girq14d.S ../src/MEC14xx/interrupts/girq15d.S ../src/MEC14xx/interrupts/girq16d.S ../src/MEC14xx/interrupts/girq17d.S ../src/MEC14xx/interrupts/girq18d.S ../src/MEC14xx/interrupts/girq19d.S ../src/MEC14xx/interrupts/girq20d.S ../src/MEC14xx/interrupts/girq21d.S ../src/MEC14xx/interrupts/girq22d.S ../src/MEC14xx/interrupts/girq23d.S ../src/MEC14xx/interrupts/girq24d.S ../src/MEC14xx/interrupts/girq25d.S ../src/MEC14xx/interrupts/girq26d.S ../src/MEC14xx/startup/MPLAB/default-on-bootstrap.c ../src/MEC14xx/startup/MPLAB/on_reset.c ../src/MEC14xx/startup/MPLAB/crt0.S ../src/MEC14xx/startup/MPLAB/crti.S ../src/MEC14xx/startup/MPLAB/crtn.S ../src/MEC14xx/mec14xx_bbled.c ../src/MEC14xx/mec14xx_gpio.c ../src/MEC14xx/mec14xx_jtvic.c ../src/MEC14xx/mec14xx_system.c ../src/MEC14xx/mec14xx_tfdp.c ../src/MEC14xx/mec14xx_timers.c ../src/main.c


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
	${MAKE}  -f nbproject/Makefile-default.mk dist/${CND_CONF}/${IMAGE_TYPE}/PIC32MEC14xx_RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}

MP_PROCESSOR_OPTION=MEC1404
MP_LINKER_FILE_OPTION=,--script="..\linkfile\custom_pMEC1404.ld"
# ------------------------------------------------------------------------------------
# Rules for buildStep: assemble
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
else
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: assembleWithPreprocess
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
${OBJECTDIR}/_ext/582319769/port_asm.o: ../../../Source/portable/MPLAB/PIC32MEC14xx/port_asm.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/582319769" 
	@${RM} ${OBJECTDIR}/_ext/582319769/port_asm.o.d 
	@${RM} ${OBJECTDIR}/_ext/582319769/port_asm.o 
	@${RM} ${OBJECTDIR}/_ext/582319769/port_asm.o.ok ${OBJECTDIR}/_ext/582319769/port_asm.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/582319769/port_asm.o.d" "${OBJECTDIR}/_ext/582319769/port_asm.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/582319769/port_asm.o.d"  -o ${OBJECTDIR}/_ext/582319769/port_asm.o ../../../Source/portable/MPLAB/PIC32MEC14xx/port_asm.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/582319769/port_asm.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o: ../src/Full_Demo/IntQueueTimer_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/950458649" 
	@${RM} ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.d 
	@${RM} ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o 
	@${RM} ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.ok ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.d" "${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.d"  -o ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o ../src/Full_Demo/IntQueueTimer_isr.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o: ../src/Full_Demo/RegisterTestTasks.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/950458649" 
	@${RM} ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.d 
	@${RM} ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o 
	@${RM} ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.ok ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.d" "${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.d"  -o ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o ../src/Full_Demo/RegisterTestTasks.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o: ../src/MEC14xx/exceptions/MPLAB/general_exception_ctx.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1801383878" 
	@${RM} ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.d 
	@${RM} ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o 
	@${RM} ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.ok ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.d" "${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.d"  -o ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o ../src/MEC14xx/exceptions/MPLAB/general_exception_ctx.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq08d.o: ../src/MEC14xx/interrupts/girq08d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq08d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq08d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq08d.o.ok ${OBJECTDIR}/_ext/1662639563/girq08d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq08d.o.d" "${OBJECTDIR}/_ext/1662639563/girq08d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq08d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq08d.o ../src/MEC14xx/interrupts/girq08d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq08d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq09d.o: ../src/MEC14xx/interrupts/girq09d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq09d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq09d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq09d.o.ok ${OBJECTDIR}/_ext/1662639563/girq09d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq09d.o.d" "${OBJECTDIR}/_ext/1662639563/girq09d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq09d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq09d.o ../src/MEC14xx/interrupts/girq09d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq09d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq10d.o: ../src/MEC14xx/interrupts/girq10d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq10d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq10d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq10d.o.ok ${OBJECTDIR}/_ext/1662639563/girq10d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq10d.o.d" "${OBJECTDIR}/_ext/1662639563/girq10d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq10d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq10d.o ../src/MEC14xx/interrupts/girq10d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq10d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq11d.o: ../src/MEC14xx/interrupts/girq11d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq11d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq11d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq11d.o.ok ${OBJECTDIR}/_ext/1662639563/girq11d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq11d.o.d" "${OBJECTDIR}/_ext/1662639563/girq11d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq11d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq11d.o ../src/MEC14xx/interrupts/girq11d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq11d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq12d.o: ../src/MEC14xx/interrupts/girq12d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq12d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq12d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq12d.o.ok ${OBJECTDIR}/_ext/1662639563/girq12d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq12d.o.d" "${OBJECTDIR}/_ext/1662639563/girq12d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq12d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq12d.o ../src/MEC14xx/interrupts/girq12d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq12d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq13d.o: ../src/MEC14xx/interrupts/girq13d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq13d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq13d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq13d.o.ok ${OBJECTDIR}/_ext/1662639563/girq13d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq13d.o.d" "${OBJECTDIR}/_ext/1662639563/girq13d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq13d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq13d.o ../src/MEC14xx/interrupts/girq13d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq13d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq14d.o: ../src/MEC14xx/interrupts/girq14d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq14d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq14d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq14d.o.ok ${OBJECTDIR}/_ext/1662639563/girq14d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq14d.o.d" "${OBJECTDIR}/_ext/1662639563/girq14d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq14d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq14d.o ../src/MEC14xx/interrupts/girq14d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq14d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq15d.o: ../src/MEC14xx/interrupts/girq15d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq15d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq15d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq15d.o.ok ${OBJECTDIR}/_ext/1662639563/girq15d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq15d.o.d" "${OBJECTDIR}/_ext/1662639563/girq15d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq15d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq15d.o ../src/MEC14xx/interrupts/girq15d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq15d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq16d.o: ../src/MEC14xx/interrupts/girq16d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq16d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq16d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq16d.o.ok ${OBJECTDIR}/_ext/1662639563/girq16d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq16d.o.d" "${OBJECTDIR}/_ext/1662639563/girq16d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq16d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq16d.o ../src/MEC14xx/interrupts/girq16d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq16d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq17d.o: ../src/MEC14xx/interrupts/girq17d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq17d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq17d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq17d.o.ok ${OBJECTDIR}/_ext/1662639563/girq17d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq17d.o.d" "${OBJECTDIR}/_ext/1662639563/girq17d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq17d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq17d.o ../src/MEC14xx/interrupts/girq17d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq17d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq18d.o: ../src/MEC14xx/interrupts/girq18d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq18d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq18d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq18d.o.ok ${OBJECTDIR}/_ext/1662639563/girq18d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq18d.o.d" "${OBJECTDIR}/_ext/1662639563/girq18d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq18d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq18d.o ../src/MEC14xx/interrupts/girq18d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq18d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq19d.o: ../src/MEC14xx/interrupts/girq19d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq19d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq19d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq19d.o.ok ${OBJECTDIR}/_ext/1662639563/girq19d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq19d.o.d" "${OBJECTDIR}/_ext/1662639563/girq19d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq19d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq19d.o ../src/MEC14xx/interrupts/girq19d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq19d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq20d.o: ../src/MEC14xx/interrupts/girq20d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq20d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq20d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq20d.o.ok ${OBJECTDIR}/_ext/1662639563/girq20d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq20d.o.d" "${OBJECTDIR}/_ext/1662639563/girq20d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq20d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq20d.o ../src/MEC14xx/interrupts/girq20d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq20d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq21d.o: ../src/MEC14xx/interrupts/girq21d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq21d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq21d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq21d.o.ok ${OBJECTDIR}/_ext/1662639563/girq21d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq21d.o.d" "${OBJECTDIR}/_ext/1662639563/girq21d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq21d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq21d.o ../src/MEC14xx/interrupts/girq21d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq21d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq22d.o: ../src/MEC14xx/interrupts/girq22d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq22d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq22d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq22d.o.ok ${OBJECTDIR}/_ext/1662639563/girq22d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq22d.o.d" "${OBJECTDIR}/_ext/1662639563/girq22d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq22d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq22d.o ../src/MEC14xx/interrupts/girq22d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq22d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq23d.o: ../src/MEC14xx/interrupts/girq23d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq23d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq23d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq23d.o.ok ${OBJECTDIR}/_ext/1662639563/girq23d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq23d.o.d" "${OBJECTDIR}/_ext/1662639563/girq23d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq23d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq23d.o ../src/MEC14xx/interrupts/girq23d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq23d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq24d.o: ../src/MEC14xx/interrupts/girq24d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq24d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq24d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq24d.o.ok ${OBJECTDIR}/_ext/1662639563/girq24d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq24d.o.d" "${OBJECTDIR}/_ext/1662639563/girq24d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq24d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq24d.o ../src/MEC14xx/interrupts/girq24d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq24d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq25d.o: ../src/MEC14xx/interrupts/girq25d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq25d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq25d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq25d.o.ok ${OBJECTDIR}/_ext/1662639563/girq25d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq25d.o.d" "${OBJECTDIR}/_ext/1662639563/girq25d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq25d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq25d.o ../src/MEC14xx/interrupts/girq25d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq25d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1662639563/girq26d.o: ../src/MEC14xx/interrupts/girq26d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq26d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq26d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq26d.o.ok ${OBJECTDIR}/_ext/1662639563/girq26d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq26d.o.d" "${OBJECTDIR}/_ext/1662639563/girq26d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq26d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq26d.o ../src/MEC14xx/interrupts/girq26d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq26d.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1068550557/crt0.o: ../src/MEC14xx/startup/MPLAB/crt0.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1068550557" 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crt0.o.d 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crt0.o 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crt0.o.ok ${OBJECTDIR}/_ext/1068550557/crt0.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1068550557/crt0.o.d" "${OBJECTDIR}/_ext/1068550557/crt0.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1068550557/crt0.o.d"  -o ${OBJECTDIR}/_ext/1068550557/crt0.o ../src/MEC14xx/startup/MPLAB/crt0.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1068550557/crt0.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1068550557/crti.o: ../src/MEC14xx/startup/MPLAB/crti.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1068550557" 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crti.o.d 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crti.o 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crti.o.ok ${OBJECTDIR}/_ext/1068550557/crti.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1068550557/crti.o.d" "${OBJECTDIR}/_ext/1068550557/crti.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1068550557/crti.o.d"  -o ${OBJECTDIR}/_ext/1068550557/crti.o ../src/MEC14xx/startup/MPLAB/crti.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1068550557/crti.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
${OBJECTDIR}/_ext/1068550557/crtn.o: ../src/MEC14xx/startup/MPLAB/crtn.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1068550557" 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crtn.o.d 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crtn.o 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crtn.o.ok ${OBJECTDIR}/_ext/1068550557/crtn.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1068550557/crtn.o.d" "${OBJECTDIR}/_ext/1068550557/crtn.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1068550557/crtn.o.d"  -o ${OBJECTDIR}/_ext/1068550557/crtn.o ../src/MEC14xx/startup/MPLAB/crtn.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1068550557/crtn.o.asm.d",--defsym=__ICD2RAM=1,--defsym=__MPLAB_DEBUG=1,--gdwarf-2,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1
	
else
${OBJECTDIR}/_ext/582319769/port_asm.o: ../../../Source/portable/MPLAB/PIC32MEC14xx/port_asm.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/582319769" 
	@${RM} ${OBJECTDIR}/_ext/582319769/port_asm.o.d 
	@${RM} ${OBJECTDIR}/_ext/582319769/port_asm.o 
	@${RM} ${OBJECTDIR}/_ext/582319769/port_asm.o.ok ${OBJECTDIR}/_ext/582319769/port_asm.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/582319769/port_asm.o.d" "${OBJECTDIR}/_ext/582319769/port_asm.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/582319769/port_asm.o.d"  -o ${OBJECTDIR}/_ext/582319769/port_asm.o ../../../Source/portable/MPLAB/PIC32MEC14xx/port_asm.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/582319769/port_asm.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o: ../src/Full_Demo/IntQueueTimer_isr.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/950458649" 
	@${RM} ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.d 
	@${RM} ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o 
	@${RM} ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.ok ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.d" "${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.d"  -o ${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o ../src/Full_Demo/IntQueueTimer_isr.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/950458649/IntQueueTimer_isr.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o: ../src/Full_Demo/RegisterTestTasks.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/950458649" 
	@${RM} ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.d 
	@${RM} ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o 
	@${RM} ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.ok ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.d" "${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.d"  -o ${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o ../src/Full_Demo/RegisterTestTasks.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/950458649/RegisterTestTasks.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o: ../src/MEC14xx/exceptions/MPLAB/general_exception_ctx.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1801383878" 
	@${RM} ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.d 
	@${RM} ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o 
	@${RM} ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.ok ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.d" "${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.d"  -o ${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o ../src/MEC14xx/exceptions/MPLAB/general_exception_ctx.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1801383878/general_exception_ctx.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq08d.o: ../src/MEC14xx/interrupts/girq08d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq08d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq08d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq08d.o.ok ${OBJECTDIR}/_ext/1662639563/girq08d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq08d.o.d" "${OBJECTDIR}/_ext/1662639563/girq08d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq08d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq08d.o ../src/MEC14xx/interrupts/girq08d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq08d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq09d.o: ../src/MEC14xx/interrupts/girq09d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq09d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq09d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq09d.o.ok ${OBJECTDIR}/_ext/1662639563/girq09d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq09d.o.d" "${OBJECTDIR}/_ext/1662639563/girq09d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq09d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq09d.o ../src/MEC14xx/interrupts/girq09d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq09d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq10d.o: ../src/MEC14xx/interrupts/girq10d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq10d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq10d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq10d.o.ok ${OBJECTDIR}/_ext/1662639563/girq10d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq10d.o.d" "${OBJECTDIR}/_ext/1662639563/girq10d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq10d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq10d.o ../src/MEC14xx/interrupts/girq10d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq10d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq11d.o: ../src/MEC14xx/interrupts/girq11d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq11d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq11d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq11d.o.ok ${OBJECTDIR}/_ext/1662639563/girq11d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq11d.o.d" "${OBJECTDIR}/_ext/1662639563/girq11d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq11d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq11d.o ../src/MEC14xx/interrupts/girq11d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq11d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq12d.o: ../src/MEC14xx/interrupts/girq12d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq12d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq12d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq12d.o.ok ${OBJECTDIR}/_ext/1662639563/girq12d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq12d.o.d" "${OBJECTDIR}/_ext/1662639563/girq12d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq12d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq12d.o ../src/MEC14xx/interrupts/girq12d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq12d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq13d.o: ../src/MEC14xx/interrupts/girq13d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq13d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq13d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq13d.o.ok ${OBJECTDIR}/_ext/1662639563/girq13d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq13d.o.d" "${OBJECTDIR}/_ext/1662639563/girq13d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq13d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq13d.o ../src/MEC14xx/interrupts/girq13d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq13d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq14d.o: ../src/MEC14xx/interrupts/girq14d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq14d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq14d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq14d.o.ok ${OBJECTDIR}/_ext/1662639563/girq14d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq14d.o.d" "${OBJECTDIR}/_ext/1662639563/girq14d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq14d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq14d.o ../src/MEC14xx/interrupts/girq14d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq14d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq15d.o: ../src/MEC14xx/interrupts/girq15d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq15d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq15d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq15d.o.ok ${OBJECTDIR}/_ext/1662639563/girq15d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq15d.o.d" "${OBJECTDIR}/_ext/1662639563/girq15d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq15d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq15d.o ../src/MEC14xx/interrupts/girq15d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq15d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq16d.o: ../src/MEC14xx/interrupts/girq16d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq16d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq16d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq16d.o.ok ${OBJECTDIR}/_ext/1662639563/girq16d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq16d.o.d" "${OBJECTDIR}/_ext/1662639563/girq16d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq16d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq16d.o ../src/MEC14xx/interrupts/girq16d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq16d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq17d.o: ../src/MEC14xx/interrupts/girq17d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq17d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq17d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq17d.o.ok ${OBJECTDIR}/_ext/1662639563/girq17d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq17d.o.d" "${OBJECTDIR}/_ext/1662639563/girq17d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq17d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq17d.o ../src/MEC14xx/interrupts/girq17d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq17d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq18d.o: ../src/MEC14xx/interrupts/girq18d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq18d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq18d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq18d.o.ok ${OBJECTDIR}/_ext/1662639563/girq18d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq18d.o.d" "${OBJECTDIR}/_ext/1662639563/girq18d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq18d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq18d.o ../src/MEC14xx/interrupts/girq18d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq18d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq19d.o: ../src/MEC14xx/interrupts/girq19d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq19d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq19d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq19d.o.ok ${OBJECTDIR}/_ext/1662639563/girq19d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq19d.o.d" "${OBJECTDIR}/_ext/1662639563/girq19d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq19d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq19d.o ../src/MEC14xx/interrupts/girq19d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq19d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq20d.o: ../src/MEC14xx/interrupts/girq20d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq20d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq20d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq20d.o.ok ${OBJECTDIR}/_ext/1662639563/girq20d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq20d.o.d" "${OBJECTDIR}/_ext/1662639563/girq20d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq20d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq20d.o ../src/MEC14xx/interrupts/girq20d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq20d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq21d.o: ../src/MEC14xx/interrupts/girq21d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq21d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq21d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq21d.o.ok ${OBJECTDIR}/_ext/1662639563/girq21d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq21d.o.d" "${OBJECTDIR}/_ext/1662639563/girq21d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq21d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq21d.o ../src/MEC14xx/interrupts/girq21d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq21d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq22d.o: ../src/MEC14xx/interrupts/girq22d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq22d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq22d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq22d.o.ok ${OBJECTDIR}/_ext/1662639563/girq22d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq22d.o.d" "${OBJECTDIR}/_ext/1662639563/girq22d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq22d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq22d.o ../src/MEC14xx/interrupts/girq22d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq22d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq23d.o: ../src/MEC14xx/interrupts/girq23d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq23d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq23d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq23d.o.ok ${OBJECTDIR}/_ext/1662639563/girq23d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq23d.o.d" "${OBJECTDIR}/_ext/1662639563/girq23d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq23d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq23d.o ../src/MEC14xx/interrupts/girq23d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq23d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq24d.o: ../src/MEC14xx/interrupts/girq24d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq24d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq24d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq24d.o.ok ${OBJECTDIR}/_ext/1662639563/girq24d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq24d.o.d" "${OBJECTDIR}/_ext/1662639563/girq24d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq24d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq24d.o ../src/MEC14xx/interrupts/girq24d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq24d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq25d.o: ../src/MEC14xx/interrupts/girq25d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq25d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq25d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq25d.o.ok ${OBJECTDIR}/_ext/1662639563/girq25d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq25d.o.d" "${OBJECTDIR}/_ext/1662639563/girq25d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq25d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq25d.o ../src/MEC14xx/interrupts/girq25d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq25d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1662639563/girq26d.o: ../src/MEC14xx/interrupts/girq26d.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq26d.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq26d.o 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq26d.o.ok ${OBJECTDIR}/_ext/1662639563/girq26d.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq26d.o.d" "${OBJECTDIR}/_ext/1662639563/girq26d.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq26d.o.d"  -o ${OBJECTDIR}/_ext/1662639563/girq26d.o ../src/MEC14xx/interrupts/girq26d.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1662639563/girq26d.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1068550557/crt0.o: ../src/MEC14xx/startup/MPLAB/crt0.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1068550557" 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crt0.o.d 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crt0.o 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crt0.o.ok ${OBJECTDIR}/_ext/1068550557/crt0.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1068550557/crt0.o.d" "${OBJECTDIR}/_ext/1068550557/crt0.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1068550557/crt0.o.d"  -o ${OBJECTDIR}/_ext/1068550557/crt0.o ../src/MEC14xx/startup/MPLAB/crt0.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1068550557/crt0.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1068550557/crti.o: ../src/MEC14xx/startup/MPLAB/crti.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1068550557" 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crti.o.d 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crti.o 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crti.o.ok ${OBJECTDIR}/_ext/1068550557/crti.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1068550557/crti.o.d" "${OBJECTDIR}/_ext/1068550557/crti.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1068550557/crti.o.d"  -o ${OBJECTDIR}/_ext/1068550557/crti.o ../src/MEC14xx/startup/MPLAB/crti.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1068550557/crti.o.asm.d",--gdwarf-2
	
${OBJECTDIR}/_ext/1068550557/crtn.o: ../src/MEC14xx/startup/MPLAB/crtn.S  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1068550557" 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crtn.o.d 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crtn.o 
	@${RM} ${OBJECTDIR}/_ext/1068550557/crtn.o.ok ${OBJECTDIR}/_ext/1068550557/crtn.o.err 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1068550557/crtn.o.d" "${OBJECTDIR}/_ext/1068550557/crtn.o.asm.d" -t $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC} $(MP_EXTRA_AS_PRE)  -c -mprocessor=$(MP_PROCESSOR_OPTION) -I"../src" -I"../src/include" -I"../src/MEC14xx" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -MMD -MF "${OBJECTDIR}/_ext/1068550557/crtn.o.d"  -o ${OBJECTDIR}/_ext/1068550557/crtn.o ../src/MEC14xx/startup/MPLAB/crtn.S  -Wa,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_AS_POST),-MD="${OBJECTDIR}/_ext/1068550557/crtn.o.asm.d",--gdwarf-2
	
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: compile
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
${OBJECTDIR}/_ext/1477011893/main_blinky.o: ../src/Blinky_Demo/main_blinky.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1477011893" 
	@${RM} ${OBJECTDIR}/_ext/1477011893/main_blinky.o.d 
	@${RM} ${OBJECTDIR}/_ext/1477011893/main_blinky.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1477011893/main_blinky.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1477011893/main_blinky.o.d" -o ${OBJECTDIR}/_ext/1477011893/main_blinky.o ../src/Blinky_Demo/main_blinky.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1884096877/heap_2.o: ../../../Source/portable/MemMang/heap_2.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1884096877" 
	@${RM} ${OBJECTDIR}/_ext/1884096877/heap_2.o.d 
	@${RM} ${OBJECTDIR}/_ext/1884096877/heap_2.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1884096877/heap_2.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1884096877/heap_2.o.d" -o ${OBJECTDIR}/_ext/1884096877/heap_2.o ../../../Source/portable/MemMang/heap_2.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/582319769/port.o: ../../../Source/portable/MPLAB/PIC32MEC14xx/port.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/582319769" 
	@${RM} ${OBJECTDIR}/_ext/582319769/port.o.d 
	@${RM} ${OBJECTDIR}/_ext/582319769/port.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/582319769/port.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/582319769/port.o.d" -o ${OBJECTDIR}/_ext/582319769/port.o ../../../Source/portable/MPLAB/PIC32MEC14xx/port.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/449926602/event_groups.o: ../../../Source/event_groups.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602" 
	@${RM} ${OBJECTDIR}/_ext/449926602/event_groups.o.d 
	@${RM} ${OBJECTDIR}/_ext/449926602/event_groups.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/event_groups.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/449926602/event_groups.o.d" -o ${OBJECTDIR}/_ext/449926602/event_groups.o ../../../Source/event_groups.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/449926602/list.o: ../../../Source/list.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602" 
	@${RM} ${OBJECTDIR}/_ext/449926602/list.o.d 
	@${RM} ${OBJECTDIR}/_ext/449926602/list.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/list.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/449926602/list.o.d" -o ${OBJECTDIR}/_ext/449926602/list.o ../../../Source/list.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/449926602/queue.o: ../../../Source/queue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602" 
	@${RM} ${OBJECTDIR}/_ext/449926602/queue.o.d 
	@${RM} ${OBJECTDIR}/_ext/449926602/queue.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/queue.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/449926602/queue.o.d" -o ${OBJECTDIR}/_ext/449926602/queue.o ../../../Source/queue.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/449926602/tasks.o: ../../../Source/tasks.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602" 
	@${RM} ${OBJECTDIR}/_ext/449926602/tasks.o.d 
	@${RM} ${OBJECTDIR}/_ext/449926602/tasks.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/tasks.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/449926602/tasks.o.d" -o ${OBJECTDIR}/_ext/449926602/tasks.o ../../../Source/tasks.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/449926602/timers.o: ../../../Source/timers.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602" 
	@${RM} ${OBJECTDIR}/_ext/449926602/timers.o.d 
	@${RM} ${OBJECTDIR}/_ext/449926602/timers.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/timers.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/449926602/timers.o.d" -o ${OBJECTDIR}/_ext/449926602/timers.o ../../../Source/timers.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/blocktim.o: ../../Common/Minimal/blocktim.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/blocktim.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/blocktim.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" -o ${OBJECTDIR}/_ext/1163846883/blocktim.o ../../Common/Minimal/blocktim.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/countsem.o: ../../Common/Minimal/countsem.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/countsem.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/countsem.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/countsem.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/countsem.o.d" -o ${OBJECTDIR}/_ext/1163846883/countsem.o ../../Common/Minimal/countsem.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/dynamic.o: ../../Common/Minimal/dynamic.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/dynamic.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/dynamic.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/dynamic.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/dynamic.o.d" -o ${OBJECTDIR}/_ext/1163846883/dynamic.o ../../Common/Minimal/dynamic.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o: ../../Common/Minimal/EventGroupsDemo.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d" -o ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o ../../Common/Minimal/EventGroupsDemo.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/GenQTest.o: ../../Common/Minimal/GenQTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/GenQTest.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/GenQTest.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" -o ${OBJECTDIR}/_ext/1163846883/GenQTest.o ../../Common/Minimal/GenQTest.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/IntQueue.o: ../../Common/Minimal/IntQueue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntQueue.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntQueue.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" -o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ../../Common/Minimal/IntQueue.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/IntSemTest.o: ../../Common/Minimal/IntSemTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntSemTest.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntSemTest.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/IntSemTest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/IntSemTest.o.d" -o ${OBJECTDIR}/_ext/1163846883/IntSemTest.o ../../Common/Minimal/IntSemTest.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/recmutex.o: ../../Common/Minimal/recmutex.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/recmutex.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/recmutex.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/recmutex.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/recmutex.o.d" -o ${OBJECTDIR}/_ext/1163846883/recmutex.o ../../Common/Minimal/recmutex.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/semtest.o: ../../Common/Minimal/semtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/semtest.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/semtest.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/semtest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/semtest.o.d" -o ${OBJECTDIR}/_ext/1163846883/semtest.o ../../Common/Minimal/semtest.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/TaskNotify.o: ../../Common/Minimal/TaskNotify.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/TaskNotify.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/TaskNotify.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/TaskNotify.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/TaskNotify.o.d" -o ${OBJECTDIR}/_ext/1163846883/TaskNotify.o ../../Common/Minimal/TaskNotify.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/TimerDemo.o: ../../Common/Minimal/TimerDemo.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/TimerDemo.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/TimerDemo.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/TimerDemo.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/TimerDemo.o.d" -o ${OBJECTDIR}/_ext/1163846883/TimerDemo.o ../../Common/Minimal/TimerDemo.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/950458649/IntQueueTimer.o: ../src/Full_Demo/IntQueueTimer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/950458649" 
	@${RM} ${OBJECTDIR}/_ext/950458649/IntQueueTimer.o.d 
	@${RM} ${OBJECTDIR}/_ext/950458649/IntQueueTimer.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/950458649/IntQueueTimer.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/950458649/IntQueueTimer.o.d" -o ${OBJECTDIR}/_ext/950458649/IntQueueTimer.o ../src/Full_Demo/IntQueueTimer.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/950458649/main_full.o: ../src/Full_Demo/main_full.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/950458649" 
	@${RM} ${OBJECTDIR}/_ext/950458649/main_full.o.d 
	@${RM} ${OBJECTDIR}/_ext/950458649/main_full.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/950458649/main_full.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/950458649/main_full.o.d" -o ${OBJECTDIR}/_ext/950458649/main_full.o ../src/Full_Demo/main_full.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/950458649/timertest.o: ../src/Full_Demo/timertest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/950458649" 
	@${RM} ${OBJECTDIR}/_ext/950458649/timertest.o.d 
	@${RM} ${OBJECTDIR}/_ext/950458649/timertest.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/950458649/timertest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/950458649/timertest.o.d" -o ${OBJECTDIR}/_ext/950458649/timertest.o ../src/Full_Demo/timertest.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1801383878/general_exception.o: ../src/MEC14xx/exceptions/MPLAB/general_exception.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1801383878" 
	@${RM} ${OBJECTDIR}/_ext/1801383878/general_exception.o.d 
	@${RM} ${OBJECTDIR}/_ext/1801383878/general_exception.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1801383878/general_exception.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1801383878/general_exception.o.d" -o ${OBJECTDIR}/_ext/1801383878/general_exception.o ../src/MEC14xx/exceptions/MPLAB/general_exception.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq08.o: ../src/MEC14xx/interrupts/girq08.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq08.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq08.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq08.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq08.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq08.o ../src/MEC14xx/interrupts/girq08.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq09.o: ../src/MEC14xx/interrupts/girq09.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq09.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq09.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq09.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq09.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq09.o ../src/MEC14xx/interrupts/girq09.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq10.o: ../src/MEC14xx/interrupts/girq10.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq10.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq10.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq10.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq10.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq10.o ../src/MEC14xx/interrupts/girq10.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq11.o: ../src/MEC14xx/interrupts/girq11.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq11.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq11.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq11.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq11.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq11.o ../src/MEC14xx/interrupts/girq11.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq12.o: ../src/MEC14xx/interrupts/girq12.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq12.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq12.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq12.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq12.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq12.o ../src/MEC14xx/interrupts/girq12.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq13.o: ../src/MEC14xx/interrupts/girq13.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq13.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq13.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq13.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq13.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq13.o ../src/MEC14xx/interrupts/girq13.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq14.o: ../src/MEC14xx/interrupts/girq14.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq14.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq14.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq14.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq14.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq14.o ../src/MEC14xx/interrupts/girq14.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq15.o: ../src/MEC14xx/interrupts/girq15.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq15.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq15.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq15.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq15.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq15.o ../src/MEC14xx/interrupts/girq15.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq16.o: ../src/MEC14xx/interrupts/girq16.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq16.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq16.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq16.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq16.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq16.o ../src/MEC14xx/interrupts/girq16.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq17.o: ../src/MEC14xx/interrupts/girq17.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq17.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq17.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq17.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq17.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq17.o ../src/MEC14xx/interrupts/girq17.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq18.o: ../src/MEC14xx/interrupts/girq18.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq18.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq18.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq18.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq18.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq18.o ../src/MEC14xx/interrupts/girq18.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq19.o: ../src/MEC14xx/interrupts/girq19.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq19.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq19.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq19.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq19.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq19.o ../src/MEC14xx/interrupts/girq19.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq20.o: ../src/MEC14xx/interrupts/girq20.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq20.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq20.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq20.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq20.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq20.o ../src/MEC14xx/interrupts/girq20.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq21.o: ../src/MEC14xx/interrupts/girq21.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq21.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq21.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq21.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq21.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq21.o ../src/MEC14xx/interrupts/girq21.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq22.o: ../src/MEC14xx/interrupts/girq22.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq22.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq22.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq22.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq22.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq22.o ../src/MEC14xx/interrupts/girq22.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq23.o: ../src/MEC14xx/interrupts/girq23.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq23.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq23.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq23.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq23.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq23.o ../src/MEC14xx/interrupts/girq23.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq24.o: ../src/MEC14xx/interrupts/girq24.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq24.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq24.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq24.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq24.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq24.o ../src/MEC14xx/interrupts/girq24.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq25.o: ../src/MEC14xx/interrupts/girq25.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq25.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq25.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq25.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq25.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq25.o ../src/MEC14xx/interrupts/girq25.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq26.o: ../src/MEC14xx/interrupts/girq26.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq26.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq26.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq26.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq26.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq26.o ../src/MEC14xx/interrupts/girq26.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girqs.o: ../src/MEC14xx/interrupts/girqs.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girqs.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girqs.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girqs.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girqs.o.d" -o ${OBJECTDIR}/_ext/1662639563/girqs.o ../src/MEC14xx/interrupts/girqs.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o: ../src/MEC14xx/startup/MPLAB/default-on-bootstrap.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1068550557" 
	@${RM} ${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o.d 
	@${RM} ${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o.d" -o ${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o ../src/MEC14xx/startup/MPLAB/default-on-bootstrap.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1068550557/on_reset.o: ../src/MEC14xx/startup/MPLAB/on_reset.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1068550557" 
	@${RM} ${OBJECTDIR}/_ext/1068550557/on_reset.o.d 
	@${RM} ${OBJECTDIR}/_ext/1068550557/on_reset.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1068550557/on_reset.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1068550557/on_reset.o.d" -o ${OBJECTDIR}/_ext/1068550557/on_reset.o ../src/MEC14xx/startup/MPLAB/on_reset.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o: ../src/MEC14xx/mec14xx_bbled.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o ../src/MEC14xx/mec14xx_bbled.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o: ../src/MEC14xx/mec14xx_gpio.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o ../src/MEC14xx/mec14xx_gpio.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o: ../src/MEC14xx/mec14xx_jtvic.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o ../src/MEC14xx/mec14xx_jtvic.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_system.o: ../src/MEC14xx/mec14xx_system.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_system.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_system.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_system.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_system.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_system.o ../src/MEC14xx/mec14xx_system.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o: ../src/MEC14xx/mec14xx_tfdp.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o ../src/MEC14xx/mec14xx_tfdp.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o: ../src/MEC14xx/mec14xx_timers.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o ../src/MEC14xx/mec14xx_timers.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1360937237/main.o: ../src/main.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1360937237" 
	@${RM} ${OBJECTDIR}/_ext/1360937237/main.o.d 
	@${RM} ${OBJECTDIR}/_ext/1360937237/main.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1360937237/main.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE) -g -D__DEBUG -D__MPLAB_DEBUGGER_ICD3=1 -fframe-base-loclist  -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1360937237/main.o.d" -o ${OBJECTDIR}/_ext/1360937237/main.o ../src/main.c    -D__DEBUG -Wall -Wextra
	
else
${OBJECTDIR}/_ext/1477011893/main_blinky.o: ../src/Blinky_Demo/main_blinky.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1477011893" 
	@${RM} ${OBJECTDIR}/_ext/1477011893/main_blinky.o.d 
	@${RM} ${OBJECTDIR}/_ext/1477011893/main_blinky.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1477011893/main_blinky.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1477011893/main_blinky.o.d" -o ${OBJECTDIR}/_ext/1477011893/main_blinky.o ../src/Blinky_Demo/main_blinky.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1884096877/heap_2.o: ../../../Source/portable/MemMang/heap_2.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1884096877" 
	@${RM} ${OBJECTDIR}/_ext/1884096877/heap_2.o.d 
	@${RM} ${OBJECTDIR}/_ext/1884096877/heap_2.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1884096877/heap_2.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1884096877/heap_2.o.d" -o ${OBJECTDIR}/_ext/1884096877/heap_2.o ../../../Source/portable/MemMang/heap_2.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/582319769/port.o: ../../../Source/portable/MPLAB/PIC32MEC14xx/port.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/582319769" 
	@${RM} ${OBJECTDIR}/_ext/582319769/port.o.d 
	@${RM} ${OBJECTDIR}/_ext/582319769/port.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/582319769/port.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/582319769/port.o.d" -o ${OBJECTDIR}/_ext/582319769/port.o ../../../Source/portable/MPLAB/PIC32MEC14xx/port.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/449926602/event_groups.o: ../../../Source/event_groups.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602" 
	@${RM} ${OBJECTDIR}/_ext/449926602/event_groups.o.d 
	@${RM} ${OBJECTDIR}/_ext/449926602/event_groups.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/event_groups.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/449926602/event_groups.o.d" -o ${OBJECTDIR}/_ext/449926602/event_groups.o ../../../Source/event_groups.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/449926602/list.o: ../../../Source/list.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602" 
	@${RM} ${OBJECTDIR}/_ext/449926602/list.o.d 
	@${RM} ${OBJECTDIR}/_ext/449926602/list.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/list.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/449926602/list.o.d" -o ${OBJECTDIR}/_ext/449926602/list.o ../../../Source/list.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/449926602/queue.o: ../../../Source/queue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602" 
	@${RM} ${OBJECTDIR}/_ext/449926602/queue.o.d 
	@${RM} ${OBJECTDIR}/_ext/449926602/queue.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/queue.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/449926602/queue.o.d" -o ${OBJECTDIR}/_ext/449926602/queue.o ../../../Source/queue.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/449926602/tasks.o: ../../../Source/tasks.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602" 
	@${RM} ${OBJECTDIR}/_ext/449926602/tasks.o.d 
	@${RM} ${OBJECTDIR}/_ext/449926602/tasks.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/tasks.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/449926602/tasks.o.d" -o ${OBJECTDIR}/_ext/449926602/tasks.o ../../../Source/tasks.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/449926602/timers.o: ../../../Source/timers.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/449926602" 
	@${RM} ${OBJECTDIR}/_ext/449926602/timers.o.d 
	@${RM} ${OBJECTDIR}/_ext/449926602/timers.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/449926602/timers.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/449926602/timers.o.d" -o ${OBJECTDIR}/_ext/449926602/timers.o ../../../Source/timers.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/blocktim.o: ../../Common/Minimal/blocktim.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/blocktim.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/blocktim.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/blocktim.o.d" -o ${OBJECTDIR}/_ext/1163846883/blocktim.o ../../Common/Minimal/blocktim.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/countsem.o: ../../Common/Minimal/countsem.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/countsem.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/countsem.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/countsem.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/countsem.o.d" -o ${OBJECTDIR}/_ext/1163846883/countsem.o ../../Common/Minimal/countsem.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/dynamic.o: ../../Common/Minimal/dynamic.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/dynamic.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/dynamic.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/dynamic.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/dynamic.o.d" -o ${OBJECTDIR}/_ext/1163846883/dynamic.o ../../Common/Minimal/dynamic.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o: ../../Common/Minimal/EventGroupsDemo.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o.d" -o ${OBJECTDIR}/_ext/1163846883/EventGroupsDemo.o ../../Common/Minimal/EventGroupsDemo.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/GenQTest.o: ../../Common/Minimal/GenQTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/GenQTest.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/GenQTest.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/GenQTest.o.d" -o ${OBJECTDIR}/_ext/1163846883/GenQTest.o ../../Common/Minimal/GenQTest.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/IntQueue.o: ../../Common/Minimal/IntQueue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntQueue.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntQueue.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/IntQueue.o.d" -o ${OBJECTDIR}/_ext/1163846883/IntQueue.o ../../Common/Minimal/IntQueue.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/IntSemTest.o: ../../Common/Minimal/IntSemTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntSemTest.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/IntSemTest.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/IntSemTest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/IntSemTest.o.d" -o ${OBJECTDIR}/_ext/1163846883/IntSemTest.o ../../Common/Minimal/IntSemTest.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/recmutex.o: ../../Common/Minimal/recmutex.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/recmutex.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/recmutex.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/recmutex.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/recmutex.o.d" -o ${OBJECTDIR}/_ext/1163846883/recmutex.o ../../Common/Minimal/recmutex.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/semtest.o: ../../Common/Minimal/semtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/semtest.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/semtest.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/semtest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/semtest.o.d" -o ${OBJECTDIR}/_ext/1163846883/semtest.o ../../Common/Minimal/semtest.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/TaskNotify.o: ../../Common/Minimal/TaskNotify.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/TaskNotify.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/TaskNotify.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/TaskNotify.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/TaskNotify.o.d" -o ${OBJECTDIR}/_ext/1163846883/TaskNotify.o ../../Common/Minimal/TaskNotify.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1163846883/TimerDemo.o: ../../Common/Minimal/TimerDemo.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1163846883" 
	@${RM} ${OBJECTDIR}/_ext/1163846883/TimerDemo.o.d 
	@${RM} ${OBJECTDIR}/_ext/1163846883/TimerDemo.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1163846883/TimerDemo.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1163846883/TimerDemo.o.d" -o ${OBJECTDIR}/_ext/1163846883/TimerDemo.o ../../Common/Minimal/TimerDemo.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/950458649/IntQueueTimer.o: ../src/Full_Demo/IntQueueTimer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/950458649" 
	@${RM} ${OBJECTDIR}/_ext/950458649/IntQueueTimer.o.d 
	@${RM} ${OBJECTDIR}/_ext/950458649/IntQueueTimer.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/950458649/IntQueueTimer.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/950458649/IntQueueTimer.o.d" -o ${OBJECTDIR}/_ext/950458649/IntQueueTimer.o ../src/Full_Demo/IntQueueTimer.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/950458649/main_full.o: ../src/Full_Demo/main_full.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/950458649" 
	@${RM} ${OBJECTDIR}/_ext/950458649/main_full.o.d 
	@${RM} ${OBJECTDIR}/_ext/950458649/main_full.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/950458649/main_full.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/950458649/main_full.o.d" -o ${OBJECTDIR}/_ext/950458649/main_full.o ../src/Full_Demo/main_full.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/950458649/timertest.o: ../src/Full_Demo/timertest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/950458649" 
	@${RM} ${OBJECTDIR}/_ext/950458649/timertest.o.d 
	@${RM} ${OBJECTDIR}/_ext/950458649/timertest.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/950458649/timertest.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/950458649/timertest.o.d" -o ${OBJECTDIR}/_ext/950458649/timertest.o ../src/Full_Demo/timertest.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1801383878/general_exception.o: ../src/MEC14xx/exceptions/MPLAB/general_exception.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1801383878" 
	@${RM} ${OBJECTDIR}/_ext/1801383878/general_exception.o.d 
	@${RM} ${OBJECTDIR}/_ext/1801383878/general_exception.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1801383878/general_exception.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1801383878/general_exception.o.d" -o ${OBJECTDIR}/_ext/1801383878/general_exception.o ../src/MEC14xx/exceptions/MPLAB/general_exception.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq08.o: ../src/MEC14xx/interrupts/girq08.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq08.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq08.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq08.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq08.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq08.o ../src/MEC14xx/interrupts/girq08.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq09.o: ../src/MEC14xx/interrupts/girq09.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq09.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq09.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq09.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq09.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq09.o ../src/MEC14xx/interrupts/girq09.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq10.o: ../src/MEC14xx/interrupts/girq10.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq10.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq10.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq10.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq10.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq10.o ../src/MEC14xx/interrupts/girq10.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq11.o: ../src/MEC14xx/interrupts/girq11.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq11.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq11.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq11.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq11.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq11.o ../src/MEC14xx/interrupts/girq11.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq12.o: ../src/MEC14xx/interrupts/girq12.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq12.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq12.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq12.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq12.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq12.o ../src/MEC14xx/interrupts/girq12.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq13.o: ../src/MEC14xx/interrupts/girq13.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq13.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq13.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq13.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq13.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq13.o ../src/MEC14xx/interrupts/girq13.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq14.o: ../src/MEC14xx/interrupts/girq14.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq14.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq14.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq14.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq14.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq14.o ../src/MEC14xx/interrupts/girq14.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq15.o: ../src/MEC14xx/interrupts/girq15.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq15.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq15.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq15.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq15.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq15.o ../src/MEC14xx/interrupts/girq15.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq16.o: ../src/MEC14xx/interrupts/girq16.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq16.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq16.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq16.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq16.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq16.o ../src/MEC14xx/interrupts/girq16.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq17.o: ../src/MEC14xx/interrupts/girq17.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq17.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq17.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq17.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq17.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq17.o ../src/MEC14xx/interrupts/girq17.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq18.o: ../src/MEC14xx/interrupts/girq18.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq18.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq18.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq18.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq18.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq18.o ../src/MEC14xx/interrupts/girq18.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq19.o: ../src/MEC14xx/interrupts/girq19.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq19.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq19.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq19.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq19.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq19.o ../src/MEC14xx/interrupts/girq19.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq20.o: ../src/MEC14xx/interrupts/girq20.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq20.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq20.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq20.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq20.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq20.o ../src/MEC14xx/interrupts/girq20.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq21.o: ../src/MEC14xx/interrupts/girq21.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq21.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq21.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq21.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq21.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq21.o ../src/MEC14xx/interrupts/girq21.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq22.o: ../src/MEC14xx/interrupts/girq22.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq22.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq22.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq22.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq22.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq22.o ../src/MEC14xx/interrupts/girq22.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq23.o: ../src/MEC14xx/interrupts/girq23.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq23.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq23.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq23.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq23.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq23.o ../src/MEC14xx/interrupts/girq23.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq24.o: ../src/MEC14xx/interrupts/girq24.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq24.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq24.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq24.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq24.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq24.o ../src/MEC14xx/interrupts/girq24.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq25.o: ../src/MEC14xx/interrupts/girq25.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq25.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq25.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq25.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq25.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq25.o ../src/MEC14xx/interrupts/girq25.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girq26.o: ../src/MEC14xx/interrupts/girq26.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq26.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girq26.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girq26.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girq26.o.d" -o ${OBJECTDIR}/_ext/1662639563/girq26.o ../src/MEC14xx/interrupts/girq26.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1662639563/girqs.o: ../src/MEC14xx/interrupts/girqs.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1662639563" 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girqs.o.d 
	@${RM} ${OBJECTDIR}/_ext/1662639563/girqs.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1662639563/girqs.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1662639563/girqs.o.d" -o ${OBJECTDIR}/_ext/1662639563/girqs.o ../src/MEC14xx/interrupts/girqs.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o: ../src/MEC14xx/startup/MPLAB/default-on-bootstrap.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1068550557" 
	@${RM} ${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o.d 
	@${RM} ${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o.d" -o ${OBJECTDIR}/_ext/1068550557/default-on-bootstrap.o ../src/MEC14xx/startup/MPLAB/default-on-bootstrap.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1068550557/on_reset.o: ../src/MEC14xx/startup/MPLAB/on_reset.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1068550557" 
	@${RM} ${OBJECTDIR}/_ext/1068550557/on_reset.o.d 
	@${RM} ${OBJECTDIR}/_ext/1068550557/on_reset.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1068550557/on_reset.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1068550557/on_reset.o.d" -o ${OBJECTDIR}/_ext/1068550557/on_reset.o ../src/MEC14xx/startup/MPLAB/on_reset.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o: ../src/MEC14xx/mec14xx_bbled.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_bbled.o ../src/MEC14xx/mec14xx_bbled.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o: ../src/MEC14xx/mec14xx_gpio.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_gpio.o ../src/MEC14xx/mec14xx_gpio.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o: ../src/MEC14xx/mec14xx_jtvic.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_jtvic.o ../src/MEC14xx/mec14xx_jtvic.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_system.o: ../src/MEC14xx/mec14xx_system.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_system.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_system.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_system.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_system.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_system.o ../src/MEC14xx/mec14xx_system.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o: ../src/MEC14xx/mec14xx_tfdp.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_tfdp.o ../src/MEC14xx/mec14xx_tfdp.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o: ../src/MEC14xx/mec14xx_timers.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1376193940" 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o.d 
	@${RM} ${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o.d" -o ${OBJECTDIR}/_ext/1376193940/mec14xx_timers.o ../src/MEC14xx/mec14xx_timers.c    -D__DEBUG -Wall -Wextra
	
${OBJECTDIR}/_ext/1360937237/main.o: ../src/main.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1360937237" 
	@${RM} ${OBJECTDIR}/_ext/1360937237/main.o.d 
	@${RM} ${OBJECTDIR}/_ext/1360937237/main.o 
	@${FIXDEPS} "${OBJECTDIR}/_ext/1360937237/main.o.d" $(SILENT) -rsi ${MP_CC_DIR}../  -c ${MP_CC}  $(MP_EXTRA_CC_PRE)  -g -x c -c -mprocessor=$(MP_PROCESSOR_OPTION)  -ffunction-sections -mmicromips -O3 -I"../src" -I"../src/include" -I"../../../Source/include" -I"../../../Source/portable/MPLAB/PIC32MEC14xx" -I"../src/MEC14xx" -I"../../Common/include" -I"../src/Full_Demo" -MMD -MF "${OBJECTDIR}/_ext/1360937237/main.o.d" -o ${OBJECTDIR}/_ext/1360937237/main.o ../src/main.c    -D__DEBUG -Wall -Wextra
	
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: compileCPP
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
else
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: link
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
dist/${CND_CONF}/${IMAGE_TYPE}/PIC32MEC14xx_RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}: ${OBJECTFILES}  nbproject/Makefile-${CND_CONF}.mk    ../linkfile/custom_pMEC1404.ld
	@${MKDIR} dist/${CND_CONF}/${IMAGE_TYPE} 
	${MP_CC} $(MP_EXTRA_LD_PRE)  -mdebugger -D__MPLAB_DEBUGGER_ICD3=1 -mprocessor=$(MP_PROCESSOR_OPTION) -nostartfiles -mmicromips -o dist/${CND_CONF}/${IMAGE_TYPE}/PIC32MEC14xx_RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX} ${OBJECTFILES_QUOTED_IF_SPACED}              -Wl,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_LD_POST)$(MP_LINKER_FILE_OPTION),--defsym=__MPLAB_DEBUG=1,--defsym=__DEBUG=1,--defsym=__MPLAB_DEBUGGER_ICD3=1,--defsym=_min_stack_size=2048,-Map="${DISTDIR}/${PROJECTNAME}.${IMAGE_TYPE}.map",--report-mem,--verbose
	
else
dist/${CND_CONF}/${IMAGE_TYPE}/PIC32MEC14xx_RTOSDemo.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}: ${OBJECTFILES}  nbproject/Makefile-${CND_CONF}.mk   ../linkfile/custom_pMEC1404.ld
	@${MKDIR} dist/${CND_CONF}/${IMAGE_TYPE} 
	${MP_CC} $(MP_EXTRA_LD_PRE)  -mprocessor=$(MP_PROCESSOR_OPTION) -nostartfiles -mmicromips -o dist/${CND_CONF}/${IMAGE_TYPE}/PIC32MEC14xx_RTOSDemo.X.${IMAGE_TYPE}.${DEBUGGABLE_SUFFIX} ${OBJECTFILES_QUOTED_IF_SPACED}          -Wl,--defsym=__MPLAB_BUILD=1$(MP_EXTRA_LD_POST)$(MP_LINKER_FILE_OPTION),--defsym=_min_stack_size=2048,-Map="${DISTDIR}/${PROJECTNAME}.${IMAGE_TYPE}.map",--report-mem,--verbose
	${MP_CC_DIR}\\xc32-bin2hex dist/${CND_CONF}/${IMAGE_TYPE}/PIC32MEC14xx_RTOSDemo.X.${IMAGE_TYPE}.${DEBUGGABLE_SUFFIX} 
endif


# Subprojects
.build-subprojects:


# Subprojects
.clean-subprojects:

# Clean Targets
.clean-conf: ${CLEAN_SUBPROJECTS}
	${RM} -r build/default
	${RM} -r dist/default

# Enable dependency checking
.dep.inc: .depcheck-impl

DEPFILES=$(shell mplabwildcard ${POSSIBLE_DEPFILES})
ifneq (${DEPFILES},)
include ${DEPFILES}
endif
