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
FINAL_IMAGE=dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}
else
IMAGE_TYPE=production
OUTPUT_SUFFIX=hex
DEBUGGABLE_SUFFIX=elf
FINAL_IMAGE=dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}
endif

ifeq ($(COMPARE_BUILD), true)
COMPARISON_BUILD=
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
SOURCEFILES_QUOTED_IF_SPACED=../Common/Full/print.c ../Common/Full/semtest.c ../Common/Minimal/PollQ.c ../Common/Minimal/TaskNotify.c ../Common/Minimal/comtest.c ../Common/Minimal/crflash.c ../Common/Minimal/integer.c ../Common/Minimal/recmutex.c ../../Source/portable/GCC/AVR_AVRDx/port.c ../../Source/croutine.c ../../Source/event_groups.c ../../Source/list.c ../../Source/queue.c ../../Source/stream_buffer.c ../../Source/tasks.c ../../Source/timers.c ParTest/partest.c serial/serial.c main.c main_blinky.c main_full.c main_minimal.c RegTest.c ../../Source/portable/MemMang/heap_1.c

# Object Files Quoted if spaced
OBJECTFILES_QUOTED_IF_SPACED=${OBJECTDIR}/_ext/923164060/print.o ${OBJECTDIR}/_ext/923164060/semtest.o ${OBJECTDIR}/_ext/270959020/PollQ.o ${OBJECTDIR}/_ext/270959020/TaskNotify.o ${OBJECTDIR}/_ext/270959020/comtest.o ${OBJECTDIR}/_ext/270959020/crflash.o ${OBJECTDIR}/_ext/270959020/integer.o ${OBJECTDIR}/_ext/270959020/recmutex.o ${OBJECTDIR}/_ext/557582343/port.o ${OBJECTDIR}/_ext/1787047461/croutine.o ${OBJECTDIR}/_ext/1787047461/event_groups.o ${OBJECTDIR}/_ext/1787047461/list.o ${OBJECTDIR}/_ext/1787047461/queue.o ${OBJECTDIR}/_ext/1787047461/stream_buffer.o ${OBJECTDIR}/_ext/1787047461/tasks.o ${OBJECTDIR}/_ext/1787047461/timers.o ${OBJECTDIR}/ParTest/partest.o ${OBJECTDIR}/serial/serial.o ${OBJECTDIR}/main.o ${OBJECTDIR}/main_blinky.o ${OBJECTDIR}/main_full.o ${OBJECTDIR}/main_minimal.o ${OBJECTDIR}/RegTest.o ${OBJECTDIR}/_ext/897580706/heap_1.o
POSSIBLE_DEPFILES=${OBJECTDIR}/_ext/923164060/print.o.d ${OBJECTDIR}/_ext/923164060/semtest.o.d ${OBJECTDIR}/_ext/270959020/PollQ.o.d ${OBJECTDIR}/_ext/270959020/TaskNotify.o.d ${OBJECTDIR}/_ext/270959020/comtest.o.d ${OBJECTDIR}/_ext/270959020/crflash.o.d ${OBJECTDIR}/_ext/270959020/integer.o.d ${OBJECTDIR}/_ext/270959020/recmutex.o.d ${OBJECTDIR}/_ext/557582343/port.o.d ${OBJECTDIR}/_ext/1787047461/croutine.o.d ${OBJECTDIR}/_ext/1787047461/event_groups.o.d ${OBJECTDIR}/_ext/1787047461/list.o.d ${OBJECTDIR}/_ext/1787047461/queue.o.d ${OBJECTDIR}/_ext/1787047461/stream_buffer.o.d ${OBJECTDIR}/_ext/1787047461/tasks.o.d ${OBJECTDIR}/_ext/1787047461/timers.o.d ${OBJECTDIR}/ParTest/partest.o.d ${OBJECTDIR}/serial/serial.o.d ${OBJECTDIR}/main.o.d ${OBJECTDIR}/main_blinky.o.d ${OBJECTDIR}/main_full.o.d ${OBJECTDIR}/main_minimal.o.d ${OBJECTDIR}/RegTest.o.d ${OBJECTDIR}/_ext/897580706/heap_1.o.d

# Object Files
OBJECTFILES=${OBJECTDIR}/_ext/923164060/print.o ${OBJECTDIR}/_ext/923164060/semtest.o ${OBJECTDIR}/_ext/270959020/PollQ.o ${OBJECTDIR}/_ext/270959020/TaskNotify.o ${OBJECTDIR}/_ext/270959020/comtest.o ${OBJECTDIR}/_ext/270959020/crflash.o ${OBJECTDIR}/_ext/270959020/integer.o ${OBJECTDIR}/_ext/270959020/recmutex.o ${OBJECTDIR}/_ext/557582343/port.o ${OBJECTDIR}/_ext/1787047461/croutine.o ${OBJECTDIR}/_ext/1787047461/event_groups.o ${OBJECTDIR}/_ext/1787047461/list.o ${OBJECTDIR}/_ext/1787047461/queue.o ${OBJECTDIR}/_ext/1787047461/stream_buffer.o ${OBJECTDIR}/_ext/1787047461/tasks.o ${OBJECTDIR}/_ext/1787047461/timers.o ${OBJECTDIR}/ParTest/partest.o ${OBJECTDIR}/serial/serial.o ${OBJECTDIR}/main.o ${OBJECTDIR}/main_blinky.o ${OBJECTDIR}/main_full.o ${OBJECTDIR}/main_minimal.o ${OBJECTDIR}/RegTest.o ${OBJECTDIR}/_ext/897580706/heap_1.o

# Source Files
SOURCEFILES=../Common/Full/print.c ../Common/Full/semtest.c ../Common/Minimal/PollQ.c ../Common/Minimal/TaskNotify.c ../Common/Minimal/comtest.c ../Common/Minimal/crflash.c ../Common/Minimal/integer.c ../Common/Minimal/recmutex.c ../../Source/portable/GCC/AVR_AVRDx/port.c ../../Source/croutine.c ../../Source/event_groups.c ../../Source/list.c ../../Source/queue.c ../../Source/stream_buffer.c ../../Source/tasks.c ../../Source/timers.c ParTest/partest.c serial/serial.c main.c main_blinky.c main_full.c main_minimal.c RegTest.c ../../Source/portable/MemMang/heap_1.c



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
	${MAKE}  -f nbproject/Makefile-default.mk dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}

MP_PROCESSOR_OPTION=AVR128DA48
# ------------------------------------------------------------------------------------
# Rules for buildStep: compile
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
${OBJECTDIR}/_ext/923164060/print.o: ../Common/Full/print.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/923164060" 
	@${RM} ${OBJECTDIR}/_ext/923164060/print.o.d 
	@${RM} ${OBJECTDIR}/_ext/923164060/print.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/923164060/print.o.d" -MT "${OBJECTDIR}/_ext/923164060/print.o.d" -MT ${OBJECTDIR}/_ext/923164060/print.o -o ${OBJECTDIR}/_ext/923164060/print.o ../Common/Full/print.c 
	
${OBJECTDIR}/_ext/923164060/semtest.o: ../Common/Full/semtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/923164060" 
	@${RM} ${OBJECTDIR}/_ext/923164060/semtest.o.d 
	@${RM} ${OBJECTDIR}/_ext/923164060/semtest.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/923164060/semtest.o.d" -MT "${OBJECTDIR}/_ext/923164060/semtest.o.d" -MT ${OBJECTDIR}/_ext/923164060/semtest.o -o ${OBJECTDIR}/_ext/923164060/semtest.o ../Common/Full/semtest.c 
	
${OBJECTDIR}/_ext/270959020/PollQ.o: ../Common/Minimal/PollQ.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/PollQ.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/PollQ.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/PollQ.o.d" -MT "${OBJECTDIR}/_ext/270959020/PollQ.o.d" -MT ${OBJECTDIR}/_ext/270959020/PollQ.o -o ${OBJECTDIR}/_ext/270959020/PollQ.o ../Common/Minimal/PollQ.c 
	
${OBJECTDIR}/_ext/270959020/TaskNotify.o: ../Common/Minimal/TaskNotify.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/TaskNotify.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/TaskNotify.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/TaskNotify.o.d" -MT "${OBJECTDIR}/_ext/270959020/TaskNotify.o.d" -MT ${OBJECTDIR}/_ext/270959020/TaskNotify.o -o ${OBJECTDIR}/_ext/270959020/TaskNotify.o ../Common/Minimal/TaskNotify.c 
	
${OBJECTDIR}/_ext/270959020/comtest.o: ../Common/Minimal/comtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/comtest.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/comtest.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/comtest.o.d" -MT "${OBJECTDIR}/_ext/270959020/comtest.o.d" -MT ${OBJECTDIR}/_ext/270959020/comtest.o -o ${OBJECTDIR}/_ext/270959020/comtest.o ../Common/Minimal/comtest.c 
	
${OBJECTDIR}/_ext/270959020/crflash.o: ../Common/Minimal/crflash.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/crflash.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/crflash.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/crflash.o.d" -MT "${OBJECTDIR}/_ext/270959020/crflash.o.d" -MT ${OBJECTDIR}/_ext/270959020/crflash.o -o ${OBJECTDIR}/_ext/270959020/crflash.o ../Common/Minimal/crflash.c 
	
${OBJECTDIR}/_ext/270959020/integer.o: ../Common/Minimal/integer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/integer.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/integer.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/integer.o.d" -MT "${OBJECTDIR}/_ext/270959020/integer.o.d" -MT ${OBJECTDIR}/_ext/270959020/integer.o -o ${OBJECTDIR}/_ext/270959020/integer.o ../Common/Minimal/integer.c 
	
${OBJECTDIR}/_ext/270959020/recmutex.o: ../Common/Minimal/recmutex.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/recmutex.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/recmutex.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/recmutex.o.d" -MT "${OBJECTDIR}/_ext/270959020/recmutex.o.d" -MT ${OBJECTDIR}/_ext/270959020/recmutex.o -o ${OBJECTDIR}/_ext/270959020/recmutex.o ../Common/Minimal/recmutex.c 
	
${OBJECTDIR}/_ext/557582343/port.o: ../../Source/portable/GCC/AVR_AVRDx/port.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/557582343" 
	@${RM} ${OBJECTDIR}/_ext/557582343/port.o.d 
	@${RM} ${OBJECTDIR}/_ext/557582343/port.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/557582343/port.o.d" -MT "${OBJECTDIR}/_ext/557582343/port.o.d" -MT ${OBJECTDIR}/_ext/557582343/port.o -o ${OBJECTDIR}/_ext/557582343/port.o ../../Source/portable/GCC/AVR_AVRDx/port.c 
	
${OBJECTDIR}/_ext/1787047461/croutine.o: ../../Source/croutine.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/croutine.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/croutine.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/croutine.o.d" -MT "${OBJECTDIR}/_ext/1787047461/croutine.o.d" -MT ${OBJECTDIR}/_ext/1787047461/croutine.o -o ${OBJECTDIR}/_ext/1787047461/croutine.o ../../Source/croutine.c 
	
${OBJECTDIR}/_ext/1787047461/event_groups.o: ../../Source/event_groups.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/event_groups.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/event_groups.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/event_groups.o.d" -MT "${OBJECTDIR}/_ext/1787047461/event_groups.o.d" -MT ${OBJECTDIR}/_ext/1787047461/event_groups.o -o ${OBJECTDIR}/_ext/1787047461/event_groups.o ../../Source/event_groups.c 
	
${OBJECTDIR}/_ext/1787047461/list.o: ../../Source/list.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/list.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/list.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/list.o.d" -MT "${OBJECTDIR}/_ext/1787047461/list.o.d" -MT ${OBJECTDIR}/_ext/1787047461/list.o -o ${OBJECTDIR}/_ext/1787047461/list.o ../../Source/list.c 
	
${OBJECTDIR}/_ext/1787047461/queue.o: ../../Source/queue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/queue.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/queue.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/queue.o.d" -MT "${OBJECTDIR}/_ext/1787047461/queue.o.d" -MT ${OBJECTDIR}/_ext/1787047461/queue.o -o ${OBJECTDIR}/_ext/1787047461/queue.o ../../Source/queue.c 
	
${OBJECTDIR}/_ext/1787047461/stream_buffer.o: ../../Source/stream_buffer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/stream_buffer.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/stream_buffer.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/stream_buffer.o.d" -MT "${OBJECTDIR}/_ext/1787047461/stream_buffer.o.d" -MT ${OBJECTDIR}/_ext/1787047461/stream_buffer.o -o ${OBJECTDIR}/_ext/1787047461/stream_buffer.o ../../Source/stream_buffer.c 
	
${OBJECTDIR}/_ext/1787047461/tasks.o: ../../Source/tasks.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/tasks.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/tasks.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/tasks.o.d" -MT "${OBJECTDIR}/_ext/1787047461/tasks.o.d" -MT ${OBJECTDIR}/_ext/1787047461/tasks.o -o ${OBJECTDIR}/_ext/1787047461/tasks.o ../../Source/tasks.c 
	
${OBJECTDIR}/_ext/1787047461/timers.o: ../../Source/timers.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/timers.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/timers.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/timers.o.d" -MT "${OBJECTDIR}/_ext/1787047461/timers.o.d" -MT ${OBJECTDIR}/_ext/1787047461/timers.o -o ${OBJECTDIR}/_ext/1787047461/timers.o ../../Source/timers.c 
	
${OBJECTDIR}/ParTest/partest.o: ParTest/partest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/ParTest" 
	@${RM} ${OBJECTDIR}/ParTest/partest.o.d 
	@${RM} ${OBJECTDIR}/ParTest/partest.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/ParTest/partest.o.d" -MT "${OBJECTDIR}/ParTest/partest.o.d" -MT ${OBJECTDIR}/ParTest/partest.o -o ${OBJECTDIR}/ParTest/partest.o ParTest/partest.c 
	
${OBJECTDIR}/serial/serial.o: serial/serial.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/serial" 
	@${RM} ${OBJECTDIR}/serial/serial.o.d 
	@${RM} ${OBJECTDIR}/serial/serial.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/serial/serial.o.d" -MT "${OBJECTDIR}/serial/serial.o.d" -MT ${OBJECTDIR}/serial/serial.o -o ${OBJECTDIR}/serial/serial.o serial/serial.c 
	
${OBJECTDIR}/main.o: main.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}" 
	@${RM} ${OBJECTDIR}/main.o.d 
	@${RM} ${OBJECTDIR}/main.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/main.o.d" -MT "${OBJECTDIR}/main.o.d" -MT ${OBJECTDIR}/main.o -o ${OBJECTDIR}/main.o main.c 
	
${OBJECTDIR}/main_blinky.o: main_blinky.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}" 
	@${RM} ${OBJECTDIR}/main_blinky.o.d 
	@${RM} ${OBJECTDIR}/main_blinky.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/main_blinky.o.d" -MT "${OBJECTDIR}/main_blinky.o.d" -MT ${OBJECTDIR}/main_blinky.o -o ${OBJECTDIR}/main_blinky.o main_blinky.c 
	
${OBJECTDIR}/main_full.o: main_full.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}" 
	@${RM} ${OBJECTDIR}/main_full.o.d 
	@${RM} ${OBJECTDIR}/main_full.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/main_full.o.d" -MT "${OBJECTDIR}/main_full.o.d" -MT ${OBJECTDIR}/main_full.o -o ${OBJECTDIR}/main_full.o main_full.c 
	
${OBJECTDIR}/main_minimal.o: main_minimal.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}" 
	@${RM} ${OBJECTDIR}/main_minimal.o.d 
	@${RM} ${OBJECTDIR}/main_minimal.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/main_minimal.o.d" -MT "${OBJECTDIR}/main_minimal.o.d" -MT ${OBJECTDIR}/main_minimal.o -o ${OBJECTDIR}/main_minimal.o main_minimal.c 
	
${OBJECTDIR}/RegTest.o: RegTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}" 
	@${RM} ${OBJECTDIR}/RegTest.o.d 
	@${RM} ${OBJECTDIR}/RegTest.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/RegTest.o.d" -MT "${OBJECTDIR}/RegTest.o.d" -MT ${OBJECTDIR}/RegTest.o -o ${OBJECTDIR}/RegTest.o RegTest.c 
	
${OBJECTDIR}/_ext/897580706/heap_1.o: ../../Source/portable/MemMang/heap_1.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/897580706" 
	@${RM} ${OBJECTDIR}/_ext/897580706/heap_1.o.d 
	@${RM} ${OBJECTDIR}/_ext/897580706/heap_1.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -D__DEBUG=1 -g -DDEBUG  -gdwarf-2  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/897580706/heap_1.o.d" -MT "${OBJECTDIR}/_ext/897580706/heap_1.o.d" -MT ${OBJECTDIR}/_ext/897580706/heap_1.o -o ${OBJECTDIR}/_ext/897580706/heap_1.o ../../Source/portable/MemMang/heap_1.c 
	
else
${OBJECTDIR}/_ext/923164060/print.o: ../Common/Full/print.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/923164060" 
	@${RM} ${OBJECTDIR}/_ext/923164060/print.o.d 
	@${RM} ${OBJECTDIR}/_ext/923164060/print.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/923164060/print.o.d" -MT "${OBJECTDIR}/_ext/923164060/print.o.d" -MT ${OBJECTDIR}/_ext/923164060/print.o -o ${OBJECTDIR}/_ext/923164060/print.o ../Common/Full/print.c 
	
${OBJECTDIR}/_ext/923164060/semtest.o: ../Common/Full/semtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/923164060" 
	@${RM} ${OBJECTDIR}/_ext/923164060/semtest.o.d 
	@${RM} ${OBJECTDIR}/_ext/923164060/semtest.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/923164060/semtest.o.d" -MT "${OBJECTDIR}/_ext/923164060/semtest.o.d" -MT ${OBJECTDIR}/_ext/923164060/semtest.o -o ${OBJECTDIR}/_ext/923164060/semtest.o ../Common/Full/semtest.c 
	
${OBJECTDIR}/_ext/270959020/PollQ.o: ../Common/Minimal/PollQ.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/PollQ.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/PollQ.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/PollQ.o.d" -MT "${OBJECTDIR}/_ext/270959020/PollQ.o.d" -MT ${OBJECTDIR}/_ext/270959020/PollQ.o -o ${OBJECTDIR}/_ext/270959020/PollQ.o ../Common/Minimal/PollQ.c 
	
${OBJECTDIR}/_ext/270959020/TaskNotify.o: ../Common/Minimal/TaskNotify.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/TaskNotify.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/TaskNotify.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/TaskNotify.o.d" -MT "${OBJECTDIR}/_ext/270959020/TaskNotify.o.d" -MT ${OBJECTDIR}/_ext/270959020/TaskNotify.o -o ${OBJECTDIR}/_ext/270959020/TaskNotify.o ../Common/Minimal/TaskNotify.c 
	
${OBJECTDIR}/_ext/270959020/comtest.o: ../Common/Minimal/comtest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/comtest.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/comtest.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/comtest.o.d" -MT "${OBJECTDIR}/_ext/270959020/comtest.o.d" -MT ${OBJECTDIR}/_ext/270959020/comtest.o -o ${OBJECTDIR}/_ext/270959020/comtest.o ../Common/Minimal/comtest.c 
	
${OBJECTDIR}/_ext/270959020/crflash.o: ../Common/Minimal/crflash.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/crflash.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/crflash.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/crflash.o.d" -MT "${OBJECTDIR}/_ext/270959020/crflash.o.d" -MT ${OBJECTDIR}/_ext/270959020/crflash.o -o ${OBJECTDIR}/_ext/270959020/crflash.o ../Common/Minimal/crflash.c 
	
${OBJECTDIR}/_ext/270959020/integer.o: ../Common/Minimal/integer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/integer.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/integer.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/integer.o.d" -MT "${OBJECTDIR}/_ext/270959020/integer.o.d" -MT ${OBJECTDIR}/_ext/270959020/integer.o -o ${OBJECTDIR}/_ext/270959020/integer.o ../Common/Minimal/integer.c 
	
${OBJECTDIR}/_ext/270959020/recmutex.o: ../Common/Minimal/recmutex.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/270959020" 
	@${RM} ${OBJECTDIR}/_ext/270959020/recmutex.o.d 
	@${RM} ${OBJECTDIR}/_ext/270959020/recmutex.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/270959020/recmutex.o.d" -MT "${OBJECTDIR}/_ext/270959020/recmutex.o.d" -MT ${OBJECTDIR}/_ext/270959020/recmutex.o -o ${OBJECTDIR}/_ext/270959020/recmutex.o ../Common/Minimal/recmutex.c 
	
${OBJECTDIR}/_ext/557582343/port.o: ../../Source/portable/GCC/AVR_AVRDx/port.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/557582343" 
	@${RM} ${OBJECTDIR}/_ext/557582343/port.o.d 
	@${RM} ${OBJECTDIR}/_ext/557582343/port.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/557582343/port.o.d" -MT "${OBJECTDIR}/_ext/557582343/port.o.d" -MT ${OBJECTDIR}/_ext/557582343/port.o -o ${OBJECTDIR}/_ext/557582343/port.o ../../Source/portable/GCC/AVR_AVRDx/port.c 
	
${OBJECTDIR}/_ext/1787047461/croutine.o: ../../Source/croutine.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/croutine.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/croutine.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/croutine.o.d" -MT "${OBJECTDIR}/_ext/1787047461/croutine.o.d" -MT ${OBJECTDIR}/_ext/1787047461/croutine.o -o ${OBJECTDIR}/_ext/1787047461/croutine.o ../../Source/croutine.c 
	
${OBJECTDIR}/_ext/1787047461/event_groups.o: ../../Source/event_groups.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/event_groups.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/event_groups.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/event_groups.o.d" -MT "${OBJECTDIR}/_ext/1787047461/event_groups.o.d" -MT ${OBJECTDIR}/_ext/1787047461/event_groups.o -o ${OBJECTDIR}/_ext/1787047461/event_groups.o ../../Source/event_groups.c 
	
${OBJECTDIR}/_ext/1787047461/list.o: ../../Source/list.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/list.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/list.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/list.o.d" -MT "${OBJECTDIR}/_ext/1787047461/list.o.d" -MT ${OBJECTDIR}/_ext/1787047461/list.o -o ${OBJECTDIR}/_ext/1787047461/list.o ../../Source/list.c 
	
${OBJECTDIR}/_ext/1787047461/queue.o: ../../Source/queue.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/queue.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/queue.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/queue.o.d" -MT "${OBJECTDIR}/_ext/1787047461/queue.o.d" -MT ${OBJECTDIR}/_ext/1787047461/queue.o -o ${OBJECTDIR}/_ext/1787047461/queue.o ../../Source/queue.c 
	
${OBJECTDIR}/_ext/1787047461/stream_buffer.o: ../../Source/stream_buffer.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/stream_buffer.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/stream_buffer.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/stream_buffer.o.d" -MT "${OBJECTDIR}/_ext/1787047461/stream_buffer.o.d" -MT ${OBJECTDIR}/_ext/1787047461/stream_buffer.o -o ${OBJECTDIR}/_ext/1787047461/stream_buffer.o ../../Source/stream_buffer.c 
	
${OBJECTDIR}/_ext/1787047461/tasks.o: ../../Source/tasks.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/tasks.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/tasks.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/tasks.o.d" -MT "${OBJECTDIR}/_ext/1787047461/tasks.o.d" -MT ${OBJECTDIR}/_ext/1787047461/tasks.o -o ${OBJECTDIR}/_ext/1787047461/tasks.o ../../Source/tasks.c 
	
${OBJECTDIR}/_ext/1787047461/timers.o: ../../Source/timers.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/1787047461" 
	@${RM} ${OBJECTDIR}/_ext/1787047461/timers.o.d 
	@${RM} ${OBJECTDIR}/_ext/1787047461/timers.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/1787047461/timers.o.d" -MT "${OBJECTDIR}/_ext/1787047461/timers.o.d" -MT ${OBJECTDIR}/_ext/1787047461/timers.o -o ${OBJECTDIR}/_ext/1787047461/timers.o ../../Source/timers.c 
	
${OBJECTDIR}/ParTest/partest.o: ParTest/partest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/ParTest" 
	@${RM} ${OBJECTDIR}/ParTest/partest.o.d 
	@${RM} ${OBJECTDIR}/ParTest/partest.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/ParTest/partest.o.d" -MT "${OBJECTDIR}/ParTest/partest.o.d" -MT ${OBJECTDIR}/ParTest/partest.o -o ${OBJECTDIR}/ParTest/partest.o ParTest/partest.c 
	
${OBJECTDIR}/serial/serial.o: serial/serial.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/serial" 
	@${RM} ${OBJECTDIR}/serial/serial.o.d 
	@${RM} ${OBJECTDIR}/serial/serial.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/serial/serial.o.d" -MT "${OBJECTDIR}/serial/serial.o.d" -MT ${OBJECTDIR}/serial/serial.o -o ${OBJECTDIR}/serial/serial.o serial/serial.c 
	
${OBJECTDIR}/main.o: main.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}" 
	@${RM} ${OBJECTDIR}/main.o.d 
	@${RM} ${OBJECTDIR}/main.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/main.o.d" -MT "${OBJECTDIR}/main.o.d" -MT ${OBJECTDIR}/main.o -o ${OBJECTDIR}/main.o main.c 
	
${OBJECTDIR}/main_blinky.o: main_blinky.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}" 
	@${RM} ${OBJECTDIR}/main_blinky.o.d 
	@${RM} ${OBJECTDIR}/main_blinky.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/main_blinky.o.d" -MT "${OBJECTDIR}/main_blinky.o.d" -MT ${OBJECTDIR}/main_blinky.o -o ${OBJECTDIR}/main_blinky.o main_blinky.c 
	
${OBJECTDIR}/main_full.o: main_full.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}" 
	@${RM} ${OBJECTDIR}/main_full.o.d 
	@${RM} ${OBJECTDIR}/main_full.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/main_full.o.d" -MT "${OBJECTDIR}/main_full.o.d" -MT ${OBJECTDIR}/main_full.o -o ${OBJECTDIR}/main_full.o main_full.c 
	
${OBJECTDIR}/main_minimal.o: main_minimal.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}" 
	@${RM} ${OBJECTDIR}/main_minimal.o.d 
	@${RM} ${OBJECTDIR}/main_minimal.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/main_minimal.o.d" -MT "${OBJECTDIR}/main_minimal.o.d" -MT ${OBJECTDIR}/main_minimal.o -o ${OBJECTDIR}/main_minimal.o main_minimal.c 
	
${OBJECTDIR}/RegTest.o: RegTest.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}" 
	@${RM} ${OBJECTDIR}/RegTest.o.d 
	@${RM} ${OBJECTDIR}/RegTest.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/RegTest.o.d" -MT "${OBJECTDIR}/RegTest.o.d" -MT ${OBJECTDIR}/RegTest.o -o ${OBJECTDIR}/RegTest.o RegTest.c 
	
${OBJECTDIR}/_ext/897580706/heap_1.o: ../../Source/portable/MemMang/heap_1.c  nbproject/Makefile-${CND_CONF}.mk
	@${MKDIR} "${OBJECTDIR}/_ext/897580706" 
	@${RM} ${OBJECTDIR}/_ext/897580706/heap_1.o.d 
	@${RM} ${OBJECTDIR}/_ext/897580706/heap_1.o 
	${MP_CC} $(MP_EXTRA_CC_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -c  -x c -D__$(MP_PROCESSOR_OPTION)__   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -DXPRJ_default=$(CND_CONF)  $(COMPARISON_BUILD)  -gdwarf-3 -flto     -MD -MP -MF "${OBJECTDIR}/_ext/897580706/heap_1.o.d" -MT "${OBJECTDIR}/_ext/897580706/heap_1.o.d" -MT ${OBJECTDIR}/_ext/897580706/heap_1.o -o ${OBJECTDIR}/_ext/897580706/heap_1.o ../../Source/portable/MemMang/heap_1.c 
	
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: assemble
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
else
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: assembleWithPreprocess
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
else
endif

# ------------------------------------------------------------------------------------
# Rules for buildStep: link
ifeq ($(TYPE_IMAGE), DEBUG_RUN)
dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}: ${OBJECTFILES}  nbproject/Makefile-${CND_CONF}.mk    
	@${MKDIR} dist/${CND_CONF}/${IMAGE_TYPE} 
	${MP_CC} $(MP_EXTRA_LD_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -Wl,-Map=dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.map  -D__DEBUG=1  -DXPRJ_default=$(CND_CONF)  -Wl,--defsym=__MPLAB_BUILD=1   -mdfp="${DFP_DIR}/xc8"   -gdwarf-2 -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -gdwarf-3     $(COMPARISON_BUILD) -Wl,--memorysummary,dist/${CND_CONF}/${IMAGE_TYPE}/memoryfile.xml -o dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.${DEBUGGABLE_SUFFIX}  -o dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}  ${OBJECTFILES_QUOTED_IF_SPACED}      -Wl,--start-group  -Wl,-lm -Wl,--end-group  -Wl,--defsym=__MPLAB_DEBUG=1,--defsym=__DEBUG=1
	@${RM} dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.hex 
	
else
dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.${OUTPUT_SUFFIX}: ${OBJECTFILES}  nbproject/Makefile-${CND_CONF}.mk   
	@${MKDIR} dist/${CND_CONF}/${IMAGE_TYPE} 
	${MP_CC} $(MP_EXTRA_LD_PRE) -mcpu=$(MP_PROCESSOR_OPTION) -Wl,-Map=dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.map  -DXPRJ_default=$(CND_CONF)  -Wl,--defsym=__MPLAB_BUILD=1   -mdfp="${DFP_DIR}/xc8"  -Wl,--gc-sections -Os -ffunction-sections -fdata-sections -fpack-struct -fshort-enums -funsigned-char -funsigned-bitfields -I"../Common/Full" -I"../Common/include" -I"../Common/Minimal" -I"../../Source/include" -I"../../Source/portable/GCC/AVR_AVRDx" -I"../../Source/portable/MemMang" -I"../../Source" -I"ParTest" -I"serial" -I"." -Wall -gdwarf-3     $(COMPARISON_BUILD) -Wl,--memorysummary,dist/${CND_CONF}/${IMAGE_TYPE}/memoryfile.xml -o dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.${DEBUGGABLE_SUFFIX}  -o dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.${DEBUGGABLE_SUFFIX}  ${OBJECTFILES_QUOTED_IF_SPACED}      -Wl,--start-group  -Wl,-lm -Wl,--end-group 
	${MP_CC_DIR}\\avr-objcopy -O ihex "dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.${DEBUGGABLE_SUFFIX}" "dist/${CND_CONF}/${IMAGE_TYPE}/AVR_Dx_MPLAB.X.${IMAGE_TYPE}.hex"
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
