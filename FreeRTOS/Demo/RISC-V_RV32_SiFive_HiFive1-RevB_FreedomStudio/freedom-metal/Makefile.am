# Copyright 2018-2019 SiFive, Inc
# SPDX-License-Identifier: Apache-2.0

########################################################
# Sources passed in by configure
########################################################

metal/machine.h: @MACHINE_HEADER@
	@mkdir -p $(dir $@)
	cp $< $@

metal/machine/inline.h: @MACHINE_INLINE@
	@mkdir -p $(dir $@)
	cp $< $@

metal/machine/platform.h: @PLATFORM_HEADER@
	@mkdir -p $(dir $@)
	cp $< $@

nobase_include_HEADERS = \
	metal/machine.h \
	metal/machine/inline.h \
	metal/machine/platform.h

# This will generate these sources before the compilation step
BUILT_SOURCES = \
	metal/machine.h \
	metal/machine/inline.h \
	metal/machine/platform.h

########################################################
# Metal header files
########################################################

nobase_include_HEADERS += \
	metal/drivers/fixed-clock.h \
	metal/drivers/fixed-factor-clock.h \
	metal/drivers/riscv_clint0.h \
	metal/drivers/riscv_cpu.h \
	metal/drivers/riscv_plic0.h \
	metal/drivers/sifive_buserror0.h \
	metal/drivers/sifive_ccache0.h \
	metal/drivers/sifive_clic0.h \
	metal/drivers/sifive_fe310-g000_hfrosc.h \
	metal/drivers/sifive_fe310-g000_hfxosc.h \
	metal/drivers/sifive_fe310-g000_lfrosc.h \
	metal/drivers/sifive_fe310-g000_pll.h \
	metal/drivers/sifive_fe310-g000_prci.h \
	metal/drivers/sifive_global-external-interrupts0.h \
	metal/drivers/sifive_gpio-buttons.h \
	metal/drivers/sifive_gpio-leds.h \
	metal/drivers/sifive_gpio-switches.h \
	metal/drivers/sifive_gpio0.h \
	metal/drivers/sifive_i2c0.h \
	metal/drivers/sifive_l2pf0.h \
	metal/drivers/sifive_local-external-interrupts0.h \
	metal/drivers/sifive_pwm0.h \
	metal/drivers/sifive_rtc0.h \
	metal/drivers/sifive_spi0.h \
	metal/drivers/sifive_test0.h \
	metal/drivers/sifive_trace.h \
	metal/drivers/sifive_uart0.h \
	metal/drivers/sifive_simuart0.h \
	metal/drivers/sifive_wdog0.h \
	metal/drivers/ucb_htif0.h \
	metal/atomic.h \
	metal/button.h \
	metal/cache.h \
	metal/clock.h \
	metal/compiler.h \
	metal/cpu.h \
	metal/csr.h \
	metal/gpio.h \
	metal/hpm.h \
	metal/i2c.h \
	metal/init.h \
	metal/interrupt.h \
	metal/io.h \
	metal/itim.h \
	metal/led.h \
	metal/lim.h \
	metal/lock.h \
	metal/memory.h \
	metal/pmp.h \
	metal/privilege.h \
	metal/pwm.h\
	metal/rtc.h \
	metal/shutdown.h \
	metal/scrub.h \
	metal/spi.h \
	metal/switch.h \
	metal/timer.h \
	metal/time.h \
	metal/tty.h \
	metal/uart.h \
	metal/watchdog.h

########################################################
# libmetal
########################################################

lib_LIBRARIES = libmetal.a

libmetal_a_SOURCES = \
	src/drivers/fixed-clock.c \
	src/drivers/fixed-factor-clock.c \
	src/drivers/inline.c \
	src/drivers/riscv_clint0.c \
	src/drivers/riscv_cpu.c \
	src/drivers/riscv_plic0.c \
	src/drivers/sifive_buserror0.c \
	src/drivers/sifive_ccache0.c \
	src/drivers/sifive_clic0.c \
	src/drivers/sifive_fe310-g000_hfrosc.c \
	src/drivers/sifive_fe310-g000_hfxosc.c \
	src/drivers/sifive_fe310-g000_lfrosc.c \
	src/drivers/sifive_fe310-g000_pll.c \
	src/drivers/sifive_fe310-g000_prci.c \
	src/drivers/sifive_global-external-interrupts0.c \
	src/drivers/sifive_gpio-buttons.c \
	src/drivers/sifive_gpio-leds.c \
	src/drivers/sifive_gpio-switches.c \
	src/drivers/sifive_gpio0.c \
	src/drivers/sifive_i2c0.c \
	src/drivers/sifive_l2pf0.c \
	src/drivers/sifive_local-external-interrupts0.c \
	src/drivers/sifive_pwm0.c \
	src/drivers/sifive_rtc0.c \
	src/drivers/sifive_spi0.c \
	src/drivers/sifive_test0.c \
	src/drivers/sifive_trace.c \
	src/drivers/sifive_uart0.c \
	src/drivers/sifive_simuart0.c \
	src/drivers/sifive_wdog0.c \
	src/drivers/ucb_htif0.c \
	src/atomic.c \
	src/button.c \
	src/cache.c \
	src/clock.c \
	src/cpu.c \
	src/entry.S \
	src/scrub.S \
	src/trap.S \
	src/gpio.c \
	src/hpm.c \
	src/i2c.c \
	src/init.c \
	src/interrupt.c \
	src/led.c \
	src/lock.c \
	src/memory.c \
	src/pmp.c \
	src/privilege.c \
	src/pwm.c\
	src/rtc.c \
	src/shutdown.c \
	src/spi.c \
	src/switch.c \
	src/synchronize_harts.c \
	src/timer.c \
	src/time.c \
	src/trap.S \
	src/tty.c \
	src/uart.c \
	src/vector.S \
	src/watchdog.c

########################################################
# libsegger
########################################################

# Provide segger hook with Freedom Metal that is built when
# --with-builtin-libmetal-segger is passed to configure
if WITH_BUILTIN_LIBMETAL_SEGGER

lib_LIBRARIES += libmetal-segger.a

libmetal_segger_a_SOURCES = \
       gloss/crt0.S \
       segger/SEGGER_target_metal.c

endif # WITH_BUILTIN_LIBMETAL_SEGGER

########################################################
# libgloss
########################################################

# Freedom Metal has its own libgloss implementation that is only built when
# --with-builtin-libgloss is passed to configure.
if WITH_BUILTIN_LIBGLOSS

lib_LIBRARIES += libmetal-gloss.a

libmetal_gloss_a_SOURCES = \
	gloss/crt0.S \
	gloss/nanosleep.c \
	gloss/sys_access.c \
	gloss/sys_chdir.c \
	gloss/sys_chmod.c \
	gloss/sys_chown.c \
	gloss/sys_clock_gettime.c \
	gloss/sys_close.c \
	gloss/sys_execve.c \
	gloss/sys_exit.c \
	gloss/sys_faccessat.c \
	gloss/sys_fork.c \
	gloss/sys_fstat.c \
	gloss/sys_fstatat.c \
	gloss/sys_ftime.c \
	gloss/sys_getcwd.c \
	gloss/sys_getpid.c \
	gloss/sys_gettimeofday.c \
	gloss/sys_isatty.c \
	gloss/sys_kill.c \
	gloss/sys_link.c \
	gloss/sys_lseek.c \
	gloss/sys_lstat.c \
	gloss/sys_open.c \
	gloss/sys_openat.c \
	gloss/sys_read.c \
	gloss/sys_sbrk.c \
	gloss/sys_stat.c \
	gloss/sys_sysconf.c \
	gloss/sys_times.c \
	gloss/sys_unlink.c \
	gloss/sys_utime.c \
	gloss/sys_wait.c \
	gloss/sys_write.c

endif

########################################################
# Clean
########################################################

clean-local:
	-rm -rf metal/machine.h metal/machine/inline.h
	-rm -rf metal/machine/platform.h
