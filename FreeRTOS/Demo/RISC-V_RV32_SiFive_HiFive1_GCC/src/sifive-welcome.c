/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <stdio.h>
#include <metal/cpu.h>
#include <metal/led.h>
#include <metal/button.h>
#include <metal/switch.h>

#define RTC_FREQ    32768

struct metal_cpu *cpu0;
struct metal_interrupt *cpu_intr, *tmr_intr;
int tmr_id;
volatile uint32_t timer_isr_flag;

void display_banner (void) {

    printf("\n");
    printf("\n");
    printf("                  SIFIVE, INC.\n");
    printf("\n");
    printf("           5555555555555555555555555\n");
    printf("          5555                   5555\n");
    printf("         5555                     5555\n");
    printf("        5555                       5555\n");
    printf("       5555       5555555555555555555555\n");
    printf("      5555       555555555555555555555555\n");
    printf("     5555                             5555\n");
    printf("    5555                               5555\n");
    printf("   5555                                 5555\n");
    printf("  5555555555555555555555555555          55555\n");
    printf("   55555           555555555           55555\n");
    printf("     55555           55555           55555\n");
    printf("       55555           5           55555\n");
    printf("         55555                   55555\n");
    printf("           55555               55555\n");
    printf("             55555           55555\n");
    printf("               55555       55555\n");
    printf("                 55555   55555\n");
    printf("                   555555555\n");
    printf("                     55555\n");
    printf("                       5\n");
    printf("\n");

    printf("\n");
    printf("               Welcome to SiFive!\n");

}

void timer_isr (int id, void *data) {

    // Disable Timer interrupt
    metal_interrupt_disable(tmr_intr, tmr_id);

    // Flag showing we hit timer isr
    timer_isr_flag = 1;
}

void wait_for_timer(struct metal_led *which_led) {

    // clear global timer isr flag
    timer_isr_flag = 0;

    // Turn on desired LED
    metal_led_on(which_led);

    // Set timer
    metal_cpu_set_mtimecmp(cpu0, metal_cpu_get_mtime(cpu0) + RTC_FREQ);

    // Enable Timer interrupt
    metal_interrupt_enable(tmr_intr, tmr_id);

    // wait till timer triggers and isr is hit
    while (timer_isr_flag == 0){};

    timer_isr_flag = 0;

    // Turn off this LED
    metal_led_off(which_led);
}

int main (void)
{
    int rc, up_cnt, dn_cnt;
    struct metal_led *led0_red, *led0_green, *led0_blue;

    // This demo will toggle LEDs colors so we define them here
    led0_red = metal_led_get_rgb("LD0", "red");
    led0_green = metal_led_get_rgb("LD0", "green");
    led0_blue = metal_led_get_rgb("LD0", "blue");
    if ((led0_red == NULL) || (led0_green == NULL) || (led0_blue == NULL)) {
        printf("At least one of LEDs is null.\n");
        return 1;
    }

    // Enable each LED
    metal_led_enable(led0_red);
    metal_led_enable(led0_green);
    metal_led_enable(led0_blue);

    // All Off
    metal_led_off(led0_red);
    metal_led_off(led0_green);
    metal_led_off(led0_blue);

    // Lets get the CPU and and its interrupt
    cpu0 = metal_cpu_get(0);
    if (cpu0 == NULL) {
        printf("CPU null.\n");
        return 2;
    }
    cpu_intr = metal_cpu_interrupt_controller(cpu0);
    if (cpu_intr == NULL) {
        printf("CPU interrupt controller is null.\n");
        return 3;
    }
    metal_interrupt_init(cpu_intr);

    // display welcome banner
    display_banner();

    // Setup Timer and its interrupt so we can toggle LEDs on 1s cadence
    tmr_intr = metal_cpu_timer_interrupt_controller(cpu0);
    if (tmr_intr == NULL) {
        printf("TIMER interrupt controller is  null.\n");
        return 4;
    }
    metal_interrupt_init(tmr_intr);
    tmr_id = metal_cpu_timer_get_interrupt_id(cpu0);
    rc = metal_interrupt_register_handler(tmr_intr, tmr_id, timer_isr, cpu0);
    if (rc < 0) {
        printf("TIMER interrupt handler registration failed\n");
        return (rc * -1);
    }

    // Lastly CPU interrupt
    if (metal_interrupt_enable(cpu_intr, 0) == -1) {
        printf("CPU interrupt enable failed\n");
        return 6;
    }

    // Red -> Green -> Blue, repeat
    while (1) {

        // Turn on RED
        wait_for_timer(led0_red);

        // Turn on Green
        wait_for_timer(led0_green);

        // Turn on Blue
        wait_for_timer(led0_blue);
    }

    // return
    return 0;
}
