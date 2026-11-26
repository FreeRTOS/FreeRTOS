# FreeRTOS Common/Minimal Demo on Espressif Targets

A port of the FreeRTOS `Common/Minimal` test bar to ESP-IDF.  A Check
task polls each demo task's `xAreXxxStillRunning()` probe on a fixed
cycle and reports per-test results in a Unity-style format.

## Quickstart

```sh
. $IDF_PATH/export.sh
idf.py set-target esp32 build flash monitor
```

Per-cycle output:

```
----- Cycle 2 (tick 6028) -----
test_MessageBuffer:PASS
test_TaskNotification:PASS
...
test_IntQueue:PASS
Cycle 2: 19 PASS  0 FAIL
```

After the configured run duration, a final summary is printed:

```
-----------------------
Demo run complete: 60 cycles, 180 s.

Per-test totals (PASS / FAIL over 60 cycles):
  test_MessageBuffer         60 /     0
  ...
  test_IntQueue              60 /     0

1140 Tests 0 Failures
OK
-----------------------
```

## Compile-time knobs

| Macro                  | Default | Effect                                          |
| ---------------------- | ------- | ----------------------------------------------- |
| `mainDEMO_DURATION_S`  | `180`   | Total runtime in seconds.  `0` runs unbounded.  |

Override via `EXTRA_CFLAGS`:

```sh
idf.py build -DEXTRA_CFLAGS="-DmainDEMO_DURATION_S=3600"   # 1 hour
idf.py build -DEXTRA_CFLAGS="-DmainDEMO_DURATION_S=0"      # forever
```

## Config sweep

Three sweep configs, selected with `-DSDKCONFIG_DEFAULTS`:

```sh
idf.py -DSDKCONFIG_DEFAULTS="sdkconfig.defaults;sdkconfig.ci.smp_multi_prio" \
       set-target esp32 build
```

| Config                          | Coverage                                              |
| ------------------------------- | ----------------------------------------------------- |
| `sdkconfig.ci.smp_single_prio`  | Primary config.  Dual-core, single-priority.          |
| `sdkconfig.ci.smp_multi_prio`   | Dual-core, multi-priority scheduling.                 |
| `sdkconfig.ci.smp_unicore`      | Single-core mode.                                     |

`sdkconfig.defaults` already selects the primary config, so each sweep file
carries only the setting it changes.

The demo requires `CONFIG_FREERTOS_SMP=y`.  `Common/Minimal` calls
`portENTER_CRITICAL()` with no arguments, which ESP-IDF's non-SMP FreeRTOS
does not provide.

## Multi-target support

Add an SoC-specific overrides file alongside `sdkconfig.defaults.esp32`:

```
sdkconfig.defaults.esp32s3
sdkconfig.defaults.esp32p4
...
```

`idf.py set-target <target>` picks up the matching one.

## Excluded tests

Some `Common/Minimal` tests assume a higher priority task blocks a lower
priority one from running, which does not hold when
`configRUN_MULTIPLE_PRIORITIES` is 1 on more than one core.  Those tests are
not created in that configuration and simply do not appear in the output; see
`mainENABLE_ORDER_DEPENDENT_TESTS` in `main/main_full.c`.  The cycle totals
differ between sweeps for that reason.

## Pass criterion

The final summary line must end with `OK`.  Any `FAIL` in any cycle is
reported in the per-test totals and flips the verdict to `FAILED`.
