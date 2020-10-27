# Generate diffs between FreeRTOS source and proofs

## Requirements

  - python3
  - ctags 5.8
  - diff 3.4+
  - [diff2html](https://diff2html.xyz/)

## Instructions

The following will extract per-function files from the original FreeRTOS source
implementation and the proof directory.


```
cd scripts
./generate_diff_files.sh
# will extract to ./FreeRTOS-Kernel/generated and ./queue/generated and ./list/generated
```

Then use `diff` for a side-by-side comparison.  Note that the `--color=always`
flag needs v3.4+:

```
diff --color=always --width=$COLUMNS --suppress-common-lines --side-by-side FreeRTOS-Kernel/generated queue/generated | less -r
diff --color=always --width=$COLUMNS --suppress-common-lines --side-by-side FreeRTOS-Kernel/generated list/generated | less -r
```

Or generate a html report using `diff2html`:

```
diff -u FreeRTOS-Kernel/generated queue/generated | diff2html -i stdin
diff -u FreeRTOS-Kernel/generated list/generated | diff2html -i stdin
```

The expectation is that the proofs make minimal changes to the original source
implementation in the form of:

  - VeriFast annotations `/*@...@*/` and `//*...`
  - Additional comments explaining the proof `/*...*/`
  - Flagged changes within `#if[n]def VERIFAST`
