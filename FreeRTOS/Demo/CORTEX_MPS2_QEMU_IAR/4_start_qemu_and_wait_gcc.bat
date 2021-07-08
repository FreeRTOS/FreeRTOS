qemu-system-arm -machine mps2-an385 -cpu cortex-m3 -kernel ./gcc-specific/output/RTOSDemo.elf -nographic -serial stdio -semihosting -semihosting-config enable=on,target=native -s -S
