qemu-system-arm -machine mps2-an385 -cpu cortex-m3 -kernel ./Debug/Exe/RTOSDemo.elf -nographic -serial stdio -semihosting -semihosting-config enable=on,target=native
