// TASKING VX-toolset for ARM
// Project linker script file
// 
#if defined(__PROC_XMC4500X1024__)
#include "xmc45xx.lsl"
#elif defined(__PROC_XMC4400X512__)
#include "xmc44xx.lsl"
#elif defined(__PROC_XMC4200X256__)
#include "xmc42xx.lsl"
#else
#include <device.lsl>
#endif
section_layout ::linear
{
    group heap "heap" ( size = 100 );
}
section_layout ::linear
{
    group stack "stack" ( size = 2k );
}
