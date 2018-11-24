#ifndef _BSP_LIBWRAP_WEAK_UNDER_ALIAS_H
#define _BSP_LIBWRAP_WEAK_UNDER_ALIAS_H

#define weak_under_alias(name) \
  extern __typeof (__wrap_##name) __wrap__##name __attribute__ ((weak, alias ("__wrap_"#name)))

#endif
