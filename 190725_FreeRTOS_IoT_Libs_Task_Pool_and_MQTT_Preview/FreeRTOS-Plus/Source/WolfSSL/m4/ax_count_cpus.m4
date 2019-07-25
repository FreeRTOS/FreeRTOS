# ===========================================================================
#       http://www.gnu.org/software/autoconf-archive/ax_count_cpus.html
# ===========================================================================
#
# SYNOPSIS
#
#   AX_COUNT_CPUS
#
# DESCRIPTION
#
#   Attempt to count the number of processors present on the machine. If the
#   detection fails, then a value of 1 is assumed.
#
#   The value is placed in the CPU_COUNT variable.
#
# LICENSE
#
#   Copyright (c) 2012 Brian Aker <brian@tangent.org>
#   Copyright (c) 2008 Michael Paul Bailey <jinxidoru@byu.net>
#   Copyright (c) 2008 Christophe Tournayre <turn3r@users.sourceforge.net>
#
#   Copying and distribution of this file, with or without modification, are
#   permitted in any medium without royalty provided the copyright notice
#   and this notice are preserved. This file is offered as-is, without any
#   warranty.

#serial 10

  AC_DEFUN([AX_COUNT_CPUS],[
      AC_REQUIRE([AC_CANONICAL_HOST])
      AC_REQUIRE([AC_PROG_EGREP])
      AC_MSG_CHECKING([the number of available CPUs])
      CPU_COUNT="0"

      AS_CASE([$host_os],[
        *darwin*],[
        AS_IF([test -x /usr/sbin/sysctl],[
          sysctl_a=`/usr/sbin/sysctl -a 2>/dev/null| grep -c hw.cpu`
          AS_IF([test sysctl_a],[
            CPU_COUNT=`/usr/sbin/sysctl -n hw.ncpu`
            ])
          ])],[
        *linux*],[
        AS_IF([test "x$CPU_COUNT" = "x0" -a -e /proc/cpuinfo],[
          AS_IF([test "x$CPU_COUNT" = "x0" -a -e /proc/cpuinfo],[
            CPU_COUNT=`$EGREP -c '^processor' /proc/cpuinfo`
            ])
          ])
        ])

      AS_IF([test "x$CPU_COUNT" = "x0"],[
        CPU_COUNT="1"
        AC_MSG_RESULT( [unable to detect (assuming 1)] )
        ],[
        AC_MSG_RESULT( $CPU_COUNT )
        ])
      ])
