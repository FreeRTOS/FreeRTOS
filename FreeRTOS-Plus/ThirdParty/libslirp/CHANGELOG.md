# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [4.7.0] - 2022-04-26

### Added

  - Allow disabling the internal DHCP server !22
  - icmp: Support falling back on trying a SOCK_RAW socket !92
  - Support Unix sockets in hostfwd !103
  - IPv6 DNS proxying support !110
  - bootp: add support for UEFI HTTP boot !111
  - New callback that supports CFI better !117

### Fixed

  - dhcp: Always send DHCP_OPT_LEN bytes in options !97
  - Fix Haiku build !98 !99
  - Fix memory leak when using libresolv !100
  - Ensure sin6_scope_id is zero for global addresses !102
  - resolv: fix IPv6 resolution on Darwin !104
  - socket: Initialize so_type in socreate !109
  - Handle ECONNABORTED from recv !116

## [4.6.1] - 2021-06-18

### Fixed

 - Fix DHCP regression introduced in 4.6.0. !95

## [4.6.0] - 2021-06-14

### Added

 - mbuf: Add debugging helpers for allocation. !90

### Changed

 -  Revert "Set macOS deployment target to macOS 10.4". !93

### Fixed

 - mtod()-related buffer overflows (CVE-2021-3592 #44, CVE-2021-3593 #45,
   CVE-2021-3594 #47, CVE-2021-3595 #46).
 - poll_fd: add missing fd registration for UDP and ICMP
 - ncsi: make ncsi_calculate_checksum work with unaligned data. !89
 - Various typos and doc fixes. !88

## [4.5.0] - 2021-05-18

### Added

 - IPv6 forwarding. !62 !75 !77
 - slirp_neighbor_info() to dump the ARP/NDP tables. !71

### Changed

 - Lazy guest address resolution for IPv6. !81
 - Improve signal handling when spawning a child. !61
 - Set macOS deployment target to macOS 10.4. !72
 - slirp_add_hostfwd: Ensure all error paths set errno. !80
 - More API documentation.

### Fixed

 - Assertion failure on unspecified IPv6 address. !86
 - Disable polling for PRI on MacOS, fixing some closing streams issues. !73 
 - Various memory leak fixes on fastq/batchq. !68
 - Memory leak on IPv6 fast-send. !67
 - Slow socket response on Windows. !64
 - Misc build and code cleanups. !60 !63 !76 !79 !84

## [4.4.0] - 2020-12-02

### Added

 - udp, udp6, icmp: handle TTL value. !48
 - Enable forwarding ICMP errors. !49
 - Add DNS resolving for iOS. !54

### Changed

 - Improve meson subproject() support. !53
 - Removed Makefile-based build system. !56

### Fixed

 - socket: consume empty packets. !55
 - check pkt_len before reading protocol header (CVE-2020-29129). !57
 - ip_stripoptions use memmove (fixes undefined behaviour). !47
 - various Coverity-related changes/fixes.

## [4.3.1] - 2020-07-08

### Changed

 - A silent truncation could occur in `slirp_fmt()`, which will now print a
   critical message. See also #22.

### Fixed

 - CVE-2020-10756 - Drop bogus IPv6 messages that could lead to data leakage.
   See !44 and !42.
 - Fix win32 builds by using the SLIRP_PACKED definition.
 - Various coverity scan errors fixed. !41
 - Fix new GCC warnings. !43

## [4.3.0] - 2020-04-22

### Added

 - `SLIRP_VERSION_STRING` macro, with the git sha suffix when building from git
 - `SlirpConfig.disable_dns`, to disable DNS redirection #16

### Changed

 - `slirp_version_string()` now has the git sha suffix when building form git
 - Limit DNS redirection to port 53 #16

### Fixed

 - Fix build regression with mingw & NetBSD
 - Fix use-afte-free in `ip_reass()` (CVE-2020-1983)

## [4.2.0] - 2020-03-17

### Added

 - New API function `slirp_add_unix`: add a forward rule to a Unix socket.
 - New API function `slirp_remove_guestfwd`: remove a forward rule previously
   added by `slirp_add_exec`, `slirp_add_unix` or `slirp_add_guestfwd`
 - New `SlirpConfig.outbound_addr{,6}` fields to bind output socket to a
   specific address

### Changed

 - socket: do not fallback on host loopback if `get_dns_addr()` failed
   or the address is in slirp network

### Fixed

 - ncsi: fix checksum OOB memory access
 - `tcp_emu()`: fix OOB accesses
 - tftp: restrict relative path access
 - state: fix loading of guestfwd state

## [4.1.0] - 2019-12-02

### Added

 - The `slirp_new()` API, simpler and more extensible than `slirp_init()`.
 - Allow custom MTU configuration.
 - Option to disable host loopback connections.
 - CI now runs scan-build too.

### Changed

 - Disable `tcp_emu()` by default. `tcp_emu()` is known to have caused
   several CVEs, and not useful today in most cases. The feature can
   be still enabled by setting `SlirpConfig.enable_emu` to true.
 - meson build system is now `subproject()` friendly.
 - Replace remaining `malloc()`/`free()` with glib (which aborts on OOM)
 - Various code cleanups.

### Deprecated

 - The `slirp_init()` API.

### Fixed

 - `getpeername()` error after `shutdown(SHUT_WR)`.
 - Exec forward: correctly parse command lines that contain spaces.
 - Allow 0.0.0.0 destination address.
 - Make host receive broadcast packets.
 - Various memory related fixes (heap overflow, leaks, NULL
   dereference).
 - Compilation warnings, dead code.

## [4.0.0] - 2019-05-24

### Added

 - Installable as a shared library.
 - meson build system
   (& make build system for in-tree QEMU integration)

### Changed

 - Standalone project, removing any QEMU dependency.
 - License clarifications.

[Unreleased]: https://gitlab.freedesktop.org/slirp/libslirp/compare/v4.7.0...master
[4.7.0]: https://gitlab.freedesktop.org/slirp/libslirp/compare/v4.6.1...v4.7.0
[4.6.1]: https://gitlab.freedesktop.org/slirp/libslirp/compare/v4.6.0...v4.6.1
[4.6.0]: https://gitlab.freedesktop.org/slirp/libslirp/compare/v4.5.0...v4.6.0
[4.5.0]: https://gitlab.freedesktop.org/slirp/libslirp/compare/v4.4.0...v4.5.0
[4.4.0]: https://gitlab.freedesktop.org/slirp/libslirp/compare/v4.3.1...v4.4.0
[4.3.1]: https://gitlab.freedesktop.org/slirp/libslirp/compare/v4.3.0...v4.3.1
[4.3.0]: https://gitlab.freedesktop.org/slirp/libslirp/compare/v4.2.0...v4.3.0
[4.2.0]: https://gitlab.freedesktop.org/slirp/libslirp/compare/v4.1.0...v4.2.0
[4.1.0]: https://gitlab.freedesktop.org/slirp/libslirp/compare/v4.0.0...v4.1.0
[4.0.0]: https://gitlab.freedesktop.org/slirp/libslirp/commits/v4.0.0
