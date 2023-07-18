project('libslirp', 'c',
  version : '4.7.0',
  license : 'BSD-3-Clause',
  default_options : ['warning_level=1', 'c_std=gnu99'],
  meson_version : '>= 0.50',
)

version = meson.project_version()
varr = version.split('.')
major_version = varr[0]
minor_version = varr[1]
micro_version = varr[2]

conf = configuration_data()
conf.set('SLIRP_MAJOR_VERSION', major_version)
conf.set('SLIRP_MINOR_VERSION', minor_version)
conf.set('SLIRP_MICRO_VERSION', micro_version)

cc = meson.get_compiler('c')

if cc.get_argument_syntax() != 'msvc'
  r = run_command('build-aux/git-version-gen',
                  '@0@/.tarball-version'.format(meson.current_source_dir()),
                  check : false)

  full_version = r.stdout().strip()
  if r.returncode() != 0 or full_version.startswith('UNKNOWN')
    full_version = meson.project_version()
  elif not full_version.startswith(meson.project_version())
    error('meson.build project version @0@ does not match git-describe output @1@'
          .format(meson.project_version(), full_version))
  endif
else
  full_version = meson.project_version()
endif
conf.set_quoted('SLIRP_VERSION_STRING', full_version + get_option('version_suffix'))

# libtool versioning - this applies to libslirp
#
# See http://sources.redhat.com/autobook/autobook/autobook_91.html#SEC91 for details
#
# - If interfaces have been changed or added, but binary compatibility
#   has been preserved, change:
#      CURRENT += 1
#      REVISION = 0
#      AGE += 1
# - If binary compatibility has been broken (eg removed or changed
#   interfaces), change:
#      CURRENT += 1
#      REVISION = 0
#      AGE = 0
# - If the interface is the same as the previous version, but bugs are
#   fixed, change:
#      REVISION += 1
lt_current = 4
lt_revision = 0
lt_age = 4
lt_version = '@0@.@1@.@2@'.format(lt_current - lt_age, lt_age, lt_revision)

host_system = host_machine.system()

glib_dep = dependency('glib-2.0')

add_project_arguments(cc.get_supported_arguments('-Wmissing-prototypes', '-Wstrict-prototypes',
                                                 '-Wredundant-decls', '-Wundef', '-Wwrite-strings'),
                      language: 'c', native: false)

platform_deps = []

if host_system == 'windows'
  platform_deps += [
    cc.find_library('ws2_32'),
    cc.find_library('iphlpapi')
  ]
elif host_system == 'darwin'
  platform_deps += [
    cc.find_library('resolv')
  ]
elif host_system == 'haiku'
  platform_deps += [
    cc.find_library('network')
  ]
endif

cargs = [
  '-DG_LOG_DOMAIN="Slirp"',
  '-DBUILDING_LIBSLIRP',
]

if cc.check_header('valgrind/valgrind.h')
  cargs += [ '-DHAVE_VALGRIND=1' ]
endif

sources = [
  'src/arp_table.c',
  'src/bootp.c',
  'src/cksum.c',
  'src/dhcpv6.c',
  'src/dnssearch.c',
  'src/if.c',
  'src/ip6_icmp.c',
  'src/ip6_input.c',
  'src/ip6_output.c',
  'src/ip_icmp.c',
  'src/ip_input.c',
  'src/ip_output.c',
  'src/mbuf.c',
  'src/misc.c',
  'src/ncsi.c',
  'src/ndp_table.c',
  'src/sbuf.c',
  'src/slirp.c',
  'src/socket.c',
  'src/state.c',
  'src/stream.c',
  'src/tcp_input.c',
  'src/tcp_output.c',
  'src/tcp_subr.c',
  'src/tcp_timer.c',
  'src/tftp.c',
  'src/udp.c',
  'src/udp6.c',
  'src/util.c',
  'src/version.c',
  'src/vmstate.c',
]

mapfile = 'src/libslirp.map'
vflag = []
vflag_test = '-Wl,--version-script,@0@/@1@'.format(meson.current_source_dir(), mapfile)
if cc.has_link_argument(vflag_test)
  vflag += vflag_test
endif

install_devel = not meson.is_subproject()

configure_file(
  input : 'src/libslirp-version.h.in',
  output : 'libslirp-version.h',
  install : install_devel,
  install_dir : join_paths(get_option('includedir'), 'slirp'),
  configuration : conf
)

lib = library('slirp', sources,
  version : lt_version,
  c_args : cargs,
  link_args : vflag,
  link_depends : mapfile,
  dependencies : [glib_dep, platform_deps],
  install : install_devel or get_option('default_library') == 'shared',
)

pingtest = executable('pingtest', 'test/pingtest.c',
  link_with: [ lib ],
  include_directories: [ 'src' ],
  dependencies : [ platform_deps ]
)

test('ping', pingtest)

ncsitest = executable('ncsitest', 'test/ncsitest.c',
  link_with: [lib],
  include_directories: ['src'],
  dependencies: [glib_dep, platform_deps]
)

test('ncsi', ncsitest)

if install_devel
  install_headers(['src/libslirp.h'], subdir : 'slirp')

  pkg = import('pkgconfig')

  pkg.generate(
    version : version,
    libraries : lib,
    requires : [
      'glib-2.0',
    ],
    name : 'slirp',
    description : 'User-space network stack',
    filebase : 'slirp',
    subdirs : 'slirp',
  )
else
  if get_option('default_library') == 'both'
    lib = lib.get_static_lib()
  endif
  libslirp_dep = declare_dependency(
    include_directories: include_directories('.', 'src'),
    link_with: lib)
endif
