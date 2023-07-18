# libslirp

libslirp is a user-mode networking library used by virtual machines,
containers or various tools.

## Getting Started

### Prerequisites

A C compiler, meson and glib2 development libraries.

(see also [.gitlab-ci.yml](.gitlab-ci.yml) DEPS variable for the list
of dependencies on Fedora)

### Building

You may build and install the shared library with meson:

``` sh
meson build
ninja -C build install
```
And configure QEMU with --enable-slirp=system to link against it.

(QEMU may build with the submodule static library using --enable-slirp=git)

### Testing

Unfortunately, there are no automated tests available.

You may run QEMU ``-net user`` linked with your development version.

## Contributing

Feel free to open issues on the [project
issues](https://gitlab.freedesktop.org/slirp/libslirp/issues) page.

You may clone the [gitlab
project](https://gitlab.freedesktop.org/slirp/libslirp) and create a
merge request.

Contributing with gitlab allows gitlab workflow, tracking issues,
running CI etc.

Alternatively, you may send patches to slirp@lists.freedesktop.org
mailing list.

## Versioning

We intend to use [libtool's
versioning](https://www.gnu.org/software/libtool/manual/html_node/Updating-version-info.html)
for the shared libraries and use [SemVer](http://semver.org/) for
project versions.

For the versions available, see the [tags on this
repository](https://gitlab.freedesktop.org/slirp/libslirp/releases).

## License

See the [COPYRIGHT](COPYRIGHT) file for details.
