# MEE Specification

The MEE is designed to provide a source-level compatibility for
bare-metal code between platforms.  This specification defines the
publicly available API.  The intent is that this API is stable so users
can rely on it not changing, but we're not going to make any guarantees
about it until our 1.0.0 release.

Note that the MEE does not define an ABI -- specifically that means that
binaries will not be compatible between different versions of the MBI,
or between different platforms.

## User API

The core of the MEE is a C API that is designed to allow programmers to
write portable bare-metal embedded code.

Any symbol beginning with `__mee_` is internal to the MEE and must not
be called or defined by user code.  Symbols beginning with `mee_` are
public interfaces and can be considered to be a stable API.  The best
documentation for most of these symbols are found in the code, but some
is listed below.

### Clock Interface

The clock interface allows for controlling the rate of various clocks in
the system.  Clocks are defined by a pointer to a `struct mee_clock`, the
contents of which is implementation defined.  Users of the clock
interface must call the functions defined below in order to interact
with a `struct mee_clock *`.

Note that no mechanism for obtaining a pointer to a `struct mee_clock`
has been defined, making it impossible to call any of these functions
without invoking implementation-defined behavior.

#### `long mee_clock_get_rate_hz(const struct mee_clock *clock)`

Returns the clock rate of the given clock, in Hz.

#### `long mee_clock_set_rate_hz(const struct mee_clock *clock, long hz)`

Attempts to set the rate of the given clock to the given value, in Hz.
Returns the rate the given clock was actually set to, which may be
different than the requested rate.  There are no hard requirements on
what clock rates can be set, but it's expected that a best effort
approach is taken to match the caller's desired clock rate.

#### `void mee_clock_register_rate_change_callback(struct mee_clock *clk, int (*cb)(struct mee_clock *, void *), void *priv)`

Registers a function (and an associated opaque data block) that will be
called whenever the giver clock's rate has been changed.  This function
will be called after the driver-specific clock frequency changing code
has returned, but before the caller of `mee_clock_set_rate_hz()` has
been returned to.

It's not guaranteed that the given clock's rate will have actually
changed every time the given function is called, but it's guaranteed
that the given function will be called every time the given clock's rate
has been changed.

### Timer Interface

The timer interface allows for access of various timers values in
the system.  Timers are defined by a pointer to a `struct mee_timer`, the
contents of which is implementation defined.  Users of the timer
interface must call the functions defined below in order to interact
with a `struct mee_timer *`.

Note that no mechanism for obtaining a pointer to a `struct mee_timer`
has been defined, making it impossible to call any of these functions
without invoking implementation-defined behavior.

#### `int mee_timer_get_cyclecount(int hartid, unsigned long long *mcc)`

Returns the cpu machine cycle count of a given hartid.

#### `int mee_timer_get_timebase_frequency(int hartid, unsigned long long *timebase)`

Returns the timebase frequency of a given hartid, s.t a time elapse duration can determined.
For example, a timebase frequency of 1000000 (1MHz) will have each cycle count of 1s.

#### `void mee_timer_init(const struct mee_timer *timer, unsigned long long timebase)`

Setup the timebase frequency for a given timer, in Hz.

### Power Control Interface

The MEE defines a mechanism to control the power state of a given
machine.  The interface is currently quite simple: it's just the
`mee_shutdown()` function.

#### `void mee_shutdown(int code) __attribute__((noreturn))`

Terminates execution of this program, attempting to pass the given code
to whomever may be looking.  The code `0` indicates success, while all
other codes indicate failure.  The exact mechanism by which execution
terminates is implementation defined, but some examples include:

* Spinning in an infinite loop.
* Printing the return code to standard out and spinning in an infinite
  loop.
* Toggling an external I/O to disable the power to the core.
* Poking through a hole to the host that's providing this environment
  and indicating success or failure.

### TTY Interface

The MEE provides an terminal interface.  This interface is designed to
provide a simple mechanism for getting text-based data outside of the
MEE -- in other words, it's designed to be used to implement C library
functions like `printf()`.

#### `int mee_tty_putc(unsigned char c);`

Writes the given character to the default terminal, returning 0 on
success or -1 on failure.

### UART Interface

The UART interface allows users of the MEE to control

Note that there is no mechanism for obtaining a pointer to a `struct
mee_uart` without invoking implementation-defined behavior, thus making
calling any of these functions impossible.

#### `int mee_uart_init(struct mee_uart *uart)`

Initializes the given UART.  This must be called exactly once before any
other function on this UART can be called.  It is invalid to initialize
a UART more than once.

#### `int mee_uart_putc(struct mee_uart *uart, unsigned char c)`

Writes the given character to the given UART, returning 0 on success and
-1 on failure.

#### `int mee_uart_getc(struct mee_uart *uart, unsigned char *c)`

Reads a character from the given UART, storing it at the given character
pointer.  This returns 0 on success and -1 on failure.

#### `int mee_uart_get_baud_rate(struct mee_uart *uart)`

Obtains the baud rate of the given UART, or `-1` to signify an error.

#### `int mee_uart_set_baud_rate(struct mee_uart *uart, int baud_rate)`

Sets the baud rate of the given UART.  Returns 0 on success, or -1 on
failure.  Failure to set the baud rate can render the UART unusable
until a subsequent coll to `mee_uart_set_baud_rate()` returns success.

### C Startup Interface

The MEE handles entering the C library's start routine, which is defined
by the symbol `_start`.  This symbol must be defined by the C library in
order to allow the MEE to do anything meaningful.

The MEE follows the standard RISC-V bootloader ABI when calling
`_start`:

* `a0` contains the hart ID.
* `a1` contains a pointer to the machine description.  The MEE always
  sets this to NULL, as machines are described statically.
* `a2` contains a callback that should be called from within the child
  environment after it has initialized itself.

This can be described as a the C function `void _start(long hartid,
unsigned char *dtb, void (*after_init)(void))'.  Note that the MEE does
not initialize a C environment and therefor this cannot actually be a C
function -- for example, there may not be a stack.
