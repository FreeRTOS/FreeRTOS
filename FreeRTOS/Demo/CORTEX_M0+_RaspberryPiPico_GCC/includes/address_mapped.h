#ifndef _ADDRESS_MAPPED_H_
#define _ADDRESS_MAPPED_H_

#include "types.h"
#include "regs/addressmap.h"

#define check_hw_layout(type, member, offset) static_assert(offsetof(type, member) == (offset), "hw offset mismatch")
#define check_hw_size(type, size) static_assert(sizeof(type) == (size), "hw size mismatch")

typedef volatile uint32_t io_rw_32;
typedef const volatile uint32_t io_ro_32;
typedef volatile uint32_t io_wo_32;
typedef volatile uint16_t io_rw_16;
typedef const volatile uint16_t io_ro_16;
typedef volatile uint16_t io_wo_16;
typedef volatile uint8_t io_rw_8;
typedef const volatile uint8_t io_ro_8;
typedef volatile uint8_t io_wo_8;

typedef volatile uint8_t *const ioptr;
typedef ioptr const const_ioptr;

// Untyped conversion alias pointer generation macros
#define hw_set_alias_untyped(addr) ((void *)(REG_ALIAS_SET_BITS | (uintptr_t)(addr)))
#define hw_clear_alias_untyped(addr) ((void *)(REG_ALIAS_CLR_BITS | (uintptr_t)(addr)))
#define hw_xor_alias_untyped(addr) ((void *)(REG_ALIAS_XOR_BITS | (uintptr_t)(addr)))

// Typed conversion alias pointer generation macros
#define hw_set_alias(p) ((typeof(p))hw_set_alias_untyped(p))
#define hw_clear_alias(p) ((typeof(p))hw_clear_alias_untyped(p))
#define hw_xor_alias(p) ((typeof(p))hw_xor_alias_untyped(p))

/*! \brief Atomically set the specified bits to 1 in a HW register
 *  \ingroup hardware_base
 *
 * \param addr Address of writable register
 * \param mask Bit-mask specifying bits to set
 */
inline static void hw_set_bits(io_rw_32 *addr, uint32_t mask) {
    *(io_rw_32 *) hw_set_alias_untyped((volatile void *) addr) = mask;
}

/*! \brief Atomically clear the specified bits to 0 in a HW register
 *  \ingroup hardware_base
 *
 * \param addr Address of writable register
 * \param mask Bit-mask specifying bits to clear
 */
inline static void hw_clear_bits(io_rw_32 *addr, uint32_t mask) {
    *(io_rw_32 *) hw_clear_alias_untyped((volatile void *) addr) = mask;
}

/*! \brief Atomically flip the specified bits in a HW register
 *  \ingroup hardware_base
 *
 * \param addr Address of writable register
 * \param mask Bit-mask specifying bits to invert
 */
inline static void hw_xor_bits(io_rw_32 *addr, uint32_t mask) {
    *(io_rw_32 *) hw_xor_alias_untyped((volatile void *) addr) = mask;
}

/*! \brief Set new values for a sub-set of the bits in a HW register
 *  \ingroup hardware_base
 *
 * Sets destination bits to values specified in \p values, if and only if corresponding bit in \p write_mask is set
 *
 * Note: this method allows safe concurrent modification of *different* bits of
 * a register, but multiple concurrent access to the same bits is still unsafe.
 *
 * \param addr Address of writable register
 * \param values Bits values
 * \param write_mask Mask of bits to change
 */
inline static void hw_write_masked(io_rw_32 *addr, uint32_t values, uint32_t write_mask) {
    hw_xor_bits(addr, (*addr ^ values) & write_mask);
}

#endif
