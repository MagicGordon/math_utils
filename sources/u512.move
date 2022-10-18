/// The implementation of large numbers written in Move language.
/// Code derived from original work by Andrew Poelstra <apoelstra@wpsoftware.net>
///
/// Rust Bitcoin Library
/// Written in 2014 by
///	   Andrew Poelstra <apoelstra@wpsoftware.net>
///
/// To the extent possible under law, the author(s) have dedicated all
/// copyright and related and neighboring rights to this software to
/// the public domain worldwide. This software is distributed without
/// any warranty.
///
/// Simplified impl by Parity Team - https://github.com/paritytech/parity-common/blob/master/uint/src/uint.rs
///
/// Features:
///     * mul
///     * div
///     * add
///     * sub
///     * shift left
///     * shift right
///     * bitwise and, xor, or.
///     * compare
///     * if math overflows the contract crashes.
///
/// Would be nice to help with the following TODO list:
/// * pow() , sqrt().
/// * math funcs that don't abort on overflows, but just returns reminders.
/// * Export of low_u128 (see original implementation).
/// * Export of low_u64 (see original implementation).
/// * Gas Optimisation:
///     * We can optimize by replacing bytecode, as far as we know Move VM itself support slices, so probably
///       we can try to replace parts works with (`v0`,`v1`,`v2`,`v3` etc) works.
///     * More?
/// * More tests (see current tests and TODOs i left):
///     * u256_arithmetic_test - https://github.com/paritytech/bigint/blob/master/src/uint.rs#L1338
///     * More from - https://github.com/paritytech/bigint/blob/master/src/uint.rs
/// * Division:
///     * Could be improved with div_mod_small (current version probably would took a lot of resources for small numbers).
///     * Also could be improved with Knuth, TAOCP, Volume 2, section 4.3.1, Algorithm D (see link to Parity above).
module math_utils::u512 {
    // Errors.
    /// When can't cast `U512` to `u128` (e.g. number too large).
    const ECAST_OVERFLOW: u64 = 0;

    /// When trying to get or put word into U256 but it's out of index.
    const EWORDS_OVERFLOW: u64 = 1;

    /// When math overflows.
    const EOVERFLOW: u64 = 2;

    /// When attempted to divide by zero.
    const EDIV_BY_ZERO: u64 = 3;

    // Constants.

    /// Max `u64` value.
    const U64_MAX: u128 = 18446744073709551615;

    /// Max `u128` value.
    const U128_MAX: u128 = 340282366920938463463374607431768211455;

    /// Total words in `U512` (64 * 8 = 512).
    const WORDS: u64 = 8;

    /// When both `U512` equal.
    const EQUAL: u8 = 0;

    /// When `a` is less than `b`.
    const LESS_THAN: u8 = 1;

    /// When `b` is greater than `b`.
    const GREATER_THAN: u8 = 2;

    // Data structs.

    /// The `U512` resource.
    /// Contains 8 u64 numbers.
    struct U512 has copy, drop, store {
        v0: u64,
        v1: u64,
        v2: u64,
        v3: u64,
        v4: u64,
        v5: u64,
        v6: u64,
        v7: u64,
    }

    /// Double `U512` used for multiple (to store overflow).
    struct DU512 has copy, drop, store {
        v0: u64,
        v1: u64,
        v2: u64,
        v3: u64,
        v4: u64,
        v5: u64,
        v6: u64,
        v7: u64,
        v8: u64,
        v9: u64,
        v10: u64,
        v11: u64,
        v12: u64,
        v13: u64,
        v14: u64,
        v15: u64,
    }

    // Public functions.
    /// Adds two `U512` and returns sum.
    public fun add(a: U512, b: U512): U512 {
        let ret = zero();
        let carry = 0u64;

        let i = 0;
        while (i < WORDS) {
            let a1 = get(&a, i);
            let b1 = get(&b, i);

            if (carry != 0) {
                let (res1, is_overflow1) = overflowing_add(a1, b1);
                let (res2, is_overflow2) = overflowing_add(res1, carry);
                put(&mut ret, i, res2);

                carry = 0;
                if (is_overflow1) {
                    carry = carry + 1;
                };

                if (is_overflow2) {
                    carry = carry + 1;
                }
            } else {
                let (res, is_overflow) = overflowing_add(a1, b1);
                put(&mut ret, i, res);

                carry = 0;
                if (is_overflow) {
                    carry = 1;
                };
            };

            i = i + 1;
        };

        assert!(carry == 0, EOVERFLOW);

        ret
    }

    /// Convert `U512` to `u128` value if possible (otherwise it aborts).
    public fun as_u128(a: U512): u128 {
        assert!(a.v2 == 0 && a.v3 == 0 && a.v4 == 0 && a.v5 == 0 && a.v6 == 0 && a.v7 == 0, ECAST_OVERFLOW);
        ((a.v1 as u128) << 64) + (a.v0 as u128)
    }

    /// Convert `U512` to `u64` value if possible (otherwise it aborts).
    public fun as_u64(a: U512): u64 {
        assert!(a.v1 == 0 && a.v2 == 0 && a.v3 == 0 && a.v4 == 0 && a.v5 == 0 && a.v6 == 0 && a.v7 == 0, ECAST_OVERFLOW);
        a.v0
    }

    /// Compares two `U512` numbers.
    public fun compare(a: &U512, b: &U512): u8 {
        let i = WORDS;
        while (i > 0) {
            i = i - 1;
            let a1 = get(a, i);
            let b1 = get(b, i);

            if (a1 != b1) {
                if (a1 < b1) {
                    return LESS_THAN
                } else {
                    return GREATER_THAN
                }
            }
        };

        EQUAL
    }

    /// Returns a `U512` from `u64` value.
    public fun from_u64(val: u64): U512 {
        from_u128((val as u128))
    }

    /// Returns a `U512` from `u128` value.
    public fun from_u128(val: u128): U512 {
        let (a2, a1) = split_u128(val);

        U512 {
            v0: a1,
            v1: a2,
            v2: 0,
            v3: 0,
            v4: 0,
            v5: 0,
            v6: 0,
            v7: 0,
        }
    }

    /// Convert `DU512` to `U512`.
    fun du512_to_u512(a: DU512): (U512, bool) {
        let b = U512 {
            v0: a.v0,
            v1: a.v1,
            v2: a.v2,
            v3: a.v3,
            v4: a.v4,
            v5: a.v5,
            v6: a.v6,
            v7: a.v7,
        };

        let overflow = false;
        if (a.v8 != 0 || a.v9 != 0 || a.v10 != 0 || a.v11 != 0 || a.v12 != 0 || a.v13 != 0 || a.v14 != 0 || a.v15 != 0) {
            overflow = true;
        };

        (b, overflow)
    }

    /// Multiples two `U512`.
    public fun mul(a: U512, b: U512): U512 {
        let ret = DU512 {
            v0: 0,
            v1: 0,
            v2: 0,
            v3: 0,
            v4: 0,
            v5: 0,
            v6: 0,
            v7: 0,
            v8: 0,
            v9: 0,
            v10: 0,
            v11: 0,
            v12: 0,
            v13: 0,
            v14: 0,
            v15: 0,
        };

        let i = 0;
        while (i < WORDS) {
            let carry = 0u64;
            let b1 = get(&b, i);

            let j = 0;
            while (j < WORDS) {
                let a1 = get(&a, j);

                if (a1 != 0 || carry != 0) {
                    let (hi, low) = split_u128((a1 as u128) * (b1 as u128));

                    let overflow = {
                        let existing_low = get_d(&ret, i + j);
                        let (low, o) = overflowing_add(low, existing_low);
                        put_d(&mut ret, i + j, low);
                        if (o) {
                            1
                        } else {
                            0
                        }
                    };

                    carry = {
                        let existing_hi = get_d(&ret, i + j + 1);
                        let hi = hi + overflow;
                        let (hi, o0) = overflowing_add(hi, carry);
                        let (hi, o1) = overflowing_add(hi, existing_hi);
                        put_d(&mut ret, i + j + 1, hi);

                        if (o0 || o1) {
                            1
                        } else {
                            0
                        }
                    };
                };

                j = j + 1;
            };

            i = i + 1;
        };
        let (r, overflow) = du512_to_u512(ret);
        assert!(!overflow, EOVERFLOW);
        r
    }

    /// Subtracts two `U512`, returns result.
    public fun sub(a: U512, b: U512): U512 {
        let ret = zero();

        let carry = 0u64;

        let i = 0;
        while (i < WORDS) {
            let a1 = get(&a, i);
            let b1 = get(&b, i);

            if (carry != 0) {
                let (res1, is_overflow1) = overflowing_sub(a1, b1);
                let (res2, is_overflow2) = overflowing_sub(res1, carry);
                put(&mut ret, i, res2);

                carry = 0;
                if (is_overflow1) {
                    carry = carry + 1;
                };

                if (is_overflow2) {
                    carry = carry + 1;
                }
            } else {
                let (res, is_overflow) = overflowing_sub(a1, b1);
                put(&mut ret, i, res);

                carry = 0;
                if (is_overflow) {
                    carry = 1;
                };
            };

            i = i + 1;
        };

        assert!(carry == 0, EOVERFLOW);
        ret
    }

    /// Divide `a` by `b`.
    public fun div(a: U512, b: U512): U512 {
        let ret = zero();

        let a_bits = bits(&a);
        let b_bits = bits(&b);

        assert!(b_bits != 0, EDIV_BY_ZERO); // DIVIDE BY ZERO.
        if (a_bits < b_bits) {
            // Immidiatelly return.
            return ret
        };

        let shift = a_bits - b_bits;
        b = shl(b, (shift as u8));

        loop {
            let cmp = compare(&a, &b);
            if (cmp == GREATER_THAN || cmp == EQUAL) {
                let index = shift / 64;
                let m = get(&ret, index);
                let c = m | 1 << ((shift % 64) as u8);
                put(&mut ret, index, c);

                a = sub(a, b);
            };

            b = shr(b, 1);
            if (shift == 0) {
                break
            };

            shift = shift - 1;
        };

        ret
    }

    /// Newton's method of integer square root.
    fun sqrt(value: U512): U512 {
        
        let guess: U512 = shr(add(value, from_u128(1)),1);
        let res: U512 = value;
        while( compare(&guess, &res) == LESS_THAN ){
            res = guess;
            guess = shr(add(div(value, guess), guess), 1);
        };

        res
    }

    /// Binary xor `a` by `b`.
    fun bitxor(a: U512, b: U512): U512 {
        let ret = zero();

        let i = 0;
        while (i < WORDS) {
            let a1 = get(&a, i);
            let b1 = get(&b, i);
            put(&mut ret, i, a1 ^ b1);

            i = i + 1;
        };

        ret
    }

    /// Binary and `a` by `b`.
    fun bitand(a: U512, b: U512): U512 {
        let ret = zero();

        let i = 0;
        while (i < WORDS) {
            let a1 = get(&a, i);
            let b1 = get(&b, i);
            put(&mut ret, i, a1 & b1);

            i = i + 1;
        };

        ret
    }

    /// Binary or `a` by `b`.
    fun bitor(a: U512, b: U512): U512 {
        let ret = zero();

        let i = 0;
        while (i < WORDS) {
            let a1 = get(&a, i);
            let b1 = get(&b, i);
            put(&mut ret, i, a1 | b1);

            i = i + 1;
        };

        ret
    }

    /// Shift right `a`  by `shift`.
    public fun shr(a: U512, shift: u8): U512 {
        let ret = zero();

        let word_shift = (shift as u64) / 64;
        let bit_shift = (shift as u64) % 64;

        let i = word_shift;
        while (i < WORDS) {
            let m = get(&a, i) >> (bit_shift as u8);
            put(&mut ret, i - word_shift, m);
            i = i + 1;
        };

        if (bit_shift > 0) {
            let j = word_shift + 1;
            while (j < WORDS) {
                let m = get(&ret, j - word_shift - 1) + (get(&a, j) << (64 - (bit_shift as u8)));
                put(&mut ret, j - word_shift - 1, m);
                j = j + 1;
            };
        };

        ret
    }

    /// Shift left `a` by `shift`.
    public fun shl(a: U512, shift: u8): U512 {
        let ret = zero();

        let word_shift = (shift as u64) / 64;
        let bit_shift = (shift as u64) % 64;

        let i = word_shift;
        while (i < WORDS) {
            let m = get(&a, i - word_shift) << (bit_shift as u8);
            put(&mut ret, i, m);
            i = i + 1;
        };

        if (bit_shift > 0) {
            let j = word_shift + 1;

            while (j < WORDS) {
                let m = get(&ret, j) + (get(&a, j - 1 - word_shift) >> (64 - (bit_shift as u8)));
                put(&mut ret, j, m);
                j = j + 1;
            };
        };

        ret
    }

    /// Returns `U512` equals to zero.
    public fun zero(): U512 {
        U512 {
            v0: 0,
            v1: 0,
            v2: 0,
            v3: 0,
            v4: 0,
            v5: 0,
            v6: 0,
            v7: 0,
        }
    }

    // Private functions.
    /// Get bits used to store `a`.
    fun bits(a: &U512): u64 {
        let i = 1;
        while (i < WORDS) {
            let a1 = get(a, WORDS - i);
            if (a1 > 0) {
                return ((0x40 * (WORDS - i + 1)) - (leading_zeros_u64(a1) as u64))
            };

            i = i + 1;
        };

        let a1 = get(a, 0);
        0x40 - (leading_zeros_u64(a1) as u64)
    }

    /// Get leading zeros of a binary representation of `a`.
    fun leading_zeros_u64(a: u64): u8 {
        if (a == 0) {
            return 64
        };

        let a1 = a & 0xFFFFFFFF;
        let a2 = a >> 32;

        if (a2 == 0) {
            let bit = 32;

            while (bit >= 1) {
                let b = (a1 >> (bit-1)) & 1;
                if (b != 0) {
                    break
                };

                bit = bit - 1;
            };

            (32 - bit) + 32
        } else {
            let bit = 64;
            while (bit >= 1) {
                let b = (a >> (bit-1)) & 1;
                if (b != 0) {
                    break
                };
                bit = bit - 1;
            };

            64 - bit
        }
    }

    /// Similar to Rust `overflowing_add`.
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fun overflowing_add(a: u64, b: u64): (u64, bool) {
        let a128 = (a as u128);
        let b128 = (b as u128);

        let r = a128 + b128;
        if (r > U64_MAX) {
            // overflow
            let overflow = r - U64_MAX - 1;
            ((overflow as u64), true)
        } else {
            (((a128 + b128) as u64), false)
        }
    }

    /// Similar to Rust `overflowing_sub`.
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fun overflowing_sub(a: u64, b: u64): (u64, bool) {
        if (a < b) {
            let r = b - a;
            ((U64_MAX as u64) - r + 1, true)
        } else {
            (a - b, false)
        }
    }

    /// Extracts two `u64` from `a` `u128`.
    fun split_u128(a: u128): (u64, u64) {
        let a1 = ((a >> 64) as u64);
        let a2 = ((a & 0xFFFFFFFFFFFFFFFF) as u64);

        (a1, a2)
    }

    /// Get word from `a` by index `i`.
    public fun get(a: &U512, i: u64): u64 {
        if (i == 0) {
            a.v0
        } else if (i == 1) {
            a.v1
        } else if (i == 2) {
            a.v2
        } else if (i == 3) {
            a.v3
        } else if (i == 4) {
            a.v4
        } else if (i == 5) {
            a.v5
        } else if (i == 6) {
            a.v6
        } else if (i == 7) {
            a.v7
        } else {
            abort EWORDS_OVERFLOW
        }
    }

    /// Get word from `U512` by index.
    fun get_d(a: &DU512, i: u64): u64 {
        if (i == 0) {
            a.v0
        } else if (i == 1) {
            a.v1
        } else if (i == 2) {
            a.v2
        } else if (i == 3) {
            a.v3
        } else if (i == 4) {
            a.v4
        } else if (i == 5) {
            a.v5
        } else if (i == 6) {
            a.v6
        } else if (i == 7) {
            a.v7
        } else if (i == 8) {
            a.v8
        } else if (i == 9) {
            a.v9
        } else if (i == 10) {
            a.v10
        } else if (i == 11) {
            a.v11
        } else if (i == 12) {
            a.v12
        } else if (i == 13) {
            a.v13
        } else if (i == 14) {
            a.v14
        } else if (i == 15) {
            a.v15
        } else {
            abort EWORDS_OVERFLOW
        }
    }

    /// Put new word `val` into `U512` by index `i`.
    fun put(a: &mut U512, i: u64, val: u64) {
        if (i == 0) {
            a.v0 = val;
        } else if (i == 1) {
            a.v1 = val;
        } else if (i == 2) {
            a.v2 = val;
        } else if (i == 3) {
            a.v3 = val;
        } else if (i == 4) {
            a.v4 = val;
        } else if (i == 5) {
            a.v5 = val;
        } else if (i == 6) {
            a.v6 = val;
        } else if (i == 7) {
            a.v7 = val;
        } else {
            abort EWORDS_OVERFLOW
        }
    }

    /// Put new word into `U512` by index `i`.
    fun put_d(a: &mut DU512, i: u64, val: u64) {
        if (i == 0) {
            a.v0 = val;
        } else if (i == 1) {
            a.v1 = val;
        } else if (i == 2) {
            a.v2 = val;
        } else if (i == 3) {
            a.v3 = val;
        } else if (i == 4) {
            a.v4 = val;
        } else if (i == 5) {
            a.v5 = val;
        } else if (i == 6) {
            a.v6 = val;
        } else if (i == 7) {
            a.v7 = val;
        } else if (i == 8) {
            a.v8 = val;
        } else if (i == 9) {
            a.v9 = val;
        } else if (i == 10) {
            a.v10 = val;
        } else if (i == 11) {
            a.v11 = val;
        } else if (i == 12) {
            a.v12 = val;
        } else if (i == 13) {
            a.v13 = val;
        } else if (i == 14) {
            a.v14 = val;
        } else if (i == 15) {
            a.v15 = val;
        } else {
            abort EWORDS_OVERFLOW
        }
    }


    // Tests.
    #[test]
    fun test_get_d() {
        let a = DU512 {
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
            v4: 5,
            v5: 6,
            v6: 7,
            v7: 8,
            v8: 9,
            v9: 10,
            v10: 11,
            v11: 12,
            v12: 13,
            v13: 14,
            v14: 15,
            v15: 16,
        };

        assert!(get_d(&a, 0) == 1, 0);
        assert!(get_d(&a, 1) == 2, 1);
        assert!(get_d(&a, 2) == 3, 2);
        assert!(get_d(&a, 3) == 4, 3);
        assert!(get_d(&a, 4) == 5, 4);
        assert!(get_d(&a, 5) == 6, 5);
        assert!(get_d(&a, 6) == 7, 6);
        assert!(get_d(&a, 7) == 8, 7);

        assert!(get_d(&a, 8) == 9, 8);
        assert!(get_d(&a, 9) == 10, 9);
        assert!(get_d(&a, 10) == 11, 10);
        assert!(get_d(&a, 11) == 12, 11);
        assert!(get_d(&a, 12) == 13, 12);
        assert!(get_d(&a, 13) == 14, 13);
        assert!(get_d(&a, 14) == 15, 14);
        assert!(get_d(&a, 15) == 16, 15);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_get_d_overflow() {
        let a = DU512 {
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
            v4: 5,
            v5: 6,
            v6: 7,
            v7: 8,
            v8: 9,
            v9: 10,
            v10: 11,
            v11: 12,
            v12: 13,
            v13: 14,
            v14: 15,
            v15: 16,
        };

        get_d(&a, 16);
    }

    #[test]
    fun test_put_d() {
        let a = DU512 {
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
            v4: 5,
            v5: 6,
            v6: 7,
            v7: 8,
            v8: 9,
            v9: 10,
            v10: 11,
            v11: 12,
            v12: 13,
            v13: 14,
            v14: 15,
            v15: 16,
        };

        put_d(&mut a, 0, 10);
        put_d(&mut a, 1, 20);
        put_d(&mut a, 2, 30);
        put_d(&mut a, 3, 40);
        put_d(&mut a, 4, 50);
        put_d(&mut a, 5, 60);
        put_d(&mut a, 6, 70);
        put_d(&mut a, 7, 80);
        put_d(&mut a, 8, 90);
        put_d(&mut a, 9, 100);
        put_d(&mut a, 10, 110);
        put_d(&mut a, 11, 120);
        put_d(&mut a, 12, 130);
        put_d(&mut a, 13, 140);
        put_d(&mut a, 14, 150);
        put_d(&mut a, 15, 160);

        assert!(get_d(&a, 0) == 10, 0);
        assert!(get_d(&a, 1) == 20, 1);
        assert!(get_d(&a, 2) == 30, 2);
        assert!(get_d(&a, 3) == 40, 3);
        assert!(get_d(&a, 4) == 50, 4);
        assert!(get_d(&a, 5) == 60, 5);
        assert!(get_d(&a, 6) == 70, 6);
        assert!(get_d(&a, 7) == 80, 7);
        assert!(get_d(&a, 8) == 90, 8);
        assert!(get_d(&a, 9) == 100, 9);
        assert!(get_d(&a, 10) == 110, 10);
        assert!(get_d(&a, 11) == 120, 11);
        assert!(get_d(&a, 12) == 130, 12);
        assert!(get_d(&a, 13) == 140, 13);
        assert!(get_d(&a, 14) == 150, 14);
        assert!(get_d(&a, 15) == 160, 15);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_put_d_overflow() {
        let a = DU512 {
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
            v4: 5,
            v5: 6,
            v6: 7,
            v7: 8,
            v8: 9,
            v9: 10,
            v10: 11,
            v11: 12,
            v12: 13,
            v13: 14,
            v14: 15,
            v15: 16,
        };

        put_d(&mut a, 16, 0);
    }

    #[test]
    fun test_du512_to_u512() {
        let a = DU512 {
            v0: 255,
            v1: 100,
            v2: 50,
            v3: 300,
            v4: 100,
            v5: 110,
            v6: 120,
            v7: 130,
            v8: 0,
            v9: 0,
            v10: 0,
            v11: 0,
            v12: 0,
            v13: 0,
            v14: 0,
            v15: 0,
        };

        let (m, overflow) = du512_to_u512(a);
        assert!(!overflow, 0);
        assert!(m.v0 == a.v0, 1);
        assert!(m.v1 == a.v1, 2);
        assert!(m.v2 == a.v2, 3);
        assert!(m.v3 == a.v3, 4);
        assert!(m.v4 == a.v4, 5);
        assert!(m.v5 == a.v5, 6);
        assert!(m.v6 == a.v6, 7);
        assert!(m.v7 == a.v7, 8);

        a.v8 = 100;
        a.v9 = 5;

        let (m, overflow) = du512_to_u512(a);
        assert!(overflow, 9);
        assert!(m.v0 == a.v0, 10);
        assert!(m.v1 == a.v1, 11);
        assert!(m.v2 == a.v2, 12);
        assert!(m.v3 == a.v3, 13);
        assert!(m.v4 == a.v4, 14);
        assert!(m.v5 == a.v5, 15);
        assert!(m.v6 == a.v6, 16);
        assert!(m.v7 == a.v7, 17);
    }

    #[test]
    fun test_get() {
        let a = U512 {
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
            v4: 5,
            v5: 6,
            v6: 7,
            v7: 8,
        };

        assert!(get(&a, 0) == 1, 0);
        assert!(get(&a, 1) == 2, 1);
        assert!(get(&a, 2) == 3, 2);
        assert!(get(&a, 3) == 4, 3);
        assert!(get(&a, 4) == 5, 4);
        assert!(get(&a, 5) == 6, 5);
        assert!(get(&a, 6) == 7, 6);
        assert!(get(&a, 7) == 8, 7);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_get_aborts() {
        let _ = get(&zero(), 9);
    }

    #[test]
    fun test_put() {
        let a = zero();
        put(&mut a, 0, 255);
        assert!(get(&a, 0) == 255, 0);

        put(&mut a, 1, (U64_MAX as u64));
        assert!(get(&a, 1) == (U64_MAX as u64), 1);

        put(&mut a, 2, 100);
        assert!(get(&a, 2) == 100, 2);

        put(&mut a, 3, 3);
        assert!(get(&a, 3) == 3, 3);

        put(&mut a, 2, 0);
        assert!(get(&a, 2) == 0, 4);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_put_overflow() {
        let a = zero();
        put(&mut a, 9, 255);
    }

    #[test]
    fun test_from_u128() {
        let i = 0;
        while (i < 1024) {
            let big = from_u128(i);
            assert!(as_u128(big) == i, 0);
            i = i + 1;
        };
    }

    #[test]
    fun test_add() {
        let a = from_u128(1000);
        let b = from_u128(500);

        let s = as_u128(add(a, b));
        assert!(s == 1500, 0);

        a = from_u128(U64_MAX);
        b = from_u128(U64_MAX);

        s = as_u128(add(a, b));
        assert!(s == (U64_MAX + U64_MAX), 1);
    }

    #[test]
    #[expected_failure(abort_code = 2)]
    fun test_add_overflow() {
        let max = (U64_MAX as u64);

        let a = U512 {
            v0: max,
            v1: max,
            v2: max,
            v3: max,
            v4: max,
            v5: max,
            v6: max,
            v7: max
        };

        let _ = add(a, from_u128(1));
    }

    #[test]
    fun test_sub() {
        let a = from_u128(1000);
        let b = from_u128(500);

        let s = as_u128(sub(a, b));
        assert!(s == 500, 0);
    }

    #[test]
    #[expected_failure(abort_code = 2)]
    fun test_sub_overflow() {
        let a = from_u128(0);
        let b = from_u128(1);

        let _ = sub(a, b);
    }

    #[test]
    #[expected_failure(abort_code = 0)]
    fun test_too_big_to_cast_to_u128() {
        let a = from_u128(U128_MAX);
        let b = from_u128(U128_MAX);

        let _ = as_u128(add(a, b));
    }

    #[test]
    fun test_overflowing_add() {
        let (n, z) = overflowing_add(10, 10);
        assert!(n == 20, 0);
        assert!(!z, 1);

        (n, z) = overflowing_add((U64_MAX as u64), 1);
        assert!(n == 0, 2);
        assert!(z, 3);

        (n, z) = overflowing_add((U64_MAX as u64), 10);
        assert!(n == 9, 4);
        assert!(z, 5);

        (n, z) = overflowing_add(5, 8);
        assert!(n == 13, 6);
        assert!(!z, 7);
    }

    #[test]
    fun test_overflowing_sub() {
        let (n, z) = overflowing_sub(10, 5);
        assert!(n == 5, 0);
        assert!(!z, 1);

        (n, z) = overflowing_sub(0, 1);
        assert!(n == (U64_MAX as u64), 2);
        assert!(z, 3);

        (n, z) = overflowing_sub(10, 10);
        assert!(n == 0, 4);
        assert!(!z, 5);
    }

    #[test]
    fun test_split_u128() {
        let (a1, a2) = split_u128(100);
        assert!(a1 == 0, 0);
        assert!(a2 == 100, 1);

        (a1, a2) = split_u128(U64_MAX + 1);
        assert!(a1 == 1, 2);
        assert!(a2 == 0, 3);
    }

    #[test]
    fun test_mul() {
        let a = from_u128(285);
        let b = from_u128(375);

        let c = as_u128(mul(a, b));
        assert!(c == 106875, 0);

        a = from_u128(0);
        b = from_u128(1);

        c = as_u128(mul(a, b));

        assert!(c == 0, 1);

        a = from_u128(U64_MAX);
        b = from_u128(2);

        c = as_u128(mul(a, b));

        assert!(c == 36893488147419103230, 2);

        a = from_u128(U128_MAX);
        b = from_u128(U128_MAX);

        let z = mul(a, b);
        assert!(bits(&z) == 256, 3);
    }

    #[test]
    #[expected_failure(abort_code = 2)]
    fun test_mul_overflow() {
        let max = (U64_MAX as u64);

        let a = U512 {
            v0: max,
            v1: max,
            v2: max,
            v3: max,
            v4: max,
            v5: max,
            v6: max,
            v7: max,
        };

        let _ = mul(a, from_u128(2));
    }

    #[test]
    fun test_zero() {
        let a = as_u128(zero());
        assert!(a == 0, 0);

        let a = zero();
        assert!(a.v0 == 0, 1);
        assert!(a.v1 == 0, 2);
        assert!(a.v2 == 0, 3);
        assert!(a.v3 == 0, 4);
        assert!(a.v4 == 0, 5);
        assert!(a.v5 == 0, 6);
        assert!(a.v6 == 0, 7);
        assert!(a.v7 == 0, 8);
    }

    #[test]
    fun test_or() {
        let a = from_u128(0);
        let b = from_u128(1);
        let c = bitor(a, b);
        assert!(as_u128(c) == 1, 0);

        let a = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let b = from_u128(0xf0f0f0f0f0f0f0f0u128);
        let c = bitor(a, b);
        assert!(as_u128(c) == 0xffffffffffffffffu128, 1);
    }

    #[test]
    fun test_and() {
        let a = from_u128(0);
        let b = from_u128(1);
        let c = bitand(a, b);
        assert!(as_u128(c) == 0, 0);

        let a = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let b = from_u128(0xf0f0f0f0f0f0f0f0u128);
        let c = bitand(a, b);
        assert!(as_u128(c) == 0, 1);

        let a = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let b = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let c = bitand(a, b);
        assert!(as_u128(c) == 0x0f0f0f0f0f0f0f0fu128, 1);
    }

    #[test]
    fun test_xor() {
        let a = from_u128(0);
        let b = from_u128(1);
        let c = bitxor(a, b);
        assert!(as_u128(c) == 1, 0);

        let a = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let b = from_u128(0xf0f0f0f0f0f0f0f0u128);
        let c = bitxor(a, b);
        assert!(as_u128(c) == 0xffffffffffffffffu128, 1);
    }

    #[test]
    fun test_from_u64() {
        let a = as_u128(from_u64(100));
        assert!(a == 100, 0);

        // TODO: more tests.
    }

    #[test]
    fun test_compare() {
        let a = from_u128(1000);
        let b = from_u128(50);

        let cmp = compare(&a, &b);
        assert!(cmp == 2, 0);

        a = from_u128(100);
        b = from_u128(100);
        cmp = compare(&a, &b);

        assert!(cmp == 0, 1);

        a = from_u128(50);
        b = from_u128(75);

        cmp = compare(&a, &b);
        assert!(cmp == 1, 2);
    }

    #[test]
    fun test_leading_zeros_u64() {
        let a = leading_zeros_u64(0);
        assert!(a == 64, 0);

        let a = leading_zeros_u64(1);
        assert!(a == 63, 1);

        // TODO: more tests.
    }

    #[test]
    fun test_bits() {
        let a = bits(&from_u128(0));
        assert!(a == 0, 0);

        a = bits(&from_u128(255));
        assert!(a == 8, 1);

        a = bits(&from_u128(256));
        assert!(a == 9, 2);

        a = bits(&from_u128(300));
        assert!(a == 9, 3);

        a = bits(&from_u128(60000));
        assert!(a == 16, 4);

        a = bits(&from_u128(70000));
        assert!(a == 17, 5);

        let b = from_u64(70000);
        let sh = shl(b, 100);
        assert!(bits(&sh) == 117, 6);

        let sh = shl(sh, 100);
        assert!(bits(&sh) == 217, 7);

        let sh = shl(sh, 100);
        assert!(bits(&sh) == 317, 8);

        let sh = shl(sh, 100);
        assert!(bits(&sh) == 417, 8);

        let sh = shl(sh, 200);
        assert!(bits(&sh) == 0, 8);
    }

    #[test]
    fun test_shift_left() {
        let a = from_u128(100);
        let b = shl(a, 2);

        assert!(as_u128(b) == 400, 0);

        // TODO: more shift left tests.
    }

    #[test]
    fun test_shift_right() {
        let a = from_u128(100);
        let b = shr(a, 2);

        assert!(as_u128(b) == 25, 0);

        // TODO: more shift right tests.
    }

    #[test]
    fun test_div() {
        let a = from_u128(100);
        let b = from_u128(5);
        let d = div(a, b);

        assert!(as_u128(d) == 20, 0);

        let a = from_u128(U64_MAX);
        let b = from_u128(U128_MAX);
        let d = div(a, b);
        assert!(as_u128(d) == 0, 1);

        let a = from_u128(U64_MAX);
        let b = from_u128(U128_MAX);
        let d = div(a, b);
        assert!(as_u128(d) == 0, 2);

        let a = from_u128(U128_MAX);
        let b = from_u128(U64_MAX);
        let d = div(a, b);
        assert!(as_u128(d) == 18446744073709551617, 2);
    }

    #[test]
    #[expected_failure(abort_code=3)]
    fun test_div_by_zero() {
        let a = from_u128(1);
        let _z = div(a, from_u128(0));
    }


    #[test]
    fun test_sqrt() {
        let a = from_u128(0);
        let b = sqrt(a);
        assert!(as_u128(b) == 0, 0);

        let a = from_u128(81);
        let b = sqrt(a);
        assert!(as_u128(b) == 9, 1);

        let a = from_u128(1000000);
        let b = sqrt(a);
        assert!(as_u128(b) == 1000, 2);

        let a = from_u128(1516156330329);
        let b = sqrt(a);
        assert!(as_u128(b) == 1231323, 3);
    }


    #[test]
    fun test_as_u64() {
        let _ = as_u64(from_u64((U64_MAX as u64)));
        let _ = as_u64(from_u128(1));
    }

    #[test]
    #[expected_failure(abort_code=0)]
    fun test_as_u64_overflow() {
        let _ = as_u64(from_u128(U128_MAX));
    }
}
