module math_utils::i256 {
    use std::error;

    use math_utils::u256::{Self, U256};
    use math_utils::i64::{Self, I64};

    /// Total words in `I256` (64 * 4 = 256).
    const WORDS: u64 = 4;

    /// When trying to get or put word into I256 but it's out of index.
    const EWORDS_OVERFLOW: u64 = 1;

    const ECONVERSION_TO_I256_OVERFLOW: u64 = 2;

    const EMUL_OVERFLOW: u64 = 3;
    const ESUB_OVERFLOW: u64 = 4;
    const EADD_OVERFLOW: u64 = 5;
    const ECAST_OVERFLOW: u64 = 6;

    /// Max `u64` value.
    const U64_MAX: u128 = 18446744073709551615;

    /// @dev u64 with the first bit set. An `I64` is negative if this bit is set.
    const U64_WITH_FIRST_BIT_SET: u64 = 1 << 63;

    /// When both `I256` equal.
    const EQUAL: u8 = 0;

    /// When `a` is less than `b`.
    const LESS_THAN: u8 = 1;

    /// When `b` is greater than `b`.
    const GREATER_THAN: u8 = 2;


    // Data structs.

    /// The `I256` resource.
    /// Contains 4 u64 numbers.
    struct I256 has copy, drop, store {
        is_minus: bool,
        v0: u64,
        v1: u64,
        v2: u64,
        v3: u64,
    }

    

    /// Double `I256` used for multiple (to store overflow).
    struct DI256 has copy, drop, store {
        v0: u64,
        v1: u64,
        v2: u64,
        v3: u64,
        v4: u64,
        v5: u64,
        v6: u64,
        v7: u64,
    }

    public fun mul(a: I256, b: I256): I256 {
        let ret = DI256 {
            v0: 0,
            v1: 0,
            v2: 0,
            v3: 0,
            v4: 0,
            v5: 0,
            v6: 0,
            v7: 0,
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

        let (r, overflow) = di256_to_i256(ret);
        assert!(!overflow, EMUL_OVERFLOW);
        r.is_minus = a.is_minus != b.is_minus;
        r
    }

    fun di256_to_i256(a: DI256): (I256, bool) {
        let b = I256 {
            is_minus: false,
            v0: a.v0,
            v1: a.v1,
            v2: a.v2,
            v3: a.v3,
        };

        let overflow = false;
        if (a.v4 != 0 || a.v5 != 0 || a.v6 != 0 || a.v7 != 0 || a.v3 > U64_WITH_FIRST_BIT_SET ) {
            overflow = true;
        };

        (b, overflow)
    }

    public fun shr(a: I256, shift: u8): I256 {
        let ret = zero();

        a = get_complement(a);

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
        if (a.is_minus) {
            let covering = u256::xor(&u256::max(), &u256::sub(u256::shl(u256::from_u64(1), 255 - shift + 1), u256::from_u64(1)));
            ret = or(from_u256_without_check(covering), ret);
            ret.is_minus = true;
            ret = get_complement(ret);
        };
        ret
    }

    public fun from_u256_without_check(val: U256): I256 {
        let (v0, v1, v2, v3) = u256::fields(val);
        I256 {
            is_minus: false,
            v0: v0,
            v1: v1,
            v2: v2,
            v3: v3,
        }
    }

    public fun as_i64(a: I256): I64 {
        assert!(a.v1 == 0 && a.v2 == 0 && a.v3 == 0, ECAST_OVERFLOW);
        if (a.is_minus) {
            i64::neg_from(a.v0)
        } else {
            i64::from(a.v0)
        }
    }

    public fun abs_compare(a: &I256, b: &I256): u8 {
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


    public fun add(a: I256, b: I256): I256 {
        if (a.is_minus == b.is_minus) {
            let ret = add_without_sign(a, b);
            ret.is_minus = a.is_minus;
            ret
        } else if (abs_compare(&a, &b) == EQUAL) {
            zero()
        } else if (abs_compare(&a, &b) == GREATER_THAN) {
            if (a.is_minus) {
                let ret = sub_without_sign(a, b);
                ret.is_minus = true;
                ret
            } else {
                sub_without_sign(b, a)
            }
        } else {
            if (a.is_minus) {
                sub_without_sign(b, a)
            } else {
                let ret = sub_without_sign(a, b);
                ret.is_minus = true;
                ret
            }
        }
    }

    public fun sub(a: I256, b: I256): I256 {
        if (a.is_minus != b.is_minus) {
            let ret = add_without_sign(a, b);
            ret.is_minus = a.is_minus;
            ret
            
        } else if (abs_compare(&a, &b) == EQUAL) {
            zero()
        } else if (abs_compare(&a, &b) == GREATER_THAN) {
            let ret = sub_without_sign(a, b);
            ret.is_minus = a.is_minus;
            ret
        } else {
            let ret = sub_without_sign(b, a);
            ret.is_minus = !a.is_minus;
            ret
        }
    }

    public fun add_without_sign(a: I256, b: I256): I256 {
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

        assert!(carry == 0 && ret.v3 < U64_WITH_FIRST_BIT_SET, EADD_OVERFLOW);

        ret
    }

    public fun sub_without_sign(a: I256, b: I256): I256 {
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

        assert!(carry == 0 && ret.v3 < U64_WITH_FIRST_BIT_SET, ESUB_OVERFLOW);
        ret
    }

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

    fun overflowing_sub(a: u64, b: u64): (u64, bool) {
        if (a < b) {
            let r = b - a;
            ((U64_MAX as u64) - r + 1, true)
        } else {
            (a - b, false)
        }
    }

    public fun or(a: I256, b: I256): I256 {
        let ret = zero();

        ret.is_minus = a.is_minus || b.is_minus;

        let complement_a = get_complement(a);
        let complement_b = get_complement(b);

        let i = 0;
        while (i < WORDS) {
            // print(&b"---------");
            // print(&complement_a);
            // print(&get(&complement_a, i));
            // print(&get(&complement_b, i));
            // print(&b"---------");
            let m = get(&complement_a, i) | get(&complement_b, i);
            put(&mut ret, i, m);
            i = i + 1;
        };

        get_complement(ret)
    }

    fun get_complement(original: I256): I256 {
        if (original.is_minus) {
            let complement = I256 {
                is_minus: original.is_minus,
                v0: original.v0 ^ 0xffffffffffffffff,
                v1: original.v1 ^ 0xffffffffffffffff,
                v2: original.v2 ^ 0xffffffffffffffff,
                v3: original.v3 ^ 0xffffffffffffffff,
            };
            let (res, is_overflow) = overflowing_add(complement.v0, 1);
            put(&mut complement, 0, res);
            let i = 1;
            while (is_overflow && i < WORDS) {
                let vali = get(&complement, i);
                let (res, is_of) = overflowing_add(vali, 1);
                is_overflow = is_of;
                put(&mut complement, i, res);
                i = i + 1;
            };
            complement
        } else {
            original
        }
    }

    public fun from_u256(val: U256): I256 {
        let (v0, v1, v2, v3) = u256::fields(val);
        assert!(v3 < U64_WITH_FIRST_BIT_SET, error::invalid_argument(ECONVERSION_TO_I256_OVERFLOW));
        I256 {
            is_minus: false,
            v0: v0,
            v1: v1,
            v2: v2,
            v3: v3,
        }
    }

    public fun from_u128(val: u128, is_minus: bool): I256 {
        let (a2, a1) = split_u128(val);

        I256 {
            is_minus: is_minus,
            v0: a1,
            v1: a2,
            v2: 0,
            v3: 0,
        }
    }

    fun split_u128(a: u128): (u64, u64) {
        let a1 = ((a >> 64) as u64);
        let a2 = ((a & 0xFFFFFFFFFFFFFFFF) as u64);

        (a1, a2)
    }

    public fun get(a: &I256, i: u64): u64 {
        if (i == 0) {
            a.v0
        } else if (i == 1) {
            a.v1
        } else if (i == 2) {
            a.v2
        } else if (i == 3) {
            a.v3
        } else {
            abort EWORDS_OVERFLOW
        }
    }

    fun get_d(a: &DI256, i: u64): u64 {
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

    fun put(a: &mut I256, i: u64, val: u64) {
        if (i == 0) {
            a.v0 = val;
        } else if (i == 1) {
            a.v1 = val;
        } else if (i == 2) {
            a.v2 = val;
        } else if (i == 3) {
            a.v3 = val;
        } else {
            abort EWORDS_OVERFLOW
        }
    }

    fun put_d(a: &mut DI256, i: u64, val: u64) {
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

    public fun zero(): I256 {
        I256 {
            is_minus: false,
            v0: 0,
            v1: 0,
            v2: 0,
            v3: 0,
        }
    }
}