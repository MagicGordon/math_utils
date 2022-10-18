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

    /// Max `u128` value.
    const U128_MAX: u128 = 340282366920938463463374607431768211455;

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

    public fun compare(a: &I256, b: &I256): u8 {
        if (a.is_minus == b.is_minus) {
            let compare_res = abs_compare(a, b);
            if (compare_res == EQUAL) {
                EQUAL
            } else {
                if (compare_res == LESS_THAN) {
                    if (a.is_minus == true) {
                        GREATER_THAN
                    } else {
                        LESS_THAN
                    }
                } else {
                    if (a.is_minus == true) {
                        LESS_THAN
                    } else {
                        GREATER_THAN
                    }
                }
            }
        } else {
            if (a.is_minus == true) {
                LESS_THAN
            } else {
                GREATER_THAN
            }
        }
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

   // Private functions.
    /// Get bits used to store `a`.
    fun bits(a: &I256): u64 {
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

    // Tests.
    #[test]
    fun test_get_d() {
        let a = DI256 {
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
            v4: 5,
            v5: 6,
            v6: 7,
            v7: 8,
        };

        assert!(get_d(&a, 0) == 1, 0);
        assert!(get_d(&a, 1) == 2, 1);
        assert!(get_d(&a, 2) == 3, 2);
        assert!(get_d(&a, 3) == 4, 3);
        assert!(get_d(&a, 4) == 5, 4);
        assert!(get_d(&a, 5) == 6, 5);
        assert!(get_d(&a, 6) == 7, 6);
        assert!(get_d(&a, 7) == 8, 7);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_get_d_overflow() {
        let a = DI256 {
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
            v4: 5,
            v5: 6,
            v6: 7,
            v7: 8,
        };

        get_d(&a, 8);
    }

    #[test]
    fun test_put_d() {
        let a = DI256 {
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
            v4: 5,
            v5: 6,
            v6: 7,
            v7: 8,
        };

        put_d(&mut a, 0, 10);
        put_d(&mut a, 1, 20);
        put_d(&mut a, 2, 30);
        put_d(&mut a, 3, 40);
        put_d(&mut a, 4, 50);
        put_d(&mut a, 5, 60);
        put_d(&mut a, 6, 70);
        put_d(&mut a, 7, 80);

        assert!(get_d(&a, 0) == 10, 0);
        assert!(get_d(&a, 1) == 20, 1);
        assert!(get_d(&a, 2) == 30, 2);
        assert!(get_d(&a, 3) == 40, 3);
        assert!(get_d(&a, 4) == 50, 4);
        assert!(get_d(&a, 5) == 60, 5);
        assert!(get_d(&a, 6) == 70, 6);
        assert!(get_d(&a, 7) == 80, 7);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_put_d_overflow() {
        let a = DI256 {
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
            v4: 5,
            v5: 6,
            v6: 7,
            v7: 8,
        };

        put_d(&mut a, 8, 0);
    }

    #[test]
    fun test_di256_to_i256() {
        let a = DI256 {
            v0: 255,
            v1: 100,
            v2: 50,
            v3: 300,
            v4: 0,
            v5: 0,
            v6: 0,
            v7: 0,
        };

        let (m, overflow) = di256_to_i256(a);
        assert!(!overflow, 0);
        assert!(m.v0 == a.v0, 1);
        assert!(m.v1 == a.v1, 2);
        assert!(m.v2 == a.v2, 3);
        assert!(m.v3 == a.v3, 4);

        a.v4 = 100;
        a.v5 = 5;

        let (m, overflow) = di256_to_i256(a);
        assert!(overflow, 5);
        assert!(m.v0 == a.v0, 6);
        assert!(m.v1 == a.v1, 7);
        assert!(m.v2 == a.v2, 8);
        assert!(m.v3 == a.v3, 9);
    }

    #[test]
    fun test_get() {
        let a = I256 {
            is_minus: true,
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
        };

        assert!(get(&a, 0) == 1, 0);
        assert!(get(&a, 1) == 2, 1);
        assert!(get(&a, 2) == 3, 2);
        assert!(get(&a, 3) == 4, 3);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_get_aborts() {
        let _ = get(&zero(), 4);
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
        put(&mut a, 6, 255);
    }

    #[test]
    fun test_from_positive_i128() {
        let i: u64 = 0;
        while (i < 1024) {
            let big = from_u256(u256::from_u64(i));
            assert!(i64::compare(&as_i64(big), &i64::from(i)) == EQUAL, 0);
            i = i + 1;
        };
    }
    
    #[test]
    fun test_from_negative_i128() {
        let i = 0;
        while (i < 1024) {
            let neg = from_u128(i, true);
            let b = zero();
            assert!(compare(&neg,&b) == LESS_THAN, 0);
            i = i + 1;
        };
    }

    #[test]
    fun test_add() {
        let a = from_u128(1000, true); // negative
        let b = from_u128(500, true); // negative

        let s = as_i64(add(a, b));
        assert!(i64::compare(&s, &i64::neg_from(1500)) == EQUAL, 0);


        a = from_u128(1000, false); // positive
        b = from_u128(500, false); // positive

        s = as_i64(add(a, b));
        assert!(i64::compare(&s, &i64::from(1500)) == EQUAL, 0);

        a = from_u128(U64_MAX, false); // positive
        b = from_u128(U64_MAX, false); // positive

        let x = add(a, b);
        let y = from_u128(U64_MAX + U64_MAX, false); // postive
        assert!(compare(&x,&y)==EQUAL, 1);

        a = from_u128(U64_MAX, true); // negative
        b = from_u128(U64_MAX, true); // negative

        x = add(a, b);
        y = from_u128(U64_MAX + U64_MAX, true); // negative
        assert!(compare(&x,&y)==EQUAL, 2);
    }

    #[test]
    #[expected_failure(abort_code = 5)]
    fun test_add_overflow() {
        let max = (U64_MAX as u64);

        let a = I256 {
            is_minus: false,
            v0: max,
            v1: max,
            v2: max,
            v3: max
        };

        let _ = add(a, from_u128(1, false));
    }

    #[test]
    fun test_sub() {
        let a = from_u128(1000, true);
        let b = from_u128(500, true);

        let s = as_i64(sub(a, b));
        assert!(i64::compare(&s, &i64::neg_from(500)) == EQUAL, 0);

        let a = from_u128(1000, false);
        let b = from_u128(500, false);

        let s = as_i64(sub(a, b));
        assert!(i64::compare(&s, &i64::from(500)) == EQUAL, 0);
    }
/*
    #[test]
    #[expected_failure(abort_code = 4)]
    fun test_sub_overflow() {
        let a = from_u128(0, false);
        let b = from_u128(1, false);

        let _ = sub(a, b);
    }


    #[test]
    #[expected_failure(abort_code = 0)]
    fun test_too_big_to_cast_to_i128() {
        let a = from_i128(U128_MAX, false);
        let b = from_i128(U128_MAX, false);

        let _ = as_i128(add(a, b));
    } 
*/

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
/*
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
*/

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
    #[expected_failure(abort_code = 3)]
    fun test_mul() {
        let a = from_u128(285, false);
        let b = from_u128(375, false);

        let c = as_i64(mul(a, b));
        assert!(i64::compare(&c, &i64::from(106875)) == EQUAL, 0);

        a = from_u128(285, true);
        b = from_u128(375, false);

        c = as_i64(mul(a, b));
        assert!(i64::compare(&c, &i64::neg_from(106875)) == EQUAL, 1);


        a = from_u128(0, false);
        b = from_u128(1, false);

        c = as_i64(mul(a, b));
        assert!(i64::compare(&c, &i64::neg_from(0)) == EQUAL, 2);


        a = from_u128(U64_MAX, false);
        b = from_u128(2, false);

        let x = mul(a, b);
        let y = from_u128(36893488147419103230, false);

        assert!(compare(&x, &y) == EQUAL, 3);

        a = from_u128(U64_MAX, true);
        b = from_u128(2, false);

        x = mul(a, b);
        y = from_u128(36893488147419103230, true);

        assert!(compare(&x, &y) == EQUAL, 4);


        //
        a = from_u128(U128_MAX, false);
        b = from_u128(U128_MAX, false);

        let z = mul(a, b);
        assert!(bits(&z) == 256, 3);
        //
    }

    #[test]
    #[expected_failure(abort_code = 3)]
    fun test_mul_overflow() {
        let max = (U64_MAX as u64);

        let a = I256 {
            is_minus: true,
            v0: max,
            v1: max,
            v2: max,
            v3: max,
        };

        let _ = mul(a, from_u128(2, true));
    }

    #[test]
    fun test_zero() {
        let a = zero();
        assert!(compare(&a, &from_u128(0, false)) == EQUAL, 0);

        let a = zero();
        assert!(a.v0 == 0, 1);
        assert!(a.v1 == 0, 2);
        assert!(a.v2 == 0, 3);
        assert!(a.v3 == 0, 4);
    }

    #[test]
    fun test_compare() {
        let a = from_u128(1000, true);
        let b = from_u128(50, true);

        let cmp = compare(&a, &b);
        assert!(cmp == 1, 0);

        a = from_u128(100,true);
        b = from_u128(100,true);
        cmp = compare(&a, &b);

        assert!(cmp == 0, 1);

        a = from_u128(50,true);
        b = from_u128(75,true);

        cmp = compare(&a, &b);
        assert!(cmp == 2, 2);
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
        let a = bits(&from_u128(0, true));
        assert!(a == 0, 0);

        a = bits(&from_u128(255, true));
        assert!(a == 8, 1);

        a = bits(&from_u128(256, true));
        assert!(a == 9, 2);

        a = bits(&from_u128(300, true));
        assert!(a == 9, 3);

        a = bits(&from_u128(60000, true));
        assert!(a == 16, 4);

        a = bits(&from_u128(70000, true));
        assert!(a == 17, 5);

    }

    #[test]
    fun test_shift_right() {
        let a = from_u128(100, true);
        let b = shr(a, 2);

        assert!(i64::compare(&as_i64(b), &i64::neg_from(25)) == EQUAL, 0);

        // TODO: more shift right tests.
    }
/*
    #[test]
    fun test_div() {
        let a = from_u128(100,true);
        let b = from_u128(5,false);
        let d = div(a, b);
        assert!(i64::compare(&as_i64(d), &i64::neg_from(20)) == EQUAL, 0);

        let a = from_u128(U64_MAX, true);
        let b = from_u128(U128_MAX, true);
        let d = div(a, b);
        //assert!(as_u128(d) == 0, 1);
        assert!(i64::compare(&as_i64(d), &i64::neg_from(0)) == EQUAL, 1);

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
    fun test_as_u64() {
        let _ = as_u64(from_u64((U64_MAX as u64)));
        let _ = as_u64(from_u128(1));
    }

    #[test]
    #[expected_failure(abort_code=0)]
    fun test_as_u64_overflow() {
        let _ = as_u64(from_u128(U128_MAX));
    }
    */
}