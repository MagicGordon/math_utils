module math_utils::math_point {
    use math_utils::u256::{Self, U256};
    use math_utils::i256::{Self, I256};
    use math_utils::i64::{Self, I64};

    use aptos_std::debug::print;

    public fun get_sqrt_price(point: I64) : U256 {
        let abs_point= i64::as_u64(&i64::abs(&point));
        let value = if (abs_point & 1 != 0) u256::from_u128(0xfffcb933bd6fad37aa2d162d1a594001) 
            else u256::add(u256::from_u128(340282366920938463463374607431768211455), u256::from_u128(1));

        if (abs_point & 0x2 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xfff97272373d413259a46990580e213a)), 128);
        if (abs_point & 0x4 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xfff2e50f5f656932ef12357cf3c7fdcc)), 128);
        if (abs_point & 0x8 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xffe5caca7e10e4e61c3624eaa0941cd0)), 128);
        if (abs_point & 0x10 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xffcb9843d60f6159c9db58835c926644)), 128);
        if (abs_point & 0x20 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xff973b41fa98c081472e6896dfb254c0)), 128);
        if (abs_point & 0x40 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xff2ea16466c96a3843ec78b326b52861)), 128);
        if (abs_point & 0x80 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xfe5dee046a99a2a811c461f1969c3053)), 128);
        if (abs_point & 0x100 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xfcbe86c7900a88aedcffc83b479aa3a4)), 128);
        if (abs_point & 0x200 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xf987a7253ac413176f2b074cf7815e54)), 128);
        if (abs_point & 0x400 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xf3392b0822b70005940c7a398e4b70f3)), 128);
        if (abs_point & 0x800 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xe7159475a2c29b7443b29c7fa6e889d9)), 128);
        if (abs_point & 0x1000 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xd097f3bdfd2022b8845ad8f792aa5825)), 128);
        if (abs_point & 0x2000 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0xa9f746462d870fdf8a65dc1f90e061e5)), 128);
        if (abs_point & 0x4000 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0x70d869a156d2a1b890bb3df62baf32f7)), 128);
        if (abs_point & 0x8000 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0x31be135f97d08fd981231505542fcfa6)), 128);
        if (abs_point & 0x10000 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0x9aa508b5b7a84e1c677de54f3e99bc9)), 128);
        if (abs_point & 0x20000 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0x5d6af8dedb81196699c329225ee604)), 128);
        if (abs_point & 0x40000 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0x2216e584f5fa1ea926041bedfe98)), 128);
        if (abs_point & 0x80000 != 0) value = u256::shr(u256::mul(value, u256::from_u128(0x48a170391f7dc42444e8fa2)), 128);
        
        if (!i64::is_neg(&point)) {
            value = u256::div(u256::max(), value);
        };
        let is_exact_division = u256::compare(&value, &u256::mul(u256::div(value, u256::from_u64(1 << 32)), u256::from_u64(1 << 32))) == 0;
        u256::add(u256::shr(value, 32), u256::from_u64(if (is_exact_division) 0 else 1))
    }

    fun update_x_m(base: u128, offset: u8, x: U256, m: u8): (u8, U256) {
        let y = if (u256::compare(&x, &u256::from_u128(base)) == 2) 1u8 << offset else 0u8;
        (m | y, u256::shr(x, y))
    }

    fun update_x_l2(offset: u8, x: U256, l2: I256): (U256, I256){
        x = u256::mul(x, x);
        x = u256::shr(x, 127);
        let y = u256::shr(x, 128);
        let offsetr = u256::as_u128(y);
        while (offsetr > 0xff){
            x = u256::shr(x, 0xff);
            offsetr = offsetr - 0xff;
        };
        x = u256::shr(x, (offsetr as u8));

        l2 = i256::or(l2, i256::from_u256(u256::shl(y, offset)));
        (x, l2)
    }

    public fun get_log_sqrt_price_floor(sqrt_price_96: U256) : I64 {
        let sqrt_price_128 = u256::shl(sqrt_price_96, 32);
        let x = sqrt_price_128;
        let m = 0u8;

        (m, x) = update_x_m(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 7, x, m);
        (m, x) = update_x_m(0xFFFFFFFFFFFFFFFF, 6, x, m);
        (m, x) = update_x_m(0xFFFFFFFF, 5, x, m);
        (m, x) = update_x_m(0xFFFF, 4, x, m);
        (m, x) = update_x_m(0xFF, 3, x, m);
        (m, x) = update_x_m(0xF, 2, x, m);
        (m, x) = update_x_m(3, 1, x, m);

        let y = if (u256::compare(&x, &u256::from_u128(1)) == 2) 1u8 else 0u8;
        m = m | y;

        let l2 = if (m >= 128) {
            x = u256::shr(sqrt_price_128, m - 127);
            i256::from_u128(((m - 128) as u128) << 64, false)
        } else {
            x = u256::shl(sqrt_price_128, 127 - m);
            i256::from_u128(((128 - m) as u128) << 64, true)
        };

        let (x, l2) = update_x_l2(63, x, l2);
        let (x, l2) = update_x_l2(62, x, l2);
        let (x, l2) = update_x_l2(61, x, l2);
        let (x, l2) = update_x_l2(60, x, l2);
        let (x, l2) = update_x_l2(59, x, l2);
        let (x, l2) = update_x_l2(58, x, l2);
        let (x, l2) = update_x_l2(57, x, l2);
        let (x, l2) = update_x_l2(56, x, l2);
        let (x, l2) = update_x_l2(55, x, l2);
        let (x, l2) = update_x_l2(54, x, l2);
        let (x, l2) = update_x_l2(53, x, l2);
        let (x, l2) = update_x_l2(52, x, l2);
        let (x, l2) = update_x_l2(51, x, l2);

        x = u256::mul(x, x);
        x = u256::shr(x, 127);
        let y = u256::shr(x, 128);
        l2 = i256::or(l2, i256::from_u256(u256::shl(y, 50)));

        let ls10001 = i256::mul(l2, i256::from_u128(255738958999603826347141, false));

        let log_floor = i256::as_i64(i256::shr(i256::sub(ls10001, i256::from_u128(3402992956809132418596140100660247210, false)), 128));
        let log_upper = i256::as_i64(i256::shr(i256::add(ls10001, i256::from_u128(291339464771989622907027621153398088495, false)), 128));

        if (i64::compare(&log_floor, &log_upper) == 0) {
            log_floor
        } else if (u256::compare(&get_sqrt_price(log_upper), &sqrt_price_96) == 0 || u256::compare(&get_sqrt_price(log_upper), &sqrt_price_96) == 1) {
            log_upper
        } else {
            log_floor
        }
    }

    #[test]
    fun test_log_sqrt_price() {
        print(&get_log_sqrt_price_floor(get_sqrt_price(i64::from(799999))));
        print(&get_log_sqrt_price_floor(get_sqrt_price(i64::from(1))));
        print(&get_log_sqrt_price_floor(get_sqrt_price(i64::from(0))));
        print(&i64::abs(&get_log_sqrt_price_floor(get_sqrt_price(i64::neg_from(1)))));
        print(&i64::abs(&get_log_sqrt_price_floor(get_sqrt_price(i64::neg_from(800000)))));
    }
}