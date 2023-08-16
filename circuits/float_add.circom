pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 * Assumes `n` bit inputs. The behavior is not well-defined if any input is more than `n`-bits long.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    assert(b < 254);
    signal input in;
    signal output out;

    var lc = 2**(b);
    component less_than = LessThan(b);
    log("checkBitLength");
    log(lc);
    log(in);
    less_than.in <== [in,lc];
    out <== less_than.out;
    log(out);

}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);


    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `b`-bit long `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(b, shift) {
    assert(shift < b);
    signal input x;
    signal output y;

    component num_bit = Num2Bits(b);
    num_bit.in <== x;

    var arr[b];
    for(var i = 0; i < b - shift; i++){
        arr[i] = num_bit.bits[shift + i];
    }

    component bit_num = Bits2Num(b);
    bit_num.bits <== arr;
    y <== bit_num.out;
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    //// Although m_prime is P+1 bits long in no overflow case, it can be P+2 bits long
    //// in the overflow case and the constraints should not fail in either case
    component right_shift = RightShift(P+2, round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;
    assert(0<= shift);
    if (skip_checks != 1) {
        assert(shift< shift_bound);
    }
    //find a  way to get number of bits
    //do loop until x = 0
    //1 more assertion (sum of bits === x * shift**2)
    var b = 252;
    signal bits[b];
    var bit_value = 0;
    var loop = 1;
    var i = 0;


    for (var i = 0; i < b; i++) {
        if (i<shift){
            bit_value = 0;
        }
        else  {
            bit_value = (x >> i-shift) & 1;
        }
        bits[i] <-- bit_value;
        bits[i] * (1 - bits[i]) === 0;
        
    } 
    
    component bit_num = Bits2Num(b);
    bit_num.bits <== bits;
    y <== bit_num.out;
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    //1 more assertion (sum of bits === x * shift**2)
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];
    signal bits[b];
    if (skip_checks != 1) {
        assert(in != 0);
    }
    var bit_value = 0;

    component num_bits = Num2Bits(b);
    num_bits.in <== in;
    bits <==  num_bits.bits;
    var msnzb = 0;
    for (var j = 0; j<b ; j++){
        if (bits[j] == 1){
            msnzb = j;
        }
    }
    for (var i = 0; i < b; i++) {
        if (i == msnzb){
            bit_value = 1;
        }
        else  {
            bit_value = 0;
        }
        one_hot[i] <-- bit_value;
        one_hot[i] * (1 - one_hot[i]) === 0;
    }
   
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */

template Normalize(k, p, P) {
    //e_out constraint
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    var ell[P+1];
    var bit_value = 0;

    if (skip_checks != 1) {
        assert(m != 0);
    }

    assert(P > p);
    component msnzp = MSNZB(P+1);
    msnzp.in <== m;
    msnzp.skip_checks <== skip_checks;
    ell = msnzp.one_hot;

    signal bits[P+1];
    var j = 0;
    var shift = -1;
    while (shift == -1) {
        shift = ell[j]*j - 1;
        j = j+1;
    }
    shift = shift + 1;
    for (var i = 0; i < P+1; i++) {
        if (i < P-shift){
            bit_value = 0;
        }
        else  {
            bit_value = (m >> i-P+shift) & 1;
        }
        bits[i] <-- bit_value;
        bits[i] * (1 - bits[i]) === 0;
    }
    component bit_num = Bits2Num(P+1);
    bit_num.bits <== bits;
    m_out <== bit_num.out;
    e_out <-- e + shift - p;
    //TO DO

}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;
    var P = 2*p+1;    

    component check_well_formedness1 = CheckWellFormedness(k,p);
    check_well_formedness1.e <== e[1];
    check_well_formedness1.m <== m[1];

    component check_well_formedness0 = CheckWellFormedness(k,p);
    check_well_formedness0.e <== e[0];
    check_well_formedness0.m <== m[0];

    component left_shift1 = LeftShift(252);
    left_shift1.x <== e[0];
    left_shift1.shift <== (p+1);
    left_shift1.skip_checks <== 0;

    component left_shift2 = LeftShift(252);
    left_shift2.x <== e[1];
    left_shift2.shift <== (p+1);
    left_shift2.skip_checks <== 0;

    var mgn_0 = left_shift1.y + m[0];
    var mgn_1 = left_shift2.y + m[1];


    component less_than = LessThan(252);
    less_than.in <== [mgn_0,mgn_1];
    signal less <== less_than.out;

    component if_then = IfThenElse();
    if_then.cond <== less;
    if_then.L <== e[0];
    if_then.R <== e[1];
    signal beta_e <== if_then.out;

    component if_then2 = IfThenElse();
    if_then2.cond <== less;
    if_then2.L <== e[1];
    if_then2.R <== e[0];
    signal alpha_e <== if_then2.out;

    component if_then3 = IfThenElse();
    if_then3.cond <== less;
    if_then3.L <== m[0];
    if_then3.R <== m[1];
    signal beta_m <== if_then3.out;

    component if_then4 = IfThenElse();
    if_then4.cond <== less;
    if_then4.L <== m[1];
    if_then4.R <== m[0];
    signal alpha_m <== if_then4.out;


    var diff = alpha_e - beta_e;
    component less_than2 = LessThan(252);
    less_than2.in <== [p+1,diff];

    component is_equal = IsEqual();
    is_equal.in <== [alpha_e,0];

    component or = OR();
    or.a <== less_than2.out;
    or.b <== is_equal.out;

    component norm = Normalize(k,p,P);
    component if_then5 = IfThenElse();
    if_then5.cond <== or.out;
    if_then5.L <== alpha_e;
    if_then5.R <== beta_e;
    norm.e <== if_then5.out;

    component left_shift = LeftShift(252);
    left_shift.x <== alpha_m;
    left_shift.shift <== diff;
    left_shift.skip_checks <== 0;

    component if_then6 = IfThenElse();
    if_then6.cond <== or.out;
    if_then6.L <== alpha_m;
    if_then6.R <== (left_shift.y + beta_m);
    norm.m <== if_then6.out;

    norm.skip_checks <== 0;
    signal norm_e <== norm.e_out;
    signal norm_m <== norm.m_out;

    component round = RoundAndCheck(k,p,P);
    round.e <== norm_e;
    round.m <== norm_m;

    e_out <== round.e_out;
    m_out <== round.m_out;

}


