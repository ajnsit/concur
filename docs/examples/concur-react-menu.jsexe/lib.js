/*
   GHCJS bignum library for integer-gmp package

   uses JavaScript arrays for big numbers
   some algorithms and code based on JSBN by Tom Wu

   Copyright Luite Stegeman 2016
 */








// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

// #define GHCJSBN_TRACE_INTEGER 1


// bits per limb




// BI_FP = 52
// BI_FP - GHCJSBN_BITS

// 2*GHCJSBN_BITS - BI_FP

// 2 ^ BI_FP


// values for the Haskell Ordering enum




var h$ghcjsbn_zero_i = (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (0)));;
var h$ghcjsbn_one_i = (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (1)));;
var h$ghcjsbn_negOne_i = (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-1)));;
var h$ghcjsbn_null_b = [-1];
var h$ghcjsbn_zero_b = [0];
var h$ghcjsbn_one_b = [1, 1];
var h$ghcjsbn_two31_b = [2, 0, 8];
var h$ghcjsbn_czero_b = [2, 268435455, 15];
var h$ghcjsbn_two31_i = (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (h$ghcjsbn_two31_b)));;
var h$ghcjsbn_negTwo31_i = (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-2147483648)));;

/******************************************************************************

 Types used here:
   - b BigNat:  array of limbs (each a number of GHCJSBN_BITS bits)
   - s Int:     small integer in range -2^31 .. 2^31-1
   - w Word:    small integer in range 0 .. 2^32-1,
                  values greater than 2^31-1 are stored as negative numbers
   - i Integer: Haskell Integer heap object, see invariants

 Integer invariants:
   - BigNat arrays do not have leading zeroes
   - Jp > S > Jn
   - S range: -2^31 .. 2^31-1 (-2147483648 .. 2147483647)

 ******************************************************************************/
// checks that the S,Jn,Jp constructor invariants hold
function h$ghcjsbn_assertValid_i(b, msg) {
  var sd, d, neg, i, n;
  // check global constants for unwanted mutations
  if(h$ghcjsbn_zero_b.length !== 1 || h$ghcjsbn_zero_b[0] !== 0) {
    throw new Error("zero_b mutated");
  }
  if(h$ghcjsbn_one_b.length !== 2 || h$ghcjsbn_one_b[0] !== 1 || h$ghcjsbn_one_b[1] !== 1) {
    throw new Error("one_b mutated");
  }
  if(((b).f === h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e)) {
    sd = ((b).d1);
    if(typeof sd !== 'number')
      throw new Error("invalid small integer: not a number");
    if((sd|0) !== sd)
      throw new Error("invalid small integer: not a small int");
  } else {
    if(((b).f === h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e)) {
      neg = false;
    } else if(((b).f === h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e)) {
      neg = true;
    } else {
      throw new Error("invalid integer: unexpected constructor");
    }
    d = ((b).d1);
    h$ghcjsbn_assertValid_b(d, "assertValid_i");
    if(d[0] < 2)
      throw new Error("invalid big integer: array too short");
    if(d[0] === 2) {
      if((d[2] >> (31-28)) === 0 ||
         (neg && d[2] === 0x20 && d[1] === 0))
        throw new Error("invalid big integer: in smallint range");
    }
    // everything ok
  }
}

// checks invariant for big number
function h$ghcjsbn_assertValid_b(d, msg) {
  var i, n;
  if(!Array.isArray(d))
    throw new Error("invalid big integer: not an array");




  if(typeof d[0] !== 'number' || d[0] > (d.length-1))
    throw new Error("invalid big integer: incorrect number of limbs");
  if(d[0] > 0 && d[d[0]] === 0)
    throw new Error("invalid big integer: leading zero");
  for(i = 1; i <= d[0]; i++) {
    n = d[i];
    if(typeof n !== 'number')
      throw new Error("invalid big integer: limb is not a number");
    if((n & 0xfffffff) !== n)
      throw new Error("invalid big integer: limb out of range");
  }
}

function h$ghcjsbn_assertValid_s(s, msg) {
  if(typeof s !== 'number')
    throw new Error("invalid int: not a number");



  if((s|0) !== s)
    throw new Error("invalid int: not in smallint range");
}

function h$ghcjsbn_assertValid_w(w, msg) {
  if(typeof w !== 'number')
    throw new Error("invalid word: not a number");



  if((w|0) !== w)
    throw new Error("invalid word: not in smallint range");
}

function h$ghcjsbn_assertValid_d(d, msg) {
  if(typeof d !== 'number')
    throw new Error("invalid double: not a number");



}
/******************************************************************************/

///////////////////////////////////////////////////////////////////////////////
// the ghcjsbn_r functions operate on the raw array data directly
///////////////////////////////////////////////////////////////////////////////



var h$ghcjsbn_smallPrimes =
 [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47
 , 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113
 , 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197
 , 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281
 , 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379
 , 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463
 , 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571
 , 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659
 , 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761
 , 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863
 , 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977
 , 983, 991, 997
 ];

var h$ghcjsbn_smallPrimesM = null;

function h$ghcjsbn_getSmallPrimesM() {
  var a, i;
  if(h$ghcjsbn_smallPrimesM === null) {
    a = [];
    for(i = 0; i < 1008; i++) {
      a[i] = false;
    }
    for(i = h$ghcjsbn_smallPrimes.length - 1; i >= 0; i--) {
      a[h$ghcjsbn_smallPrimes[i]] = true;
    }
    h$ghcjsbn_smallPrimesM = a;
  }
  return h$ghcjsbn_smallPrimesM;
}


// Int -> Int -> Bool
// fixme: seed
function h$ghcjsbn_isPrime_s(s, rounds) {
  if(s < 2 || (s > 2 && ((s&1) === 1))) return false;
  if(s <= 1008) {
    return h$ghcjsbn_getSmallPrimesM()[s];
  }
  throw new Error("isPrime_s");
}

// BigNat -> Int -> Bool
// fixme: seed
function h$ghcjsbn_isPrime_b(b, rounds) {
  h$ghcjsbn_assertValid_b(b, "isPrime");
  throw new Error("isPrime_b");
}

// BigNat -> BigNat -> Bool
/*
function h$ghcjsbn_eq_bb(b1, b2) {
  ASSERTVALID_B(b1, "eq_bb b1");
  ASSERTVALID_B(b2, "eq_bb b2");
  var l1 = b1.length, l2 = b2.length;
  if(l1 !== l2) return false;
  while(--l1 >= 0) {
    if(b1[l1] !== b2[l1]) return false;
  }
  return true;
}
*/

// BigNat -> BigNat -> Int (Ordering: LT,EQ,GT)
function h$ghcjsbn_cmp_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "cmp_bb b1");
  h$ghcjsbn_assertValid_b(b2, "cmp_bb b2");
  var l1 = b1[0], l2 = b2[0], d1, d2;
  if(l1 === l2) {
    while(--l1 >= 0) {
      d1 = b1[l1+1];
      d2 = b2[l1+1];
      if(d1 !== d2) return d1 < d2 ? 0 : 2;
    }
    return 1;
  } else {
    return l1 > l2 ? 2 : 0;
  }
}

// fixed size tmp, these should not grow
var h$ghcjsbn_tmp_2a = [0, 0, 0];
var h$ghcjsbn_tmp_2b = [0, 0, 0];

// this is variable size scratch space
var h$ghcjsbn_tmp_a = [0, 0, 0, 0, 0, 0, 0, 0];
var h$ghcjsbn_tmp_b = [0, 0, 0, 0, 0, 0, 0, 0];

// b - w :: BigNat -> Word -> BigNat

function h$ghcjsbn_sub_bw(b, w) {
  var a = h$ghcjsbn_tmp_2a;
  h$ghcjsbn_toBigNat_w(a, w);
  return h$ghcjsbn_sub_bb(b, a);
}

// b - s :: BigNat -> Int -> BigNat
// returns new BigNat, nullBigNat in case of underflow
// returns size of t
function h$ghcjsbn_sub_bs(b, s) {
  h$ghcjsbn_assertValid_b(b, "sub_bs");
  h$ghcjsbn_assertValid_s(s, "sub_bs");
  var a, ms, r;
  if(s < 0) {
    if(s === -2147483648) {
      r = h$ghcjsbn_add_bb(b, h$ghcjsbn_two31_b);
    } else {
      a = h$ghcjsn_tmp_2a;
      h$ghcjsbn_toBigNat_s(a, -s);
      r = h$ghcjsbn_add_bb(b, a);
    }
  } else {
    a = h$ghcjsn_tmp_2a;
    h$ghcjsbn_toBigNat_s(a, s);
    r = h$ghcjsbn_sub_bb(b, a);
  }
  h$ghcjsbn_assertValid_b(r, "sub_bs result");
  return r;
}

// t = b + w :: BigNat -> BigNat -> Word -> Int
// returns size of t
function h$ghcjsbn_add_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "add_bw");
  h$ghcjsbn_assertValid_w(w, "add_bw");
  var a = h$ghcjsbn_tmp_2a;
  h$ghcjsbn_toBigNat_w(a, w);
  return h$ghcjsbn_add_bb(b, a);
}

// t = b + s :: BigNat -> BigNat -> Int -> Int
// returns size of t, nullBigNat in case of underflow
function h$ghcjsbn_add_bs(b, s) {
  h$ghcjsbn_assertValid_b(b, "add_bs");
  h$ghcjsbn_assertValid_s(s, "add_bs");
  var a, ms, r;
  if(s < 0) {
    if(s === -2147483648) {
      r = h$ghcjsbn_sub_bb(b, h$ghcjsbn_two31_r);
    } else {
      ms = -s;
      a = h$ghcjsbn_tmp_2a;
      h$ghcjsbn_toBigNat_s(a, ms);
      r = h$ghcjsbn_sub(b, a);
    }
  } else {
    a = h$ghcjsbn_tmp_2a;
    h$ghcjsbn_toBigNat_s(a, s);
    r = h$ghcjsbn_add_bb(b, a);
  }
  h$ghcjsbn_assertValid_b(r, "add_bs result");
  return r;
}

// t = b1 + b2 :: BigNat -> BigNat -> BigNat -> Int
// returns size of t
function h$ghcjsbn_add_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "add_bb b1");
  h$ghcjsbn_assertValid_b(b2, "add_bb b2");
  var i, c = 0, l1 = b1[0], l2 = b2[0], t = [0];
  var bl, lmin, lmax;
  if(l1 <= l2) {
    lmin = l1;
    lmax = l2;
    bl = b2;
  } else {
    lmin = l2;
    lmax = l1;
    bl = b1;
  }
  for(i=1;i<=lmin;i++) {
    c += b1[i] + b2[i];
    t[i] = c & 0xfffffff;
    c >>= 28;
  }
  for(i=lmin+1;i<=lmax;i++) {
    c += bl[i];
    t[i] = c & 0xfffffff;
    c >>= 28;
  }
  if(c !== 0) t[++lmax] = c;
  t[0] = lmax;
  h$ghcjsbn_assertValid_b(t, "add_bb result");
  return t;
}

// b1 += b2 :: BigNat -> BigNat -> Int
// returns new size of b1
function h$ghcjsbn_addTo_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "addTo_bb b1");
  h$ghcjsbn_assertValid_b(b2, "addTo_bb b2");
  var i, c = 0, l1 = b1[0], l2 = b2[0];
  if(l2 > l1) {
    for(i = l1 + 1; i <= l2; i++) {
      b1[i] = 0;
    }
    l1 = l2;
  }
  for(i = 1; i <= l2; i++) {
    c += b1[i] + b2[i];
    b1[i] = c & 0xfffffff;
    c >>= 28;
  }
  // propagate carry as long as needed
  for(i = l2 + 1; c !== 0 && i <= l1; i++) {
    c += b1[i];
    b1[i] = c & 0xfffffff;
    c >>= 28;
  }
  if(c !== 0) {
    b1[l1] = c;
    b1[0] = l1+1;
  } else {
    b1[0] = l1;
  }
  h$ghcjsbn_assertValid_b(b1, "addTo_bb result");
}

// b1 - b2 :: BigNat -> BigNat -> BigNat
// returns a new BigNat, nullBigNat in case of underflow
function h$ghcjsbn_sub_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "sub_bb b1");
  h$ghcjsbn_assertValid_b(b2, "sub_bb b2");
  if(h$ghcjsbn_cmp_bb(b1,b2) === 0) {
    return [];
  } else {
    var i, c = 0, l1 = b1[0], l2 = b2[0], t = [0];
    for(i = 1; i <= l2; i++) {
      c += b1[i] - b2[i];
      t[i] = c & 0xfffffff;
      c >>= 28;
    }
    for(i = l2 + 1; i <= l1; i++) {
      c += b1[i];
      t[i] = c & 0xfffffff;
      c >>= 28;
    }
    while(l1 > 0 && t[l1] === 0) l1--;
    t[0] = l1;
    h$ghcjsbn_assertValid_b(t, "sub_bb result");
    return t;
  }
}

// b1 -= b2 :: BigNat -> BigNat -> Int
// returns size of t, b1 must be >= b2
function h$ghcjsbn_subTo_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "subTo_bb b1");
  h$ghcjsbn_assertValid_b(b2, "subTo_bb b2");

  if(h$ghcjsbn_cmp_bb(b1, b2) === 0) {
    throw new Error("h$ghcjsbn_subTo_bb assertion failed: b1 >= b2");
  }

  var i, c = 0, l1 = b1[0], l2 = b2[0];
  for(i = 1; i <= l2; i++) {
    c += b1[i] - b2[i];
    b1[i] = c & 0xfffffff;
    c >>= 28;
  }
  for(i = l2 + 1; c !== 0 && i <= l1; i++) {
    c += b1[i];
    b1[i] = c & 0xfffffff;
    c >>= 28;
  }
  while(l1 > 0 && b1[l1] === 0) l1--;
  b1[0] = l1;
  h$ghcjsbn_assertValid_b(b1, "subTo_bb result");
}

// t = b1 / b2, BigNat -> BigNat -> BigNat -> Int (returns size of t)
/* function h$ghcjsbn_div_bb(t, b1, b2) {

}

// t = b1 % b2, BigNat -> BigNat -> BigNat -> Int (returns size of t)
function h$ghcjsbn_mod_bb(t, b1, b2) {

}

// b % s, BigNat -> Int -> Int
function h$ghcjsbn_mod_bs(b, s) {

}
*/
// BigNat -> Integer (nonnegative, known length)
/*
function h$ghcjsbn_wrap_pl(b, l) {
  var lb;
  if(l === 0) {
    return MK_INTEGER_S(0);
  } else if(l === 1) {
    return MK_INTEGER_S(b[0]);
  } else if(l === 2 && (b[1] >> (31 - GHCJSBN_BITS)) === 0) {
    return MK_INTEGER_S((b[1] << GHCJSBN_BITS)|b[0]);
  } else {
    lb = b.length - l;
    while(lb-- > 0) b.pop();
    return MK_INTEGER_Jp(b);
  }
}
*/
// BigNat -> Integer (nonnegative)
function h$ghcjsbn_wrap_p(b) {
  var l = b[0];
  if(l === 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (0)));;
  } else if(l === 1) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (b[1])));;
  } else if(l === 2 && (b[2] >> (31 - 28)) === 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, ((b[2] << 28)|b[1])));;
  } else {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (b)));;
  }
}
/*
function h$ghcjsbn_wrap_nl(b, l) {
  var lb;
  if(l === 0) {
    return MK_INTEGER_S(0);
  } else if(l === 1) {
    return MK_INTEGER_S(-b[0]);
  } else if(l === 2 &&
            ((b[1] >> (31 - GHCJSN_BITS)) === 0 ||
             (b[1] === (1 << (31 - GHCJSBN_BITS)) && b[0] === 0))) {
    return MK_INTEGER_S((-b[1]-b[0])|0);
  } else {
    lb = b.length - l;
    while(lb-- > 0) b.pop();
    return MK_INTEGER_Jn(b);
  }
}
*/
// BigNat -> Integer (nonnegative)
function h$ghcjsbn_wrap_n(b) {
  var l = b[0];
  if(l === 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (0)));;
  } else if(l === 1) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-b[1])));;
  } else if(l === 2 &&
            ((b[2] >> (31 - GHCJSN_BITS)) === 0 ||
             (b[2] === (1 << (31 - 28)) && b[1] === 0))) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, ((-b[2]-b[1])|0)));;
  } else {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (b)));;
  }
}

// b1 *= b2 :: BigNat -> BigNat -> IO ()
function h$ghcjsbn_mulTo_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "mulTo_bb b1");
  h$ghcjsbn_assertValid_b(b2, "mulTo_bb b2");
  var t = h$ghcjsbn_mul_bb(b1, b2);
  h$ghcjsbn_copy(b1, t);
  h$ghcjsbn_assertValid_b(b1, "mulTo_bb result");
}

// b1 * b2 ::  BigNat -> BigNat -> BigNat
function h$ghcjsbn_mul_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "mul_bb b1");
  h$ghcjsbn_assertValid_b(b2, "mul_bb b2");
  var l1 = b1[0], l2 = b2[0];
/*  if(l1 > 50 && l2 > 50) {
    return h$ghcjsbn_mul_karatsuba_bb(b1, b2);
  } fixme update this */
  var n = l1 + l2, i, t = [0];
  for(i = 1; i <= n; i++) t[i] = 0;
  if(l1 > l2) {
    for(i = 0; i < l2; i++) {
      t[i + l1 + 1] = h$ghcjsbn_mul_limb(0, b1, b2[i+1], t, i, 0, l1);
    }
  } else {
    for(i = 0; i < l1; i++) {
      t[i + l2 + 1] = h$ghcjsbn_mul_limb(0, b2, b1[i+1], t, i, 0, l2);
    }
  }
  for(i = l1 + l2; i > 0 && t[i] === 0; i--);
  t[0] = i;
  h$ghcjsbn_assertValid_b(t, "mul_bb result");
  return t;
}

function h$ghcjsbn_mul_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "mul_bw");
  h$ghcjsbn_assertValid_w(w, "mul_bw");
  var a = h$ghcjsbn_tmp_2a;
  h$ghcjsbn_toBigNat_w(a, w);
  var t = h$ghcjsbn_mul_bb(b, a);
  h$ghcjsbn_assertValid_b(t, "mul_bw result");
  return t;
}


// karatzuba multiplication for long numbers
function h$ghcjsbn_mul_karatsuba_bb(t, b1, b2) {
  throw new Error("not yet updated");
  var l1 = b1.length, l2 = b2.length;
  var i, b = (l1 < l2 ? l1 : l2) >> 1;
  var x0 = [b], x1 = [l1-b], y0 = [b], y1 = [l2-b];
  for(i = 1; i <= b; i++) {
    x0[i] = b1[i];
    y0[i] = b2[i];
  }
  for(i = b + 1; i <= l1; i++) x1[i - b] = b1[i];
  for(i = b + 1; i <= l2; i++) y1[i - b] = b2[i];
  var z0 = h$ghcjsbn_mul_bb(x0, y0), z1, z2 = h$ghcjsbn_mul_bb(x1, y1);

  // compute z1 = (x1 + x0)(y1 + y0) - z2 - z0
  // (reusing x0 and y0 for (x1 + x0) and (y1 + y0))
  h$ghcjsbn_addTo_bb(x0, x1);
  h$ghcjsbn_addTo_bb(y0, x1);
  z1 = h$ghcjsbn_mul_bb(x0, y0);
  h$ghcjsbn_subTo_bb(z1, z2);
  h$ghcjsbn_subTo_bb(z1, z0);
  // store shifted z2 in t
  // fixme this looks wrong
  for(i = 0; i < 2*b; i++) t[i] = 0;
  l2 = z2.length;
  for(i = 0; i < l2; i++) t[i+2*b] = z2[i];
  // compute shifted z1s = z1 * B
  var z1s = [];
  l1 = z1.length;
  for(i = 0; i < b; i++) z1s[i] = 0;
  for(i = 0; i < l1; i++) z1s[i+b] = z1[i];
  // add the results so that t = z2 * (2*B) + z1 * B + z0
  h$ghcjsbn_addTo_bb(t, z1s);
  h$ghcjsbn_addTo_bb(t, z0);
  return t;
}

// from JSBN am3
// w_j += (x*b_i) ?
/* c = carry?
   n = iterations?
 */

function h$ghcjsbn_mul_limb(i,b,x,w,j,c,n) {
  // ASSERTVALID_B(b, "mul_limb b");
  // ASSERTVALID_B(w, "mul_limb w");
  var xl = x & 0x3fff, xh = x >> 14;
  while(--n >= 0) {
    var l = b[++i] & 0x3fff;
    var h = b[i] >> 14;
    var m = xh * l + h * xl;
    l = xl *l + ((m & 0x3fff) << 14) + w[++j] + c;
    c = (l >> 28) + (m >> 14) + xh * h;
    // h$log("mul_limb: c: " + c + " l: " + l + " xh: " + xh + " h: " + h);
    w[j] = l & 0xfffffff;
  }
  return c;
}




// q = b1 / b2, r = b1 % b2 :: BigNat -> BigNat -> BigNat -> BigNat -> Int
// b2 must be > 0
// returns length of r
// d is normalized before return

/*
   algorithm:
 y = 0?
 nsh = number of leading zeroes in most significant word
 pm = positive modulus
 pt = positive divident
 y = tmp, shifted modulus
 r = shifted divident
 ys = length of y
 y0 = biggest limb of y
 yt = new estimated length of y?
 */

function h$ghcjsbn_quotRem_bb(q, r, b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "quotRem_bb b1");
  h$ghcjsbn_assertValid_b(b2, "quotRem_bb b2");

  if(h$ghcjsbn_cmp_bw(b2, 0) !== 2) {
    throw new Error("h$ghcjsbn_quotRem_bb: operand not positive");
  }

  if(q === null) q = h$ghcjsbn_tmp_a;
  if(r === null) r = h$ghcjsbn_tmp_b;
  var l1 = b1[0], l2 = b2[0], nsh, y = [];
  if(l1 === 0) {
    q[0] = 0;
    r[0] = 0;
    return;
  }
  if(h$ghcjsbn_cmp_bb(b1,b2) === 0) {
    q[0] = 0;
    h$ghcjsbn_copy(r, b1);
    return;
  }
  nsh = 28 -h$ghcjsbn_nbits_s(b2[l2]);
  h$ghcjsbn_assertValid_s(nsh, "quotRem_bb nsh");
  if(nsh !== 0) {
    h$ghcjsbn_shlTo_b(y, b2, nsh);
    h$ghcjsbn_shlTo_b(r, b1, nsh);
  } else {
    h$ghcjsbn_copy(y, b2);
    h$ghcjsbn_copy(r, b1);
  }
  h$ghcjsbn_assertValid_b(y, "quotRem_bb y_0");
  h$ghcjsbn_assertValid_b(r, "quotRem_bb r_0");
  var ys = y[0], y0 = y[ys];
  var yt = y0*(1<<24)+((ys>1)?y[ys-1]>>4:0);
  var d1 = 4503599627370496/yt, d2 = (1<<24)/yt, e = 1 << 4;
  var i = r[0], j = i-ys, t = q;
  h$ghcjsbn_shlTo_limbs_b(t,y,j);
  // h$log("rt1: " + i);
  // h$log("[" + r.join(",") + "] [" + t.join(",") + "]");
  if(h$ghcjsbn_cmp_bb(r, t) !== 0) {
    r[r[0]+1] = 1;
    r[0] += 1;
    // h$log("rt1a: " + r[0]);
    h$ghcjsbn_subTo_bb(r, t);
  }
  // h$log("rt2: " + r[0]);
  // h$log("y0: " + y0 + " yt: " + yt + " d1: " + d1 + " d2: " + d2 + " e: " + e);
  h$ghcjsbn_shlTo_limbs_b(t, h$ghcjsbn_one_b, ys);
  y = h$ghcjsbn_sub_bb(t, y);
  while(y.length <= ys) y[y.length] = 0; // fixme? no looks ok
  while(--j >= 0) {
    // Estimate quotient digit
    var qd = (r[(--i)+1]===y0)?0xfffffff:Math.floor(r[i+1]*d1+(r[i]+e)*d2);
    // h$log("i: " + i + " j: " + j + " qd: " + qd + " rdi: " + r[i+1] + " ys: " + ys);
    // h$log("yd: [" + y.join(',') + "] rd: [" + r.join(',') + "]");
    var am = h$ghcjsbn_mul_limb(0, y, qd, r, j, 0, ys);
    // h$log("am: " + am);
    if((r[i+1] += am) < qd) {
    // if((r[i+1] += h$ghcjsbn_mul_limb(0, y, qd, r, j, 0, ys)) < qd) {
      h$ghcjsbn_shlTo_limbs_b(t, y, j);
      h$ghcjsbn_subTo_bb(r, t);
      // h$log("0. rdi: " + r[i+1] + " qd: " + qd);
      while(r[i+1] < --qd) {
        // h$log("1. rdi: " + r[i+1] + " qd: " + qd);
        h$ghcjsbn_subTo_bb(r, t);
      }
    }
  }
  h$ghcjsbn_assertValid_b(r, "intermediate r");
  h$ghcjsbn_shrTo_limbs_b(q, r, ys);
  r[0] = ys;
  while(r[r[0]] === 0 && r[0] > 0 && r[0]--);
  if(nsh !== 0) {
    var r0 = [];
    h$ghcjsbn_copy(r0, r);
    h$ghcjsbn_shrTo_b(r, r0, nsh);
  }
  h$ghcjsbn_assertValid_b(q, "quotRem_bb result q");
  h$ghcjsbn_assertValid_b(r, "quotRem_bb result r");
}

// b % w , q = b / w :: BigNat -> BigNat -> Word -> Word
function h$ghcjsbn_quotRem_bw(q, b, w) {
  h$ghcjsbn_assertValid_b(b, "quotRem_bw");
  h$ghcjsbn_assertValid_w(w, "quotRem_bw");
  var a = h$ghcjsbn_tmp_2a;
  h$ghcjsbn_toBigNat_w(a, w);
/*  if(w === 0) {
    a[0] = 0;
  } else if(w > 0 && w <= GHCJSBN_MASK) {
    a[0] = 1;
    a[1] = w;
  } else {
    a[0] = 2;
    a[1] = w   & GHCJSBN_MASK;
    a[2] = w >>> GHCJSBN_BITS;
  } */
  var r = [];
  h$ghcjsbn_quotRem_bb(q, r, b, a);
  return h$ghcjsbn_toWord_b(r);
}

// BigNat -> JSBN
// assumes same number of bits
function h$ghcjsbn_tmp_toJSBN(b) {
  var j = new BigInteger(), bl = b[0], i;
  for(i = 0; i < bl; i++) j.data[i] = b[i+1];
  j.s = 0;
  j.t = bl;
  return j;
/*  ASSERTVALID_B(b, "toJSBN");
  var j0 = new BigInteger();
  var j1 = new BigInteger();
  var j2 = new BigInteger();
  for(var i = b[0]; i > 0; i--) {
    h$log("i: " + b[i]);
    j2.fromString('' + b[i]);
    j0.lShiftTo(28, j1);
    j1.addTo(j2, j0);
  }
  return j0; */
}

// b = fromJSBN(j) :: BigNat -> JSBN -> Int
// returns length
function h$ghcjsbn_tmp_fromJSBN(b, j) {
  var bl = j.t, i;
  for(i = 0; i < bl; i++) {
    b[i] = j.data[i];
  }
  return bl;
}


// function h$ghcjsbn_divMod_bs(d

// t = b1 % b2 :: BigNat -> BigNat -> BigNat
function h$ghcjsbn_rem_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "rem_bb b1");
  h$ghcjsbn_assertValid_b(b2, "rem_bb b2");
  var t1 = [], t2 = [];
  h$ghcjsbn_quotRem_bb(t1, t2, b1, b2);
  h$ghcjsbn_assertValid_b(t2, "rem_bb result");
  return t2;
}

// b1 % s :: BigNat -> Word -> Word
function h$ghcjsbn_rem_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "rem_bw");
  h$ghcjsbn_assertValid_w(w, "rem_bw");
  //  var t1 = [];
  var r = h$ghcjsbn_quotRem_bw([] /* t1 */, b, w);
  h$ghcjsbn_assertValid_w(r, "rem_bw result");
  return r;
//  var a = h$ghcjsbn_tmp_2a;
//  h$ghcjsbn_toBigNat_w(a, w);
//  a[1] = w   & GHCJSBN_MASK;
//  a[2] = w >>> GHCJSBN_BITS;
//  var t1 = []; // , t2 = h$ghcjsbn_tmp_2b;
//  return h$ghcjsbn_quotRem_bw(t1, /* t2 , */ b, a);
//  return t[1] | (t[2] << GHCJSBN_BITS);
}

// b1 / b2 :: BigNat -> BigNat -> BigNat
function h$ghcjsbn_quot_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "quot_bb b1");
  h$ghcjsbn_assertValid_b(b2, "quot_bb b2");
  var t1 = [], t2 = [];
  h$ghcjsbn_quotRem_bb(t1, t2, b1, b2);
  h$ghcjsbn_assertValid_b(t1, "quot_bb result");
  return t1;
}
/*
// b / s :: BigNat -> Int -> BigNat
function h$ghcjsbn_div_bs(b, w) {
  ASSERTVALID_B(b, "div_bs");
  ASSERTVALID_S(s, "div_bs");
#ifdef GHCJS_ASSERT_INTEGER
  if(s <= 0) {
    throw new Error("h$ghcjsbn_div_bs: divisor must be positive");
  }
#endif
  var a = h$ghcjsbn_tmp_2a;
  a[0] = s &  GHCJSBN_MASK;
  a[1] = s >> GHCJSBN_BITS;
  return h$ghcjsbn_div_bb(t, b, a);
}
*/
// t = b % w :: BigNat -> BigNat -> Word -> Int
// returns length of t
/*
function h$ghcjsbn_div_bw(t, b, w) {
  ASSERTVALID_B(b, "div_bw");
  ASSWRTVALID_W(w, "div_bw");
  var a = h$ghcjsbn_tmp_2a;
 a[0] = w   & GHCJSBN_MASK;
 a[1] = w >>> GHCJSBN_BITS;
  return h$ghcjsbn_div_bb(t, b, a);
}
*/
// b ^ 2 :: BigNat -> BigNat
function h$ghcjsbn_sqr_b(b) {
  h$ghcjsbn_assertValid_b(b, "sqr_b");
  var l = b[0], n = 2 * l, i, c, t = [0];
  for(i = 1; i <= n; i++) t[i] = 0;
  for(i = 0; i < l - 1; i++) {
    c = h$ghcjsbn_mul_limb(i, b, b[i+1],t,2*i,0,1);
    if((t[i + l + 1] += h$ghcjsbn_mul_limb(i+1, b, 2*b[i+1], t, 2*i+1, c, l - i - 1)) >= 0x10000000) {
      t[i + l + 1] -= 0x10000000;
      t[i + l + 2] = 1;
    }
  }
  if(n > 0) t[n] += h$ghcjsbn_mul_limb(i, b, b[i+1], t, 2*i, 0, 1);
  if(t[n] === 0) n--;
  t[0] = n;
  h$ghcjsbn_assertValid_b(t, "sqr_b result");
  return t;
}

// b1 ^ b2 :: BigNat -> BigNat -> BigNat
// returns size of t
function h$ghcjsbn_pow_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "pow_bb b1");
  h$ghcjsbn_assertValid_b(b2, "pow_bb b2");
  var i, sq = b1, t = [1,1];
  var bits = h$ghcjsbn_nbits_b(b2);
  for(i = 0; i < bits; i++) {
    if(h$ghcjsbn_testBit_b(b2, i)) {
      h$ghcjsbn_mulTo_bb(t, sq);
    }
    sq = h$ghcjsbn_sqr_b(sq);
  }
  return t;
}

// t = b ^ s :: BigNat -> Word -> BigNat
function h$ghcjsbn_pow_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "pow_bw");
  h$ghcjsbn_assertValid_w(w, "pow_bw");
  var i, sq = b, t = [1,1];
  while(w) {
    if(w&1) h$ghcjsbn_mulTo_bb(t, sq);
    w >>>= 1;
    if(w) {
      sq = h$ghcjsbn_sqr_b(sq);
    }
  }
  h$ghcjsbn_assertValid_b(t, "pow_bw result");
  return t;
}

// w1 ^ w2 :: Word -> Word -> BigNat
function h$ghcjsbn_pow_ww(w1, w2) {
  h$ghcjsbn_assertValid_s(w1, "pow_ww w1");
  h$ghcjsbn_assertValid_s(w2, "pow_ww w2");
  var b = h$ghcjsbn_tmp_2a;
  h$ghcjsbn_toBigNat_w(b, w1);
  var t = h$ghcjsbn_pow_bw(b, w2);
  h$ghcjsbn_assertValid_b(t, "pow_ww result");
  return t;
}

// (b ^ s1) % s2 :: BigNat -> BigNat -> BigNat -> BigNat
function h$ghcjsbn_modPow_bbb(b, s1, s2) {
  throw new Error("modPow_bbb");
}

// (b ^ s1) % s2 :: BigNat -> Int -> Int -> Int
function h$ghcjsbn_modPow_bss(b, s1, s2) {
  throw new Error("modPow_bss");
}

// (s1 ^ s2) % s3 :: Int -> Int -> Int -> Int
function h$ghcjsbn_modPow_sss(s1, s2, s3) {
  throw new Error("modPow_sss");
}



// r = gcd(b1,b2) BigNat -> BigNat -> BigNat
function h$ghcjsbn_gcd_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "gcd_bb b1");
  h$ghcjsbn_assertValid_b(b2, "gcd_bb b2");
  var r;
  if(h$ghcjsbn_cmp_bb(b1, b2) === 2) {
    r = b1;
    b1 = b2;
    b2 = r;
  }
  while(b1[0] > 0) {
    r = h$ghcjsbn_rem_bb(b2, b1);
    b2 = b1;
    b1 = r;
  }
  h$ghcjsbn_assertValid_b(b2, "gcd_bb result");
  return b2;
}
// gcd(b,s) :: BigNat -> Int -> Int
function h$ghcjsbn_gcd_bs(b, s) {
  throw new Error("h$ghcjsbn_gcd_bs not implemented");
}

// gcd(s1,s2) :: Int -> Int -> Int
function h$ghcjsbn_gcd_ss(s1, s2) {
  h$ghcjsbn_assertValid_s(s1, "gcd_ss s1");
  h$ghcjsbn_assertValid_s(s2, "gcd_ss s2");
  var a, b, r;
  a = s1 < 0 ? -s1 : s1;
  b = s2 < 0 ? -s2 : s2;
  if(b < a) {
    r = a;
    a = b;
    b = r;
  }
  while(a !== 0) {
    r = b % a;
    b = a;
    a = r;
  }
  h$ghcjsbn_assertValid_s(b, "gcd_ss result");
  return b;
}

// gcd(w1,w2) :: Word -> Word -> Word
// fixme negatives are probably wrong here
function h$ghcjsbn_gcd_ww(w1, w2) {
  h$ghcjsbn_assertValid_w(w1, "gcd_ww w1");
  h$ghcjsbn_assertValid_w(w2, "gcd_ww w2");
  var a, b, r;
  a = w1 < 0 ? (w1 + 4294967296) : w1;
  b = w2 < 0 ? (w2 + 4294967296) : w2;
  if(b < a) {
    r = a;
    a = b;
    b = r;
  }
  while(a !== 0) {
    r = b % a;
    b = a;
    a = r;
  }
  b = b|0;
  h$ghcjsbn_assertValid_w(b, "gcd_ww result");
  return b;
}

function h$ghcjsbn_gcd_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "gcd_bw");
  h$ghcjsbn_assertValid_w(w, "gcd_bw");
  var q = [], r = h$ghcjsbn_quotRem_bw(q, b, w);
  h$ghcjsbn_assertValid_w(r, "gcd_bw r");
  if(r === 0) {
    return b[0] === 0 ? 0 : w;
  } else {
    return h$ghcjsbn_gcd_ww(r, w);
  }
}

// b >> s :: BigNat -> Int -> BigNat
function h$ghcjsbn_shr_b(b, s) {
  h$ghcjsbn_assertValid_b(b, "shr_b");
  h$ghcjsbn_assertValid_s(s, "shr_b");

  if(s < 0) throw new Error("h$ghcjsbn_shr_b: negative operand");

  var i, v1, v2, l = b[0], sl = (s / 28)|0, t = [0];
  l -= sl;
  if(l <= 0) {
    t[0] = 0;
  } else {
    var sb1 = s % 28, sb2 = 28 - sb1, m = (1<<sb1)-1;
    var c = b[sl + 1] >> sb1, v;
    for(i = 1; i < l; i++) {
      v = b[i + sl + 1];
      t[i] = ((v&m) << sb2)|c;
      c = v >> sb1;
    }
    if(c !== 0) {
      t[l] = c;
      t[0] = l;
    } else {
      t[0] = l - 1;
    }
  }
  h$ghcjsbn_assertValid_b(t, "shr_b result");
  return t;
}

// t = b >> s :: BigNat -> BigNat -> Int -> IO ()
function h$ghcjsbn_shrTo_b(t, b, s) {
  h$ghcjsbn_assertValid_b(b, "shrTo_b");
  h$ghcjsbn_assertValid_s(s, "shrTo_b");

  if(s < 0) throw new Error("h$ghcjsbn_shrTo_b: negative operand");

  var i, v1, v2, l = b[0], sl = (s / 28)|0;
  t[0] = 0;
  l -= sl;
  if(l <= 0) {
    t[0] = 0;
  } else {
    var sb1 = s % 28, sb2 = 28 - sb1, m = (1<<sb1)-1;
    var c = b[sl + 1] >> sb1, v;
    for(i = 1; i < l; i++) {
      v = b[i + sl + 1];
      t[i] = ((v&m) << sb2)|c;
      c = v >> sb1;
    }
    if(c !== 0) {
      t[l] = c;
      t[0] = l;
    } else {
      t[0] = l - 1;
    }
  }
  h$ghcjsbn_assertValid_b(t, "shrTo_b result");
}

function h$ghcjsbn_shr_neg_b(b, s) {
  throw new Error ("shr_neg_b not implemented");
}

// b << s :: BigNat -> Int -> BigNat
function h$ghcjsbn_shl_b(b, s) {
  h$ghcjsbn_assertValid_b(b, "shl_b");
  h$ghcjsbn_assertValid_s(s, "shl_b");

  if(s < 0) throw new Error("h$ghcjsbn_shl_b: negative operand");

  var sl = (s / 28)|0;
  var sb1 = s % 28, sb2 = 28 - sb1;
  // mask wrong
  var l = b[0];
  if(l === 0) return h$ghcjsbn_zero_b;
  var c = 0, i, v, m = (1 <<sb1) - 1, t = [0];
  for(i = 1; i <= sl; i++) {
    t[i] = 0;
  }
  for(i = 1; i <= l; i++) {
    v = b[i];
    t[i + sl] = ((v << sb1) & 0xfffffff) | c;
    c = v >> sb2;
  }
  if(c !== 0) {
    t[l+sl+1] = c;
    t[0] = l + sl + 1;
  } else {
    t[0] = l + sl;
  }
  h$ghcjsbn_assertValid_b(t, "shl_b result");
  return t;
}

// t = b << s :: BigNat -> BigNat -> Int -> IO ()
function h$ghcjsbn_shlTo_b(t, b, s) {
  h$ghcjsbn_assertValid_b(b, "shlTo_b");
  h$ghcjsbn_assertValid_s(s, "shlTo_b");

  if(s < 0) throw new Error("h$ghcjsbn_shlTo_b: negative operand");

  var sl = (s / 28)|0;
  var sb1 = s % 28, sb2 = 28 - sb1;
  // mask wrong
  var l = b[0], c = 0, i, v, m = (1 <<sb1) - 1;
  t[0] = 0;
  for(i = 1; i <= sl; i++) {
    t[i] = 0;
  }
  for(i = 1; i <= l; i++) {
    v = b[i];
    t[i + sl] = ((v << sb1) & 0xfffffff) | c;
    c = v >> sb2;
  }
  if(c !== 0) {
    t[l+sl+1] = c;
    t[0] = l + sl + 1;
  } else {
    t[0] = l + sl;
  }
  h$ghcjsbn_assertValid_b(t, "shlTo_b result");
}


// t = b >> (GHCJSBN_BITS * s) :: BigNat -> BigNat -> Int
function h$ghcjsbn_shrTo_limbs_b(t, b, s) {
  h$ghcjsbn_assertValid_b(b, "shrTo_limbs_b");
  h$ghcjsbn_assertValid_s(s, "shrTo_limbs_b");

  if(s < 0) throw new Error("h$ghcjsbn_shrTo_limbs_b: negative operand");

  var l = b[0], l1 = l - s, i;
  if(l1 < 1) {
    t[0] = 0;
  } else {
    t[0] = l1;
    for(i = 1; i <= l1; i++) t[i] = b[i+s];
  }
  h$ghcjsbn_assertValid_b(t, "shrTo_limbs_b result");
}

// t = b << (GHCJSBN_BITS * s) :: BigNat -> BigNat -> Int
function h$ghcjsbn_shlTo_limbs_b(t, b, s) {
  h$ghcjsbn_assertValid_b(b, "shlTo_limbs_b");
  h$ghcjsbn_assertValid_s(s, "shlTo_limbs_b");

  if(s < 0) throw new Error("h$ghcjsbn_shlTo_limbs_b: negative operand");

  var l = b[0], l1 = l + s, i;
  if(l === 0) {
    t[0] = 0;
  } else {
    t[0] = l1;
    for(i = 1; i <= s; i++) t[i] = 0;
    for(i = s+1; i <= l1; i++) t[i] = b[i-s];
  }
  h$ghcjsbn_assertValid_b(t, "shlTo_limbs_b result");
}

function h$ghcjsbn_nbits_b(b) {
  h$ghcjsbn_assertValid_b(b, "nbits_b");
  var l = b[0], c = 0, s, t;
  if(l === 0) {
    return 0;
  } else {
    var r = ((l-1)*28) + h$ghcjsbn_nbits_s(b[l]);
    h$ghcjsbn_assertValid_s(r, "nbits_b result");
    return r;
  }
}

function h$ghcjsbn_nbits_s(s) {
  h$ghcjsbn_assertValid_s(s, "nbits_s");
  var c = 1, t;
  if((t = s >>> 16) != 0) { s = t; c += 16; }
  if((t = s >> 8) != 0) { s = t; c += 8; }
  if((t = s >> 4) != 0) { s = t; c += 4; }
  if((t = s >> 2) != 0) { s = t; c += 2; }
  if((t = s >> 1) != 0) { s = t; c += 1; }
  h$ghcjsbn_assertValid_s(c, "nbits_s result");
  return c;
}

// BigNat -> Word -> String
function h$ghcjsbn_showBase(b, base) {
  h$ghcjsbn_assertValid_b(b, "showBase");
  h$ghcjsbn_assertValid_s(base, "showBase");
  if(h$ghcjsbn_cmp_bb(b, h$ghcjsbn_zero_b) === 1) {
    return "0";
  } else {
    return h$ghcjsbn_showBase_rec(b, base, Math.log(base), 0);
  }
}

function h$ghcjsbn_showBase_rec(b, base, logBase, pad) {
  var bits = h$ghcjsbn_nbits_b(b), r;
  // h$log("[" + b.join(",") + "] bits: " + bits);
  if(h$ghcjsbn_cmp_bb(b, h$ghcjsbn_two31_b) === 0) {
    // convert short numbers to int and show in base
    var ti = h$ghcjsbn_toInt_b(b);
    // h$log("############# got base limb: " + ti);
    r = ti === 0 ? "" : ti.toString(base);
  } else {
    // divide and conquer for long numbers
    var digits = Math.floor(bits * 0.6931471805599453 / logBase);
    var d2 = Math.round(digits/2), p, q = [], r = [];
    p = h$ghcjsbn_pow_ww(base, d2);
    h$ghcjsbn_quotRem_bb(q, r, b, p);
    r = h$ghcjsbn_showBase_rec(q, base, logBase, 0) +
        h$ghcjsbn_showBase_rec(r, base, logBase, d2);
  }
  var rl = r.length;
  if(rl < pad) {
    while(rl <= pad-8) { r = "00000000" + r; rl += 8; }
    switch(pad-rl) {
    case 1: r = "0" + r; break;
    case 2: r = "00" + r; break;
    case 3: r = "000" + r; break;
    case 4: r = "0000" + r; break;
    case 5: r = "00000" + r; break;
    case 6: r = "000000" + r; break;
    case 7: r = "0000000" + r; break;
    }
  }
  return r;
}

// BigNat -> String (decimal)
function h$ghcjsbn_show(b) {
  throw new Error("show not implemented");
  // digits =
}

// BigNat -> String
function h$ghcjsbn_showHex(b) {
  throw new Error("showHex not implemented");
}

// s = b[l - 1];

// normalize a number to length l by stripping unused leading digits
/*
function h$ghcjsbn_normalize(b, l) {
  var d = b.length - l;
  while(d--) b.pop();
}

// normalize a number by stripping leading zeroes
function h$ghcjsbn_normalize0(b) {
  var l = b.length;
  while(b[--l] === 0) b.pop();
}
*/
// t = b :: BigNat -> BigNat -> Int, returns length of t
function h$ghcjsbn_copy(t, b) {
  h$ghcjsbn_assertValid_b(b, "copy");
  var l = b[0];
  for(var i = 0; i <= l; i++) {
    t[i] = b[i];
  }
  return l;
}

// BigNat -> Int -> Bool
// test if bit n is set in b (least significant bit is 0)
function h$ghcjsbn_testBit_b(b, n) {
  h$ghcjsbn_assertValid_b(b, "testBit_b");
  h$ghcjsbn_assertValid_s(n, "testBit_b");
  var limb = (n / 28)|0;
  if(limb >= b[0]) {
    return false;
  } else {
    var d = b[limb];
    var bit = n - (28 * limb);
    return (b[limb] & (1 << bit)) !== 0;
  }
}

function h$ghcjsbn_popCount_b(b) {
  h$ghcjsbn_assertValid_b(b, "popCount_b");
  var c = 0, l = b[0];
  while(l > 0) {
    c += h$popCnt32(b[l--]);
  }
  return c;
}

// t = b1 ^ b2 :: BigNat -> BigNat -> BigNat -> Int
// returns length of t
function h$ghcjsbn_xor_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "xor_bb b1");
  h$ghcjsbn_assertValid_b(b2, "xor_bb b2");
  var i, lmin, lmax, blmax, l1 = b1[0], l2 = b2[0], t = [0];
  if(l1 <= l2) {
    lmin = l1;
    lmax = l2;
    blmax = b2;
  } else {
    lmin = l2;
    lmax = l1;
    blmax = b1;
  }
  for(i = 1; i <= lmin; i++) {
    t[i] = b1[i] ^ b2[i];
  }
  for(i = lmin + 1; i <= lmax; i++) {
    t[i] = blmax[i];
  }
  while(lmax > 0 && t[lmax] === 0) lmax--;
  t[0] = lmax;
  h$ghcjsbn_assertValid_b(t, "xor_bb result");
  return t;
}

// b1 | b2 :: BigNat -> BigNat -> BigNat
function h$ghcjsbn_or_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "or_bb b1");
  h$ghcjsbn_assertValid_b(b2, "or_bb b2");
  var i, lmin, lmax, blmax, l1 = b1[0], l2 = b2[0], t = [0];
  if(l1 <= l2) {
    lmin = l1;
    lmax = l2;
    blmax = b2;
  } else {
    lmin = l2;
    lmax = l1;
    blmax = b1;
  }
  for(i = 1; i <= lmin; i++) {
    t[i] = b1[i] | b2[i];
  }
  for(i = lmin + 1; i <= lmax; i++) {
    t[i] = blmax[i];
  }
  t[0] = lmax;
  h$ghcjsbn_assertValid_b(t, "or_bb result");
  return t;
}

// b1 & b2 :: BigNat -> BigNat -> BigNat
function h$ghcjsbn_and_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "and_bb b1");
  h$ghcjsbn_assertValid_b(b2, "and_bb b2");
  var i, lmin, l1 = b1[0], l2 = b2[0], t = [0];
  lmin = l1 <= l2 ? l1 : l2;
  for(i = 1; i <= lmin; i++) {
    t[i] = b1[i] & b2[i];
  }
  while(lmin > 0 && t[lmin] === 0) lmin--;
  t[0] = lmin;
  h$ghcjsbn_assertValid_b(t, "and_bb result");
  return t;
}

// b1 & (~b2) :: BigNat -> BigNat -> BigNat
// fixme is this one correct?
function h$ghcjsbn_andn_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "andn_bb b1");
  h$ghcjsbn_assertValid_b(b2, "andn_bb b2");
  var i, lmin, l1 = b1[0], l2 = b2[0], t = [0];
  if(l1 <= l2) {
    for(i = 0; i <= l1; i++) t[i] = b1[i] & (~b2[i]);
  } else {
    for(i = 0; i <= l2; i++) t[i] = b1[i] & (~b2[i]);
    for(i = l2+1; i <= l1; i++) t[i] = b1[i];
  }
  while(l1 > 0 && t[l1] === 0) l1--;
  t[0] = l1;
  h$ghcjsbn_assertValid_b(t, "andn_bb result");
  return t;
}

function h$ghcjsbn_toInt_b(b) {
  h$ghcjsbn_assertValid_b(b, "toInt_b");
  var bl = b[0], r;
  if(bl >= 2) {
    r = (b[2] << 28) | b[1];
  } else if(bl === 1) {
    r = b[1];
  } else {
    r = 0;
  }
  h$ghcjsbn_assertValid_s(r, "toInt_b result");
  return r;
}

function h$ghcjsbn_toWord_b(b) {
  h$ghcjsbn_assertValid_b(b, "toWord_b");
  var bl = b[0], w;
  if(bl >= 2) {
    w = (b[2] << 28) | b[1];
  } else if(bl === 1) {
    w = b[1];
  } else {
    w = 0;
  }
  h$ghcjsbn_assertValid_w(w, "toWord_b result");
  return w;
}

var h$integer_bigNatToWord64 = h$ghcjsbn_toWord64_b;
var h$integer_word64ToBigNat = h$ghcjsbn_mkBigNat_ww; // fixme?


function h$ghcjsbn_toWord64_b(b) {
  h$ghcjsbn_assertValid_b(b, "toWord64_b");
  var len = b[0], w1, w2;
  if(len < 2) {
    w2 = 0;
    w1 = (len === 1) ? b[1] : 0;
  } else {
    w1 = b[1] | (b[2] << 28);
    if(len === 2) {
      w2 = b[2] >>> 4;
    } else {
      w2 = (b[2] >>> 4) | (b[3] << 24);
    }
  }
  h$ghcjsbn_assertValid_w(w2, "toWord64_b result w2");
  h$ghcjsbn_assertValid_w(w1, "toWord64_b result w1");
  { h$ret1 = (w1); return (w2); };
}




// BigNat -> Int -> IO ()
function h$ghcjsbn_toBigNat_s(b, s) {
  h$ghcjsbn_assertValid_s(s, "toBigNat_s");

  if(s < 0) {
    throw new Error("h$ghcjsbn_toBigNat_s: negative operand");
  }

  if(s === 0) {
    b[0] = 0;
  } else if(s <= 0xfffffff) {
    b[0] = 1;
    b[1] = s;
  } else {
    b[0] = 2;
    b[1] = s & 0xfffffff;
    b[2] = s >> 0xfffffff;
  }
  h$ghcjsbn_assertValid_b(b, "toBigNat_s result");
}

// BigNat -> Word -> IO ()
function h$ghcjsbn_toBigNat_w(b, w) {
  h$ghcjsbn_assertValid_w(w, "toBigNat_w");
  if(w === 0) {
    b[0] = 0;
  } else if(w > 0 && w <= 0xfffffff) {
    b[0] = 1;
    b[1] = w;
  } else {
    b[0] = 2;
    b[1] = w & 0xfffffff;
    b[2] = w >>> 28;
  }
  h$ghcjsbn_assertValid_b(b, "toBigNat_w result");
}

function h$ghcjsbn_mkBigNat_w(w) {
  h$ghcjsbn_assertValid_w(w, "mkBigNat_w");
  var r;
  if(w === 0) r = h$ghcjsbn_zero_b;
  else if(w === 1) r = h$ghcjsbn_one_b;
  else if(w > 0 && w <= 0xfffffff) r = [1,w];
  else r = [2, w & 0xfffffff, w >>> 28];
  h$ghcjsbn_assertValid_b(r, "mkBigNat_w result");
  // ASSERTVALID_B(h$ghcjsbn_zero_b, "mkBigNat_w zero");
  return r;
}


function h$ghcjsbn_mkBigNat_ww(hw, lw) {
  h$ghcjsbn_assertValid_w(hw, "mkBigNat_ww hw");
  h$ghcjsbn_assertValid_w(lw, "mkBigNat_ww lw");
  var r;
  if(hw === 0) r = h$ghcjsbn_mkBigNat_w(lw);
  else {
    var w1 = lw & 0xfffffff;
    var w2 = (lw >>> 28) | ((hw << 4) & 0xfffffff);
    var w3 = hw >>> 24;
    if(w3 === 0) {
      r = [2, w1, w2];
    } else {
      r = [3, w1, w2, w3];
    }
  }
  h$ghcjsbn_assertValid_b(r, "mkBigNat_ww result");
  return r;
}


// fixme remove after reboot
var h$ghcjsbn_toBigNat_ww = h$ghcjsbn_mkBigNat_ww;

/* fixme re-enable after reboot
function h$ghcjsbn_toBigNat_ww(b, hw, lw) {
  ASSERTVALID_W(hw, "toBigNat_ww hw");
  ASSERTVALID_W(lw, "toBigNat_ww lw");
  if(hw === 0) h$ghcjsbn_toBigNat_w(b, lw);
  else {
    var w1 = lw & GHCJSBN_MASK;
    var w2 = (lw >>> GHCJSBN_BITS) | ((hw << 4) & GHCJSBN_MASK);
    var w3 = hw >>> 24;
    if(w3 === 0) {
      r[0] = 2;
      r[1] = w1;
      r[2] = w2;
    } else {
      r[0] = 3;
      r[1] = w1;
      r[2] = w2;
      r[3] = w3;
    }
  }
}
*/




// fixme remove later
var h$integer_mkInteger = h$ghcjsbn_mkInteger;


function h$ghcjsbn_mkInteger(nonNeg, xs) {
  // fixme write proper optimized version
  var r = [0], s = 0, t;
  while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
    t = h$ghcjsbn_shl_b(h$ghcjsbn_mkBigNat_w(((typeof(((xs).d1)) === 'number')?(((xs).d1)):(((xs).d1)).d1)), s);
    h$ghcjsbn_addTo_bb(r, t);
    s += 31;
    xs = ((xs).d2);
  }
  if(nonNeg) {
    if(h$ghcjsbn_cmp_bb(r, h$ghcjsbn_two31_b) === 0) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (h$ghcjsbn_toInt_b(r))));;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (r)));;
    }
  } else {
    var c = h$ghcjsbn_cmp_bb(r, h$ghcjsbn_two31_b);
    if(c === 2) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (r)));;
    } else if(c === 1) {
      return h$ghcjsbn_negTwo31_i;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-h$ghcjsbn_toInt_b(r))));;
    }
  }
/*  var r = h$ghcjsbn_mkBigNat_w(0), l = 0, s = 0, y, t;
  while(IS_CONS(xs)) {
    l++;
    y  = UNWRAP_NUMBER(CONS_HEAD(xs));
    r[++l] = (y << s | c) & GHCJSBN_MASK;
    c  = y >>> s;
    xs = CONS_TAIL(xs);
    s  += 3;
    l++;
    if(s > GHCJSBN_BITS) {
      s  -= GHCJSBN_BITS;
      r[++l] = c & GHCJSBN_MASK;
      c >>= GHCJSBN_BITS;
    }
  }
  if(c !== 0) r[++l] =
  while(
  if(l === 0) {
    return MK_INTEGER_S(0);
  } else if(l === 1) {

  } else if(l === 2) {

  } */
}




// BigNat -> Int -> Int
function h$ghcjsbn_indexBigNat(b, i) {
  h$ghcjsbn_assertValid_b(b, "indexBigNat");
  h$ghcjsbn_assertValid_s(i, "indexBigNat");
  var bl = b[0];
  return i >= bl ? 0 : b[i+1];
}

// BigNat -> Word -> Int (Ordering)
function h$ghcjsbn_cmp_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "cmp_bw");
  h$ghcjsbn_assertValid_w(w, "cmp_bw");
  var w1 = w & 0xfffffff, w2 = w >>> 28, bl = b[0];
  if(w2 === 0) {
    if(bl === 0) {
      return w1 > 0 ? 0 : 1;
    } else if(bl === 1) {
      var bw = b[1];
      return bw > w1 ? 2 : (bw === w1 ? 1 : 0);
    } else {
      return 2;
    }
  } else {
    if(bl < 2) {
      return 0;
    } else if(bl > 2) {
      return 2;
    } else {
      var bw1 = b[1], bw2 = b[2];
      return (bw2 > w2) ? 2
                        : (bw2 < w2 ? 0
                                    : (bw1 > w1 ? 2
                                                : (bw1 < w1 ? 0
                                                            : 1)));
    }
  }
}

/*
function h$ghcjsbn_gt_bw(b, w) {
  var r = h$ghcjsbn_gt_bw0(b,w);
  h$log("gt_bw result: " + r);
  return r;
}
*/

function h$ghcjsbn_gt_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "gt_bw");
  h$ghcjsbn_assertValid_w(w, "gt_bw");
  var bl = b[0];
  if(bl > 2) return true;
  else if(bl === 0) return false;
  else if(bl === 1) return w >= 0 && b[1] > w;
  else { // bl === 2
    var wh = w >>> 28, wl = w & 0xfffffff, b2 = b[2];
    // var r = (wh > b2 || ((wh === b2) && wl > b[1]));
    // h$log("r: " + r + " " + wh + " " + wl + " " );
    return (b2 > wh || ((wh === b2) && b[1] > wl));
  }
}

// BigNat -> BigNat -> Bool
function h$ghcjsbn_eq_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "eq_bb");
  h$ghcjsbn_assertValid_b(b2, "eq_bb");
  var bl1 = b1[0], bl2 = b2[0];
  if(bl1 !== bl2) {
    return false;
  } else {
    for(var i = bl1; i >= 1; i--) {
      var bw1 = b1[i], bw2 = b2[i];
      if(bw1 !== bw2) return false;
    }
  }
  return true; // GHCJSBN_EQ;
}

// BigNat -> BigNat -> Bool
function h$ghcjsbn_neq_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "neq_bb");
  h$ghcjsbn_assertValid_b(b2, "neq_bb");
  var bl1 = b1[0], bl2 = b2[0];
  if(bl1 !== bl2) {
    return true;
  } else {
    for(var i = bl1; i >= 1; i--) {
      var bw1 = b1[i], bw2 = b2[i];
      if(bw1 !== bw2) return true;
    }
  }
  return false;
}

// BigNat -> BigNat -> Bool
/*
function h$ghcjsbn_eq_bw(b, w) {
  var r = h$ghcjsbn_eq_bw0(b, w);
  return r;
}
*/
function h$ghcjsbn_eq_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "eq_bw");
  h$ghcjsbn_assertValid_w(w, "eq_bw");
  var w1 = w & 0xfffffff, w2 = w >>> 28, bl = b[0];
  if(w2 === 0) {
    if(w1 === 0) {
      return bl === 0;
    } else {
      return bl === 1 && b[1] === w;
    }
  } else {
    return bl === 2 && b[1] === w1 && b[2] === w2;
  }
}

// BigNat -> Bool
function h$ghcjsbn_isZero_b(b) {
  h$ghcjsbn_assertValid_b(b, "isZero_b");
  return b[0] === 0;
}

// BigNat -> Int
function h$ghcjsbn_isNull_b(b) {
  return b[0] === -1;
}

// 1 << n
function h$ghcjsbn_bitBigNat(n) {

  if(n < 0) {
    throw new Error("bitBigNat: argument must be positive");
  }

  if(n === 0) {
    r = h$ghcjsbn_one_b;
  } else if(n < 28) {
    r = [1, 1 << n];
  } else {
    var l = (n / 28)|0;
    var r = [l+1];
    for(var i = 1; i<= l; i++) r[i] = 0;
    r[l+1] = 1 << (n - (28 * l));
  }
  h$ghcjsbn_assertValid_b(r, "bitBigNat result");
  return r;
}


// Integer -> Int
// assumes argument is strictly positive
function h$ghcjsbn_integerLog2(i) {
  h$ghcjsbn_assertValid_i(i, "integerLog2");

/*  if(h$ghcjsbn_cmp_ii(i, h$ghcjsbn_zero_i) !== GHCJSBN_GT) {
    throw new Error("integerLog2: argument must be positive");
  } */

  if(((i).f === h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e)) {
    return h$ghcjsbn_nbits_s(((i).d1));
  } else {
    return h$ghcjsbn_nbits_b(((i).d1));
  }
}

// Integer -> Int
// returns negation of result if integer is exactly a power of two
function h$ghcjsbn_integerLog2IsPowerOf2(i) {
  h$ghcjsbn_assertValid_i(i, "integerLog2IsPowerOf2");

/*  if(h$ghcjbn_cmp_ii(i, h$ghcjsbn_zero_i) !== GHCJSBN_GT) {
    throw new Error("integerLog2IsPowerOf2: argument must be positive");
  } */

  var nb;
  if(((i).f === h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e)) {
    var sd = ((i).d1);
    h$ghcjsbn_assertValid_s(sd, "integerLog2IsPowerOf2 sd");
    nb = h$ghcjsbn_nbits_s(sd);
    return ((sd === 1 << nb) ? -nb : nb);
  } else {
    var bd = ((i).d1);
    h$ghcjsbn_assertValid_b(bd, "integerLog2IsPowerOf2 bd");
    nb = h$ghcjsbn_nbits_b(bd);
    var i, bl = (nb / 28) | 0, lb = nb - 28 * bl, l = bd[bl+1];
    if(l !== (1 << lb)) return nb;
    for(i = bl; i >= 1; i--) {
      if(bd[i] !== 0) return nb;
    }
    return -nb;
  }
}

// BigNat? -> Int
function h$ghcjsbn_isValid_b(b) {
  if(!Array.isArray(b)) return 0;
  if(b.length < 1) return 0;
  var bl = b[0], w;
  if(b.length < (bl+1)) return 0;
  for(var i = 0; i <= bl; i++) {
    w = b[i];
    if(typeof w !== 'number' || (w & 0xfffffff) !== w) return 0;
  }
  return 1;
}

// BigNat -> Integer
function h$ghcjsbn_toInteger_b(b) {
  h$ghcjsbn_assertValid_b(b, "toInteger_b");
  if(h$ghcjsbn_cmp_bb(b, h$ghcjsbn_two31_b) === 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (h$ghcjsbn_toInt_b(b))));;
  } else {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (b)));;
  }
}

// BigNat -> Integer
function h$ghcjsbn_toNegInteger_b(b) {
  h$ghcjsbn_assertValid_b(b, "toNegInteger_b");
  var c = h$ghcjsbn_cmp_bb(b, h$ghcjsbn_two31_b);
  if(c === 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-h$ghcjsbn_toInt_b(b))));;
  } else if(c === 1) {
    return h$ghcjsbn_negTwo31_i;
  } else {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (b)));;
  }
}

// BigNat? -> Int
// (can be called with invalid bignat)
function h$ghcjsbn_sizeof_b(b) {
  if(b.length < 1) return 0;
  var bl = b[0];
  return Math.ceil((bl * 28) / 32);
}

// extract a word from a BigNat
function h$ghcjsbn_index_b(b, w) {
  throw new Error("index_b");
  h$ghcjsbn_assertValid_b(b, "index_b");
  h$ghcjsbn_assertValid_w(w, "index_b");
  var wbit = 32*w, len = b[0], limb = (wbit / 28) | 0, lb = wbit - (limb * 28);
  var r = b[limb+1] >>> lb;
/*  if() {

  } */
  h$ghcjsbn_assertValid_w(r, "index_b result");
}

// Bool -> BigNat -> Double
function h$ghcjsbn_toDouble_b(nonNeg, b) {
  throw new Error("toDouble_b");
}

function h$ghcjsbn_byteArrayToBigNat(ba, len) {
  throw new Error("h$ghcjsbn_byteArrayToBigNat not yet implemented");
}

function h$ghcjsbn_importBigNatFromAddr(a_d, a_o, len, msbf) {
  throw new Error("h$ghcjsbn_importBigNatFromAddr not yet implemented");
}

function h$ghcjsbn_importBigNatFromByteArray(ba, ofs, len, msbf) {
  throw new Error("h$ghcjsbn_importBigNatFromByteArray not yet implemented");
}


//////////////////////////////////////////////////////////////////////////////
// fixme move to primop places later

var h$integer_int64ToInteger = h$ghcjsbn_toInteger_s64;

function h$ghcjsbn_toInteger_s64(s_a, s_b) {
  h$ghcjsbn_assertValid_s(s_a, "toInteger_s64 s_a");
  h$ghcjsbn_assertValid_s(s_b, "toInteger_s64 s_b");
  if(s_a === 0) {
    if(s_b >= 0) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (s_b)));;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (h$ghcjsbn_mkBigNat_w(s_b))));;
    }
  } else if(s_a === -1) {
    if(s_b < 0) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (s_b)));;
    } else if(s_b === 0) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (h$ghcjsbn_mkBigNat_ww(1,0))));;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (h$ghcjsbn_mkBigNat_w(((~s_b)+1)|0))));;
    }
  } else if(s_a > 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (h$ghcjsbn_mkBigNat_ww(s_a, s_b))));;
  } else {
    if(s_b === 0) { // zero should be correct!
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (h$ghcjsbn_mkBigNat_ww(((~s_a)+1)|0, 0))));;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (h$ghcjsbn_mkBigNat_ww((~s_a)|0, ((~s_b)+1)|0))));;
    }
    /*
     if(s_b === 0) { // zero should be correct!
      return MK_INTEGER_Jn(h$ghcjsbn_mkBigNat_ww(((~s_a)+1)|0, 0));
    } else {
      return MK_INTEGER_Jn(h$ghcjsbn_mkBigNat_ww(~s_a, ((~s_b)+1)|0));
    } */
  }
}

function h$decodeDoubleInt64(d) {
  h$ghcjsbn_assertValid_d(d, "DoubleDecode_Int64");
  if(isNaN(d)) {
    // RETURN_UBX_TUP4(null, -1572864, 0, 972);
    { h$ret1 = (-1572864); h$ret2 = (0); return (972); };
  }
  h$convertDouble[0] = d;
  var i0 = h$convertInt[0], i1 = h$convertInt[1];
  var exp = (i1&2146435072)>>>20;
  var ret1, ret2 = i0, ret3;
  if(exp === 0) { // denormal or zero
    if((i1&2147483647) === 0 && ret2 === 0) {
      ret1 = 0;
      ret3 = 0;
    } else {
      h$convertDouble[0] = d*9007199254740992;
      i1 = h$convertInt[1];
      ret1 = (i1&1048575)|1048576;
      ret2 = h$convertInt[0];
      ret3 = ((i1&2146435072)>>>20)-1128;
    }
  } else {
    ret3 = exp-1075;
    ret1 = (i1&1048575)|1048576;
  }
  // negate mantissa for negative input
  if(d < 0) {
    if(ret2 === 0) {
      ret1 = ((~ret1) + 1) | 0;
      // ret2 = 0;
    } else {
      ret1 = ~ret1;
      ret2 = ((~ret2) + 1) | 0;
    }
  }
  // prim ubx tup returns don't return the first value!
  { h$ret1 = (ret1); h$ret2 = (ret2); return (ret3); };
}

// fixme remove this once rebooted
function h$primop_DoubleDecode_Int64Op(d) {
  h$ghcjsbn_assertValid_d(d, "DoubleDecode_Int64");
  if(isNaN(d)) {
    // RETURN_UBX_TUP4(null, -1572864, 0, 972);
    { h$ret1 = (-1572864); h$ret2 = (0); h$ret3 = (972); return (null); };
  }
  h$convertDouble[0] = d;
  var i0 = h$convertInt[0], i1 = h$convertInt[1];
  var exp = (i1&2146435072)>>>20;
  var ret1, ret2 = i0, ret3;
  if(exp === 0) { // denormal or zero
    if((i1&2147483647) === 0 && ret2 === 0) {
      ret1 = 0;
      ret3 = 0;
    } else {
      h$convertDouble[0] = d*9007199254740992;
      i1 = h$convertInt[1];
      ret1 = (i1&1048575)|1048576;
      ret2 = h$convertInt[0];
      ret3 = ((i1&2146435072)>>>20)-1128;
    }
  } else {
    ret3 = exp-1075;
    ret1 = (i1&1048575)|1048576;
  }
  // negate mantissa for negative input
  if(d < 0) {
    if(ret2 === 0) {
      ret1 = ((~ret1) + 1) | 0;
      // ret2 = 0;
    } else {
      ret1 = ~ret1;
      ret2 = ((~ret2) + 1) | 0;
    }
  }
  // prim ubx tup returns don't return the first value!
  { h$ret1 = (ret1); h$ret2 = (ret2); h$ret3 = (ret3); return (null); };
}

function h$ghcjsbn_encodeDouble_b(pos, b, e) {
  h$ghcjsbn_assertValid_b(b, "encodeDouble_b");
  h$ghcjsbn_assertValid_s(e, "encodeDouble_b");
  if(e >= 972) {
    return pos ? Infinity : -Infinity;
  }
  var ls = 1, bl = b[0], i, r = b[bl], mul = 1 << 28, rmul = 1/mul, s = 1;
  for(i = bl-1; i >= 1; i--) {
/*    if(e > GHCJSBN_BITS) {
      e -= GHCJSBN_BITS;
      s *= rmul;
      r  = r + s * b[i];
    } else { */
      r = r * mul + s * b[i];
//    }
  }
  // h$log("remaning exp: " + e);
  if(e > 600) {
    r = r * Math.pow(2, e-600) * Math.pow(2,600);
  } else if(e < -600) {
    r = r * Math.pow(2, e+600) * Math.pow(2,-600);
  } else {
    r = r * Math.pow(2, e);
  }
  h$ghcjsbn_assertValid_d(r, "encodeDouble_b result");
  return pos ? r : -r;
}

function h$ghcjsbn_toDouble_b(nonNeg, b) {
  return h$ghcjsbn_encodeDouble_b(nonNeg, b, 0);
}

// fixme
var h$ghcjsbn_encodeDouble_i = h$ghcjsbn_encodeDouble_s;

function h$ghcjsbn_encodeDouble_s(m, e) {
  h$ghcjsbn_assertValid_s(m, "encodeDouble_s m");
  h$ghcjsbn_assertValid_s(e, "encodeDouble_s e");
  var r = m * Math.pow(2, e);
  h$ghcjsbn_assertValid_d(r, "encodeDouble_s result");
  return r;
}






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

function h$createWebSocket(url, protocols) {
  return new WebSocket(url, protocols);
}

/*
   this must be called before the websocket has connected,
   typically synchronously after creating the socket
 */
function h$openWebSocket(ws, mcb, ccb, c) {
  if(ws.readyState !== 0) {
    throw new Error("h$openWebSocket: unexpected readyState, socket must be CONNECTING");
  }
  ws.lastError = null;
  ws.onopen = function() {
    if(mcb) {
      ws.onmessage = mcb;
    }
    if(ccb || mcb) {
      ws.onclose = function(ce) {
        if(ws.onmessage) {
          h$release(ws.onmessage);
          ws.onmessage = null;
        }
        if(ccb) {
          h$release(ccb);
          ccb(ce);
        }
      };
    };
    ws.onerror = function(err) {
      ws.lastError = err;
      if(ws.onmessage) {
        h$release(ws.onmessage);
        ws.onmessage = null;
      }
      ws.close();
    };
    c(null);
  };
  ws.onerror = function(err) {
    if(ccb) h$release(ccb);
    if(mcb) h$release(mcb);
    ws.onmessage = null;
    ws.close();
    c(err);
  };
}

function h$closeWebSocket(status, reason, ws) {
  ws.onerror = null;
  if(ws.onmessage) {
    h$release(ws.onmessage);
    ws.onmessage = null;
  }
  ws.close(status, reason);
}






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

/*
   convert an array to a Haskell list, wrapping each element in a
   JSVal constructor
 */
function h$fromArray(a) {
    var r = h$ghczmprimZCGHCziTypesziZMZN;
    for(var i=a.length-1;i>=0;i--) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return a;
}

/*
   convert an array to a Haskell list. No additional wrapping of the
   elements is performed. Only use this when the elements are directly
   usable as Haskell heap objects (numbers, boolean) or when the
   array elements have already been appropriately wrapped
 */
function h$fromArrayNoWrap(a) {
    var r = h$ghczmprimZCGHCziTypesziZMZN;
    for(var i=a.length-1;i>=0;i--) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return a;
}

/*
   convert a list of JSVal to an array. the list must have been fully forced,
   not just the spine.
 */
function h$listToArray(xs) {
    var a = [], i = 0;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 a[i++] = ((((xs).d1)).d1);
 xs = ((xs).d2);
    }
    return a;
}

function h$listToArrayWrap(xs) {
    return (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (h$listToArray(xs))));
}
function h$animationFrameCancel(h) {
    if(h.handle) window.cancelAnimationFrame(h.handle);
    if(h.callback) {
        h$release(h.callback)
        h.callback = null;
    }
}

function h$animationFrameRequest(h) {
    h.handle = window.requestAnimationFrame(function(ts) {
        var cb = h.callback;
        if(cb) {
         h$release(cb);
         h.callback = null;
         cb(ts);
        }
    });
}
function h$exportValue(fp1a,fp1b,fp2a,fp2b,o) {
  var e = { fp1a: fp1a
          , fp1b: fp1b
          , fp2a: fp2a
          , fp2b: fp2b
          , released: false
          , root: o
          , _key: -1
          };
  h$retain(e);
  return e;
}

function h$derefExport(fp1a,fp1b,fp2a,fp2b,e) {
  if(!e || typeof e !== 'object') return null;
  if(e.released) return null;
  if(fp1a !== e.fp1a || fp1b !== e.fp1b ||
     fp2a !== e.fp2a || fp2b !== e.fp2b) return null;
  return e.root;
}

function h$releaseExport(e) {
  h$release(e);
  e.released = true;
  e.root = null;
}






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

/*
 * Support code for the Data.JSString module. This code presents a JSString
 * as a sequence of code points and hides the underlying encoding ugliness of
 * the JavaScript strings.
 *
 * Use Data.JSString.Raw for direct access to the JSThis makes the operations more expen
 */

/*
 * Some workarounds here for JS engines that do not support proper
 * code point access
 */
var h$jsstringEmpty = (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, ('')));

var h$jsstringHead, h$jsstringTail, h$jsstringCons,
    h$jsstringSingleton, h$jsstringSnoc, h$jsstringUncons,
    h$jsstringIndex, h$jsstringUncheckedIndex,
    h$jsstringTake, h$jsstringDrop, h$jsstringTakeEnd, h$jsstringDropEnd;

if(String.prototype.codePointAt) {
    h$jsstringSingleton = function(ch) {
                                                        ;
 return String.fromCodePoint(ch);
    }
    h$jsstringHead = function(str) {
                                                    ;
 var cp = ch.codePointAt(0);
 return (cp === undefined) ? -1 : (cp|0);
    }
    h$jsstringTail = function(str) {
                                                    ;
 var l = str.length;
 if(l===0) return null;
 var ch = str.codePointAt(0);
 if(ch === undefined) return null;
 // string length is at least two if ch comes from a surrogate pair
 return str.substr(((ch)>=0x10000)?2:1);
    }
    h$jsstringCons = function(ch, str) {
                                                                      ;
 return String.fromCodePoint(ch)+str;
    }
    h$jsstringSnoc = function(str, ch) {
                                                                 ;
 return str+String.fromCodePoint(ch);
    }
    h$jsstringUncons = function(str) {
                                                             ;
 var l = str.length;
 if(l===0) return null;
 var ch = str.codePointAt(0);
        if(ch === undefined) {
     { h$ret1 = (null); return (null); };
        }
        { h$ret1 = (str.substr(((ch)>=0x10000)?2:1)); return (ch); };
    }
    // index is the first part of the character
    h$jsstringIndex = function(i, str) {
                                                                      ;
 var ch = str.codePointAt(i);
 if(ch === undefined) return -1;
 return ch;
    }
    h$jsstringUncheckedIndex = function(i, str) {
                                                                                      ;
 return str.codePointAt(i);
    }
} else {
    h$jsstringSingleton = function(ch) {
                                                           ;
 return (((ch)>=0x10000)) ? String.fromCharCode(((((ch)-0x10000)>>>10)+0xDC00), (((ch)&0x3FF)+0xD800))
                               : String.fromCharCode(ch);
    }
    h$jsstringHead = function(str) {
                                                       ;
 var l = str.length;
 if(l===0) return -1;
 var ch = str.charCodeAt(0);
 if(((ch|1023)===0xDBFF)) {
     return (l>1) ? ((((ch)-0xD800)<<10)+(str.charCodeAt(1))-9216) : -1;
 } else {
     return ch;
 }
    }
    h$jsstringTail = function(str) {
                                                       ;
 var l = str.length;
 if(l===0) return null;
 var ch = str.charCodeAt(0);
 if(((ch|1023)===0xDBFF)) {
     return (l>1)?str.substr(2):null;
 } else return str.substr(1);
    }
    h$jsstringCons = function(ch, str) {
                                                                         ;
 return ((((ch)>=0x10000)) ? String.fromCharCode(((((ch)-0x10000)>>>10)+0xDC00), (((ch)&0x3FF)+0xD800))
                                : String.fromCharCode(ch))
                                + str;
    }
    h$jsstringSnoc = function(str, ch) {
                                                                    ;
 return str + ((((ch)>=0x10000)) ? String.fromCharCode(((((ch)-0x10000)>>>10)+0xDC00), (((ch)&0x3FF)+0xD800))
                                      : String.fromCharCode(ch));
    }
    h$jsstringUncons = function(str) {
                                                                ;
 var l = str.length;
 if(l===0) return -1;
 var ch = str.charCodeAt(0);
 if(((ch|1023)===0xDBFF)) {
   if(l > 1) {
        { h$ret1 = (str.substr(2)); return (((((ch)-0xD800)<<10)+(str.charCodeAt(1))-9216)); };
   } else {
       { h$ret1 = (null); return (-1); };
   }
 } else {
      { h$ret1 = (str.substr(1)); return (ch); };
 }
    }
    // index is the first part of the character
    h$jsstringIndex = function(i, str) {
        // TRACE_JSSTRING("(no codePointAt) index: " + i + " '" + str + "'");
 var ch = str.charCodeAt(i);
 if(ch != ch) return -1; // NaN test
 return (((ch|1023)===0xDBFF)) ? ((((ch)-0xD800)<<10)+(str.charCodeAt(i+1))-9216) : ch;
    }
    h$jsstringUncheckedIndex = function(i, str) {
                                                                                         ;
 var ch = str.charCodeAt(i);
 return (((ch|1023)===0xDBFF)) ? ((((ch)-0xD800)<<10)+(str.charCodeAt(i+1))-9216) : ch;
    }
}

function h$jsstringPack(xs) {
    var r = '', i = 0, a = [], c;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 c = ((xs).d1);
 a[i++] = ((typeof(c) === 'number')?(c):(c).d1);
 if(i >= 60000) {
     r += String.fromCharCode.apply(null, a);
     a = [];
     i = 0;
 }
 xs = ((xs).d2);
    }
    if(i > 0) r += String.fromCharCode.apply(null, a);
                                       ;
    return r;
}

function h$jsstringPackReverse(xs) {
    var a = [], i = 0, c;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 c = ((xs).d1);
 a[i++] = ((typeof(c) === 'number')?(c):(c).d1);
 xs = ((xs).d2);
    }
    if(i===0) return '';
    var r = h$jsstringConvertArray(a.reverse());
                                              ;
    return r;
}

function h$jsstringPackArray(arr) {
                                        ;
    return h$jsstringConvertArray(arr);
}

function h$jsstringPackArrayReverse(arr) {
                                                ;
    return h$jsstringConvertArray(arr.reverse());
}

function h$jsstringConvertArray(arr) {
    if(arr.length < 60000) {
 return String.fromCharCode.apply(null, arr);
    } else {
 var r = '';
 for(var i=0; i<arr.length; i+=60000) {
     r += String.fromCharCode.apply(null, arr.slice(i, i+60000));
 }
 return r;
    }
}

function h$jsstringInit(str) {
                                         ;
    var l = str.length;
    if(l===0) return null;
    var ch = str.charCodeAt(l-1);
    var o = ((ch|1023)===0xDFFF)?2:1;
    var r = str.substr(0, l-o);
    return r;
}

function h$jsstringLast(str) {
                                         ;
    var l = str.length;
    if(l===0) return -1;
    var ch = str.charCodeAt(l-1);
    if(((ch|1023)===0xDFFF)) {
 return (l>1) ? ((((str.charCodeAt(l-2))-0xD800)<<10)+(ch)-9216) : -1;

    } else return ch;
}

// index is the last part of the character
function h$jsstringIndexR(i, str) {
                                                     ;
    if(i < 0 || i > str.length) return -1;
    var ch = str.charCodeAt(i);
    return (((ch|1023)===0xDFFF)) ? ((((str.charCodeAt(i-1))-0xD800)<<10)+(ch)-9216) : ch;
}

function h$jsstringNextIndex(i, str) {
                                                        ;
    return i + (((str.charCodeAt(i)|1023)===0xDBFF)?2:1);
}

function h$jsstringTake(n, str) {
                                                   ;
    if(n <= 0) return '';
    var i = 0, l = str.length, ch;
    if(n >= l) return str;
    while(n--) {
 ch = str.charCodeAt(i++);
 if(((ch|1023)===0xDBFF)) i++;
 if(i >= l) return str;
    }
    return str.substr(0,i);
}

function h$jsstringDrop(n, str) {
                                                   ;
    if(n <= 0) return str;
    var i = 0, l = str.length, ch;
    if(n >= l) return '';
    while(n--) {
 ch = str.charCodeAt(i++);
 if(((ch|1023)===0xDBFF)) i++;
 if(i >= l) return str;
    }
    return str.substr(i);
}

function h$jsstringSplitAt(n, str) {
                                                    ;
  if(n <= 0) {
    { h$ret1 = (str); return (""); };
  } else if(n >= str.length) {
    { h$ret1 = (""); return (str); };
  }
  var i = 0, l = str.length, ch;
  while(n--) {
    ch = str.charCodeAt(i++);
    if(((ch|1023)===0xDBFF)) i++;
    if(i >= l) {
      { h$ret1 = (""); return (str); };
    }
  }
  { h$ret1 = (str.substr(i)); return (str.substr(0,i)); };
}

function h$jsstringTakeEnd(n, str) {
                                                      ;
    if(n <= 0) return '';
    var l = str.length, i = l-1, ch;
    if(n >= l) return str;
    while(n-- && i > 0) {
 ch = str.charCodeAt(i--);
 if(((ch|1023)===0xDFFF)) i--;
    }
    return (i<0) ? str : str.substr(i+1);
}

function h$jsstringDropEnd(n, str) {
                                                      ;
    if(n <= 0) return str;
    var l = str.length, i = l-1, ch;
    if(n >= l) return '';
    while(n-- && i > 0) {
 ch = str.charCodeAt(i--);
 if(((ch|1023)===0xDFFF)) i--;
    }
    return (i<0) ? '' : str.substr(0,i+1);
}

function h$jsstringIntercalate(x, ys) {
                                              ;
    var a = [], i = 0;
    while(((ys).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 if(i) a[i++] = x;
 a[i++] = ((((ys).d1)).d1);
 ys = ((ys).d2);
    }
    return a.join('');
}

function h$jsstringIntersperse(ch, ys) {
                                                          ;
    var i = 0, l = ys.length, j = 0, a = [], ych;
    if(((ch)>=0x10000)) {
 var ch1 = ((((ch)-0x10000)>>>10)+0xDC00), ch2 = (((ch)&0x3FF)+0xD800);
 while(j < l) {
     if(i) {
  a[i++] = ch1;
  a[i++] = ch2;
     }
     ych = ys.charCodeAt(j++);
     a[i++] = ych;
     if(((ych|1023)===0xDBFF)) a[i++] = ys.charCodeAt(j++);
 }
    } else {
 while(j < l) {
     if(i) a[i++] = ch;
     ych = ys.charCodeAt(j++);
     a[i++] = ych;
     if(((ych|1023)===0xDBFF)) a[i++] = ys.charCodeAt(j++);
 }
    }
    return h$jsstringConvertArray(a);
}

function h$jsstringConcat(xs) {
                            ;
    var a = [], i = 0;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 a[i++] = ((((xs).d1)).d1);
 xs = ((xs).d2);
    }
    return a.join('');
}

var h$jsstringStripPrefix, h$jsstringStripSuffix,
    h$jsstringIsPrefixOf, h$jsstringIsSuffixOf,
    h$jsstringIsInfixOf;
if(String.prototype.startsWith) {
    h$jsstringStripPrefix = function(p, x) {
                                                                    ;
 if(x.startsWith(p)) {
     return (h$c1(h$baseZCGHCziBaseziJust_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(p.length)))))));
 } else {
     return h$baseZCGHCziBaseziNothing;
 }
    }

    h$jsstringIsPrefixOf = function(p, x) {
                                                                   ;
 return x.startsWith(p);
    }

} else {
    h$jsstringStripPrefix = function(p, x) {
                                                                       ;
 if(x.indexOf(p) === 0) { // this has worse complexity than it should
     return (h$c1(h$baseZCGHCziBaseziJust_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(p.length)))))));
 } else {
   return h$baseZCGHCziBaseziNothing;
 }
    }

    h$jsstringIsPrefixOf = function(p, x) {
                                                                      ;
 return x.indexOf(p) === 0; // this has worse complexity than it should
    }
}

if(String.prototype.endsWith) {
    h$jsstringStripSuffix = function(s, x) {
                                                                  ;
 if(x.endsWith(s)) {
     return (h$c1(h$baseZCGHCziBaseziJust_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(0,x.length-s.length)))))));
 } else {
   return h$baseZCGHCziBaseziNothing;
 }
    }

    h$jsstringIsSuffixOf = function(s, x) {
                                                                 ;
 return x.endsWith(s);
    }
} else {
    h$jsstringStripSuffix = function(s, x) {
                                                                     ;
 var i = x.lastIndexOf(s); // this has worse complexity than it should
 var l = x.length - s.length;
 if(i !== -1 && i === l) {
     return (h$c1(h$baseZCGHCziBaseziJust_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(0,l)))))));
 } else {
   return h$baseZCGHCziBaseziNothing;
 }
    }

      h$jsstringIsSuffixOf = function(s, x) {
                                                                    ;
        var i = x.lastIndexOf(s); // this has worse complexity than it should
 return i !== -1 && i === x.length - s.length;
    }
}

if(String.prototype.includes) {
    h$jsstringIsInfixOf = function(i, x) {
                                                                       ;
 return x.includes(i);
    }
} else {
    h$jsstringIsInfixOf = function(i, x) {
                                                                          ;
 return x.indexOf(i) !== -1; // this has worse complexity than it should
    }
}

function h$jsstringCommonPrefixes(x, y) {
                                                             ;
    var lx = x.length, ly = y.length, i = 0, cx;
    var l = lx <= ly ? lx : ly;
    if(lx === 0 || ly === 0 || x.charCodeAt(0) !== y.charCodeAt(0)) {
      return h$baseZCGHCziBaseziNothing;
    }
    while(++i<l) {
 cx = x.charCodeAt(i);
 if(cx !== y.charCodeAt(i)) {
     if(((cx|1023)===0xDFFF)) i--;
     break;
 }
    }
  if(i===0) return h$baseZCGHCziBaseziNothing;
    return (h$c1(h$baseZCGHCziBaseziJust_con_e, ((h$c3(h$ghczmprimZCGHCziTupleziZLz2cUz2cUZR_con_e,((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, ((i===lx)?x:((i===ly)?y:x.substr(0,i)))))),((i===lx) ? h$jsstringEmpty : (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(i))))),((i===ly) ? h$jsstringEmpty : (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (y.substr(i))))))))));



}

function h$jsstringBreakOn(b, x) {
                                                      ;
    var i = x.indexOf(b);
    if(i===-1) {
        { h$ret1 = (""); return (x); };
    }
    if(i===0) {
        { h$ret1 = (x); return (""); };
    }
    { h$ret1 = (x.substr(i)); return (x.substr(0,i)); };
}

function h$jsstringBreakOnEnd(b, x) {
                                                         ;
    var i = x.lastIndexOf(b);
  if(i===-1) {
    { h$ret1 = (x); return (""); };

    }
  i += b.length;
    { h$ret1 = (x.substr(i)); return (x.substr(0,i)); };
}

function h$jsstringBreakOnAll1(n, b, x) {
                                                                    ;
    var i = x.indexOf(b, n);
    if(i===0) {
       { h$ret1 = (""); h$ret2 = (x); return (b.length); };
    }
    if(i===-1) {
       { h$ret1 = (null); h$ret2 = (null); return (-1); };
    }
    { h$ret1 = (x.substr(0,i)); h$ret2 = (x.substr(i)); return (i+b.length); };
}

function h$jsstringBreakOnAll(pat, src) {
                                ;
    var a = [], i = 0, n = 0, r = h$ghczmprimZCGHCziTypesziZMZN, pl = pat.length;
    while(true) {
 var x = src.indexOf(pat, n);
 if(x === -1) break;
 a[i++] = (h$c2(h$ghczmprimZCGHCziTupleziZLz2cUZR_con_e,((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (src.substr(0,x))))),((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (src.substr(x)))))));
 n = x + pl;
    }
    while(--i >= 0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return r;
}

function h$jsstringSplitOn1(n, p, x) {
                                                                 ;
    var i = x.indexOf(p, n);
    if(i === -1) {
        { h$ret1 = (null); return (-1); };
    }
    var r1 = (i==n) ? "" : x.substr(n, i-n);
    { h$ret1 = (r1); return (i + p.length); };
}

function h$jsstringSplitOn(p, x) {
                                                      ;
    var a = x.split(p);
    var r = h$ghczmprimZCGHCziTypesziZMZN, i = a.length;
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return r;
}

// returns -1 for end of input, start of next token otherwise
// word in h$ret1
// this function assumes that there are no whitespace characters >= 0x10000
function h$jsstringWords1(n, x) {
                                                   ;
    var m = n, s = n, l = x.length;
    if(m >= l) return -1;
    // skip leading spaces
    do {
 if(m >= l) return -1;
    } while(h$isSpace(x.charCodeAt(m++)));
    // found start of word
    s = m - 1;
    while(m < l) {
 if(h$isSpace(x.charCodeAt(m++))) {
     // found end of word
            var r1 = (m-s<=1) ? "" : x.substr(s,m-s-1);
            { h$ret1 = (r1); return (m); };
 }
    }
    // end of string
    if(s < l) {
        var r1 = s === 0 ? x : x.substr(s);
        { h$ret1 = (r1); return (m); };
    }
    { h$ret1 = (null); return (-1); };
}

function h$jsstringWords(x) {
                                        ;
    var a = null, i = 0, n, s = -1, m = 0, w, l = x.length, r = h$ghczmprimZCGHCziTypesziZMZN;
    outer:
    while(m < l) {
 // skip leading spaces
 do {
     if(m >= l) { s = m; break outer; }
 } while(h$isSpace(x.charCodeAt(m++)));
 // found start of word
 s = m - 1;
 while(m < l) {
     if(h$isSpace(x.charCodeAt(m++))) {
  // found end of word
  w = (m-s<=1) ? h$jsstringEmpty
                             : (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(s,m-s-1))));
  if(i) a[i++] = w; else { a = [w]; i = 1; }
  s = m;
  break;
     }
 }
    }
    // end of string
    if(s !== -1 && s < l) {
 w = (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (s === 0 ? x : x.substr(s))));
 if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    // build resulting list
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return r;
}

// returns -1 for end of input, start of next token otherwise
// line in h$ret1
function h$jsstringLines1(n, x) {
                                                   ;
    var m = n, l = x.length;
    if(n >= l) return -1;
    while(m < l) {
 if(x.charCodeAt(m++) === 10) {
     // found newline
     if(n > 0 && n === l-1) return -1; // it was the last character
            var r1 = (m-n<=1) ? "" : x.substr(n,m-n-1);
            { h$ret1 = (r1); return (m); };
 }
    }
    // end of string
    { h$ret1 = (x.substr(n)); return (m); };
}

function h$jsstringLines(x) {
                                        ;
    var a = null, m = 0, i = 0, l = x.length, s = 0, r = h$ghczmprimZCGHCziTypesziZMZN, w;
    if(l === 0) return h$ghczmprimZCGHCziTypesziZMZN;
    outer:
    while(true) {
 s = m;
 do {
     if(m >= l) break outer;
 } while(x.charCodeAt(m++) !== 10);
 w = (m-s<=1) ? h$jsstringEmpty : (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(s,m-s-1))));
 if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    if(s < l) {
 w = (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(s))));
 if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return r;
}

function h$jsstringGroup(x) {
                                        ;
    var xl = x.length;
    if(xl === 0) return h$ghczmprimZCGHCziTypesziZMZN;
    var i = xl-1, si, ch, s=xl, r=h$ghczmprimZCGHCziTypesziZMZN;
    var tch = x.charCodeAt(i--);
    if(((tch|1023)===0xDFFF)) tch = ((((x.charCodeAt(i--))-0xD800)<<10)+(tch)-9216);
    while(i >= 0) {
 si = i;
 ch = x.charCodeAt(i--);
 if(((ch|1023)===0xDFFF)) {
     ch = ((((x.charCodeAt(i--))-0xD800)<<10)+(ch)-9216);
 }
 if(ch != tch) {
     tch = ch;
     r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(si+1,s-si))))), (r)));
     s = si;
 }
    }
    return (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(0,s+1))))), (r)));
}

function h$jsstringChunksOf1(n, s, x) {
                                                                ;
    var m = s, c = 0, l = x.length, ch;
    if(n <= 0 || l === 0 || s >= l) return -1
    while(++m < l && ++c < n) {
 ch = x.charCodeAt(m);
 if(((ch|1023)===0xDBFF)) ++m;
    }
    var r1 = (m >= l && s === c) ? x : x.substr(s,m-s);
    { h$ret1 = (r1); return (m); };
}

function h$jsstringChunksOf(n, x) {
                                                     ;
    var l = x.length;
    if(l===0 || n <= 0) return h$ghczmprimZCGHCziTypesziZMZN;
    if(l <= n) return (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x)))), (h$ghczmprimZCGHCziTypesziZMZN)));
    var a = [], i = 0, s = 0, ch, m = 0, c, r = h$ghczmprimZCGHCziTypesziZMZN;
    while(m < l) {
 s = m;
 c = 0;
 while(m < l && ++c <= n) {
     ch = x.charCodeAt(m++);
     if(((ch|1023)===0xDBFF)) ++m;
 }
 if(c) a[i++] = x.substr(s, m-s);
    }
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return r;
}

function h$jsstringCount(pat, src) {
                                                        ;
    var i = 0, n = 0, pl = pat.length, sl = src.length;
    while(i<sl) {
 i = src.indexOf(pat, i);
 if(i===-1) break;
 n++;
 i += pl;
    }
    return n;
}

function h$jsstringReplicate(n, str) {
                                                        ;
    if(n === 0 || str == '') return '';
    if(n === 1) return str;
    var r = '';
    do {
 if(n&1) r+=str;
        str+=str;
        n >>= 1;
    } while(n > 1);
    return r+str;
}

// this does not deal with combining diacritics, Data.Text does not either
var h$jsstringReverse;
if(Array.from) {
    h$jsstringReverse = function(str) {
                                                      ;
 return Array.from(str).reverse().join('');
    }
} else {
    h$jsstringReverse = function(str) {
                                                         ;
 var l = str.length, a = [], o = 0, i = 0, c, c1, s = '';
 while(i < l) {
     c = str.charCodeAt(i);
     if(((c|1023)===0xDBFF)) {
  a[i] = str.charCodeAt(i+1);
  a[i+1] = c;
  i += 2;
     } else a[i++] = c;
     if(i-o > 60000) {
  s = String.fromCharCode.apply(null, a.reverse()) + s;
  o = -i;
  a = [];
     }
 }
 return (i===0) ? s : String.fromCharCode.apply(null,a.reverse()) + s;
    }
}

function h$jsstringUnpack(str) {
                                           ;
    var r = h$ghczmprimZCGHCziTypesziZMZN, i = str.length-1, c;
    while(i >= 0) {
 c = str.charCodeAt(i--);
 if(((c|1023)===0xDFFF)) c = ((((str.charCodeAt(i--))-0xD800)<<10)+(c)-9216)
 r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (c), (r)));
    }
    return r;
}

function h$jsstringDecI64(hi,lo) {
                                              ;
    var lo0 = (lo < 0) ? lo+4294967296:lo;
    if(hi < 0) {
 if(hi === -1) return ''+(lo0-4294967296);
 lo0 = 4294967296 - lo0;
 var hi0 = -1 - hi;
 var x0 = hi0 * 967296;
 var x1 = (lo0 + x0) % 1000000;
 var x2 = hi0*4294+Math.floor((x0+lo0-x1)/1000000);
 return '-' + x2 + h$jsstringDecIPadded6(x1);
    } else {
 if(hi === 0) return ''+lo0;
 var x0 = hi * 967296;
 var x1 = (lo0 + x0) % 1000000;
 var x2 = hi*4294+Math.floor((x0+lo0-x1)/1000000);
 return '' + x2 + h$jsstringDecIPadded6(x1);
    }
}

function h$jsstringDecW64(hi,lo) {
                                              ;
    var lo0 = (lo < 0) ? lo+4294967296 : lo;
    if(hi === 0) return ''+lo0;
    var hi0 = (hi < 0) ? hi+4294967296 : hi;
    var x0 = hi0 * 967296;
    var x1 = (lo0 + x0) % 1000000;
    var x2 = hi0*4294+Math.floor((x0+lo0-x1)/1000000);
    return '' + x2 + h$jsstringDecIPadded6(x1);
}

function h$jsstringHexI64(hi,lo) {
    var lo0 = lo<0 ? lo+4294967296 : lo;
    if(hi === 0) return lo0.toString(16);
    return ((hi<0)?hi+4294967296:hi).toString(16) + h$jsstringHexIPadded8(lo0);
}

function h$jsstringHexW64(hi,lo) {
    var lo0 = lo<0 ? lo+4294967296 : lo;
    if(hi === 0) return lo0.toString(16);
    return ((hi<0)?hi+4294967296:hi).toString(16) + h$jsstringHexIPadded8(lo0);
}

// n in [0, 1000000000)
function h$jsstringDecIPadded9(n) {
                                       ;
    if(n === 0) return '000000000';
    var pad = (n>=100000000)?'':
              (n>=10000000)?'0':
              (n>=1000000)?'00':
              (n>=100000)?'000':
              (n>=10000)?'0000':
              (n>=1000)?'00000':
              (n>=100)?'000000':
              (n>=10)?'0000000':
                     '00000000';
    return pad+n;
}

// n in [0, 1000000)
function h$jsstringDecIPadded6(n) {
                                       ;
    if(n === 0) return '000000';
    var pad = (n>=100000)?'':
              (n>=10000)?'0':
              (n>=1000)?'00':
              (n>=100)?'000':
              (n>=10)?'0000':
                     '00000';
    return pad+n;
}

// n in [0, 2147483648)
function h$jsstringHexIPadded8(n) {
                                       ;
   if(n === 0) return '00000000';
   var pad = (n>=0x10000000)?'':
             (n>=0x1000000)?'0':
             (n>=0x100000)?'00':
             (n>=0x10000)?'000':
             (n>=0x1000)?'0000':
             (n>=0x100)?'00000':
             (n>=0x10)?'000000':
                      '0000000';
    return pad+n.toString(16);
}

function h$jsstringZeroes(n) {
    var r;
    switch(n&7) {
 case 0: r = ''; break;
 case 1: r = '0'; break;
 case 2: r = '00'; break;
 case 3: r = '000'; break;
 case 4: r = '0000'; break;
 case 5: r = '00000'; break;
 case 6: r = '000000'; break;
 case 7: r = '0000000';
    }
    for(var i=n>>3;i>0;i--) r = r + '00000000';
    return r;
}

function h$jsstringDoubleToFixed(decs, d) {
    if(decs >= 0) {
 if(Math.abs(d) < 1e21) {
     var r = d.toFixed(Math.min(20,decs));
     if(decs > 20) r = r + h$jsstringZeroes(decs-20);
     return r;
 } else {
     var r = d.toExponential();
     var ei = r.indexOf('e');
     var di = r.indexOf('.');
     var e = parseInt(r.substr(ei+1));
     return r.substring(0,di) + r.substring(di,ei) + h$jsstringZeroes(di-ei+e) +
                   ((decs > 0) ? ('.' + h$jsstringZeroes(decs)) : '');
 }
    }
    var r = Math.abs(d).toExponential();
    var ei = r.indexOf('e');
    var e = parseInt(r.substr(ei+1));
    var m = d < 0 ? '-' : '';
    r = r.substr(0,1) + r.substring(2,ei);
    if(e >= 0) {
 return (e > r.length) ? m + r + h$jsstringZeroes(r.length-e-1) + '.0'
                       : m + r.substr(0,e+1) + '.' + r.substr(e+1);
    } else {
 return m + '0.' + h$jsstringZeroes(-e-1) + r;
    }
}

function h$jsstringDoubleToExponent(decs, d) {
    var r;
    if(decs ===-1) {
 r = d.toExponential().replace('+','');
    } else {
 r = d.toExponential(Math.max(1, Math.min(20,decs))).replace('+','');
    }
    if(r.indexOf('.') === -1) {
 r = r.replace('e', '.0e');
    }
    if(decs > 20) r = r.replace('e', h$jsstringZeroes(decs-20)+'e');
    return r;
}

function h$jsstringDoubleGeneric(decs, d) {
    var r;
    if(decs === -1) {
 r = d.toString(10).replace('+','');
    } else {
 r = d.toPrecision(Math.max(decs+1,1)).replace('+','');
    }
    if(decs !== 0 && r.indexOf('.') === -1) {
 if(r.indexOf('e') !== -1) {
     r = r.replace('e', '.0e');
 } else {
     r = r + '.0';
 }
    }
    return r;
}

function h$jsstringAppend(x, y) {
                                                     ;
    return x+y;
}

function h$jsstringCompare(x, y) {
                                                      ;
    return (x<y)?-1:((x>y)?1:0);
}

function h$jsstringUnlines(xs) {
    var r = '';
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 r = r + ((((xs).d1)).d1) + '\n';
 xs = ((xs).d2);
    }
    return r;
}

function h$jsstringUnwords(xs) {
    if(((xs).f === h$ghczmprimZCGHCziTypesziZMZN_con_e)) return '';
    var r = ((((xs).d1)).d1);
    xs = ((xs).d2);
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 r = r + ' ' + ((((xs).d1)).d1);
 xs = ((xs).d2);
    }
    return r;
}

function h$jsstringReplace(pat, rep, src) {
                                                                        ;
    var r = src.replace(pat, rep, 'g');
    // the 'g' flag is not supported everywhere, check and fall back if necessary
    if(r.indexOf(pat) !== -1) {
 r = src.split(pat).join(rep);
    }
    return r;
}

function h$jsstringReplicateChar(n, ch) {
                                                    ;
    return h$jsstringReplicate(n, h$jsstringSingleton(ch));
}

function h$jsstringIsInteger(str) {
    return /^-?\d+$/.test(str);
}

function h$jsstringIsNatural(str) {
    return /^\d+$/.test(str);
}

function h$jsstringReadInt(str) {
    if(!/^-?\d+/.test(str)) return null;
    var x = parseInt(str, 10);
    var x0 = x|0;
    return (x===x0) ? x0 : null;
}

function h$jsstringLenientReadInt(str) {
    var x = parseInt(str, 10);
    var x0 = x|0;
    return (x===x0) ? x0 : null;
}

function h$jsstringReadWord(str) {
  if(!/^\d+/.test(str)) return null;
  var x = parseInt(str, 10);
  var x0 = x|0;
  if(x0<0) return (x===x0+2147483648) ? x0 : null;
  else return (x===x0) ? x0 : null;
}

function h$jsstringReadDouble(str) {
    return parseFloat(str, 10);
}

function h$jsstringLenientReadDouble(str) {
    return parseFloat(str, 10);
}

function h$jsstringReadInteger(str) {
                                       ;
  if(!/^(-)?\d+$/.test(str)) {
    return null;
  } else if(str.length <= 9) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (parseInt(str, 10))));;
  } else {
    return MK_INTEGER_J(new BigInteger(str, 10));
  }
}

function h$jsstringReadInt64(str) {
  if(!/^(-)?\d+$/.test(str)) {
      { h$ret1 = (0); h$ret2 = (0); return (0); };
  }
  if(str.charCodeAt(0) === 45) { // '-'
    return h$jsstringReadValue64(str, 1, true);
  } else {
    return h$jsstringReadValue64(str, 0, false);
  }
}

function h$jsstringReadWord64(str) {
  if(!/^\d+$/.test(str)) {
    { h$ret1 = (0); h$ret2 = (0); return (0); };
  }
  return h$jsstringReadValue64(str, 0, false);
}

var h$jsstringLongs = null;

function h$jsstringReadValue64(str, start, negate) {
  var l = str.length, i = start;
  while(i < l) {
    if(str.charCodeAt(i) !== 48) break;
    i++;
  }
  if(i >= l) { h$ret1 = (0); h$ret2 = (0); return (1); }; // only zeroes
  if(h$jsstringLongs === null) {
    h$jsstringLongs = [];
    for(var t=10; t<=1000000000; t*=10) {
      h$jsstringLongs.push(goog.math.Long.fromInt(t));
    }
  }
  var li = l-i;
  if(li < 10 && !negate) {
    { h$ret1 = (0); h$ret2 = (parseInt(str.substr(i), 10)); return (1); };
  }
  var r = goog.math.Long.fromInt(parseInt(str.substr(li,9),10));
  li += 9;
  while(li < l) {
    r = r.multiply(h$jsstringLongs[Math.min(l-li-1,8)])
         .add(goog.math.Long.fromInt(parseInt(str.substr(li,9), 10)));
    li += 9;
  }
  if(negate) {
    r = r.negate();
  }
  { h$ret1 = (r.getHighBits()); h$ret2 = (r.getLowBits()); return (1); };
}

function h$jsstringExecRE(i, str, re) {
    re.lastIndex = i;
    var m = re.exec(str);
    if(m === null) return -1;
    var a = [], x, j = 1, r = h$ghczmprimZCGHCziTypesziZMZN;
    while(true) {
 x = m[j];
 if(typeof x === 'undefined') break;
 a[j-1] = x;
 j++;
    }
    j-=1;
    while(--j>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (a[j])))), (r)));
    { h$ret1 = (m[0]); h$ret2 = (r); return (m.index); };
}

function h$jsstringReplaceRE(pat, replacement, str) {
    return str.replace(pat, replacement);
}

function h$jsstringSplitRE(limit, re, str) {
    re.lastIndex = i;
    var s = (limit < 0) ? str.split(re) : str.split(re, limit);
    var i = s.length, r = h$ghczmprimZCGHCziTypesziZMZN;
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return r;
}






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

/*
 * Functions that directly access JavaScript strings, ignoring character
 * widths and surrogate pairs.
 */

function h$jsstringRawChunksOf(k, x) {
    var l = x.length;
    if(l === 0) return h$ghczmprimZCGHCziTypesziZMZN;
    if(l <= k) return (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x)))), (h$ghczmprimZCGHCziTypesziZMZN)));
    var r=h$ghczmprimZCGHCziTypesziZMZN;
    for(var i=ls-k;i>=0;i-=k) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(i,i+k))))), (r)));
    return r;
}

function h$jsstringRawSplitAt(k, x) {
    if(k === 0) return (h$c2(h$ghczmprimZCGHCziTupleziZLz2cUZR_con_e,(h$jsstringEmpty),((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x))))));
    if(k >= x.length) return (h$c2(h$ghczmprimZCGHCziTupleziZLz2cUZR_con_e,((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x)))),(h$jsstringEmpty)));
    return (h$c2(h$ghczmprimZCGHCziTupleziZLz2cUZR_con_e,((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(0,k))))),((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(k)))))));
}
function h$foreignListProps(o) {
    var r = HS_NIL;
    if(typeof o === 'undefined' || o === null) return null;
    throw "h$foreignListProps";
/*    for(var p in o) {

    } */
}
// conversion between JavaScript string and Data.Text







// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;


/*
  convert a Data.Text buffer with offset/length to a JavaScript string
 */
function h$textToString(arr, off, len) {
    var a = [];
    var end = off+len;
    var k = 0;
    var u1 = arr.u1;
    var s = '';
    for(var i=off;i<end;i++) {
 var cc = u1[i];
 a[k++] = cc;
 if(k === 60000) {
     s += String.fromCharCode.apply(this, a);
     k = 0;
     a = [];
 }
    }
    return s + String.fromCharCode.apply(this, a);
}

/*
   convert a JavaScript string to a Data.Text buffer, second return
   value is length
 */
function h$textFromString(s) {
    var l = s.length;
    var b = h$newByteArray(l * 2);
    var u1 = b.u1;
    for(var i=l-1;i>=0;i--) u1[i] = s.charCodeAt(i);
    { h$ret1 = (l); return (b); };
}

function h$lazyTextToString(txt) {
    var s = '';
    while(((txt).f.a === 2)) {
        var head = ((txt));
        s += h$textToString(((head).d1), ((head).d2.d1), ((head).d2.d2));
        txt = ((txt).d2.d3);
    }
    return s;
}

function h$safeTextFromString(x) {
    if(typeof x !== 'string') {
 { h$ret1 = (0); return (null); };
    }
    return h$textFromString(x);
}






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

function h$allProps(o) {
    var a = [], i = 0;
    for(var p in o) a[i++] = p;
    return a;
}

function h$listProps(o) {
    var r = h$ghczmprimZCGHCziTypesziZMZN;
    for(var p in o) { r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (p)))), (r))); }
    return r;
}

function h$listAssocs(o) {
    var r = h$ghczmprimZCGHCziTypesziZMZN;
    for(var p in o) { r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c2(h$ghczmprimZCGHCziTupleziZLz2cUZR_con_e,((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (p)))),((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (o[p]))))))), (r))); }
    return r;
}

function h$isNumber(o) {
    return typeof(o) === 'number';
}

// returns true for null, but not for functions and host objects
function h$isObject(o) {
    return typeof(o) === 'object';
}

function h$isString(o) {
    return typeof(o) === 'string';
}

function h$isSymbol(o) {
    return typeof(o) === 'symbol';
}

function h$isBoolean(o) {
    return typeof(o) === 'boolean';
}

function h$isFunction(o) {
    return typeof(o) === 'function';
}

function h$jsTypeOf(o) {
    var t = typeof(o);
    if(t === 'undefined') return 0;
    if(t === 'object') return 1;
    if(t === 'boolean') return 2;
    if(t === 'number') return 3;
    if(t === 'string') return 4;
    if(t === 'symbol') return 5;
    if(t === 'function') return 6;
    return 7; // other, host object etc
}

/*
        -- 0 - null, 1 - integer,
        -- 2 - float, 3 - bool,
        -- 4 - string, 5 - array
        -- 6 - object
*/
function h$jsonTypeOf(o) {
    if (!(o instanceof Object)) {
        if (o == null) {
            return 0;
        } else if (typeof o == 'number') {
            if (h$isInteger(o)) {
                return 1;
            } else {
                return 2;
            }
        } else if (typeof o == 'boolean') {
            return 3;
        } else {
            return 4;
        }
    } else {
        if (Object.prototype.toString.call(o) == '[object Array]') {
            // it's an array
            return 5;
        } else if (!o) {
            // null 
            return 0;
        } else {
            // it's an object
            return 6;
        }
    }

}
function h$sendXHR(xhr, d, cont) {
    xhr.addEventListener('error', function () {
 cont(2);
    });
    xhr.addEventListener('abort', function() {
 cont(1);
    });
    xhr.addEventListener('load', function() {
 cont(0);
    });
    if(d) {
 xhr.send(d);
    } else {
 xhr.send();
    }
}
(function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){(function(global){global.h$concur={React:require("react"),ReactDOM:require("react-dom"),makeHandler:function(action,async){var f=function(ev){return h$concurEventCallback(async,action,ev)};f.hsAction=action;return f}}}).call(this,typeof global!=="undefined"?global:typeof self!=="undefined"?self:typeof window!=="undefined"?window:{})},{react:183,"react-dom":31}],2:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var emptyObject=require("fbjs/lib/emptyObject");var _invariant=require("fbjs/lib/invariant");if(process.env.NODE_ENV!=="production"){var warning=require("fbjs/lib/warning")}var MIXINS_KEY="mixins";function identity(fn){return fn}var ReactPropTypeLocationNames;if(process.env.NODE_ENV!=="production"){ReactPropTypeLocationNames={prop:"prop",context:"context",childContext:"child context"}}else{ReactPropTypeLocationNames={}}function factory(ReactComponent,isValidElement,ReactNoopUpdateQueue){var injectedMixins=[];var ReactClassInterface={mixins:"DEFINE_MANY",statics:"DEFINE_MANY",propTypes:"DEFINE_MANY",contextTypes:"DEFINE_MANY",childContextTypes:"DEFINE_MANY",getDefaultProps:"DEFINE_MANY_MERGED",getInitialState:"DEFINE_MANY_MERGED",getChildContext:"DEFINE_MANY_MERGED",render:"DEFINE_ONCE",componentWillMount:"DEFINE_MANY",componentDidMount:"DEFINE_MANY",componentWillReceiveProps:"DEFINE_MANY",shouldComponentUpdate:"DEFINE_ONCE",componentWillUpdate:"DEFINE_MANY",componentDidUpdate:"DEFINE_MANY",componentWillUnmount:"DEFINE_MANY",updateComponent:"OVERRIDE_BASE"};var RESERVED_SPEC_KEYS={displayName:function(Constructor,displayName){Constructor.displayName=displayName},mixins:function(Constructor,mixins){if(mixins){for(var i=0;i<mixins.length;i++){mixSpecIntoComponent(Constructor,mixins[i])}}},childContextTypes:function(Constructor,childContextTypes){if(process.env.NODE_ENV!=="production"){validateTypeDef(Constructor,childContextTypes,"childContext")}Constructor.childContextTypes=_assign({},Constructor.childContextTypes,childContextTypes)},contextTypes:function(Constructor,contextTypes){if(process.env.NODE_ENV!=="production"){validateTypeDef(Constructor,contextTypes,"context")}Constructor.contextTypes=_assign({},Constructor.contextTypes,contextTypes)},getDefaultProps:function(Constructor,getDefaultProps){if(Constructor.getDefaultProps){Constructor.getDefaultProps=createMergedResultFunction(Constructor.getDefaultProps,getDefaultProps)}else{Constructor.getDefaultProps=getDefaultProps}},propTypes:function(Constructor,propTypes){if(process.env.NODE_ENV!=="production"){validateTypeDef(Constructor,propTypes,"prop")}Constructor.propTypes=_assign({},Constructor.propTypes,propTypes)},statics:function(Constructor,statics){mixStaticSpecIntoComponent(Constructor,statics)},autobind:function(){}};function validateTypeDef(Constructor,typeDef,location){for(var propName in typeDef){if(typeDef.hasOwnProperty(propName)){if(process.env.NODE_ENV!=="production"){warning(typeof typeDef[propName]==="function","%s: %s type `%s` is invalid; it must be a function, usually from "+"React.PropTypes.",Constructor.displayName||"ReactClass",ReactPropTypeLocationNames[location],propName)}}}}function validateMethodOverride(isAlreadyDefined,name){var specPolicy=ReactClassInterface.hasOwnProperty(name)?ReactClassInterface[name]:null;if(ReactClassMixin.hasOwnProperty(name)){_invariant(specPolicy==="OVERRIDE_BASE","ReactClassInterface: You are attempting to override "+"`%s` from your class specification. Ensure that your method names "+"do not overlap with React methods.",name)}if(isAlreadyDefined){_invariant(specPolicy==="DEFINE_MANY"||specPolicy==="DEFINE_MANY_MERGED","ReactClassInterface: You are attempting to define "+"`%s` on your component more than once. This conflict may be due "+"to a mixin.",name)}}function mixSpecIntoComponent(Constructor,spec){if(!spec){if(process.env.NODE_ENV!=="production"){var typeofSpec=typeof spec;var isMixinValid=typeofSpec==="object"&&spec!==null;if(process.env.NODE_ENV!=="production"){warning(isMixinValid,"%s: You're attempting to include a mixin that is either null "+"or not an object. Check the mixins included by the component, "+"as well as any mixins they include themselves. "+"Expected object but got %s.",Constructor.displayName||"ReactClass",spec===null?null:typeofSpec)}}return}_invariant(typeof spec!=="function","ReactClass: You're attempting to "+"use a component class or function as a mixin. Instead, just use a "+"regular object.");_invariant(!isValidElement(spec),"ReactClass: You're attempting to "+"use a component as a mixin. Instead, just use a regular object.");var proto=Constructor.prototype;var autoBindPairs=proto.__reactAutoBindPairs;if(spec.hasOwnProperty(MIXINS_KEY)){RESERVED_SPEC_KEYS.mixins(Constructor,spec.mixins)}for(var name in spec){if(!spec.hasOwnProperty(name)){continue}if(name===MIXINS_KEY){continue}var property=spec[name];var isAlreadyDefined=proto.hasOwnProperty(name);validateMethodOverride(isAlreadyDefined,name);if(RESERVED_SPEC_KEYS.hasOwnProperty(name)){RESERVED_SPEC_KEYS[name](Constructor,property)}else{var isReactClassMethod=ReactClassInterface.hasOwnProperty(name);var isFunction=typeof property==="function";var shouldAutoBind=isFunction&&!isReactClassMethod&&!isAlreadyDefined&&spec.autobind!==false;if(shouldAutoBind){autoBindPairs.push(name,property);proto[name]=property}else{if(isAlreadyDefined){var specPolicy=ReactClassInterface[name];_invariant(isReactClassMethod&&(specPolicy==="DEFINE_MANY_MERGED"||specPolicy==="DEFINE_MANY"),"ReactClass: Unexpected spec policy %s for key %s "+"when mixing in component specs.",specPolicy,name);if(specPolicy==="DEFINE_MANY_MERGED"){proto[name]=createMergedResultFunction(proto[name],property)}else if(specPolicy==="DEFINE_MANY"){proto[name]=createChainedFunction(proto[name],property)}}else{proto[name]=property;if(process.env.NODE_ENV!=="production"){if(typeof property==="function"&&spec.displayName){proto[name].displayName=spec.displayName+"_"+name}}}}}}}function mixStaticSpecIntoComponent(Constructor,statics){if(!statics){return}for(var name in statics){var property=statics[name];if(!statics.hasOwnProperty(name)){continue}var isReserved=name in RESERVED_SPEC_KEYS;_invariant(!isReserved,"ReactClass: You are attempting to define a reserved "+'property, `%s`, that shouldn\'t be on the "statics" key. Define it '+"as an instance property instead; it will still be accessible on the "+"constructor.",name);var isInherited=name in Constructor;_invariant(!isInherited,"ReactClass: You are attempting to define "+"`%s` on your component more than once. This conflict may be "+"due to a mixin.",name);Constructor[name]=property}}function mergeIntoWithNoDuplicateKeys(one,two){_invariant(one&&two&&typeof one==="object"&&typeof two==="object","mergeIntoWithNoDuplicateKeys(): Cannot merge non-objects.");for(var key in two){if(two.hasOwnProperty(key)){_invariant(one[key]===undefined,"mergeIntoWithNoDuplicateKeys(): "+"Tried to merge two objects with the same key: `%s`. This conflict "+"may be due to a mixin; in particular, this may be caused by two "+"getInitialState() or getDefaultProps() methods returning objects "+"with clashing keys.",key);one[key]=two[key]}}return one}function createMergedResultFunction(one,two){return function mergedResult(){var a=one.apply(this,arguments);var b=two.apply(this,arguments);if(a==null){return b}else if(b==null){return a}var c={};mergeIntoWithNoDuplicateKeys(c,a);mergeIntoWithNoDuplicateKeys(c,b);return c}}function createChainedFunction(one,two){return function chainedFunction(){one.apply(this,arguments);two.apply(this,arguments)}}function bindAutoBindMethod(component,method){var boundMethod=method.bind(component);if(process.env.NODE_ENV!=="production"){boundMethod.__reactBoundContext=component;boundMethod.__reactBoundMethod=method;boundMethod.__reactBoundArguments=null;var componentName=component.constructor.displayName;var _bind=boundMethod.bind;boundMethod.bind=function(newThis){for(var _len=arguments.length,args=Array(_len>1?_len-1:0),_key=1;_key<_len;_key++){args[_key-1]=arguments[_key]}if(newThis!==component&&newThis!==null){if(process.env.NODE_ENV!=="production"){warning(false,"bind(): React component methods may only be bound to the "+"component instance. See %s",componentName)}}else if(!args.length){if(process.env.NODE_ENV!=="production"){warning(false,"bind(): You are binding a component method to the component. "+"React does this for you automatically in a high-performance "+"way, so you can safely remove this call. See %s",componentName)}return boundMethod}var reboundMethod=_bind.apply(boundMethod,arguments);reboundMethod.__reactBoundContext=component;reboundMethod.__reactBoundMethod=method;reboundMethod.__reactBoundArguments=args;return reboundMethod}}return boundMethod}function bindAutoBindMethods(component){var pairs=component.__reactAutoBindPairs;for(var i=0;i<pairs.length;i+=2){var autoBindKey=pairs[i];var method=pairs[i+1];component[autoBindKey]=bindAutoBindMethod(component,method)}}var IsMountedPreMixin={componentDidMount:function(){this.__isMounted=true}};var IsMountedPostMixin={componentWillUnmount:function(){this.__isMounted=false}};var ReactClassMixin={replaceState:function(newState,callback){this.updater.enqueueReplaceState(this,newState,callback)},isMounted:function(){if(process.env.NODE_ENV!=="production"){warning(this.__didWarnIsMounted,"%s: isMounted is deprecated. Instead, make sure to clean up "+"subscriptions and pending requests in componentWillUnmount to "+"prevent memory leaks.",this.constructor&&this.constructor.displayName||this.name||"Component");this.__didWarnIsMounted=true}return!!this.__isMounted}};var ReactClassComponent=function(){};_assign(ReactClassComponent.prototype,ReactComponent.prototype,ReactClassMixin);function createClass(spec){var Constructor=identity(function(props,context,updater){if(process.env.NODE_ENV!=="production"){warning(this instanceof Constructor,"Something is calling a React component directly. Use a factory or "+"JSX instead. See: https://fb.me/react-legacyfactory")}if(this.__reactAutoBindPairs.length){bindAutoBindMethods(this)}this.props=props;this.context=context;this.refs=emptyObject;this.updater=updater||ReactNoopUpdateQueue;this.state=null;var initialState=this.getInitialState?this.getInitialState():null;if(process.env.NODE_ENV!=="production"){if(initialState===undefined&&this.getInitialState._isMockFunction){initialState=null}}_invariant(typeof initialState==="object"&&!Array.isArray(initialState),"%s.getInitialState(): must return an object or null",Constructor.displayName||"ReactCompositeComponent");this.state=initialState});Constructor.prototype=new ReactClassComponent;Constructor.prototype.constructor=Constructor;Constructor.prototype.__reactAutoBindPairs=[];injectedMixins.forEach(mixSpecIntoComponent.bind(null,Constructor));mixSpecIntoComponent(Constructor,IsMountedPreMixin);mixSpecIntoComponent(Constructor,spec);mixSpecIntoComponent(Constructor,IsMountedPostMixin);if(Constructor.getDefaultProps){Constructor.defaultProps=Constructor.getDefaultProps()}if(process.env.NODE_ENV!=="production"){if(Constructor.getDefaultProps){Constructor.getDefaultProps.isReactClassApproved={}}if(Constructor.prototype.getInitialState){Constructor.prototype.getInitialState.isReactClassApproved={}}}_invariant(Constructor.prototype.render,"createClass(...): Class specification must implement a `render` method.");if(process.env.NODE_ENV!=="production"){warning(!Constructor.prototype.componentShouldUpdate,"%s has a method called "+"componentShouldUpdate(). Did you mean shouldComponentUpdate()? "+"The name is phrased as a question because the function is "+"expected to return a value.",spec.displayName||"A component");warning(!Constructor.prototype.componentWillRecieveProps,"%s has a method called "+"componentWillRecieveProps(). Did you mean componentWillReceiveProps()?",spec.displayName||"A component")}for(var methodName in ReactClassInterface){if(!Constructor.prototype[methodName]){Constructor.prototype[methodName]=null}}return Constructor}return createClass}module.exports=factory}).call(this,require("_process"))},{_process:184,"fbjs/lib/emptyObject":11,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"object-assign":26}],3:[function(require,module,exports){(function(process){"use strict";var emptyFunction=require("./emptyFunction");var EventListener={listen:function listen(target,eventType,callback){if(target.addEventListener){target.addEventListener(eventType,callback,false);return{remove:function remove(){target.removeEventListener(eventType,callback,false)}}}else if(target.attachEvent){target.attachEvent("on"+eventType,callback);return{remove:function remove(){target.detachEvent("on"+eventType,callback)}}}},capture:function capture(target,eventType,callback){if(target.addEventListener){target.addEventListener(eventType,callback,true);return{remove:function remove(){target.removeEventListener(eventType,callback,true)}}}else{if(process.env.NODE_ENV!=="production"){console.error("Attempted to listen to events during the capture phase on a "+"browser that does not support the capture phase. Your application "+"will not receive some events.")}return{remove:emptyFunction}}},registerDefault:function registerDefault(){}};module.exports=EventListener}).call(this,require("_process"))},{"./emptyFunction":10,_process:184}],4:[function(require,module,exports){"use strict";var canUseDOM=!!(typeof window!=="undefined"&&window.document&&window.document.createElement);var ExecutionEnvironment={canUseDOM:canUseDOM,canUseWorkers:typeof Worker!=="undefined",canUseEventListeners:canUseDOM&&!!(window.addEventListener||window.attachEvent),canUseViewport:canUseDOM&&!!window.screen,isInWorker:!canUseDOM};module.exports=ExecutionEnvironment},{}],5:[function(require,module,exports){"use strict";var _hyphenPattern=/-(.)/g;function camelize(string){return string.replace(_hyphenPattern,function(_,character){return character.toUpperCase()})}module.exports=camelize},{}],6:[function(require,module,exports){"use strict";var camelize=require("./camelize");var msPattern=/^-ms-/;function camelizeStyleName(string){return camelize(string.replace(msPattern,"ms-"))}module.exports=camelizeStyleName},{"./camelize":5}],7:[function(require,module,exports){"use strict";var isTextNode=require("./isTextNode");function containsNode(outerNode,innerNode){if(!outerNode||!innerNode){return false}else if(outerNode===innerNode){return true}else if(isTextNode(outerNode)){return false}else if(isTextNode(innerNode)){return containsNode(outerNode,innerNode.parentNode)}else if("contains"in outerNode){return outerNode.contains(innerNode)}else if(outerNode.compareDocumentPosition){return!!(outerNode.compareDocumentPosition(innerNode)&16)}else{return false}}module.exports=containsNode},{"./isTextNode":20}],8:[function(require,module,exports){(function(process){"use strict";var invariant=require("./invariant");function toArray(obj){var length=obj.length;!(!Array.isArray(obj)&&(typeof obj==="object"||typeof obj==="function"))?process.env.NODE_ENV!=="production"?invariant(false,"toArray: Array-like object expected"):invariant(false):void 0;!(typeof length==="number")?process.env.NODE_ENV!=="production"?invariant(false,"toArray: Object needs a length property"):invariant(false):void 0;!(length===0||length-1 in obj)?process.env.NODE_ENV!=="production"?invariant(false,"toArray: Object should have keys for indices"):invariant(false):void 0;!(typeof obj.callee!=="function")?process.env.NODE_ENV!=="production"?invariant(false,"toArray: Object can't be `arguments`. Use rest params "+"(function(...args) {}) or Array.from() instead."):invariant(false):void 0;if(obj.hasOwnProperty){try{return Array.prototype.slice.call(obj)}catch(e){}}var ret=Array(length);for(var ii=0;ii<length;ii++){ret[ii]=obj[ii]}return ret}function hasArrayNature(obj){return!!obj&&(typeof obj=="object"||typeof obj=="function")&&"length"in obj&&!("setInterval"in obj)&&typeof obj.nodeType!="number"&&(Array.isArray(obj)||"callee"in obj||"item"in obj)}function createArrayFromMixed(obj){if(!hasArrayNature(obj)){return[obj]}else if(Array.isArray(obj)){return obj.slice()}else{return toArray(obj)}}module.exports=createArrayFromMixed}).call(this,require("_process"))},{"./invariant":18,_process:184}],9:[function(require,module,exports){(function(process){"use strict";var ExecutionEnvironment=require("./ExecutionEnvironment");var createArrayFromMixed=require("./createArrayFromMixed");var getMarkupWrap=require("./getMarkupWrap");var invariant=require("./invariant");var dummyNode=ExecutionEnvironment.canUseDOM?document.createElement("div"):null;var nodeNamePattern=/^\s*<(\w+)/;function getNodeName(markup){var nodeNameMatch=markup.match(nodeNamePattern);return nodeNameMatch&&nodeNameMatch[1].toLowerCase()}function createNodesFromMarkup(markup,handleScript){var node=dummyNode;!!!dummyNode?process.env.NODE_ENV!=="production"?invariant(false,"createNodesFromMarkup dummy not initialized"):invariant(false):void 0;var nodeName=getNodeName(markup);var wrap=nodeName&&getMarkupWrap(nodeName);if(wrap){node.innerHTML=wrap[1]+markup+wrap[2];var wrapDepth=wrap[0];while(wrapDepth--){node=node.lastChild}}else{node.innerHTML=markup}var scripts=node.getElementsByTagName("script");if(scripts.length){!handleScript?process.env.NODE_ENV!=="production"?invariant(false,"createNodesFromMarkup(...): Unexpected <script> element rendered."):invariant(false):void 0;createArrayFromMixed(scripts).forEach(handleScript)}var nodes=Array.from(node.childNodes);while(node.lastChild){node.removeChild(node.lastChild)}return nodes}module.exports=createNodesFromMarkup}).call(this,require("_process"))},{"./ExecutionEnvironment":4,"./createArrayFromMixed":8,"./getMarkupWrap":14,"./invariant":18,_process:184}],10:[function(require,module,exports){"use strict";function makeEmptyFunction(arg){return function(){return arg}}var emptyFunction=function emptyFunction(){};emptyFunction.thatReturns=makeEmptyFunction;emptyFunction.thatReturnsFalse=makeEmptyFunction(false);emptyFunction.thatReturnsTrue=makeEmptyFunction(true);emptyFunction.thatReturnsNull=makeEmptyFunction(null);emptyFunction.thatReturnsThis=function(){return this};emptyFunction.thatReturnsArgument=function(arg){return arg};module.exports=emptyFunction},{}],11:[function(require,module,exports){(function(process){"use strict";var emptyObject={};if(process.env.NODE_ENV!=="production"){Object.freeze(emptyObject)}module.exports=emptyObject}).call(this,require("_process"))},{_process:184}],12:[function(require,module,exports){"use strict";function focusNode(node){try{node.focus()}catch(e){}}module.exports=focusNode},{}],13:[function(require,module,exports){"use strict";function getActiveElement(doc){doc=doc||(typeof document!=="undefined"?document:undefined);if(typeof doc==="undefined"){return null}try{return doc.activeElement||doc.body}catch(e){return doc.body}}module.exports=getActiveElement},{}],14:[function(require,module,exports){(function(process){"use strict";var ExecutionEnvironment=require("./ExecutionEnvironment");var invariant=require("./invariant");var dummyNode=ExecutionEnvironment.canUseDOM?document.createElement("div"):null;var shouldWrap={};var selectWrap=[1,'<select multiple="true">',"</select>"];var tableWrap=[1,"<table>","</table>"];var trWrap=[3,"<table><tbody><tr>","</tr></tbody></table>"];var svgWrap=[1,'<svg xmlns="http://www.w3.org/2000/svg">',"</svg>"];var markupWrap={"*":[1,"?<div>","</div>"],area:[1,"<map>","</map>"],col:[2,"<table><tbody></tbody><colgroup>","</colgroup></table>"],legend:[1,"<fieldset>","</fieldset>"],param:[1,"<object>","</object>"],tr:[2,"<table><tbody>","</tbody></table>"],optgroup:selectWrap,option:selectWrap,caption:tableWrap,colgroup:tableWrap,tbody:tableWrap,tfoot:tableWrap,thead:tableWrap,td:trWrap,th:trWrap};var svgElements=["circle","clipPath","defs","ellipse","g","image","line","linearGradient","mask","path","pattern","polygon","polyline","radialGradient","rect","stop","text","tspan"];svgElements.forEach(function(nodeName){markupWrap[nodeName]=svgWrap;shouldWrap[nodeName]=true});function getMarkupWrap(nodeName){!!!dummyNode?process.env.NODE_ENV!=="production"?invariant(false,"Markup wrapping node not initialized"):invariant(false):void 0;if(!markupWrap.hasOwnProperty(nodeName)){nodeName="*"}if(!shouldWrap.hasOwnProperty(nodeName)){if(nodeName==="*"){dummyNode.innerHTML="<link />"}else{dummyNode.innerHTML="<"+nodeName+"></"+nodeName+">"}shouldWrap[nodeName]=!dummyNode.firstChild}return shouldWrap[nodeName]?markupWrap[nodeName]:null}module.exports=getMarkupWrap}).call(this,require("_process"))},{"./ExecutionEnvironment":4,"./invariant":18,_process:184}],15:[function(require,module,exports){"use strict";function getUnboundedScrollPosition(scrollable){if(scrollable.Window&&scrollable instanceof scrollable.Window){return{x:scrollable.pageXOffset||scrollable.document.documentElement.scrollLeft,y:scrollable.pageYOffset||scrollable.document.documentElement.scrollTop}}return{x:scrollable.scrollLeft,y:scrollable.scrollTop}}module.exports=getUnboundedScrollPosition},{}],16:[function(require,module,exports){"use strict";var _uppercasePattern=/([A-Z])/g;function hyphenate(string){return string.replace(_uppercasePattern,"-$1").toLowerCase()}module.exports=hyphenate},{}],17:[function(require,module,exports){"use strict";var hyphenate=require("./hyphenate");var msPattern=/^ms-/;function hyphenateStyleName(string){return hyphenate(string).replace(msPattern,"-ms-")}module.exports=hyphenateStyleName},{"./hyphenate":16}],18:[function(require,module,exports){(function(process){"use strict";var validateFormat=function validateFormat(format){};if(process.env.NODE_ENV!=="production"){validateFormat=function validateFormat(format){if(format===undefined){throw new Error("invariant requires an error message argument")}}}function invariant(condition,format,a,b,c,d,e,f){validateFormat(format);if(!condition){var error;if(format===undefined){error=new Error("Minified exception occurred; use the non-minified dev environment "+"for the full error message and additional helpful warnings.")}else{var args=[a,b,c,d,e,f];var argIndex=0;error=new Error(format.replace(/%s/g,function(){return args[argIndex++]}));error.name="Invariant Violation"}error.framesToPop=1;throw error}}module.exports=invariant}).call(this,require("_process"))},{_process:184}],19:[function(require,module,exports){"use strict";function isNode(object){var doc=object?object.ownerDocument||object:document;var defaultView=doc.defaultView||window;return!!(object&&(typeof defaultView.Node==="function"?object instanceof defaultView.Node:typeof object==="object"&&typeof object.nodeType==="number"&&typeof object.nodeName==="string"))}module.exports=isNode},{}],20:[function(require,module,exports){"use strict";var isNode=require("./isNode");function isTextNode(object){return isNode(object)&&object.nodeType==3}module.exports=isTextNode},{"./isNode":19}],21:[function(require,module,exports){"use strict";function memoizeStringOnly(callback){var cache={};return function(string){if(!cache.hasOwnProperty(string)){cache[string]=callback.call(this,string)}return cache[string]}}module.exports=memoizeStringOnly},{}],22:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("./ExecutionEnvironment");var performance;if(ExecutionEnvironment.canUseDOM){performance=window.performance||window.msPerformance||window.webkitPerformance}module.exports=performance||{}},{"./ExecutionEnvironment":4}],23:[function(require,module,exports){"use strict";var performance=require("./performance");var performanceNow;if(performance.now){performanceNow=function performanceNow(){return performance.now()}}else{performanceNow=function performanceNow(){return Date.now()}}module.exports=performanceNow},{"./performance":22}],24:[function(require,module,exports){"use strict";var hasOwnProperty=Object.prototype.hasOwnProperty;function is(x,y){if(x===y){return x!==0||y!==0||1/x===1/y}else{return x!==x&&y!==y}}function shallowEqual(objA,objB){if(is(objA,objB)){return true}if(typeof objA!=="object"||objA===null||typeof objB!=="object"||objB===null){return false}var keysA=Object.keys(objA);var keysB=Object.keys(objB);if(keysA.length!==keysB.length){return false}for(var i=0;i<keysA.length;i++){if(!hasOwnProperty.call(objB,keysA[i])||!is(objA[keysA[i]],objB[keysA[i]])){return false}}return true}module.exports=shallowEqual},{}],25:[function(require,module,exports){(function(process){"use strict";var emptyFunction=require("./emptyFunction");var warning=emptyFunction;if(process.env.NODE_ENV!=="production"){var printWarning=function printWarning(format){for(var _len=arguments.length,args=Array(_len>1?_len-1:0),_key=1;_key<_len;_key++){args[_key-1]=arguments[_key]}var argIndex=0;var message="Warning: "+format.replace(/%s/g,function(){return args[argIndex++]});if(typeof console!=="undefined"){console.error(message)}try{throw new Error(message)}catch(x){}};warning=function warning(condition,format){if(format===undefined){throw new Error("`warning(condition, format, ...args)` requires a warning "+"message argument")}if(format.indexOf("Failed Composite propType: ")===0){return}if(!condition){for(var _len2=arguments.length,args=Array(_len2>2?_len2-2:0),_key2=2;_key2<_len2;_key2++){args[_key2-2]=arguments[_key2]}printWarning.apply(undefined,[format].concat(args))}}}module.exports=warning}).call(this,require("_process"))},{"./emptyFunction":10,_process:184}],26:[function(require,module,exports){"use strict";var getOwnPropertySymbols=Object.getOwnPropertySymbols;var hasOwnProperty=Object.prototype.hasOwnProperty;var propIsEnumerable=Object.prototype.propertyIsEnumerable;function toObject(val){if(val===null||val===undefined){throw new TypeError("Object.assign cannot be called with null or undefined")}return Object(val)}function shouldUseNative(){try{if(!Object.assign){return false}var test1=new String("abc");test1[5]="de";if(Object.getOwnPropertyNames(test1)[0]==="5"){return false}var test2={};for(var i=0;i<10;i++){test2["_"+String.fromCharCode(i)]=i}var order2=Object.getOwnPropertyNames(test2).map(function(n){return test2[n]});if(order2.join("")!=="0123456789"){return false}var test3={};"abcdefghijklmnopqrst".split("").forEach(function(letter){test3[letter]=letter});if(Object.keys(Object.assign({},test3)).join("")!=="abcdefghijklmnopqrst"){return false}return true}catch(err){return false}}module.exports=shouldUseNative()?Object.assign:function(target,source){var from;var to=toObject(target);var symbols;for(var s=1;s<arguments.length;s++){from=Object(arguments[s]);for(var key in from){if(hasOwnProperty.call(from,key)){to[key]=from[key]}}if(getOwnPropertySymbols){symbols=getOwnPropertySymbols(from);for(var i=0;i<symbols.length;i++){if(propIsEnumerable.call(from,symbols[i])){to[symbols[i]]=from[symbols[i]]}}}}return to}},{}],27:[function(require,module,exports){(function(process){"use strict";if(process.env.NODE_ENV!=="production"){var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ReactPropTypesSecret=require("./lib/ReactPropTypesSecret");var loggedTypeFailures={}}function checkPropTypes(typeSpecs,values,location,componentName,getStack){if(process.env.NODE_ENV!=="production"){for(var typeSpecName in typeSpecs){if(typeSpecs.hasOwnProperty(typeSpecName)){var error;try{invariant(typeof typeSpecs[typeSpecName]==="function","%s: %s type `%s` is invalid; it must be a function, usually from "+"React.PropTypes.",componentName||"React class",location,typeSpecName);error=typeSpecs[typeSpecName](values,typeSpecName,componentName,location,null,ReactPropTypesSecret)}catch(ex){error=ex}warning(!error||error instanceof Error,"%s: type specification of %s `%s` is invalid; the type checker "+"function must return `null` or an `Error` but returned a %s. "+"You may have forgotten to pass an argument to the type checker "+"creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and "+"shape all require an argument).",componentName||"React class",location,typeSpecName,typeof error);if(error instanceof Error&&!(error.message in loggedTypeFailures)){loggedTypeFailures[error.message]=true;var stack=getStack?getStack():"";warning(false,"Failed %s type: %s%s",location,error.message,stack!=null?stack:"")}}}}}module.exports=checkPropTypes}).call(this,require("_process"))},{"./lib/ReactPropTypesSecret":30,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],28:[function(require,module,exports){"use strict";var factory=require("./factoryWithTypeCheckers");module.exports=function(isValidElement){var throwOnDirectAccess=false;return factory(isValidElement,throwOnDirectAccess)}},{"./factoryWithTypeCheckers":29}],29:[function(require,module,exports){(function(process){"use strict";var emptyFunction=require("fbjs/lib/emptyFunction");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ReactPropTypesSecret=require("./lib/ReactPropTypesSecret");var checkPropTypes=require("./checkPropTypes");module.exports=function(isValidElement,throwOnDirectAccess){var ITERATOR_SYMBOL=typeof Symbol==="function"&&Symbol.iterator;var FAUX_ITERATOR_SYMBOL="@@iterator";function getIteratorFn(maybeIterable){var iteratorFn=maybeIterable&&(ITERATOR_SYMBOL&&maybeIterable[ITERATOR_SYMBOL]||maybeIterable[FAUX_ITERATOR_SYMBOL]);if(typeof iteratorFn==="function"){return iteratorFn}}var ANONYMOUS="<<anonymous>>";var ReactPropTypes={array:createPrimitiveTypeChecker("array"),bool:createPrimitiveTypeChecker("boolean"),func:createPrimitiveTypeChecker("function"),number:createPrimitiveTypeChecker("number"),object:createPrimitiveTypeChecker("object"),string:createPrimitiveTypeChecker("string"),symbol:createPrimitiveTypeChecker("symbol"),any:createAnyTypeChecker(),arrayOf:createArrayOfTypeChecker,element:createElementTypeChecker(),instanceOf:createInstanceTypeChecker,node:createNodeChecker(),objectOf:createObjectOfTypeChecker,oneOf:createEnumTypeChecker,oneOfType:createUnionTypeChecker,shape:createShapeTypeChecker};function is(x,y){if(x===y){return x!==0||1/x===1/y}else{return x!==x&&y!==y}}function PropTypeError(message){this.message=message;this.stack=""}PropTypeError.prototype=Error.prototype;function createChainableTypeChecker(validate){if(process.env.NODE_ENV!=="production"){var manualPropTypeCallCache={};var manualPropTypeWarningCount=0}function checkType(isRequired,props,propName,componentName,location,propFullName,secret){componentName=componentName||ANONYMOUS;propFullName=propFullName||propName;if(secret!==ReactPropTypesSecret){if(throwOnDirectAccess){invariant(false,"Calling PropTypes validators directly is not supported by the `prop-types` package. "+"Use `PropTypes.checkPropTypes()` to call them. "+"Read more at http://fb.me/use-check-prop-types")}else if(process.env.NODE_ENV!=="production"&&typeof console!=="undefined"){var cacheKey=componentName+":"+propName;if(!manualPropTypeCallCache[cacheKey]&&manualPropTypeWarningCount<3){warning(false,"You are manually calling a React.PropTypes validation "+"function for the `%s` prop on `%s`. This is deprecated "+"and will throw in the standalone `prop-types` package. "+"You may be seeing this warning due to a third-party PropTypes "+"library. See https://fb.me/react-warning-dont-call-proptypes "+"for details.",propFullName,componentName);manualPropTypeCallCache[cacheKey]=true;manualPropTypeWarningCount++}}}if(props[propName]==null){if(isRequired){if(props[propName]===null){return new PropTypeError("The "+location+" `"+propFullName+"` is marked as required "+("in `"+componentName+"`, but its value is `null`."))}return new PropTypeError("The "+location+" `"+propFullName+"` is marked as required in "+("`"+componentName+"`, but its value is `undefined`."))}return null}else{return validate(props,propName,componentName,location,propFullName)}}var chainedCheckType=checkType.bind(null,false);chainedCheckType.isRequired=checkType.bind(null,true);return chainedCheckType}function createPrimitiveTypeChecker(expectedType){function validate(props,propName,componentName,location,propFullName,secret){var propValue=props[propName];var propType=getPropType(propValue);if(propType!==expectedType){var preciseType=getPreciseType(propValue);return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type "+("`"+preciseType+"` supplied to `"+componentName+"`, expected ")+("`"+expectedType+"`."))}return null}return createChainableTypeChecker(validate)}function createAnyTypeChecker(){return createChainableTypeChecker(emptyFunction.thatReturnsNull)}function createArrayOfTypeChecker(typeChecker){function validate(props,propName,componentName,location,propFullName){if(typeof typeChecker!=="function"){return new PropTypeError("Property `"+propFullName+"` of component `"+componentName+"` has invalid PropType notation inside arrayOf.")}var propValue=props[propName];if(!Array.isArray(propValue)){var propType=getPropType(propValue);return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type "+("`"+propType+"` supplied to `"+componentName+"`, expected an array."))}for(var i=0;i<propValue.length;i++){var error=typeChecker(propValue,i,componentName,location,propFullName+"["+i+"]",ReactPropTypesSecret);if(error instanceof Error){return error}}return null}return createChainableTypeChecker(validate)}function createElementTypeChecker(){function validate(props,propName,componentName,location,propFullName){var propValue=props[propName];if(!isValidElement(propValue)){var propType=getPropType(propValue);return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type "+("`"+propType+"` supplied to `"+componentName+"`, expected a single ReactElement."))}return null}return createChainableTypeChecker(validate)}function createInstanceTypeChecker(expectedClass){function validate(props,propName,componentName,location,propFullName){if(!(props[propName]instanceof expectedClass)){var expectedClassName=expectedClass.name||ANONYMOUS;var actualClassName=getClassName(props[propName]);return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type "+("`"+actualClassName+"` supplied to `"+componentName+"`, expected ")+("instance of `"+expectedClassName+"`."))}return null}return createChainableTypeChecker(validate)}function createEnumTypeChecker(expectedValues){if(!Array.isArray(expectedValues)){process.env.NODE_ENV!=="production"?warning(false,"Invalid argument supplied to oneOf, expected an instance of array."):void 0;return emptyFunction.thatReturnsNull}function validate(props,propName,componentName,location,propFullName){var propValue=props[propName];for(var i=0;i<expectedValues.length;i++){if(is(propValue,expectedValues[i])){return null}}var valuesString=JSON.stringify(expectedValues);return new PropTypeError("Invalid "+location+" `"+propFullName+"` of value `"+propValue+"` "+("supplied to `"+componentName+"`, expected one of "+valuesString+"."))}return createChainableTypeChecker(validate)}function createObjectOfTypeChecker(typeChecker){function validate(props,propName,componentName,location,propFullName){if(typeof typeChecker!=="function"){return new PropTypeError("Property `"+propFullName+"` of component `"+componentName+"` has invalid PropType notation inside objectOf.")}var propValue=props[propName];var propType=getPropType(propValue);if(propType!=="object"){return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type "+("`"+propType+"` supplied to `"+componentName+"`, expected an object."))}for(var key in propValue){if(propValue.hasOwnProperty(key)){var error=typeChecker(propValue,key,componentName,location,propFullName+"."+key,ReactPropTypesSecret);if(error instanceof Error){return error}}}return null}return createChainableTypeChecker(validate)}function createUnionTypeChecker(arrayOfTypeCheckers){if(!Array.isArray(arrayOfTypeCheckers)){process.env.NODE_ENV!=="production"?warning(false,"Invalid argument supplied to oneOfType, expected an instance of array."):void 0;return emptyFunction.thatReturnsNull}for(var i=0;i<arrayOfTypeCheckers.length;i++){var checker=arrayOfTypeCheckers[i];if(typeof checker!=="function"){warning(false,"Invalid argument supplid to oneOfType. Expected an array of check functions, but "+"received %s at index %s.",getPostfixForTypeWarning(checker),i);return emptyFunction.thatReturnsNull}}function validate(props,propName,componentName,location,propFullName){for(var i=0;i<arrayOfTypeCheckers.length;i++){var checker=arrayOfTypeCheckers[i];if(checker(props,propName,componentName,location,propFullName,ReactPropTypesSecret)==null){return null}}return new PropTypeError("Invalid "+location+" `"+propFullName+"` supplied to "+("`"+componentName+"`."))}return createChainableTypeChecker(validate)}function createNodeChecker(){function validate(props,propName,componentName,location,propFullName){if(!isNode(props[propName])){return new PropTypeError("Invalid "+location+" `"+propFullName+"` supplied to "+("`"+componentName+"`, expected a ReactNode."))}return null}return createChainableTypeChecker(validate)}function createShapeTypeChecker(shapeTypes){function validate(props,propName,componentName,location,propFullName){var propValue=props[propName];var propType=getPropType(propValue);if(propType!=="object"){return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type `"+propType+"` "+("supplied to `"+componentName+"`, expected `object`."))}for(var key in shapeTypes){var checker=shapeTypes[key];if(!checker){continue}var error=checker(propValue,key,componentName,location,propFullName+"."+key,ReactPropTypesSecret);if(error){return error}}return null}return createChainableTypeChecker(validate)}function isNode(propValue){switch(typeof propValue){case"number":case"string":case"undefined":return true;case"boolean":return!propValue;case"object":if(Array.isArray(propValue)){return propValue.every(isNode)}if(propValue===null||isValidElement(propValue)){return true}var iteratorFn=getIteratorFn(propValue);if(iteratorFn){var iterator=iteratorFn.call(propValue);var step;if(iteratorFn!==propValue.entries){while(!(step=iterator.next()).done){if(!isNode(step.value)){return false}}}else{while(!(step=iterator.next()).done){var entry=step.value;if(entry){if(!isNode(entry[1])){return false}}}}}else{return false}return true;default:return false}}function isSymbol(propType,propValue){if(propType==="symbol"){return true}if(propValue["@@toStringTag"]==="Symbol"){return true}if(typeof Symbol==="function"&&propValue instanceof Symbol){return true}return false}function getPropType(propValue){var propType=typeof propValue;if(Array.isArray(propValue)){return"array"}if(propValue instanceof RegExp){return"object"}if(isSymbol(propType,propValue)){return"symbol"}return propType}function getPreciseType(propValue){if(typeof propValue==="undefined"||propValue===null){return""+propValue}var propType=getPropType(propValue);if(propType==="object"){if(propValue instanceof Date){return"date"}else if(propValue instanceof RegExp){return"regexp"}}return propType}function getPostfixForTypeWarning(value){var type=getPreciseType(value);switch(type){case"array":case"object":return"an "+type;case"boolean":case"date":case"regexp":return"a "+type;default:return type}}function getClassName(propValue){if(!propValue.constructor||!propValue.constructor.name){return ANONYMOUS}return propValue.constructor.name}ReactPropTypes.checkPropTypes=checkPropTypes;ReactPropTypes.PropTypes=ReactPropTypes;return ReactPropTypes}}).call(this,require("_process"))},{"./checkPropTypes":27,"./lib/ReactPropTypesSecret":30,_process:184,"fbjs/lib/emptyFunction":10,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],30:[function(require,module,exports){"use strict";var ReactPropTypesSecret="SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED";module.exports=ReactPropTypesSecret},{}],31:[function(require,module,exports){"use strict";module.exports=require("./lib/ReactDOM")},{"./lib/ReactDOM":61}],32:[function(require,module,exports){"use strict";var ARIADOMPropertyConfig={Properties:{"aria-current":0,"aria-details":0,"aria-disabled":0,"aria-hidden":0,"aria-invalid":0,"aria-keyshortcuts":0,"aria-label":0,"aria-roledescription":0,"aria-autocomplete":0,"aria-checked":0,"aria-expanded":0,"aria-haspopup":0,"aria-level":0,"aria-modal":0,"aria-multiline":0,"aria-multiselectable":0,"aria-orientation":0,"aria-placeholder":0,"aria-pressed":0,"aria-readonly":0,"aria-required":0,"aria-selected":0,"aria-sort":0,"aria-valuemax":0,"aria-valuemin":0,"aria-valuenow":0,"aria-valuetext":0,"aria-atomic":0,"aria-busy":0,"aria-live":0,"aria-relevant":0,"aria-dropeffect":0,"aria-grabbed":0,"aria-activedescendant":0,"aria-colcount":0,"aria-colindex":0,"aria-colspan":0,"aria-controls":0,"aria-describedby":0,"aria-errormessage":0,"aria-flowto":0,"aria-labelledby":0,"aria-owns":0,"aria-posinset":0,"aria-rowcount":0,"aria-rowindex":0,"aria-rowspan":0,"aria-setsize":0},DOMAttributeNames:{},DOMPropertyNames:{}};module.exports=ARIADOMPropertyConfig},{}],33:[function(require,module,exports){"use strict";var ReactDOMComponentTree=require("./ReactDOMComponentTree");var focusNode=require("fbjs/lib/focusNode");var AutoFocusUtils={focusDOMComponent:function(){focusNode(ReactDOMComponentTree.getNodeFromInstance(this))}};module.exports=AutoFocusUtils},{"./ReactDOMComponentTree":64,"fbjs/lib/focusNode":12}],34:[function(require,module,exports){"use strict";var EventPropagators=require("./EventPropagators");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var FallbackCompositionState=require("./FallbackCompositionState");var SyntheticCompositionEvent=require("./SyntheticCompositionEvent");var SyntheticInputEvent=require("./SyntheticInputEvent");var END_KEYCODES=[9,13,27,32];var START_KEYCODE=229;var canUseCompositionEvent=ExecutionEnvironment.canUseDOM&&"CompositionEvent"in window;var documentMode=null;if(ExecutionEnvironment.canUseDOM&&"documentMode"in document){documentMode=document.documentMode}var canUseTextInputEvent=ExecutionEnvironment.canUseDOM&&"TextEvent"in window&&!documentMode&&!isPresto();var useFallbackCompositionData=ExecutionEnvironment.canUseDOM&&(!canUseCompositionEvent||documentMode&&documentMode>8&&documentMode<=11);function isPresto(){var opera=window.opera;return typeof opera==="object"&&typeof opera.version==="function"&&parseInt(opera.version(),10)<=12}var SPACEBAR_CODE=32;var SPACEBAR_CHAR=String.fromCharCode(SPACEBAR_CODE);var eventTypes={beforeInput:{phasedRegistrationNames:{bubbled:"onBeforeInput",captured:"onBeforeInputCapture"},dependencies:["topCompositionEnd","topKeyPress","topTextInput","topPaste"]},compositionEnd:{phasedRegistrationNames:{bubbled:"onCompositionEnd",captured:"onCompositionEndCapture"},dependencies:["topBlur","topCompositionEnd","topKeyDown","topKeyPress","topKeyUp","topMouseDown"]},compositionStart:{phasedRegistrationNames:{bubbled:"onCompositionStart",captured:"onCompositionStartCapture"},dependencies:["topBlur","topCompositionStart","topKeyDown","topKeyPress","topKeyUp","topMouseDown"]},compositionUpdate:{phasedRegistrationNames:{bubbled:"onCompositionUpdate",captured:"onCompositionUpdateCapture"},dependencies:["topBlur","topCompositionUpdate","topKeyDown","topKeyPress","topKeyUp","topMouseDown"]}};var hasSpaceKeypress=false;function isKeypressCommand(nativeEvent){return(nativeEvent.ctrlKey||nativeEvent.altKey||nativeEvent.metaKey)&&!(nativeEvent.ctrlKey&&nativeEvent.altKey)}function getCompositionEventType(topLevelType){switch(topLevelType){case"topCompositionStart":return eventTypes.compositionStart;case"topCompositionEnd":return eventTypes.compositionEnd;case"topCompositionUpdate":return eventTypes.compositionUpdate}}function isFallbackCompositionStart(topLevelType,nativeEvent){return topLevelType==="topKeyDown"&&nativeEvent.keyCode===START_KEYCODE}function isFallbackCompositionEnd(topLevelType,nativeEvent){switch(topLevelType){case"topKeyUp":return END_KEYCODES.indexOf(nativeEvent.keyCode)!==-1;case"topKeyDown":return nativeEvent.keyCode!==START_KEYCODE;case"topKeyPress":case"topMouseDown":case"topBlur":return true;default:return false}}function getDataFromCustomEvent(nativeEvent){var detail=nativeEvent.detail;if(typeof detail==="object"&&"data"in detail){return detail.data}return null}var currentComposition=null;function extractCompositionEvent(topLevelType,targetInst,nativeEvent,nativeEventTarget){var eventType;var fallbackData;if(canUseCompositionEvent){eventType=getCompositionEventType(topLevelType)}else if(!currentComposition){if(isFallbackCompositionStart(topLevelType,nativeEvent)){eventType=eventTypes.compositionStart}}else if(isFallbackCompositionEnd(topLevelType,nativeEvent)){eventType=eventTypes.compositionEnd}if(!eventType){return null}if(useFallbackCompositionData){if(!currentComposition&&eventType===eventTypes.compositionStart){currentComposition=FallbackCompositionState.getPooled(nativeEventTarget)}else if(eventType===eventTypes.compositionEnd){if(currentComposition){fallbackData=currentComposition.getData()}}}var event=SyntheticCompositionEvent.getPooled(eventType,targetInst,nativeEvent,nativeEventTarget);if(fallbackData){event.data=fallbackData}else{var customData=getDataFromCustomEvent(nativeEvent);if(customData!==null){event.data=customData}}EventPropagators.accumulateTwoPhaseDispatches(event);return event}function getNativeBeforeInputChars(topLevelType,nativeEvent){switch(topLevelType){case"topCompositionEnd":return getDataFromCustomEvent(nativeEvent);case"topKeyPress":var which=nativeEvent.which;if(which!==SPACEBAR_CODE){return null}hasSpaceKeypress=true;return SPACEBAR_CHAR;case"topTextInput":var chars=nativeEvent.data;if(chars===SPACEBAR_CHAR&&hasSpaceKeypress){return null}return chars;default:return null}}function getFallbackBeforeInputChars(topLevelType,nativeEvent){if(currentComposition){if(topLevelType==="topCompositionEnd"||!canUseCompositionEvent&&isFallbackCompositionEnd(topLevelType,nativeEvent)){var chars=currentComposition.getData();FallbackCompositionState.release(currentComposition);currentComposition=null;return chars}return null}switch(topLevelType){case"topPaste":return null;case"topKeyPress":if(nativeEvent.which&&!isKeypressCommand(nativeEvent)){return String.fromCharCode(nativeEvent.which)}return null;case"topCompositionEnd":return useFallbackCompositionData?null:nativeEvent.data;default:return null}}function extractBeforeInputEvent(topLevelType,targetInst,nativeEvent,nativeEventTarget){var chars;if(canUseTextInputEvent){chars=getNativeBeforeInputChars(topLevelType,nativeEvent)}else{chars=getFallbackBeforeInputChars(topLevelType,nativeEvent)}if(!chars){return null}var event=SyntheticInputEvent.getPooled(eventTypes.beforeInput,targetInst,nativeEvent,nativeEventTarget);event.data=chars;EventPropagators.accumulateTwoPhaseDispatches(event);return event}var BeforeInputEventPlugin={eventTypes:eventTypes,extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){return[extractCompositionEvent(topLevelType,targetInst,nativeEvent,nativeEventTarget),extractBeforeInputEvent(topLevelType,targetInst,nativeEvent,nativeEventTarget)]}};module.exports=BeforeInputEventPlugin},{"./EventPropagators":50,"./FallbackCompositionState":51,"./SyntheticCompositionEvent":115,"./SyntheticInputEvent":119,"fbjs/lib/ExecutionEnvironment":4}],35:[function(require,module,exports){"use strict";var isUnitlessNumber={animationIterationCount:true,borderImageOutset:true,borderImageSlice:true,borderImageWidth:true,boxFlex:true,boxFlexGroup:true,boxOrdinalGroup:true,columnCount:true,flex:true,flexGrow:true,flexPositive:true,flexShrink:true,flexNegative:true,flexOrder:true,gridRow:true,gridRowEnd:true,gridRowSpan:true,gridRowStart:true,gridColumn:true,gridColumnEnd:true,gridColumnSpan:true,gridColumnStart:true,fontWeight:true,lineClamp:true,lineHeight:true,opacity:true,order:true,orphans:true,tabSize:true,widows:true,zIndex:true,zoom:true,fillOpacity:true,floodOpacity:true,stopOpacity:true,strokeDasharray:true,strokeDashoffset:true,strokeMiterlimit:true,strokeOpacity:true,strokeWidth:true};function prefixKey(prefix,key){return prefix+key.charAt(0).toUpperCase()+key.substring(1)}var prefixes=["Webkit","ms","Moz","O"];Object.keys(isUnitlessNumber).forEach(function(prop){prefixes.forEach(function(prefix){isUnitlessNumber[prefixKey(prefix,prop)]=isUnitlessNumber[prop]})});var shorthandPropertyExpansions={background:{backgroundAttachment:true,backgroundColor:true,backgroundImage:true,backgroundPositionX:true,backgroundPositionY:true,backgroundRepeat:true},backgroundPosition:{backgroundPositionX:true,backgroundPositionY:true},border:{borderWidth:true,borderStyle:true,borderColor:true},borderBottom:{borderBottomWidth:true,borderBottomStyle:true,borderBottomColor:true},borderLeft:{borderLeftWidth:true,borderLeftStyle:true,borderLeftColor:true},borderRight:{borderRightWidth:true,borderRightStyle:true,borderRightColor:true},borderTop:{borderTopWidth:true,borderTopStyle:true,borderTopColor:true},font:{fontStyle:true,fontVariant:true,fontWeight:true,fontSize:true,lineHeight:true,fontFamily:true},outline:{outlineWidth:true,outlineStyle:true,outlineColor:true}};var CSSProperty={isUnitlessNumber:isUnitlessNumber,shorthandPropertyExpansions:shorthandPropertyExpansions};module.exports=CSSProperty},{}],36:[function(require,module,exports){(function(process){"use strict";var CSSProperty=require("./CSSProperty");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var ReactInstrumentation=require("./ReactInstrumentation");var camelizeStyleName=require("fbjs/lib/camelizeStyleName");var dangerousStyleValue=require("./dangerousStyleValue");var hyphenateStyleName=require("fbjs/lib/hyphenateStyleName");var memoizeStringOnly=require("fbjs/lib/memoizeStringOnly");var warning=require("fbjs/lib/warning");var processStyleName=memoizeStringOnly(function(styleName){return hyphenateStyleName(styleName)});var hasShorthandPropertyBug=false;var styleFloatAccessor="cssFloat";if(ExecutionEnvironment.canUseDOM){var tempStyle=document.createElement("div").style;try{tempStyle.font=""}catch(e){hasShorthandPropertyBug=true}if(document.documentElement.style.cssFloat===undefined){styleFloatAccessor="styleFloat"}}if(process.env.NODE_ENV!=="production"){var badVendoredStyleNamePattern=/^(?:webkit|moz|o)[A-Z]/;var badStyleValueWithSemicolonPattern=/;\s*$/;var warnedStyleNames={};var warnedStyleValues={};var warnedForNaNValue=false;var warnHyphenatedStyleName=function(name,owner){if(warnedStyleNames.hasOwnProperty(name)&&warnedStyleNames[name]){return}warnedStyleNames[name]=true;process.env.NODE_ENV!=="production"?warning(false,"Unsupported style property %s. Did you mean %s?%s",name,camelizeStyleName(name),checkRenderMessage(owner)):void 0};var warnBadVendoredStyleName=function(name,owner){if(warnedStyleNames.hasOwnProperty(name)&&warnedStyleNames[name]){return}warnedStyleNames[name]=true;process.env.NODE_ENV!=="production"?warning(false,"Unsupported vendor-prefixed style property %s. Did you mean %s?%s",name,name.charAt(0).toUpperCase()+name.slice(1),checkRenderMessage(owner)):void 0};var warnStyleValueWithSemicolon=function(name,value,owner){if(warnedStyleValues.hasOwnProperty(value)&&warnedStyleValues[value]){return}warnedStyleValues[value]=true;process.env.NODE_ENV!=="production"?warning(false,"Style property values shouldn't contain a semicolon.%s "+'Try "%s: %s" instead.',checkRenderMessage(owner),name,value.replace(badStyleValueWithSemicolonPattern,"")):void 0};var warnStyleValueIsNaN=function(name,value,owner){if(warnedForNaNValue){return}warnedForNaNValue=true;process.env.NODE_ENV!=="production"?warning(false,"`NaN` is an invalid value for the `%s` css style property.%s",name,checkRenderMessage(owner)):void 0};var checkRenderMessage=function(owner){if(owner){var name=owner.getName();if(name){return" Check the render method of `"+name+"`."}}return""};var warnValidStyle=function(name,value,component){var owner;if(component){owner=component._currentElement._owner}if(name.indexOf("-")>-1){warnHyphenatedStyleName(name,owner)}else if(badVendoredStyleNamePattern.test(name)){warnBadVendoredStyleName(name,owner)}else if(badStyleValueWithSemicolonPattern.test(value)){warnStyleValueWithSemicolon(name,value,owner)}if(typeof value==="number"&&isNaN(value)){warnStyleValueIsNaN(name,value,owner)}}}var CSSPropertyOperations={createMarkupForStyles:function(styles,component){var serialized="";for(var styleName in styles){if(!styles.hasOwnProperty(styleName)){continue}var isCustomProperty=styleName.indexOf("--")===0;var styleValue=styles[styleName];if(process.env.NODE_ENV!=="production"){if(!isCustomProperty){warnValidStyle(styleName,styleValue,component)}}if(styleValue!=null){serialized+=processStyleName(styleName)+":";serialized+=dangerousStyleValue(styleName,styleValue,component,isCustomProperty)+";"}}return serialized||null},setValueForStyles:function(node,styles,component){if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:component._debugID,type:"update styles",payload:styles})}var style=node.style;for(var styleName in styles){if(!styles.hasOwnProperty(styleName)){continue}var isCustomProperty=styleName.indexOf("--")===0;if(process.env.NODE_ENV!=="production"){if(!isCustomProperty){warnValidStyle(styleName,styles[styleName],component)}}var styleValue=dangerousStyleValue(styleName,styles[styleName],component,isCustomProperty);if(styleName==="float"||styleName==="cssFloat"){styleName=styleFloatAccessor}if(isCustomProperty){style.setProperty(styleName,styleValue)}else if(styleValue){style[styleName]=styleValue}else{var expansion=hasShorthandPropertyBug&&CSSProperty.shorthandPropertyExpansions[styleName];if(expansion){for(var individualStyleName in expansion){style[individualStyleName]=""}}else{style[styleName]=""}}}}};module.exports=CSSPropertyOperations}).call(this,require("_process"))},{"./CSSProperty":35,"./ReactInstrumentation":93,"./dangerousStyleValue":132,_process:184,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/camelizeStyleName":6,"fbjs/lib/hyphenateStyleName":17,"fbjs/lib/memoizeStringOnly":21,"fbjs/lib/warning":25}],37:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");function _classCallCheck(instance,Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function")}}var PooledClass=require("./PooledClass");var invariant=require("fbjs/lib/invariant");var CallbackQueue=function(){function CallbackQueue(arg){_classCallCheck(this,CallbackQueue);this._callbacks=null;this._contexts=null;this._arg=arg}CallbackQueue.prototype.enqueue=function enqueue(callback,context){this._callbacks=this._callbacks||[];this._callbacks.push(callback);this._contexts=this._contexts||[];this._contexts.push(context)};CallbackQueue.prototype.notifyAll=function notifyAll(){var callbacks=this._callbacks;var contexts=this._contexts;var arg=this._arg;if(callbacks&&contexts){!(callbacks.length===contexts.length)?process.env.NODE_ENV!=="production"?invariant(false,"Mismatched list of contexts in callback queue"):_prodInvariant("24"):void 0;this._callbacks=null;this._contexts=null;for(var i=0;i<callbacks.length;i++){callbacks[i].call(contexts[i],arg)}callbacks.length=0;contexts.length=0}};CallbackQueue.prototype.checkpoint=function checkpoint(){return this._callbacks?this._callbacks.length:0};CallbackQueue.prototype.rollback=function rollback(len){if(this._callbacks&&this._contexts){this._callbacks.length=len;this._contexts.length=len}};CallbackQueue.prototype.reset=function reset(){this._callbacks=null;this._contexts=null};CallbackQueue.prototype.destructor=function destructor(){this.reset()};return CallbackQueue}();module.exports=PooledClass.addPoolingTo(CallbackQueue)}).call(this,require("_process"))},{"./PooledClass":55,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],38:[function(require,module,exports){"use strict";var EventPluginHub=require("./EventPluginHub");var EventPropagators=require("./EventPropagators");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactUpdates=require("./ReactUpdates");var SyntheticEvent=require("./SyntheticEvent");var inputValueTracking=require("./inputValueTracking");var getEventTarget=require("./getEventTarget");var isEventSupported=require("./isEventSupported");var isTextInputElement=require("./isTextInputElement");var eventTypes={change:{phasedRegistrationNames:{bubbled:"onChange",captured:"onChangeCapture"},dependencies:["topBlur","topChange","topClick","topFocus","topInput","topKeyDown","topKeyUp","topSelectionChange"]}};function createAndAccumulateChangeEvent(inst,nativeEvent,target){var event=SyntheticEvent.getPooled(eventTypes.change,inst,nativeEvent,target);event.type="change";EventPropagators.accumulateTwoPhaseDispatches(event);return event}var activeElement=null;var activeElementInst=null;function shouldUseChangeEvent(elem){var nodeName=elem.nodeName&&elem.nodeName.toLowerCase();return nodeName==="select"||nodeName==="input"&&elem.type==="file"}var doesChangeEventBubble=false;if(ExecutionEnvironment.canUseDOM){doesChangeEventBubble=isEventSupported("change")&&(!document.documentMode||document.documentMode>8)}function manualDispatchChangeEvent(nativeEvent){var event=createAndAccumulateChangeEvent(activeElementInst,nativeEvent,getEventTarget(nativeEvent));ReactUpdates.batchedUpdates(runEventInBatch,event)}function runEventInBatch(event){EventPluginHub.enqueueEvents(event);EventPluginHub.processEventQueue(false)}function startWatchingForChangeEventIE8(target,targetInst){activeElement=target;activeElementInst=targetInst;activeElement.attachEvent("onchange",manualDispatchChangeEvent)}function stopWatchingForChangeEventIE8(){if(!activeElement){return}activeElement.detachEvent("onchange",manualDispatchChangeEvent);activeElement=null;activeElementInst=null}function getInstIfValueChanged(targetInst,nativeEvent){var updated=inputValueTracking.updateValueIfChanged(targetInst);var simulated=nativeEvent.simulated===true&&ChangeEventPlugin._allowSimulatedPassThrough;if(updated||simulated){return targetInst}}function getTargetInstForChangeEvent(topLevelType,targetInst){if(topLevelType==="topChange"){return targetInst}}function handleEventsForChangeEventIE8(topLevelType,target,targetInst){if(topLevelType==="topFocus"){stopWatchingForChangeEventIE8();startWatchingForChangeEventIE8(target,targetInst)}else if(topLevelType==="topBlur"){stopWatchingForChangeEventIE8()}}var isInputEventSupported=false;if(ExecutionEnvironment.canUseDOM){isInputEventSupported=isEventSupported("input")&&(!("documentMode"in document)||document.documentMode>9)}function startWatchingForValueChange(target,targetInst){activeElement=target;activeElementInst=targetInst;activeElement.attachEvent("onpropertychange",handlePropertyChange)}function stopWatchingForValueChange(){if(!activeElement){return}activeElement.detachEvent("onpropertychange",handlePropertyChange);activeElement=null;activeElementInst=null}function handlePropertyChange(nativeEvent){if(nativeEvent.propertyName!=="value"){return}if(getInstIfValueChanged(activeElementInst,nativeEvent)){manualDispatchChangeEvent(nativeEvent)}}function handleEventsForInputEventPolyfill(topLevelType,target,targetInst){if(topLevelType==="topFocus"){stopWatchingForValueChange();startWatchingForValueChange(target,targetInst)}else if(topLevelType==="topBlur"){stopWatchingForValueChange()}}function getTargetInstForInputEventPolyfill(topLevelType,targetInst,nativeEvent){if(topLevelType==="topSelectionChange"||topLevelType==="topKeyUp"||topLevelType==="topKeyDown"){return getInstIfValueChanged(activeElementInst,nativeEvent)}}function shouldUseClickEvent(elem){var nodeName=elem.nodeName;return nodeName&&nodeName.toLowerCase()==="input"&&(elem.type==="checkbox"||elem.type==="radio")}function getTargetInstForClickEvent(topLevelType,targetInst,nativeEvent){if(topLevelType==="topClick"){return getInstIfValueChanged(targetInst,nativeEvent)}}function getTargetInstForInputOrChangeEvent(topLevelType,targetInst,nativeEvent){if(topLevelType==="topInput"||topLevelType==="topChange"){return getInstIfValueChanged(targetInst,nativeEvent)}}function handleControlledInputBlur(inst,node){if(inst==null){return}var state=inst._wrapperState||node._wrapperState;if(!state||!state.controlled||node.type!=="number"){return}var value=""+node.value;if(node.getAttribute("value")!==value){node.setAttribute("value",value)}}var ChangeEventPlugin={eventTypes:eventTypes,_allowSimulatedPassThrough:true,_isInputEventSupported:isInputEventSupported,extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){var targetNode=targetInst?ReactDOMComponentTree.getNodeFromInstance(targetInst):window;var getTargetInstFunc,handleEventFunc;if(shouldUseChangeEvent(targetNode)){if(doesChangeEventBubble){getTargetInstFunc=getTargetInstForChangeEvent}else{handleEventFunc=handleEventsForChangeEventIE8}}else if(isTextInputElement(targetNode)){if(isInputEventSupported){getTargetInstFunc=getTargetInstForInputOrChangeEvent}else{getTargetInstFunc=getTargetInstForInputEventPolyfill;handleEventFunc=handleEventsForInputEventPolyfill}}else if(shouldUseClickEvent(targetNode)){getTargetInstFunc=getTargetInstForClickEvent}if(getTargetInstFunc){var inst=getTargetInstFunc(topLevelType,targetInst,nativeEvent);if(inst){var event=createAndAccumulateChangeEvent(inst,nativeEvent,nativeEventTarget);return event}}if(handleEventFunc){handleEventFunc(topLevelType,targetNode,targetInst)}if(topLevelType==="topBlur"){handleControlledInputBlur(targetInst,targetNode)}}};module.exports=ChangeEventPlugin},{"./EventPluginHub":47,"./EventPropagators":50,"./ReactDOMComponentTree":64,"./ReactUpdates":108,"./SyntheticEvent":117,"./getEventTarget":140,"./inputValueTracking":146,"./isEventSupported":148,"./isTextInputElement":149,"fbjs/lib/ExecutionEnvironment":4}],39:[function(require,module,exports){(function(process){"use strict";var DOMLazyTree=require("./DOMLazyTree");var Danger=require("./Danger");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactInstrumentation=require("./ReactInstrumentation");var createMicrosoftUnsafeLocalFunction=require("./createMicrosoftUnsafeLocalFunction");var setInnerHTML=require("./setInnerHTML");var setTextContent=require("./setTextContent");function getNodeAfter(parentNode,node){if(Array.isArray(node)){node=node[1]}return node?node.nextSibling:parentNode.firstChild}var insertChildAt=createMicrosoftUnsafeLocalFunction(function(parentNode,childNode,referenceNode){parentNode.insertBefore(childNode,referenceNode)});function insertLazyTreeChildAt(parentNode,childTree,referenceNode){DOMLazyTree.insertTreeBefore(parentNode,childTree,referenceNode)}function moveChild(parentNode,childNode,referenceNode){if(Array.isArray(childNode)){moveDelimitedText(parentNode,childNode[0],childNode[1],referenceNode)}else{insertChildAt(parentNode,childNode,referenceNode)}}function removeChild(parentNode,childNode){if(Array.isArray(childNode)){var closingComment=childNode[1];childNode=childNode[0];removeDelimitedText(parentNode,childNode,closingComment);parentNode.removeChild(closingComment)}parentNode.removeChild(childNode)}function moveDelimitedText(parentNode,openingComment,closingComment,referenceNode){var node=openingComment;while(true){var nextNode=node.nextSibling;insertChildAt(parentNode,node,referenceNode);if(node===closingComment){break}node=nextNode}}function removeDelimitedText(parentNode,startNode,closingComment){while(true){var node=startNode.nextSibling;if(node===closingComment){break}else{parentNode.removeChild(node)}}}function replaceDelimitedText(openingComment,closingComment,stringText){var parentNode=openingComment.parentNode;var nodeAfterComment=openingComment.nextSibling;if(nodeAfterComment===closingComment){if(stringText){insertChildAt(parentNode,document.createTextNode(stringText),nodeAfterComment)}}else{if(stringText){setTextContent(nodeAfterComment,stringText);removeDelimitedText(parentNode,nodeAfterComment,closingComment)}else{removeDelimitedText(parentNode,openingComment,closingComment)}}if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:ReactDOMComponentTree.getInstanceFromNode(openingComment)._debugID,type:"replace text",payload:stringText})}}var dangerouslyReplaceNodeWithMarkup=Danger.dangerouslyReplaceNodeWithMarkup;if(process.env.NODE_ENV!=="production"){dangerouslyReplaceNodeWithMarkup=function(oldChild,markup,prevInstance){Danger.dangerouslyReplaceNodeWithMarkup(oldChild,markup);if(prevInstance._debugID!==0){ReactInstrumentation.debugTool.onHostOperation({instanceID:prevInstance._debugID,type:"replace with",payload:markup.toString()})}else{var nextInstance=ReactDOMComponentTree.getInstanceFromNode(markup.node);if(nextInstance._debugID!==0){ReactInstrumentation.debugTool.onHostOperation({instanceID:nextInstance._debugID,type:"mount",payload:markup.toString()})}}}}var DOMChildrenOperations={dangerouslyReplaceNodeWithMarkup:dangerouslyReplaceNodeWithMarkup,replaceDelimitedText:replaceDelimitedText,processUpdates:function(parentNode,updates){if(process.env.NODE_ENV!=="production"){var parentNodeDebugID=ReactDOMComponentTree.getInstanceFromNode(parentNode)._debugID}for(var k=0;k<updates.length;k++){var update=updates[k];switch(update.type){case"INSERT_MARKUP":insertLazyTreeChildAt(parentNode,update.content,getNodeAfter(parentNode,update.afterNode));if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:parentNodeDebugID,type:"insert child",payload:{toIndex:update.toIndex,content:update.content.toString()}})}break;case"MOVE_EXISTING":moveChild(parentNode,update.fromNode,getNodeAfter(parentNode,update.afterNode));if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:parentNodeDebugID,type:"move child",payload:{fromIndex:update.fromIndex,toIndex:update.toIndex}})}break;case"SET_MARKUP":setInnerHTML(parentNode,update.content);if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:parentNodeDebugID,type:"replace children",payload:update.content.toString()})}break;case"TEXT_CONTENT":setTextContent(parentNode,update.content);if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:parentNodeDebugID,type:"replace text",payload:update.content.toString()})}break;case"REMOVE_NODE":removeChild(parentNode,update.fromNode);if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:parentNodeDebugID,type:"remove child",payload:{fromIndex:update.fromIndex}})}break}}}};module.exports=DOMChildrenOperations}).call(this,require("_process"))},{"./DOMLazyTree":40,"./Danger":44,"./ReactDOMComponentTree":64,"./ReactInstrumentation":93,"./createMicrosoftUnsafeLocalFunction":131,"./setInnerHTML":153,"./setTextContent":154,_process:184}],40:[function(require,module,exports){"use strict";var DOMNamespaces=require("./DOMNamespaces");var setInnerHTML=require("./setInnerHTML");var createMicrosoftUnsafeLocalFunction=require("./createMicrosoftUnsafeLocalFunction");var setTextContent=require("./setTextContent");var ELEMENT_NODE_TYPE=1;var DOCUMENT_FRAGMENT_NODE_TYPE=11;var enableLazy=typeof document!=="undefined"&&typeof document.documentMode==="number"||typeof navigator!=="undefined"&&typeof navigator.userAgent==="string"&&/\bEdge\/\d/.test(navigator.userAgent);function insertTreeChildren(tree){if(!enableLazy){return}var node=tree.node;var children=tree.children;if(children.length){for(var i=0;i<children.length;i++){insertTreeBefore(node,children[i],null)}}else if(tree.html!=null){setInnerHTML(node,tree.html)}else if(tree.text!=null){setTextContent(node,tree.text)}}var insertTreeBefore=createMicrosoftUnsafeLocalFunction(function(parentNode,tree,referenceNode){if(tree.node.nodeType===DOCUMENT_FRAGMENT_NODE_TYPE||tree.node.nodeType===ELEMENT_NODE_TYPE&&tree.node.nodeName.toLowerCase()==="object"&&(tree.node.namespaceURI==null||tree.node.namespaceURI===DOMNamespaces.html)){insertTreeChildren(tree);parentNode.insertBefore(tree.node,referenceNode)}else{parentNode.insertBefore(tree.node,referenceNode);insertTreeChildren(tree)}});function replaceChildWithTree(oldNode,newTree){oldNode.parentNode.replaceChild(newTree.node,oldNode);insertTreeChildren(newTree)}function queueChild(parentTree,childTree){if(enableLazy){parentTree.children.push(childTree)}else{parentTree.node.appendChild(childTree.node)}}function queueHTML(tree,html){if(enableLazy){tree.html=html}else{setInnerHTML(tree.node,html)}}function queueText(tree,text){if(enableLazy){tree.text=text}else{setTextContent(tree.node,text)}}function toString(){return this.node.nodeName}function DOMLazyTree(node){return{node:node,children:[],html:null,text:null,toString:toString}}DOMLazyTree.insertTreeBefore=insertTreeBefore;DOMLazyTree.replaceChildWithTree=replaceChildWithTree;DOMLazyTree.queueChild=queueChild;DOMLazyTree.queueHTML=queueHTML;DOMLazyTree.queueText=queueText;module.exports=DOMLazyTree},{"./DOMNamespaces":41,"./createMicrosoftUnsafeLocalFunction":131,"./setInnerHTML":153,"./setTextContent":154}],41:[function(require,module,exports){"use strict";var DOMNamespaces={html:"http://www.w3.org/1999/xhtml",mathml:"http://www.w3.org/1998/Math/MathML",svg:"http://www.w3.org/2000/svg"};module.exports=DOMNamespaces},{}],42:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");function checkMask(value,bitmask){return(value&bitmask)===bitmask}var DOMPropertyInjection={MUST_USE_PROPERTY:1,HAS_BOOLEAN_VALUE:4,HAS_NUMERIC_VALUE:8,HAS_POSITIVE_NUMERIC_VALUE:16|8,HAS_OVERLOADED_BOOLEAN_VALUE:32,injectDOMPropertyConfig:function(domPropertyConfig){var Injection=DOMPropertyInjection;var Properties=domPropertyConfig.Properties||{};var DOMAttributeNamespaces=domPropertyConfig.DOMAttributeNamespaces||{};var DOMAttributeNames=domPropertyConfig.DOMAttributeNames||{};var DOMPropertyNames=domPropertyConfig.DOMPropertyNames||{};var DOMMutationMethods=domPropertyConfig.DOMMutationMethods||{};if(domPropertyConfig.isCustomAttribute){DOMProperty._isCustomAttributeFunctions.push(domPropertyConfig.isCustomAttribute)}for(var propName in Properties){!!DOMProperty.properties.hasOwnProperty(propName)?process.env.NODE_ENV!=="production"?invariant(false,"injectDOMPropertyConfig(...): You're trying to inject DOM property '%s' which has already been injected. You may be accidentally injecting the same DOM property config twice, or you may be injecting two configs that have conflicting property names.",propName):_prodInvariant("48",propName):void 0;var lowerCased=propName.toLowerCase();var propConfig=Properties[propName];var propertyInfo={attributeName:lowerCased,attributeNamespace:null,propertyName:propName,mutationMethod:null,mustUseProperty:checkMask(propConfig,Injection.MUST_USE_PROPERTY),hasBooleanValue:checkMask(propConfig,Injection.HAS_BOOLEAN_VALUE),hasNumericValue:checkMask(propConfig,Injection.HAS_NUMERIC_VALUE),hasPositiveNumericValue:checkMask(propConfig,Injection.HAS_POSITIVE_NUMERIC_VALUE),hasOverloadedBooleanValue:checkMask(propConfig,Injection.HAS_OVERLOADED_BOOLEAN_VALUE)};!(propertyInfo.hasBooleanValue+propertyInfo.hasNumericValue+propertyInfo.hasOverloadedBooleanValue<=1)?process.env.NODE_ENV!=="production"?invariant(false,"DOMProperty: Value can be one of boolean, overloaded boolean, or numeric value, but not a combination: %s",propName):_prodInvariant("50",propName):void 0;if(process.env.NODE_ENV!=="production"){DOMProperty.getPossibleStandardName[lowerCased]=propName}if(DOMAttributeNames.hasOwnProperty(propName)){var attributeName=DOMAttributeNames[propName];propertyInfo.attributeName=attributeName;if(process.env.NODE_ENV!=="production"){DOMProperty.getPossibleStandardName[attributeName]=propName}}if(DOMAttributeNamespaces.hasOwnProperty(propName)){propertyInfo.attributeNamespace=DOMAttributeNamespaces[propName]}if(DOMPropertyNames.hasOwnProperty(propName)){propertyInfo.propertyName=DOMPropertyNames[propName]}if(DOMMutationMethods.hasOwnProperty(propName)){propertyInfo.mutationMethod=DOMMutationMethods[propName]}DOMProperty.properties[propName]=propertyInfo}}};var ATTRIBUTE_NAME_START_CHAR=":A-Z_a-z\\u00C0-\\u00D6\\u00D8-\\u00F6\\u00F8-\\u02FF\\u0370-\\u037D\\u037F-\\u1FFF\\u200C-\\u200D\\u2070-\\u218F\\u2C00-\\u2FEF\\u3001-\\uD7FF\\uF900-\\uFDCF\\uFDF0-\\uFFFD";var DOMProperty={ID_ATTRIBUTE_NAME:"data-reactid",ROOT_ATTRIBUTE_NAME:"data-reactroot",ATTRIBUTE_NAME_START_CHAR:ATTRIBUTE_NAME_START_CHAR,ATTRIBUTE_NAME_CHAR:ATTRIBUTE_NAME_START_CHAR+"\\-.0-9\\u00B7\\u0300-\\u036F\\u203F-\\u2040",properties:{},getPossibleStandardName:process.env.NODE_ENV!=="production"?{autofocus:"autoFocus"}:null,_isCustomAttributeFunctions:[],isCustomAttribute:function(attributeName){for(var i=0;i<DOMProperty._isCustomAttributeFunctions.length;i++){var isCustomAttributeFn=DOMProperty._isCustomAttributeFunctions[i];if(isCustomAttributeFn(attributeName)){return true}}return false},injection:DOMPropertyInjection};module.exports=DOMProperty}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],43:[function(require,module,exports){(function(process){"use strict";var DOMProperty=require("./DOMProperty");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactInstrumentation=require("./ReactInstrumentation");var quoteAttributeValueForBrowser=require("./quoteAttributeValueForBrowser");var warning=require("fbjs/lib/warning");var VALID_ATTRIBUTE_NAME_REGEX=new RegExp("^["+DOMProperty.ATTRIBUTE_NAME_START_CHAR+"]["+DOMProperty.ATTRIBUTE_NAME_CHAR+"]*$");var illegalAttributeNameCache={};var validatedAttributeNameCache={};function isAttributeNameSafe(attributeName){if(validatedAttributeNameCache.hasOwnProperty(attributeName)){return true}if(illegalAttributeNameCache.hasOwnProperty(attributeName)){return false}if(VALID_ATTRIBUTE_NAME_REGEX.test(attributeName)){validatedAttributeNameCache[attributeName]=true;return true}illegalAttributeNameCache[attributeName]=true;process.env.NODE_ENV!=="production"?warning(false,"Invalid attribute name: `%s`",attributeName):void 0;return false}function shouldIgnoreValue(propertyInfo,value){return value==null||propertyInfo.hasBooleanValue&&!value||propertyInfo.hasNumericValue&&isNaN(value)||propertyInfo.hasPositiveNumericValue&&value<1||propertyInfo.hasOverloadedBooleanValue&&value===false}var DOMPropertyOperations={createMarkupForID:function(id){return DOMProperty.ID_ATTRIBUTE_NAME+"="+quoteAttributeValueForBrowser(id)},setAttributeForID:function(node,id){node.setAttribute(DOMProperty.ID_ATTRIBUTE_NAME,id)},createMarkupForRoot:function(){return DOMProperty.ROOT_ATTRIBUTE_NAME+'=""'},setAttributeForRoot:function(node){node.setAttribute(DOMProperty.ROOT_ATTRIBUTE_NAME,"")},createMarkupForProperty:function(name,value){var propertyInfo=DOMProperty.properties.hasOwnProperty(name)?DOMProperty.properties[name]:null;if(propertyInfo){if(shouldIgnoreValue(propertyInfo,value)){return""}var attributeName=propertyInfo.attributeName;if(propertyInfo.hasBooleanValue||propertyInfo.hasOverloadedBooleanValue&&value===true){return attributeName+'=""'}return attributeName+"="+quoteAttributeValueForBrowser(value)}else if(DOMProperty.isCustomAttribute(name)){if(value==null){return""}return name+"="+quoteAttributeValueForBrowser(value)}return null},createMarkupForCustomAttribute:function(name,value){if(!isAttributeNameSafe(name)||value==null){return""}return name+"="+quoteAttributeValueForBrowser(value)},setValueForProperty:function(node,name,value){var propertyInfo=DOMProperty.properties.hasOwnProperty(name)?DOMProperty.properties[name]:null;if(propertyInfo){var mutationMethod=propertyInfo.mutationMethod;if(mutationMethod){mutationMethod(node,value)}else if(shouldIgnoreValue(propertyInfo,value)){this.deleteValueForProperty(node,name);return}else if(propertyInfo.mustUseProperty){node[propertyInfo.propertyName]=value}else{var attributeName=propertyInfo.attributeName;var namespace=propertyInfo.attributeNamespace;if(namespace){node.setAttributeNS(namespace,attributeName,""+value)}else if(propertyInfo.hasBooleanValue||propertyInfo.hasOverloadedBooleanValue&&value===true){node.setAttribute(attributeName,"")}else{node.setAttribute(attributeName,""+value)}}}else if(DOMProperty.isCustomAttribute(name)){DOMPropertyOperations.setValueForAttribute(node,name,value);return}if(process.env.NODE_ENV!=="production"){var payload={};payload[name]=value;ReactInstrumentation.debugTool.onHostOperation({instanceID:ReactDOMComponentTree.getInstanceFromNode(node)._debugID,type:"update attribute",payload:payload})}},setValueForAttribute:function(node,name,value){if(!isAttributeNameSafe(name)){return}if(value==null){node.removeAttribute(name)}else{node.setAttribute(name,""+value)}if(process.env.NODE_ENV!=="production"){var payload={};payload[name]=value;ReactInstrumentation.debugTool.onHostOperation({instanceID:ReactDOMComponentTree.getInstanceFromNode(node)._debugID,type:"update attribute",payload:payload})}},deleteValueForAttribute:function(node,name){node.removeAttribute(name);if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:ReactDOMComponentTree.getInstanceFromNode(node)._debugID,type:"remove attribute",payload:name})}},deleteValueForProperty:function(node,name){var propertyInfo=DOMProperty.properties.hasOwnProperty(name)?DOMProperty.properties[name]:null;if(propertyInfo){var mutationMethod=propertyInfo.mutationMethod;if(mutationMethod){mutationMethod(node,undefined)}else if(propertyInfo.mustUseProperty){var propName=propertyInfo.propertyName;if(propertyInfo.hasBooleanValue){node[propName]=false}else{node[propName]=""}}else{node.removeAttribute(propertyInfo.attributeName)}}else if(DOMProperty.isCustomAttribute(name)){node.removeAttribute(name)}if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:ReactDOMComponentTree.getInstanceFromNode(node)._debugID,type:"remove attribute",payload:name})}}};module.exports=DOMPropertyOperations}).call(this,require("_process"))},{"./DOMProperty":42,"./ReactDOMComponentTree":64,"./ReactInstrumentation":93,"./quoteAttributeValueForBrowser":150,_process:184,"fbjs/lib/warning":25}],44:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var DOMLazyTree=require("./DOMLazyTree");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var createNodesFromMarkup=require("fbjs/lib/createNodesFromMarkup");var emptyFunction=require("fbjs/lib/emptyFunction");var invariant=require("fbjs/lib/invariant");var Danger={dangerouslyReplaceNodeWithMarkup:function(oldChild,markup){!ExecutionEnvironment.canUseDOM?process.env.NODE_ENV!=="production"?invariant(false,"dangerouslyReplaceNodeWithMarkup(...): Cannot render markup in a worker thread. Make sure `window` and `document` are available globally before requiring React when unit testing or use ReactDOMServer.renderToString() for server rendering."):_prodInvariant("56"):void 0;!markup?process.env.NODE_ENV!=="production"?invariant(false,"dangerouslyReplaceNodeWithMarkup(...): Missing markup."):_prodInvariant("57"):void 0;!(oldChild.nodeName!=="HTML")?process.env.NODE_ENV!=="production"?invariant(false,"dangerouslyReplaceNodeWithMarkup(...): Cannot replace markup of the <html> node. This is because browser quirks make this unreliable and/or slow. If you want to render to the root you must use server rendering. See ReactDOMServer.renderToString()."):_prodInvariant("58"):void 0;if(typeof markup==="string"){var newChild=createNodesFromMarkup(markup,emptyFunction)[0];oldChild.parentNode.replaceChild(newChild,oldChild)}else{DOMLazyTree.replaceChildWithTree(oldChild,markup)}}};module.exports=Danger}).call(this,require("_process"))},{"./DOMLazyTree":40,"./reactProdInvariant":151,_process:184,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/createNodesFromMarkup":9,"fbjs/lib/emptyFunction":10,"fbjs/lib/invariant":18}],45:[function(require,module,exports){"use strict";var DefaultEventPluginOrder=["ResponderEventPlugin","SimpleEventPlugin","TapEventPlugin","EnterLeaveEventPlugin","ChangeEventPlugin","SelectEventPlugin","BeforeInputEventPlugin"];module.exports=DefaultEventPluginOrder},{}],46:[function(require,module,exports){"use strict";var EventPropagators=require("./EventPropagators");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var SyntheticMouseEvent=require("./SyntheticMouseEvent");var eventTypes={mouseEnter:{registrationName:"onMouseEnter",dependencies:["topMouseOut","topMouseOver"]},mouseLeave:{registrationName:"onMouseLeave",dependencies:["topMouseOut","topMouseOver"]}};var EnterLeaveEventPlugin={eventTypes:eventTypes,extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){if(topLevelType==="topMouseOver"&&(nativeEvent.relatedTarget||nativeEvent.fromElement)){return null}if(topLevelType!=="topMouseOut"&&topLevelType!=="topMouseOver"){return null}var win;if(nativeEventTarget.window===nativeEventTarget){win=nativeEventTarget}else{var doc=nativeEventTarget.ownerDocument;if(doc){win=doc.defaultView||doc.parentWindow}else{win=window}}var from;var to;if(topLevelType==="topMouseOut"){from=targetInst;var related=nativeEvent.relatedTarget||nativeEvent.toElement;to=related?ReactDOMComponentTree.getClosestInstanceFromNode(related):null}else{from=null;to=targetInst}if(from===to){return null}var fromNode=from==null?win:ReactDOMComponentTree.getNodeFromInstance(from);var toNode=to==null?win:ReactDOMComponentTree.getNodeFromInstance(to);var leave=SyntheticMouseEvent.getPooled(eventTypes.mouseLeave,from,nativeEvent,nativeEventTarget);leave.type="mouseleave";leave.target=fromNode;leave.relatedTarget=toNode;var enter=SyntheticMouseEvent.getPooled(eventTypes.mouseEnter,to,nativeEvent,nativeEventTarget);enter.type="mouseenter";enter.target=toNode;enter.relatedTarget=fromNode;EventPropagators.accumulateEnterLeaveDispatches(leave,enter,from,to);return[leave,enter]}};module.exports=EnterLeaveEventPlugin},{"./EventPropagators":50,"./ReactDOMComponentTree":64,"./SyntheticMouseEvent":121}],47:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var EventPluginRegistry=require("./EventPluginRegistry");var EventPluginUtils=require("./EventPluginUtils");var ReactErrorUtils=require("./ReactErrorUtils");var accumulateInto=require("./accumulateInto");var forEachAccumulated=require("./forEachAccumulated");var invariant=require("fbjs/lib/invariant");var listenerBank={};var eventQueue=null;var executeDispatchesAndRelease=function(event,simulated){if(event){EventPluginUtils.executeDispatchesInOrder(event,simulated);if(!event.isPersistent()){event.constructor.release(event)}}};var executeDispatchesAndReleaseSimulated=function(e){return executeDispatchesAndRelease(e,true)};var executeDispatchesAndReleaseTopLevel=function(e){return executeDispatchesAndRelease(e,false)};var getDictionaryKey=function(inst){return"."+inst._rootNodeID};function isInteractive(tag){return tag==="button"||tag==="input"||tag==="select"||tag==="textarea"}function shouldPreventMouseEvent(name,type,props){switch(name){case"onClick":case"onClickCapture":case"onDoubleClick":case"onDoubleClickCapture":case"onMouseDown":case"onMouseDownCapture":case"onMouseMove":case"onMouseMoveCapture":case"onMouseUp":case"onMouseUpCapture":return!!(props.disabled&&isInteractive(type));default:return false}}var EventPluginHub={injection:{injectEventPluginOrder:EventPluginRegistry.injectEventPluginOrder,injectEventPluginsByName:EventPluginRegistry.injectEventPluginsByName},putListener:function(inst,registrationName,listener){!(typeof listener==="function")?process.env.NODE_ENV!=="production"?invariant(false,"Expected %s listener to be a function, instead got type %s",registrationName,typeof listener):_prodInvariant("94",registrationName,typeof listener):void 0;var key=getDictionaryKey(inst);var bankForRegistrationName=listenerBank[registrationName]||(listenerBank[registrationName]={});bankForRegistrationName[key]=listener;var PluginModule=EventPluginRegistry.registrationNameModules[registrationName];if(PluginModule&&PluginModule.didPutListener){PluginModule.didPutListener(inst,registrationName,listener)}},getListener:function(inst,registrationName){var bankForRegistrationName=listenerBank[registrationName];if(shouldPreventMouseEvent(registrationName,inst._currentElement.type,inst._currentElement.props)){return null}var key=getDictionaryKey(inst);return bankForRegistrationName&&bankForRegistrationName[key]},deleteListener:function(inst,registrationName){var PluginModule=EventPluginRegistry.registrationNameModules[registrationName];if(PluginModule&&PluginModule.willDeleteListener){PluginModule.willDeleteListener(inst,registrationName)}var bankForRegistrationName=listenerBank[registrationName];if(bankForRegistrationName){var key=getDictionaryKey(inst);delete bankForRegistrationName[key]}},deleteAllListeners:function(inst){var key=getDictionaryKey(inst);for(var registrationName in listenerBank){if(!listenerBank.hasOwnProperty(registrationName)){continue}if(!listenerBank[registrationName][key]){continue}var PluginModule=EventPluginRegistry.registrationNameModules[registrationName];if(PluginModule&&PluginModule.willDeleteListener){PluginModule.willDeleteListener(inst,registrationName)}delete listenerBank[registrationName][key]}},extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){var events;var plugins=EventPluginRegistry.plugins;for(var i=0;i<plugins.length;i++){var possiblePlugin=plugins[i];if(possiblePlugin){var extractedEvents=possiblePlugin.extractEvents(topLevelType,targetInst,nativeEvent,nativeEventTarget);if(extractedEvents){events=accumulateInto(events,extractedEvents)}}}return events},enqueueEvents:function(events){if(events){eventQueue=accumulateInto(eventQueue,events)}},processEventQueue:function(simulated){var processingEventQueue=eventQueue;eventQueue=null;if(simulated){forEachAccumulated(processingEventQueue,executeDispatchesAndReleaseSimulated)}else{forEachAccumulated(processingEventQueue,executeDispatchesAndReleaseTopLevel)}!!eventQueue?process.env.NODE_ENV!=="production"?invariant(false,"processEventQueue(): Additional events were enqueued while processing an event queue. Support for this has not yet been implemented."):_prodInvariant("95"):void 0;ReactErrorUtils.rethrowCaughtError()},__purge:function(){listenerBank={}},__getListenerBank:function(){return listenerBank}};module.exports=EventPluginHub}).call(this,require("_process"))},{"./EventPluginRegistry":48,"./EventPluginUtils":49,"./ReactErrorUtils":84,"./accumulateInto":128,"./forEachAccumulated":136,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],48:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");var eventPluginOrder=null;var namesToPlugins={};function recomputePluginOrdering(){if(!eventPluginOrder){return}for(var pluginName in namesToPlugins){var pluginModule=namesToPlugins[pluginName];var pluginIndex=eventPluginOrder.indexOf(pluginName);!(pluginIndex>-1)?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginRegistry: Cannot inject event plugins that do not exist in the plugin ordering, `%s`.",pluginName):_prodInvariant("96",pluginName):void 0;if(EventPluginRegistry.plugins[pluginIndex]){continue}!pluginModule.extractEvents?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginRegistry: Event plugins must implement an `extractEvents` method, but `%s` does not.",pluginName):_prodInvariant("97",pluginName):void 0;EventPluginRegistry.plugins[pluginIndex]=pluginModule;var publishedEvents=pluginModule.eventTypes;for(var eventName in publishedEvents){!publishEventForPlugin(publishedEvents[eventName],pluginModule,eventName)?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginRegistry: Failed to publish event `%s` for plugin `%s`.",eventName,pluginName):_prodInvariant("98",eventName,pluginName):void 0}}}function publishEventForPlugin(dispatchConfig,pluginModule,eventName){!!EventPluginRegistry.eventNameDispatchConfigs.hasOwnProperty(eventName)?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginHub: More than one plugin attempted to publish the same event name, `%s`.",eventName):_prodInvariant("99",eventName):void 0;EventPluginRegistry.eventNameDispatchConfigs[eventName]=dispatchConfig;var phasedRegistrationNames=dispatchConfig.phasedRegistrationNames;if(phasedRegistrationNames){for(var phaseName in phasedRegistrationNames){if(phasedRegistrationNames.hasOwnProperty(phaseName)){var phasedRegistrationName=phasedRegistrationNames[phaseName];publishRegistrationName(phasedRegistrationName,pluginModule,eventName)}}return true}else if(dispatchConfig.registrationName){publishRegistrationName(dispatchConfig.registrationName,pluginModule,eventName);return true}return false}function publishRegistrationName(registrationName,pluginModule,eventName){!!EventPluginRegistry.registrationNameModules[registrationName]?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginHub: More than one plugin attempted to publish the same registration name, `%s`.",registrationName):_prodInvariant("100",registrationName):void 0;EventPluginRegistry.registrationNameModules[registrationName]=pluginModule;EventPluginRegistry.registrationNameDependencies[registrationName]=pluginModule.eventTypes[eventName].dependencies;if(process.env.NODE_ENV!=="production"){var lowerCasedName=registrationName.toLowerCase();EventPluginRegistry.possibleRegistrationNames[lowerCasedName]=registrationName;if(registrationName==="onDoubleClick"){EventPluginRegistry.possibleRegistrationNames.ondblclick=registrationName}}}var EventPluginRegistry={plugins:[],eventNameDispatchConfigs:{},registrationNameModules:{},registrationNameDependencies:{},possibleRegistrationNames:process.env.NODE_ENV!=="production"?{}:null,injectEventPluginOrder:function(injectedEventPluginOrder){!!eventPluginOrder?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginRegistry: Cannot inject event plugin ordering more than once. You are likely trying to load more than one copy of React."):_prodInvariant("101"):void 0;eventPluginOrder=Array.prototype.slice.call(injectedEventPluginOrder);recomputePluginOrdering()},injectEventPluginsByName:function(injectedNamesToPlugins){var isOrderingDirty=false;for(var pluginName in injectedNamesToPlugins){if(!injectedNamesToPlugins.hasOwnProperty(pluginName)){continue}var pluginModule=injectedNamesToPlugins[pluginName];if(!namesToPlugins.hasOwnProperty(pluginName)||namesToPlugins[pluginName]!==pluginModule){!!namesToPlugins[pluginName]?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginRegistry: Cannot inject two different event plugins using the same name, `%s`.",pluginName):_prodInvariant("102",pluginName):void 0;namesToPlugins[pluginName]=pluginModule;isOrderingDirty=true}}if(isOrderingDirty){recomputePluginOrdering()}},getPluginModuleForEvent:function(event){var dispatchConfig=event.dispatchConfig;if(dispatchConfig.registrationName){return EventPluginRegistry.registrationNameModules[dispatchConfig.registrationName]||null}if(dispatchConfig.phasedRegistrationNames!==undefined){var phasedRegistrationNames=dispatchConfig.phasedRegistrationNames;for(var phase in phasedRegistrationNames){if(!phasedRegistrationNames.hasOwnProperty(phase)){continue}var pluginModule=EventPluginRegistry.registrationNameModules[phasedRegistrationNames[phase]];if(pluginModule){return pluginModule}}}return null},_resetEventPlugins:function(){eventPluginOrder=null;for(var pluginName in namesToPlugins){if(namesToPlugins.hasOwnProperty(pluginName)){delete namesToPlugins[pluginName]}}EventPluginRegistry.plugins.length=0;var eventNameDispatchConfigs=EventPluginRegistry.eventNameDispatchConfigs;for(var eventName in eventNameDispatchConfigs){if(eventNameDispatchConfigs.hasOwnProperty(eventName)){delete eventNameDispatchConfigs[eventName]}}var registrationNameModules=EventPluginRegistry.registrationNameModules;for(var registrationName in registrationNameModules){if(registrationNameModules.hasOwnProperty(registrationName)){delete registrationNameModules[registrationName]}}if(process.env.NODE_ENV!=="production"){var possibleRegistrationNames=EventPluginRegistry.possibleRegistrationNames;for(var lowerCasedName in possibleRegistrationNames){if(possibleRegistrationNames.hasOwnProperty(lowerCasedName)){delete possibleRegistrationNames[lowerCasedName]}}}}};module.exports=EventPluginRegistry}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],49:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactErrorUtils=require("./ReactErrorUtils");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ComponentTree;var TreeTraversal;var injection={injectComponentTree:function(Injected){ComponentTree=Injected;if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(Injected&&Injected.getNodeFromInstance&&Injected.getInstanceFromNode,"EventPluginUtils.injection.injectComponentTree(...): Injected "+"module is missing getNodeFromInstance or getInstanceFromNode."):void 0}},injectTreeTraversal:function(Injected){TreeTraversal=Injected;if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(Injected&&Injected.isAncestor&&Injected.getLowestCommonAncestor,"EventPluginUtils.injection.injectTreeTraversal(...): Injected "+"module is missing isAncestor or getLowestCommonAncestor."):void 0}}};function isEndish(topLevelType){return topLevelType==="topMouseUp"||topLevelType==="topTouchEnd"||topLevelType==="topTouchCancel"}function isMoveish(topLevelType){return topLevelType==="topMouseMove"||topLevelType==="topTouchMove"}function isStartish(topLevelType){return topLevelType==="topMouseDown"||topLevelType==="topTouchStart"}var validateEventDispatches;if(process.env.NODE_ENV!=="production"){validateEventDispatches=function(event){var dispatchListeners=event._dispatchListeners;var dispatchInstances=event._dispatchInstances;var listenersIsArr=Array.isArray(dispatchListeners);var listenersLen=listenersIsArr?dispatchListeners.length:dispatchListeners?1:0;var instancesIsArr=Array.isArray(dispatchInstances);var instancesLen=instancesIsArr?dispatchInstances.length:dispatchInstances?1:0;process.env.NODE_ENV!=="production"?warning(instancesIsArr===listenersIsArr&&instancesLen===listenersLen,"EventPluginUtils: Invalid `event`."):void 0}}function executeDispatch(event,simulated,listener,inst){var type=event.type||"unknown-event";event.currentTarget=EventPluginUtils.getNodeFromInstance(inst);if(simulated){ReactErrorUtils.invokeGuardedCallbackWithCatch(type,listener,event)}else{ReactErrorUtils.invokeGuardedCallback(type,listener,event)}event.currentTarget=null}function executeDispatchesInOrder(event,simulated){var dispatchListeners=event._dispatchListeners;var dispatchInstances=event._dispatchInstances;if(process.env.NODE_ENV!=="production"){validateEventDispatches(event)}if(Array.isArray(dispatchListeners)){for(var i=0;i<dispatchListeners.length;i++){if(event.isPropagationStopped()){break}executeDispatch(event,simulated,dispatchListeners[i],dispatchInstances[i])}}else if(dispatchListeners){executeDispatch(event,simulated,dispatchListeners,dispatchInstances)}event._dispatchListeners=null;event._dispatchInstances=null}function executeDispatchesInOrderStopAtTrueImpl(event){var dispatchListeners=event._dispatchListeners;var dispatchInstances=event._dispatchInstances;if(process.env.NODE_ENV!=="production"){validateEventDispatches(event)}if(Array.isArray(dispatchListeners)){for(var i=0;i<dispatchListeners.length;i++){if(event.isPropagationStopped()){break}if(dispatchListeners[i](event,dispatchInstances[i])){return dispatchInstances[i]}}}else if(dispatchListeners){if(dispatchListeners(event,dispatchInstances)){return dispatchInstances}}return null}function executeDispatchesInOrderStopAtTrue(event){var ret=executeDispatchesInOrderStopAtTrueImpl(event);event._dispatchInstances=null;event._dispatchListeners=null;return ret}function executeDirectDispatch(event){if(process.env.NODE_ENV!=="production"){validateEventDispatches(event)}var dispatchListener=event._dispatchListeners;var dispatchInstance=event._dispatchInstances;!!Array.isArray(dispatchListener)?process.env.NODE_ENV!=="production"?invariant(false,"executeDirectDispatch(...): Invalid `event`."):_prodInvariant("103"):void 0;event.currentTarget=dispatchListener?EventPluginUtils.getNodeFromInstance(dispatchInstance):null;var res=dispatchListener?dispatchListener(event):null;event.currentTarget=null;event._dispatchListeners=null;event._dispatchInstances=null;return res}function hasDispatches(event){return!!event._dispatchListeners}var EventPluginUtils={isEndish:isEndish,isMoveish:isMoveish,isStartish:isStartish,executeDirectDispatch:executeDirectDispatch,executeDispatchesInOrder:executeDispatchesInOrder,executeDispatchesInOrderStopAtTrue:executeDispatchesInOrderStopAtTrue,hasDispatches:hasDispatches,getInstanceFromNode:function(node){return ComponentTree.getInstanceFromNode(node)},getNodeFromInstance:function(node){return ComponentTree.getNodeFromInstance(node)},isAncestor:function(a,b){return TreeTraversal.isAncestor(a,b)},getLowestCommonAncestor:function(a,b){return TreeTraversal.getLowestCommonAncestor(a,b)},getParentInstance:function(inst){return TreeTraversal.getParentInstance(inst)},traverseTwoPhase:function(target,fn,arg){return TreeTraversal.traverseTwoPhase(target,fn,arg)},traverseEnterLeave:function(from,to,fn,argFrom,argTo){return TreeTraversal.traverseEnterLeave(from,to,fn,argFrom,argTo)},injection:injection};module.exports=EventPluginUtils}).call(this,require("_process"))},{"./ReactErrorUtils":84,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],50:[function(require,module,exports){(function(process){"use strict";var EventPluginHub=require("./EventPluginHub");var EventPluginUtils=require("./EventPluginUtils");var accumulateInto=require("./accumulateInto");var forEachAccumulated=require("./forEachAccumulated");var warning=require("fbjs/lib/warning");var getListener=EventPluginHub.getListener;function listenerAtPhase(inst,event,propagationPhase){var registrationName=event.dispatchConfig.phasedRegistrationNames[propagationPhase];return getListener(inst,registrationName)}function accumulateDirectionalDispatches(inst,phase,event){if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(inst,"Dispatching inst must not be null"):void 0}var listener=listenerAtPhase(inst,event,phase);if(listener){event._dispatchListeners=accumulateInto(event._dispatchListeners,listener);event._dispatchInstances=accumulateInto(event._dispatchInstances,inst)}}function accumulateTwoPhaseDispatchesSingle(event){if(event&&event.dispatchConfig.phasedRegistrationNames){EventPluginUtils.traverseTwoPhase(event._targetInst,accumulateDirectionalDispatches,event)}}function accumulateTwoPhaseDispatchesSingleSkipTarget(event){if(event&&event.dispatchConfig.phasedRegistrationNames){var targetInst=event._targetInst;var parentInst=targetInst?EventPluginUtils.getParentInstance(targetInst):null;EventPluginUtils.traverseTwoPhase(parentInst,accumulateDirectionalDispatches,event)}}function accumulateDispatches(inst,ignoredDirection,event){if(event&&event.dispatchConfig.registrationName){var registrationName=event.dispatchConfig.registrationName;var listener=getListener(inst,registrationName);if(listener){event._dispatchListeners=accumulateInto(event._dispatchListeners,listener);event._dispatchInstances=accumulateInto(event._dispatchInstances,inst)}}}function accumulateDirectDispatchesSingle(event){if(event&&event.dispatchConfig.registrationName){accumulateDispatches(event._targetInst,null,event)}}function accumulateTwoPhaseDispatches(events){forEachAccumulated(events,accumulateTwoPhaseDispatchesSingle)}function accumulateTwoPhaseDispatchesSkipTarget(events){forEachAccumulated(events,accumulateTwoPhaseDispatchesSingleSkipTarget)}function accumulateEnterLeaveDispatches(leave,enter,from,to){EventPluginUtils.traverseEnterLeave(from,to,accumulateDispatches,leave,enter)}function accumulateDirectDispatches(events){forEachAccumulated(events,accumulateDirectDispatchesSingle)}var EventPropagators={accumulateTwoPhaseDispatches:accumulateTwoPhaseDispatches,accumulateTwoPhaseDispatchesSkipTarget:accumulateTwoPhaseDispatchesSkipTarget,accumulateDirectDispatches:accumulateDirectDispatches,accumulateEnterLeaveDispatches:accumulateEnterLeaveDispatches};module.exports=EventPropagators}).call(this,require("_process"))},{"./EventPluginHub":47,"./EventPluginUtils":49,"./accumulateInto":128,"./forEachAccumulated":136,_process:184,"fbjs/lib/warning":25}],51:[function(require,module,exports){"use strict";var _assign=require("object-assign");var PooledClass=require("./PooledClass");var getTextContentAccessor=require("./getTextContentAccessor");function FallbackCompositionState(root){this._root=root;this._startText=this.getText();this._fallbackText=null}_assign(FallbackCompositionState.prototype,{destructor:function(){this._root=null;this._startText=null;this._fallbackText=null},getText:function(){if("value"in this._root){return this._root.value}return this._root[getTextContentAccessor()]},getData:function(){if(this._fallbackText){return this._fallbackText}var start;var startValue=this._startText;var startLength=startValue.length;var end;var endValue=this.getText();var endLength=endValue.length;for(start=0;start<startLength;start++){if(startValue[start]!==endValue[start]){break}}var minEnd=startLength-start;for(end=1;end<=minEnd;end++){if(startValue[startLength-end]!==endValue[endLength-end]){break}}var sliceTail=end>1?1-end:undefined;this._fallbackText=endValue.slice(start,sliceTail);return this._fallbackText}});PooledClass.addPoolingTo(FallbackCompositionState);module.exports=FallbackCompositionState},{"./PooledClass":55,"./getTextContentAccessor":144,"object-assign":26}],52:[function(require,module,exports){"use strict";var DOMProperty=require("./DOMProperty");var MUST_USE_PROPERTY=DOMProperty.injection.MUST_USE_PROPERTY;var HAS_BOOLEAN_VALUE=DOMProperty.injection.HAS_BOOLEAN_VALUE;var HAS_NUMERIC_VALUE=DOMProperty.injection.HAS_NUMERIC_VALUE;var HAS_POSITIVE_NUMERIC_VALUE=DOMProperty.injection.HAS_POSITIVE_NUMERIC_VALUE;var HAS_OVERLOADED_BOOLEAN_VALUE=DOMProperty.injection.HAS_OVERLOADED_BOOLEAN_VALUE;var HTMLDOMPropertyConfig={isCustomAttribute:RegExp.prototype.test.bind(new RegExp("^(data|aria)-["+DOMProperty.ATTRIBUTE_NAME_CHAR+"]*$")),Properties:{accept:0,acceptCharset:0,accessKey:0,action:0,allowFullScreen:HAS_BOOLEAN_VALUE,allowTransparency:0,alt:0,as:0,async:HAS_BOOLEAN_VALUE,autoComplete:0,autoPlay:HAS_BOOLEAN_VALUE,capture:HAS_BOOLEAN_VALUE,cellPadding:0,cellSpacing:0,charSet:0,challenge:0,checked:MUST_USE_PROPERTY|HAS_BOOLEAN_VALUE,cite:0,classID:0,className:0,cols:HAS_POSITIVE_NUMERIC_VALUE,colSpan:0,content:0,contentEditable:0,contextMenu:0,controls:HAS_BOOLEAN_VALUE,coords:0,crossOrigin:0,data:0,dateTime:0,default:HAS_BOOLEAN_VALUE,defer:HAS_BOOLEAN_VALUE,dir:0,disabled:HAS_BOOLEAN_VALUE,download:HAS_OVERLOADED_BOOLEAN_VALUE,draggable:0,encType:0,form:0,formAction:0,formEncType:0,formMethod:0,formNoValidate:HAS_BOOLEAN_VALUE,formTarget:0,frameBorder:0,headers:0,height:0,hidden:HAS_BOOLEAN_VALUE,high:0,href:0,hrefLang:0,htmlFor:0,httpEquiv:0,icon:0,id:0,inputMode:0,integrity:0,is:0,keyParams:0,keyType:0,kind:0,label:0,lang:0,list:0,loop:HAS_BOOLEAN_VALUE,low:0,manifest:0,marginHeight:0,marginWidth:0,max:0,maxLength:0,media:0,mediaGroup:0,method:0,min:0,minLength:0,multiple:MUST_USE_PROPERTY|HAS_BOOLEAN_VALUE,muted:MUST_USE_PROPERTY|HAS_BOOLEAN_VALUE,name:0,nonce:0,noValidate:HAS_BOOLEAN_VALUE,open:HAS_BOOLEAN_VALUE,optimum:0,pattern:0,placeholder:0,playsInline:HAS_BOOLEAN_VALUE,poster:0,preload:0,profile:0,radioGroup:0,readOnly:HAS_BOOLEAN_VALUE,referrerPolicy:0,rel:0,required:HAS_BOOLEAN_VALUE,reversed:HAS_BOOLEAN_VALUE,role:0,rows:HAS_POSITIVE_NUMERIC_VALUE,rowSpan:HAS_NUMERIC_VALUE,sandbox:0,scope:0,scoped:HAS_BOOLEAN_VALUE,scrolling:0,seamless:HAS_BOOLEAN_VALUE,selected:MUST_USE_PROPERTY|HAS_BOOLEAN_VALUE,shape:0,size:HAS_POSITIVE_NUMERIC_VALUE,sizes:0,span:HAS_POSITIVE_NUMERIC_VALUE,spellCheck:0,src:0,srcDoc:0,srcLang:0,srcSet:0,start:HAS_NUMERIC_VALUE,step:0,style:0,summary:0,tabIndex:0,target:0,title:0,type:0,useMap:0,value:0,width:0,wmode:0,wrap:0,about:0,datatype:0,inlist:0,prefix:0,property:0,resource:0,typeof:0,vocab:0,autoCapitalize:0,autoCorrect:0,autoSave:0,color:0,itemProp:0,itemScope:HAS_BOOLEAN_VALUE,itemType:0,itemID:0,itemRef:0,results:0,security:0,unselectable:0},DOMAttributeNames:{acceptCharset:"accept-charset",className:"class",htmlFor:"for",httpEquiv:"http-equiv"},DOMPropertyNames:{},DOMMutationMethods:{value:function(node,value){if(value==null){return node.removeAttribute("value")}if(node.type!=="number"||node.hasAttribute("value")===false){node.setAttribute("value",""+value)}else if(node.validity&&!node.validity.badInput&&node.ownerDocument.activeElement!==node){node.setAttribute("value",""+value)}}}};module.exports=HTMLDOMPropertyConfig},{"./DOMProperty":42}],53:[function(require,module,exports){"use strict";function escape(key){var escapeRegex=/[=:]/g;var escaperLookup={"=":"=0",":":"=2"};var escapedString=(""+key).replace(escapeRegex,function(match){return escaperLookup[match]});return"$"+escapedString}function unescape(key){var unescapeRegex=/(=0|=2)/g;var unescaperLookup={"=0":"=","=2":":"};var keySubstring=key[0]==="."&&key[1]==="$"?key.substring(2):key.substring(1);return(""+keySubstring).replace(unescapeRegex,function(match){return unescaperLookup[match]})}var KeyEscapeUtils={escape:escape,unescape:unescape};module.exports=KeyEscapeUtils},{}],54:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactPropTypesSecret=require("./ReactPropTypesSecret");var propTypesFactory=require("prop-types/factory");var React=require("react/lib/React");var PropTypes=propTypesFactory(React.isValidElement);var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var hasReadOnlyValue={button:true,checkbox:true,image:true,hidden:true,radio:true,reset:true,submit:true};function _assertSingleLink(inputProps){!(inputProps.checkedLink==null||inputProps.valueLink==null)?process.env.NODE_ENV!=="production"?invariant(false,"Cannot provide a checkedLink and a valueLink. If you want to use checkedLink, you probably don't want to use valueLink and vice versa."):_prodInvariant("87"):void 0}function _assertValueLink(inputProps){_assertSingleLink(inputProps);!(inputProps.value==null&&inputProps.onChange==null)?process.env.NODE_ENV!=="production"?invariant(false,"Cannot provide a valueLink and a value or onChange event. If you want to use value or onChange, you probably don't want to use valueLink."):_prodInvariant("88"):void 0}function _assertCheckedLink(inputProps){_assertSingleLink(inputProps);!(inputProps.checked==null&&inputProps.onChange==null)?process.env.NODE_ENV!=="production"?invariant(false,"Cannot provide a checkedLink and a checked property or onChange event. If you want to use checked or onChange, you probably don't want to use checkedLink"):_prodInvariant("89"):void 0}var propTypes={value:function(props,propName,componentName){if(!props[propName]||hasReadOnlyValue[props.type]||props.onChange||props.readOnly||props.disabled){return null}return new Error("You provided a `value` prop to a form field without an "+"`onChange` handler. This will render a read-only field. If "+"the field should be mutable use `defaultValue`. Otherwise, "+"set either `onChange` or `readOnly`.")},checked:function(props,propName,componentName){if(!props[propName]||props.onChange||props.readOnly||props.disabled){return null}return new Error("You provided a `checked` prop to a form field without an "+"`onChange` handler. This will render a read-only field. If "+"the field should be mutable use `defaultChecked`. Otherwise, "+"set either `onChange` or `readOnly`.")},onChange:PropTypes.func};var loggedTypeFailures={};function getDeclarationErrorAddendum(owner){if(owner){var name=owner.getName();if(name){return" Check the render method of `"+name+"`."}}return""}var LinkedValueUtils={checkPropTypes:function(tagName,props,owner){for(var propName in propTypes){if(propTypes.hasOwnProperty(propName)){var error=propTypes[propName](props,propName,tagName,"prop",null,ReactPropTypesSecret)}if(error instanceof Error&&!(error.message in loggedTypeFailures)){loggedTypeFailures[error.message]=true;var addendum=getDeclarationErrorAddendum(owner);process.env.NODE_ENV!=="production"?warning(false,"Failed form propType: %s%s",error.message,addendum):void 0}}},getValue:function(inputProps){if(inputProps.valueLink){_assertValueLink(inputProps);return inputProps.valueLink.value}return inputProps.value},getChecked:function(inputProps){if(inputProps.checkedLink){_assertCheckedLink(inputProps);return inputProps.checkedLink.value}return inputProps.checked},executeOnChange:function(inputProps,event){if(inputProps.valueLink){_assertValueLink(inputProps);return inputProps.valueLink.requestChange(event.target.value)}else if(inputProps.checkedLink){_assertCheckedLink(inputProps);return inputProps.checkedLink.requestChange(event.target.checked)}else if(inputProps.onChange){return inputProps.onChange.call(undefined,event)}}};module.exports=LinkedValueUtils}).call(this,require("_process"))},{"./ReactPropTypesSecret":101,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"prop-types/factory":28,"react/lib/React":160}],55:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");var oneArgumentPooler=function(copyFieldsFrom){var Klass=this;if(Klass.instancePool.length){var instance=Klass.instancePool.pop();Klass.call(instance,copyFieldsFrom);return instance}else{return new Klass(copyFieldsFrom)}};var twoArgumentPooler=function(a1,a2){var Klass=this;if(Klass.instancePool.length){var instance=Klass.instancePool.pop();Klass.call(instance,a1,a2);return instance}else{return new Klass(a1,a2)}};var threeArgumentPooler=function(a1,a2,a3){var Klass=this;if(Klass.instancePool.length){var instance=Klass.instancePool.pop();Klass.call(instance,a1,a2,a3);return instance}else{return new Klass(a1,a2,a3)}};var fourArgumentPooler=function(a1,a2,a3,a4){var Klass=this;if(Klass.instancePool.length){var instance=Klass.instancePool.pop();Klass.call(instance,a1,a2,a3,a4);return instance}else{return new Klass(a1,a2,a3,a4)}};var standardReleaser=function(instance){var Klass=this;!(instance instanceof Klass)?process.env.NODE_ENV!=="production"?invariant(false,"Trying to release an instance into a pool of a different type."):_prodInvariant("25"):void 0;instance.destructor();if(Klass.instancePool.length<Klass.poolSize){Klass.instancePool.push(instance)}};var DEFAULT_POOL_SIZE=10;var DEFAULT_POOLER=oneArgumentPooler;var addPoolingTo=function(CopyConstructor,pooler){var NewKlass=CopyConstructor;NewKlass.instancePool=[];NewKlass.getPooled=pooler||DEFAULT_POOLER;if(!NewKlass.poolSize){NewKlass.poolSize=DEFAULT_POOL_SIZE}NewKlass.release=standardReleaser;return NewKlass};var PooledClass={addPoolingTo:addPoolingTo,oneArgumentPooler:oneArgumentPooler,twoArgumentPooler:twoArgumentPooler,threeArgumentPooler:threeArgumentPooler,fourArgumentPooler:fourArgumentPooler};module.exports=PooledClass}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],56:[function(require,module,exports){"use strict";var _assign=require("object-assign");var EventPluginRegistry=require("./EventPluginRegistry");var ReactEventEmitterMixin=require("./ReactEventEmitterMixin");var ViewportMetrics=require("./ViewportMetrics");var getVendorPrefixedEventName=require("./getVendorPrefixedEventName");var isEventSupported=require("./isEventSupported");var hasEventPageXY;var alreadyListeningTo={};var isMonitoringScrollValue=false;var reactTopListenersCounter=0;var topEventMapping={topAbort:"abort",topAnimationEnd:getVendorPrefixedEventName("animationend")||"animationend",topAnimationIteration:getVendorPrefixedEventName("animationiteration")||"animationiteration",topAnimationStart:getVendorPrefixedEventName("animationstart")||"animationstart",topBlur:"blur",topCanPlay:"canplay",topCanPlayThrough:"canplaythrough",topChange:"change",topClick:"click",topCompositionEnd:"compositionend",topCompositionStart:"compositionstart",topCompositionUpdate:"compositionupdate",topContextMenu:"contextmenu",topCopy:"copy",topCut:"cut",topDoubleClick:"dblclick",topDrag:"drag",topDragEnd:"dragend",topDragEnter:"dragenter",topDragExit:"dragexit",topDragLeave:"dragleave",topDragOver:"dragover",topDragStart:"dragstart",topDrop:"drop",topDurationChange:"durationchange",topEmptied:"emptied",topEncrypted:"encrypted",topEnded:"ended",topError:"error",topFocus:"focus",topInput:"input",topKeyDown:"keydown",topKeyPress:"keypress",topKeyUp:"keyup",topLoadedData:"loadeddata",topLoadedMetadata:"loadedmetadata",topLoadStart:"loadstart",topMouseDown:"mousedown",topMouseMove:"mousemove",topMouseOut:"mouseout",topMouseOver:"mouseover",topMouseUp:"mouseup",topPaste:"paste",topPause:"pause",topPlay:"play",topPlaying:"playing",topProgress:"progress",topRateChange:"ratechange",topScroll:"scroll",topSeeked:"seeked",topSeeking:"seeking",topSelectionChange:"selectionchange",topStalled:"stalled",topSuspend:"suspend",topTextInput:"textInput",topTimeUpdate:"timeupdate",topTouchCancel:"touchcancel",topTouchEnd:"touchend",topTouchMove:"touchmove",topTouchStart:"touchstart",topTransitionEnd:getVendorPrefixedEventName("transitionend")||"transitionend",topVolumeChange:"volumechange",topWaiting:"waiting",topWheel:"wheel"};var topListenersIDKey="_reactListenersID"+String(Math.random()).slice(2);function getListeningForDocument(mountAt){if(!Object.prototype.hasOwnProperty.call(mountAt,topListenersIDKey)){mountAt[topListenersIDKey]=reactTopListenersCounter++;alreadyListeningTo[mountAt[topListenersIDKey]]={}}return alreadyListeningTo[mountAt[topListenersIDKey]]}var ReactBrowserEventEmitter=_assign({},ReactEventEmitterMixin,{ReactEventListener:null,injection:{injectReactEventListener:function(ReactEventListener){ReactEventListener.setHandleTopLevel(ReactBrowserEventEmitter.handleTopLevel);ReactBrowserEventEmitter.ReactEventListener=ReactEventListener}},setEnabled:function(enabled){if(ReactBrowserEventEmitter.ReactEventListener){ReactBrowserEventEmitter.ReactEventListener.setEnabled(enabled)}},isEnabled:function(){return!!(ReactBrowserEventEmitter.ReactEventListener&&ReactBrowserEventEmitter.ReactEventListener.isEnabled())},listenTo:function(registrationName,contentDocumentHandle){var mountAt=contentDocumentHandle;var isListening=getListeningForDocument(mountAt);var dependencies=EventPluginRegistry.registrationNameDependencies[registrationName];for(var i=0;i<dependencies.length;i++){var dependency=dependencies[i];if(!(isListening.hasOwnProperty(dependency)&&isListening[dependency])){if(dependency==="topWheel"){if(isEventSupported("wheel")){ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topWheel","wheel",mountAt)}else if(isEventSupported("mousewheel")){ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topWheel","mousewheel",mountAt)}else{ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topWheel","DOMMouseScroll",mountAt)}}else if(dependency==="topScroll"){if(isEventSupported("scroll",true)){ReactBrowserEventEmitter.ReactEventListener.trapCapturedEvent("topScroll","scroll",mountAt)}else{ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topScroll","scroll",ReactBrowserEventEmitter.ReactEventListener.WINDOW_HANDLE)}}else if(dependency==="topFocus"||dependency==="topBlur"){if(isEventSupported("focus",true)){ReactBrowserEventEmitter.ReactEventListener.trapCapturedEvent("topFocus","focus",mountAt);ReactBrowserEventEmitter.ReactEventListener.trapCapturedEvent("topBlur","blur",mountAt)}else if(isEventSupported("focusin")){ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topFocus","focusin",mountAt);ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topBlur","focusout",mountAt)}isListening.topBlur=true;isListening.topFocus=true}else if(topEventMapping.hasOwnProperty(dependency)){ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent(dependency,topEventMapping[dependency],mountAt)}isListening[dependency]=true}}},trapBubbledEvent:function(topLevelType,handlerBaseName,handle){return ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent(topLevelType,handlerBaseName,handle)},trapCapturedEvent:function(topLevelType,handlerBaseName,handle){return ReactBrowserEventEmitter.ReactEventListener.trapCapturedEvent(topLevelType,handlerBaseName,handle)},supportsEventPageXY:function(){if(!document.createEvent){return false}var ev=document.createEvent("MouseEvent");return ev!=null&&"pageX"in ev},ensureScrollValueMonitoring:function(){if(hasEventPageXY===undefined){hasEventPageXY=ReactBrowserEventEmitter.supportsEventPageXY()}if(!hasEventPageXY&&!isMonitoringScrollValue){var refresh=ViewportMetrics.refreshScrollValues;ReactBrowserEventEmitter.ReactEventListener.monitorScrollValue(refresh);isMonitoringScrollValue=true}}});module.exports=ReactBrowserEventEmitter},{"./EventPluginRegistry":48,"./ReactEventEmitterMixin":85,"./ViewportMetrics":127,"./getVendorPrefixedEventName":145,"./isEventSupported":148,"object-assign":26}],57:[function(require,module,exports){(function(process){"use strict";var ReactReconciler=require("./ReactReconciler");var instantiateReactComponent=require("./instantiateReactComponent");var KeyEscapeUtils=require("./KeyEscapeUtils");var shouldUpdateReactComponent=require("./shouldUpdateReactComponent");var traverseAllChildren=require("./traverseAllChildren");var warning=require("fbjs/lib/warning");var ReactComponentTreeHook;if(typeof process!=="undefined"&&process.env&&process.env.NODE_ENV==="test"){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}function instantiateChild(childInstances,child,name,selfDebugID){var keyUnique=childInstances[name]===undefined;if(process.env.NODE_ENV!=="production"){if(!ReactComponentTreeHook){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}if(!keyUnique){process.env.NODE_ENV!=="production"?warning(false,"flattenChildren(...): Encountered two children with the same key, "+"`%s`. Child keys must be unique; when two children share a key, only "+"the first child will be used.%s",KeyEscapeUtils.unescape(name),ReactComponentTreeHook.getStackAddendumByID(selfDebugID)):void 0}}if(child!=null&&keyUnique){childInstances[name]=instantiateReactComponent(child,true)}}var ReactChildReconciler={instantiateChildren:function(nestedChildNodes,transaction,context,selfDebugID){if(nestedChildNodes==null){return null}var childInstances={};if(process.env.NODE_ENV!=="production"){traverseAllChildren(nestedChildNodes,function(childInsts,child,name){return instantiateChild(childInsts,child,name,selfDebugID)},childInstances)}else{traverseAllChildren(nestedChildNodes,instantiateChild,childInstances)}return childInstances},updateChildren:function(prevChildren,nextChildren,mountImages,removedNodes,transaction,hostParent,hostContainerInfo,context,selfDebugID){if(!nextChildren&&!prevChildren){return}var name;var prevChild;for(name in nextChildren){if(!nextChildren.hasOwnProperty(name)){continue}prevChild=prevChildren&&prevChildren[name];var prevElement=prevChild&&prevChild._currentElement;var nextElement=nextChildren[name];if(prevChild!=null&&shouldUpdateReactComponent(prevElement,nextElement)){ReactReconciler.receiveComponent(prevChild,nextElement,transaction,context);nextChildren[name]=prevChild}else{if(prevChild){removedNodes[name]=ReactReconciler.getHostNode(prevChild);ReactReconciler.unmountComponent(prevChild,false)}var nextChildInstance=instantiateReactComponent(nextElement,true);nextChildren[name]=nextChildInstance;var nextChildMountImage=ReactReconciler.mountComponent(nextChildInstance,transaction,hostParent,hostContainerInfo,context,selfDebugID);mountImages.push(nextChildMountImage)}}for(name in prevChildren){if(prevChildren.hasOwnProperty(name)&&!(nextChildren&&nextChildren.hasOwnProperty(name))){prevChild=prevChildren[name];removedNodes[name]=ReactReconciler.getHostNode(prevChild);ReactReconciler.unmountComponent(prevChild,false)}}},unmountChildren:function(renderedChildren,safely){for(var name in renderedChildren){if(renderedChildren.hasOwnProperty(name)){var renderedChild=renderedChildren[name];ReactReconciler.unmountComponent(renderedChild,safely)}}}};module.exports=ReactChildReconciler}).call(this,require("_process"))},{"./KeyEscapeUtils":53,"./ReactReconciler":103,"./instantiateReactComponent":147,"./shouldUpdateReactComponent":155,"./traverseAllChildren":156,_process:184,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],58:[function(require,module,exports){"use strict";var DOMChildrenOperations=require("./DOMChildrenOperations");var ReactDOMIDOperations=require("./ReactDOMIDOperations");var ReactComponentBrowserEnvironment={processChildrenUpdates:ReactDOMIDOperations.dangerouslyProcessChildrenUpdates,replaceNodeWithMarkup:DOMChildrenOperations.dangerouslyReplaceNodeWithMarkup};module.exports=ReactComponentBrowserEnvironment},{"./DOMChildrenOperations":39,"./ReactDOMIDOperations":68}],59:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");var injected=false;var ReactComponentEnvironment={replaceNodeWithMarkup:null,processChildrenUpdates:null,injection:{injectEnvironment:function(environment){!!injected?process.env.NODE_ENV!=="production"?invariant(false,"ReactCompositeComponent: injectEnvironment() can only be called once."):_prodInvariant("104"):void 0;ReactComponentEnvironment.replaceNodeWithMarkup=environment.replaceNodeWithMarkup;ReactComponentEnvironment.processChildrenUpdates=environment.processChildrenUpdates;injected=true}}};module.exports=ReactComponentEnvironment}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],60:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var React=require("react/lib/React");var ReactComponentEnvironment=require("./ReactComponentEnvironment");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var ReactErrorUtils=require("./ReactErrorUtils");var ReactInstanceMap=require("./ReactInstanceMap");var ReactInstrumentation=require("./ReactInstrumentation");var ReactNodeTypes=require("./ReactNodeTypes");var ReactReconciler=require("./ReactReconciler");if(process.env.NODE_ENV!=="production"){var checkReactTypeSpec=require("./checkReactTypeSpec")}var emptyObject=require("fbjs/lib/emptyObject");var invariant=require("fbjs/lib/invariant");var shallowEqual=require("fbjs/lib/shallowEqual");var shouldUpdateReactComponent=require("./shouldUpdateReactComponent");var warning=require("fbjs/lib/warning");var CompositeTypes={ImpureClass:0,PureClass:1,StatelessFunctional:2};function StatelessComponent(Component){}StatelessComponent.prototype.render=function(){var Component=ReactInstanceMap.get(this)._currentElement.type;var element=Component(this.props,this.context,this.updater);warnIfInvalidElement(Component,element);return element};function warnIfInvalidElement(Component,element){if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(element===null||element===false||React.isValidElement(element),"%s(...): A valid React element (or null) must be returned. You may have "+"returned undefined, an array or some other invalid object.",Component.displayName||Component.name||"Component"):void 0;process.env.NODE_ENV!=="production"?warning(!Component.childContextTypes,"%s(...): childContextTypes cannot be defined on a functional component.",Component.displayName||Component.name||"Component"):void 0}}function shouldConstruct(Component){return!!(Component.prototype&&Component.prototype.isReactComponent)}function isPureComponent(Component){return!!(Component.prototype&&Component.prototype.isPureReactComponent)}function measureLifeCyclePerf(fn,debugID,timerType){if(debugID===0){return fn()}ReactInstrumentation.debugTool.onBeginLifeCycleTimer(debugID,timerType);try{return fn()}finally{ReactInstrumentation.debugTool.onEndLifeCycleTimer(debugID,timerType)}}var nextMountID=1;var ReactCompositeComponent={construct:function(element){this._currentElement=element;this._rootNodeID=0;this._compositeType=null;this._instance=null;this._hostParent=null;this._hostContainerInfo=null;this._updateBatchNumber=null;this._pendingElement=null;this._pendingStateQueue=null;this._pendingReplaceState=false;this._pendingForceUpdate=false;this._renderedNodeType=null;this._renderedComponent=null;this._context=null;this._mountOrder=0;this._topLevelWrapper=null;this._pendingCallbacks=null;this._calledComponentWillUnmount=false;if(process.env.NODE_ENV!=="production"){this._warnedAboutRefsInRender=false}},mountComponent:function(transaction,hostParent,hostContainerInfo,context){var _this=this;this._context=context;this._mountOrder=nextMountID++;this._hostParent=hostParent;this._hostContainerInfo=hostContainerInfo;var publicProps=this._currentElement.props;var publicContext=this._processContext(context);var Component=this._currentElement.type;var updateQueue=transaction.getUpdateQueue();var doConstruct=shouldConstruct(Component);var inst=this._constructComponent(doConstruct,publicProps,publicContext,updateQueue);var renderedElement;if(!doConstruct&&(inst==null||inst.render==null)){renderedElement=inst;warnIfInvalidElement(Component,renderedElement);!(inst===null||inst===false||React.isValidElement(inst))?process.env.NODE_ENV!=="production"?invariant(false,"%s(...): A valid React element (or null) must be returned. You may have returned undefined, an array or some other invalid object.",Component.displayName||Component.name||"Component"):_prodInvariant("105",Component.displayName||Component.name||"Component"):void 0;inst=new StatelessComponent(Component);this._compositeType=CompositeTypes.StatelessFunctional}else{if(isPureComponent(Component)){this._compositeType=CompositeTypes.PureClass}else{this._compositeType=CompositeTypes.ImpureClass}}if(process.env.NODE_ENV!=="production"){if(inst.render==null){process.env.NODE_ENV!=="production"?warning(false,"%s(...): No `render` method found on the returned component "+"instance: you may have forgotten to define `render`.",Component.displayName||Component.name||"Component"):void 0}var propsMutated=inst.props!==publicProps;var componentName=Component.displayName||Component.name||"Component";process.env.NODE_ENV!=="production"?warning(inst.props===undefined||!propsMutated,"%s(...): When calling super() in `%s`, make sure to pass "+"up the same props that your component's constructor was passed.",componentName,componentName):void 0}inst.props=publicProps;inst.context=publicContext;inst.refs=emptyObject;inst.updater=updateQueue;this._instance=inst;ReactInstanceMap.set(inst,this);if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(!inst.getInitialState||inst.getInitialState.isReactClassApproved||inst.state,"getInitialState was defined on %s, a plain JavaScript class. "+"This is only supported for classes created using React.createClass. "+"Did you mean to define a state property instead?",this.getName()||"a component"):void 0;process.env.NODE_ENV!=="production"?warning(!inst.getDefaultProps||inst.getDefaultProps.isReactClassApproved,"getDefaultProps was defined on %s, a plain JavaScript class. "+"This is only supported for classes created using React.createClass. "+"Use a static property to define defaultProps instead.",this.getName()||"a component"):void 0;process.env.NODE_ENV!=="production"?warning(!inst.propTypes,"propTypes was defined as an instance property on %s. Use a static "+"property to define propTypes instead.",this.getName()||"a component"):void 0;process.env.NODE_ENV!=="production"?warning(!inst.contextTypes,"contextTypes was defined as an instance property on %s. Use a "+"static property to define contextTypes instead.",this.getName()||"a component"):void 0;process.env.NODE_ENV!=="production"?warning(typeof inst.componentShouldUpdate!=="function","%s has a method called "+"componentShouldUpdate(). Did you mean shouldComponentUpdate()? "+"The name is phrased as a question because the function is "+"expected to return a value.",this.getName()||"A component"):void 0;process.env.NODE_ENV!=="production"?warning(typeof inst.componentDidUnmount!=="function","%s has a method called "+"componentDidUnmount(). But there is no such lifecycle method. "+"Did you mean componentWillUnmount()?",this.getName()||"A component"):void 0;process.env.NODE_ENV!=="production"?warning(typeof inst.componentWillRecieveProps!=="function","%s has a method called "+"componentWillRecieveProps(). Did you mean componentWillReceiveProps()?",this.getName()||"A component"):void 0}var initialState=inst.state;if(initialState===undefined){inst.state=initialState=null}!(typeof initialState==="object"&&!Array.isArray(initialState))?process.env.NODE_ENV!=="production"?invariant(false,"%s.state: must be set to an object or null",this.getName()||"ReactCompositeComponent"):_prodInvariant("106",this.getName()||"ReactCompositeComponent"):void 0;this._pendingStateQueue=null;this._pendingReplaceState=false;this._pendingForceUpdate=false;var markup;if(inst.unstable_handleError){markup=this.performInitialMountWithErrorHandling(renderedElement,hostParent,hostContainerInfo,transaction,context)}else{markup=this.performInitialMount(renderedElement,hostParent,hostContainerInfo,transaction,context)}if(inst.componentDidMount){if(process.env.NODE_ENV!=="production"){transaction.getReactMountReady().enqueue(function(){measureLifeCyclePerf(function(){return inst.componentDidMount()},_this._debugID,"componentDidMount")})}else{transaction.getReactMountReady().enqueue(inst.componentDidMount,inst)}}return markup},_constructComponent:function(doConstruct,publicProps,publicContext,updateQueue){if(process.env.NODE_ENV!=="production"){ReactCurrentOwner.current=this;try{return this._constructComponentWithoutOwner(doConstruct,publicProps,publicContext,updateQueue)}finally{ReactCurrentOwner.current=null}}else{return this._constructComponentWithoutOwner(doConstruct,publicProps,publicContext,updateQueue)}},_constructComponentWithoutOwner:function(doConstruct,publicProps,publicContext,updateQueue){var Component=this._currentElement.type;if(doConstruct){if(process.env.NODE_ENV!=="production"){return measureLifeCyclePerf(function(){return new Component(publicProps,publicContext,updateQueue)},this._debugID,"ctor")}else{return new Component(publicProps,publicContext,updateQueue)}}if(process.env.NODE_ENV!=="production"){return measureLifeCyclePerf(function(){return Component(publicProps,publicContext,updateQueue)},this._debugID,"render")}else{return Component(publicProps,publicContext,updateQueue)}},performInitialMountWithErrorHandling:function(renderedElement,hostParent,hostContainerInfo,transaction,context){var markup;var checkpoint=transaction.checkpoint();try{markup=this.performInitialMount(renderedElement,hostParent,hostContainerInfo,transaction,context)}catch(e){transaction.rollback(checkpoint);this._instance.unstable_handleError(e);if(this._pendingStateQueue){this._instance.state=this._processPendingState(this._instance.props,this._instance.context)}checkpoint=transaction.checkpoint();this._renderedComponent.unmountComponent(true);transaction.rollback(checkpoint);markup=this.performInitialMount(renderedElement,hostParent,hostContainerInfo,transaction,context)}return markup},performInitialMount:function(renderedElement,hostParent,hostContainerInfo,transaction,context){var inst=this._instance;var debugID=0;if(process.env.NODE_ENV!=="production"){debugID=this._debugID}if(inst.componentWillMount){if(process.env.NODE_ENV!=="production"){measureLifeCyclePerf(function(){return inst.componentWillMount()},debugID,"componentWillMount")}else{inst.componentWillMount()}if(this._pendingStateQueue){inst.state=this._processPendingState(inst.props,inst.context)}}if(renderedElement===undefined){renderedElement=this._renderValidatedComponent()}var nodeType=ReactNodeTypes.getType(renderedElement);this._renderedNodeType=nodeType;var child=this._instantiateReactComponent(renderedElement,nodeType!==ReactNodeTypes.EMPTY);this._renderedComponent=child;var markup=ReactReconciler.mountComponent(child,transaction,hostParent,hostContainerInfo,this._processChildContext(context),debugID);if(process.env.NODE_ENV!=="production"){if(debugID!==0){var childDebugIDs=child._debugID!==0?[child._debugID]:[];ReactInstrumentation.debugTool.onSetChildren(debugID,childDebugIDs)}}return markup},getHostNode:function(){return ReactReconciler.getHostNode(this._renderedComponent)},unmountComponent:function(safely){if(!this._renderedComponent){return}var inst=this._instance;if(inst.componentWillUnmount&&!inst._calledComponentWillUnmount){inst._calledComponentWillUnmount=true;if(safely){var name=this.getName()+".componentWillUnmount()";ReactErrorUtils.invokeGuardedCallback(name,inst.componentWillUnmount.bind(inst))}else{if(process.env.NODE_ENV!=="production"){measureLifeCyclePerf(function(){return inst.componentWillUnmount()},this._debugID,"componentWillUnmount")}else{inst.componentWillUnmount()}}}if(this._renderedComponent){ReactReconciler.unmountComponent(this._renderedComponent,safely);this._renderedNodeType=null;this._renderedComponent=null;this._instance=null}this._pendingStateQueue=null;this._pendingReplaceState=false;this._pendingForceUpdate=false;this._pendingCallbacks=null;this._pendingElement=null;this._context=null;this._rootNodeID=0;this._topLevelWrapper=null;ReactInstanceMap.remove(inst)},_maskContext:function(context){var Component=this._currentElement.type;var contextTypes=Component.contextTypes;if(!contextTypes){return emptyObject}var maskedContext={};for(var contextName in contextTypes){maskedContext[contextName]=context[contextName]}return maskedContext},_processContext:function(context){var maskedContext=this._maskContext(context);if(process.env.NODE_ENV!=="production"){var Component=this._currentElement.type;if(Component.contextTypes){this._checkContextTypes(Component.contextTypes,maskedContext,"context")}}return maskedContext},_processChildContext:function(currentContext){var Component=this._currentElement.type;var inst=this._instance;var childContext;if(inst.getChildContext){if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onBeginProcessingChildContext();try{childContext=inst.getChildContext()}finally{ReactInstrumentation.debugTool.onEndProcessingChildContext()}}else{childContext=inst.getChildContext()}}if(childContext){!(typeof Component.childContextTypes==="object")?process.env.NODE_ENV!=="production"?invariant(false,"%s.getChildContext(): childContextTypes must be defined in order to use getChildContext().",this.getName()||"ReactCompositeComponent"):_prodInvariant("107",this.getName()||"ReactCompositeComponent"):void 0;if(process.env.NODE_ENV!=="production"){this._checkContextTypes(Component.childContextTypes,childContext,"child context")}for(var name in childContext){!(name in Component.childContextTypes)?process.env.NODE_ENV!=="production"?invariant(false,'%s.getChildContext(): key "%s" is not defined in childContextTypes.',this.getName()||"ReactCompositeComponent",name):_prodInvariant("108",this.getName()||"ReactCompositeComponent",name):void 0}return _assign({},currentContext,childContext)}return currentContext},_checkContextTypes:function(typeSpecs,values,location){if(process.env.NODE_ENV!=="production"){checkReactTypeSpec(typeSpecs,values,location,this.getName(),null,this._debugID)}},receiveComponent:function(nextElement,transaction,nextContext){var prevElement=this._currentElement;var prevContext=this._context;this._pendingElement=null;this.updateComponent(transaction,prevElement,nextElement,prevContext,nextContext)},performUpdateIfNecessary:function(transaction){if(this._pendingElement!=null){ReactReconciler.receiveComponent(this,this._pendingElement,transaction,this._context)}else if(this._pendingStateQueue!==null||this._pendingForceUpdate){this.updateComponent(transaction,this._currentElement,this._currentElement,this._context,this._context)}else{this._updateBatchNumber=null}},updateComponent:function(transaction,prevParentElement,nextParentElement,prevUnmaskedContext,nextUnmaskedContext){var inst=this._instance;!(inst!=null)?process.env.NODE_ENV!=="production"?invariant(false,"Attempted to update component `%s` that has already been unmounted (or failed to mount).",this.getName()||"ReactCompositeComponent"):_prodInvariant("136",this.getName()||"ReactCompositeComponent"):void 0;var willReceive=false;var nextContext;if(this._context===nextUnmaskedContext){nextContext=inst.context}else{nextContext=this._processContext(nextUnmaskedContext);willReceive=true}var prevProps=prevParentElement.props;var nextProps=nextParentElement.props;if(prevParentElement!==nextParentElement){willReceive=true}if(willReceive&&inst.componentWillReceiveProps){if(process.env.NODE_ENV!=="production"){measureLifeCyclePerf(function(){return inst.componentWillReceiveProps(nextProps,nextContext)},this._debugID,"componentWillReceiveProps")}else{inst.componentWillReceiveProps(nextProps,nextContext)}}var nextState=this._processPendingState(nextProps,nextContext);var shouldUpdate=true;if(!this._pendingForceUpdate){if(inst.shouldComponentUpdate){if(process.env.NODE_ENV!=="production"){shouldUpdate=measureLifeCyclePerf(function(){return inst.shouldComponentUpdate(nextProps,nextState,nextContext)},this._debugID,"shouldComponentUpdate")}else{shouldUpdate=inst.shouldComponentUpdate(nextProps,nextState,nextContext)}}else{if(this._compositeType===CompositeTypes.PureClass){shouldUpdate=!shallowEqual(prevProps,nextProps)||!shallowEqual(inst.state,nextState)}}}if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(shouldUpdate!==undefined,"%s.shouldComponentUpdate(): Returned undefined instead of a "+"boolean value. Make sure to return true or false.",this.getName()||"ReactCompositeComponent"):void 0}this._updateBatchNumber=null;if(shouldUpdate){this._pendingForceUpdate=false;this._performComponentUpdate(nextParentElement,nextProps,nextState,nextContext,transaction,nextUnmaskedContext)}else{this._currentElement=nextParentElement;this._context=nextUnmaskedContext;inst.props=nextProps;inst.state=nextState;inst.context=nextContext}},_processPendingState:function(props,context){var inst=this._instance;var queue=this._pendingStateQueue;var replace=this._pendingReplaceState;this._pendingReplaceState=false;this._pendingStateQueue=null;if(!queue){return inst.state}if(replace&&queue.length===1){return queue[0]}var nextState=_assign({},replace?queue[0]:inst.state);for(var i=replace?1:0;i<queue.length;i++){var partial=queue[i];_assign(nextState,typeof partial==="function"?partial.call(inst,nextState,props,context):partial)}return nextState},_performComponentUpdate:function(nextElement,nextProps,nextState,nextContext,transaction,unmaskedContext){var _this2=this;var inst=this._instance;var hasComponentDidUpdate=Boolean(inst.componentDidUpdate);var prevProps;var prevState;var prevContext;if(hasComponentDidUpdate){prevProps=inst.props;prevState=inst.state;prevContext=inst.context}if(inst.componentWillUpdate){if(process.env.NODE_ENV!=="production"){measureLifeCyclePerf(function(){return inst.componentWillUpdate(nextProps,nextState,nextContext)},this._debugID,"componentWillUpdate")}else{inst.componentWillUpdate(nextProps,nextState,nextContext)}}this._currentElement=nextElement;this._context=unmaskedContext;inst.props=nextProps;inst.state=nextState;inst.context=nextContext;this._updateRenderedComponent(transaction,unmaskedContext);if(hasComponentDidUpdate){if(process.env.NODE_ENV!=="production"){transaction.getReactMountReady().enqueue(function(){measureLifeCyclePerf(inst.componentDidUpdate.bind(inst,prevProps,prevState,prevContext),_this2._debugID,"componentDidUpdate")})}else{transaction.getReactMountReady().enqueue(inst.componentDidUpdate.bind(inst,prevProps,prevState,prevContext),inst)}}},_updateRenderedComponent:function(transaction,context){var prevComponentInstance=this._renderedComponent;var prevRenderedElement=prevComponentInstance._currentElement;var nextRenderedElement=this._renderValidatedComponent();var debugID=0;if(process.env.NODE_ENV!=="production"){debugID=this._debugID}if(shouldUpdateReactComponent(prevRenderedElement,nextRenderedElement)){ReactReconciler.receiveComponent(prevComponentInstance,nextRenderedElement,transaction,this._processChildContext(context))}else{var oldHostNode=ReactReconciler.getHostNode(prevComponentInstance);ReactReconciler.unmountComponent(prevComponentInstance,false);var nodeType=ReactNodeTypes.getType(nextRenderedElement);this._renderedNodeType=nodeType;var child=this._instantiateReactComponent(nextRenderedElement,nodeType!==ReactNodeTypes.EMPTY);this._renderedComponent=child;var nextMarkup=ReactReconciler.mountComponent(child,transaction,this._hostParent,this._hostContainerInfo,this._processChildContext(context),debugID);if(process.env.NODE_ENV!=="production"){if(debugID!==0){var childDebugIDs=child._debugID!==0?[child._debugID]:[];ReactInstrumentation.debugTool.onSetChildren(debugID,childDebugIDs)}}this._replaceNodeWithMarkup(oldHostNode,nextMarkup,prevComponentInstance)}},_replaceNodeWithMarkup:function(oldHostNode,nextMarkup,prevInstance){ReactComponentEnvironment.replaceNodeWithMarkup(oldHostNode,nextMarkup,prevInstance)},_renderValidatedComponentWithoutOwnerOrContext:function(){var inst=this._instance;var renderedElement;if(process.env.NODE_ENV!=="production"){renderedElement=measureLifeCyclePerf(function(){return inst.render()},this._debugID,"render")}else{renderedElement=inst.render()}if(process.env.NODE_ENV!=="production"){if(renderedElement===undefined&&inst.render._isMockFunction){renderedElement=null}}return renderedElement},_renderValidatedComponent:function(){var renderedElement;if(process.env.NODE_ENV!=="production"||this._compositeType!==CompositeTypes.StatelessFunctional){ReactCurrentOwner.current=this;try{renderedElement=this._renderValidatedComponentWithoutOwnerOrContext()}finally{ReactCurrentOwner.current=null}}else{renderedElement=this._renderValidatedComponentWithoutOwnerOrContext()}!(renderedElement===null||renderedElement===false||React.isValidElement(renderedElement))?process.env.NODE_ENV!=="production"?invariant(false,"%s.render(): A valid React element (or null) must be returned. You may have returned undefined, an array or some other invalid object.",this.getName()||"ReactCompositeComponent"):_prodInvariant("109",this.getName()||"ReactCompositeComponent"):void 0;return renderedElement},attachRef:function(ref,component){var inst=this.getPublicInstance();!(inst!=null)?process.env.NODE_ENV!=="production"?invariant(false,"Stateless function components cannot have refs."):_prodInvariant("110"):void 0;var publicComponentInstance=component.getPublicInstance();if(process.env.NODE_ENV!=="production"){var componentName=component&&component.getName?component.getName():"a component";process.env.NODE_ENV!=="production"?warning(publicComponentInstance!=null||component._compositeType!==CompositeTypes.StatelessFunctional,"Stateless function components cannot be given refs "+'(See ref "%s" in %s created by %s). '+"Attempts to access this ref will fail.",ref,componentName,this.getName()):void 0}var refs=inst.refs===emptyObject?inst.refs={}:inst.refs;refs[ref]=publicComponentInstance},detachRef:function(ref){var refs=this.getPublicInstance().refs;delete refs[ref]},getName:function(){var type=this._currentElement.type;var constructor=this._instance&&this._instance.constructor;return type.displayName||constructor&&constructor.displayName||type.name||constructor&&constructor.name||null},getPublicInstance:function(){var inst=this._instance;if(this._compositeType===CompositeTypes.StatelessFunctional){return null}return inst},_instantiateReactComponent:null};module.exports=ReactCompositeComponent}).call(this,require("_process"))},{"./ReactComponentEnvironment":59,"./ReactErrorUtils":84,"./ReactInstanceMap":92,"./ReactInstrumentation":93,"./ReactNodeTypes":98,"./ReactReconciler":103,"./checkReactTypeSpec":130,"./reactProdInvariant":151,"./shouldUpdateReactComponent":155,_process:184,"fbjs/lib/emptyObject":11,"fbjs/lib/invariant":18,"fbjs/lib/shallowEqual":24,"fbjs/lib/warning":25,"object-assign":26,"react/lib/React":160,"react/lib/ReactCurrentOwner":164}],61:[function(require,module,exports){(function(process){"use strict";var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDefaultInjection=require("./ReactDefaultInjection");var ReactMount=require("./ReactMount");var ReactReconciler=require("./ReactReconciler");var ReactUpdates=require("./ReactUpdates");var ReactVersion=require("./ReactVersion");var findDOMNode=require("./findDOMNode");var getHostComponentFromComposite=require("./getHostComponentFromComposite");var renderSubtreeIntoContainer=require("./renderSubtreeIntoContainer");var warning=require("fbjs/lib/warning");ReactDefaultInjection.inject();var ReactDOM={findDOMNode:findDOMNode,render:ReactMount.render,unmountComponentAtNode:ReactMount.unmountComponentAtNode,version:ReactVersion,unstable_batchedUpdates:ReactUpdates.batchedUpdates,unstable_renderSubtreeIntoContainer:renderSubtreeIntoContainer};if(typeof __REACT_DEVTOOLS_GLOBAL_HOOK__!=="undefined"&&typeof __REACT_DEVTOOLS_GLOBAL_HOOK__.inject==="function"){__REACT_DEVTOOLS_GLOBAL_HOOK__.inject({ComponentTree:{getClosestInstanceFromNode:ReactDOMComponentTree.getClosestInstanceFromNode,getNodeFromInstance:function(inst){if(inst._renderedComponent){inst=getHostComponentFromComposite(inst)}if(inst){return ReactDOMComponentTree.getNodeFromInstance(inst)}else{return null}}},Mount:ReactMount,Reconciler:ReactReconciler})}if(process.env.NODE_ENV!=="production"){var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");if(ExecutionEnvironment.canUseDOM&&window.top===window.self){if(typeof __REACT_DEVTOOLS_GLOBAL_HOOK__==="undefined"){if(navigator.userAgent.indexOf("Chrome")>-1&&navigator.userAgent.indexOf("Edge")===-1||navigator.userAgent.indexOf("Firefox")>-1){var showFileUrlMessage=window.location.protocol.indexOf("http")===-1&&navigator.userAgent.indexOf("Firefox")===-1;console.debug("Download the React DevTools "+(showFileUrlMessage?"and use an HTTP server (instead of a file: URL) ":"")+"for a better development experience: "+"https://fb.me/react-devtools")}}var testFunc=function testFn(){};process.env.NODE_ENV!=="production"?warning((testFunc.name||testFunc.toString()).indexOf("testFn")!==-1,"It looks like you're using a minified copy of the development build "+"of React. When deploying React apps to production, make sure to use "+"the production build which skips development warnings and is faster. "+"See https://fb.me/react-minification for more details."):void 0;var ieCompatibilityMode=document.documentMode&&document.documentMode<8;process.env.NODE_ENV!=="production"?warning(!ieCompatibilityMode,"Internet Explorer is running in compatibility mode; please add the "+"following tag to your HTML to prevent this from happening: "+'<meta http-equiv="X-UA-Compatible" content="IE=edge" />'):void 0;var expectedFeatures=[Array.isArray,Array.prototype.every,Array.prototype.forEach,Array.prototype.indexOf,Array.prototype.map,Date.now,Function.prototype.bind,Object.keys,String.prototype.trim];for(var i=0;i<expectedFeatures.length;i++){if(!expectedFeatures[i]){process.env.NODE_ENV!=="production"?warning(false,"One or more ES5 shims expected by React are not available: "+"https://fb.me/react-warning-polyfills"):void 0;break}}}}if(process.env.NODE_ENV!=="production"){var ReactInstrumentation=require("./ReactInstrumentation");var ReactDOMUnknownPropertyHook=require("./ReactDOMUnknownPropertyHook");var ReactDOMNullInputValuePropHook=require("./ReactDOMNullInputValuePropHook");var ReactDOMInvalidARIAHook=require("./ReactDOMInvalidARIAHook");ReactInstrumentation.debugTool.addHook(ReactDOMUnknownPropertyHook);ReactInstrumentation.debugTool.addHook(ReactDOMNullInputValuePropHook);ReactInstrumentation.debugTool.addHook(ReactDOMInvalidARIAHook)}module.exports=ReactDOM}).call(this,require("_process"))},{"./ReactDOMComponentTree":64,"./ReactDOMInvalidARIAHook":70,"./ReactDOMNullInputValuePropHook":71,"./ReactDOMUnknownPropertyHook":78,"./ReactDefaultInjection":81,"./ReactInstrumentation":93,"./ReactMount":96,"./ReactReconciler":103,"./ReactUpdates":108,"./ReactVersion":109,"./findDOMNode":134,"./getHostComponentFromComposite":141,"./renderSubtreeIntoContainer":152,_process:184,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/warning":25}],62:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var AutoFocusUtils=require("./AutoFocusUtils");var CSSPropertyOperations=require("./CSSPropertyOperations");var DOMLazyTree=require("./DOMLazyTree");var DOMNamespaces=require("./DOMNamespaces");var DOMProperty=require("./DOMProperty");var DOMPropertyOperations=require("./DOMPropertyOperations");var EventPluginHub=require("./EventPluginHub");var EventPluginRegistry=require("./EventPluginRegistry");var ReactBrowserEventEmitter=require("./ReactBrowserEventEmitter");var ReactDOMComponentFlags=require("./ReactDOMComponentFlags");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMInput=require("./ReactDOMInput");var ReactDOMOption=require("./ReactDOMOption");var ReactDOMSelect=require("./ReactDOMSelect");var ReactDOMTextarea=require("./ReactDOMTextarea");var ReactInstrumentation=require("./ReactInstrumentation");var ReactMultiChild=require("./ReactMultiChild");var ReactServerRenderingTransaction=require("./ReactServerRenderingTransaction");var emptyFunction=require("fbjs/lib/emptyFunction");var escapeTextContentForBrowser=require("./escapeTextContentForBrowser");var invariant=require("fbjs/lib/invariant");var isEventSupported=require("./isEventSupported");var shallowEqual=require("fbjs/lib/shallowEqual");var inputValueTracking=require("./inputValueTracking");var validateDOMNesting=require("./validateDOMNesting");var warning=require("fbjs/lib/warning");var Flags=ReactDOMComponentFlags;var deleteListener=EventPluginHub.deleteListener;var getNode=ReactDOMComponentTree.getNodeFromInstance;var listenTo=ReactBrowserEventEmitter.listenTo;var registrationNameModules=EventPluginRegistry.registrationNameModules;var CONTENT_TYPES={string:true,number:true};var STYLE="style";var HTML="__html";var RESERVED_PROPS={children:null,dangerouslySetInnerHTML:null,suppressContentEditableWarning:null};var DOC_FRAGMENT_TYPE=11;function getDeclarationErrorAddendum(internalInstance){if(internalInstance){var owner=internalInstance._currentElement._owner||null;if(owner){var name=owner.getName();if(name){return" This DOM node was rendered by `"+name+"`."}}}return""}function friendlyStringify(obj){if(typeof obj==="object"){if(Array.isArray(obj)){return"["+obj.map(friendlyStringify).join(", ")+"]"}else{var pairs=[];for(var key in obj){if(Object.prototype.hasOwnProperty.call(obj,key)){var keyEscaped=/^[a-z$_][\w$_]*$/i.test(key)?key:JSON.stringify(key);pairs.push(keyEscaped+": "+friendlyStringify(obj[key]))}}return"{"+pairs.join(", ")+"}"}}else if(typeof obj==="string"){return JSON.stringify(obj)}else if(typeof obj==="function"){return"[function object]"}return String(obj)}var styleMutationWarning={};function checkAndWarnForMutatedStyle(style1,style2,component){if(style1==null||style2==null){return}if(shallowEqual(style1,style2)){return}var componentName=component._tag;var owner=component._currentElement._owner;var ownerName;if(owner){ownerName=owner.getName()}var hash=ownerName+"|"+componentName;if(styleMutationWarning.hasOwnProperty(hash)){return}styleMutationWarning[hash]=true;process.env.NODE_ENV!=="production"?warning(false,"`%s` was passed a style object that has previously been mutated. "+"Mutating `style` is deprecated. Consider cloning it beforehand. Check "+"the `render` %s. Previous style: %s. Mutated style: %s.",componentName,owner?"of `"+ownerName+"`":"using <"+componentName+">",friendlyStringify(style1),friendlyStringify(style2)):void 0}function assertValidProps(component,props){if(!props){return}if(voidElementTags[component._tag]){!(props.children==null&&props.dangerouslySetInnerHTML==null)?process.env.NODE_ENV!=="production"?invariant(false,"%s is a void element tag and must neither have `children` nor use `dangerouslySetInnerHTML`.%s",component._tag,component._currentElement._owner?" Check the render method of "+component._currentElement._owner.getName()+".":""):_prodInvariant("137",component._tag,component._currentElement._owner?" Check the render method of "+component._currentElement._owner.getName()+".":""):void 0}if(props.dangerouslySetInnerHTML!=null){!(props.children==null)?process.env.NODE_ENV!=="production"?invariant(false,"Can only set one of `children` or `props.dangerouslySetInnerHTML`."):_prodInvariant("60"):void 0;!(typeof props.dangerouslySetInnerHTML==="object"&&HTML in props.dangerouslySetInnerHTML)?process.env.NODE_ENV!=="production"?invariant(false,"`props.dangerouslySetInnerHTML` must be in the form `{__html: ...}`. Please visit https://fb.me/react-invariant-dangerously-set-inner-html for more information."):_prodInvariant("61"):void 0}if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(props.innerHTML==null,"Directly setting property `innerHTML` is not permitted. "+"For more information, lookup documentation on `dangerouslySetInnerHTML`."):void 0;process.env.NODE_ENV!=="production"?warning(props.suppressContentEditableWarning||!props.contentEditable||props.children==null,"A component is `contentEditable` and contains `children` managed by "+"React. It is now your responsibility to guarantee that none of "+"those nodes are unexpectedly modified or duplicated. This is "+"probably not intentional."):void 0;process.env.NODE_ENV!=="production"?warning(props.onFocusIn==null&&props.onFocusOut==null,"React uses onFocus and onBlur instead of onFocusIn and onFocusOut. "+"All React events are normalized to bubble, so onFocusIn and onFocusOut "+"are not needed/supported by React."):void 0}!(props.style==null||typeof props.style==="object")?process.env.NODE_ENV!=="production"?invariant(false,"The `style` prop expects a mapping from style properties to values, not a string. For example, style={{marginRight: spacing + 'em'}} when using JSX.%s",getDeclarationErrorAddendum(component)):_prodInvariant("62",getDeclarationErrorAddendum(component)):void 0}function enqueuePutListener(inst,registrationName,listener,transaction){if(transaction instanceof ReactServerRenderingTransaction){return}if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(registrationName!=="onScroll"||isEventSupported("scroll",true),"This browser doesn't support the `onScroll` event"):void 0}var containerInfo=inst._hostContainerInfo;var isDocumentFragment=containerInfo._node&&containerInfo._node.nodeType===DOC_FRAGMENT_TYPE;var doc=isDocumentFragment?containerInfo._node:containerInfo._ownerDocument;listenTo(registrationName,doc);transaction.getReactMountReady().enqueue(putListener,{inst:inst,registrationName:registrationName,listener:listener})}function putListener(){var listenerToPut=this;EventPluginHub.putListener(listenerToPut.inst,listenerToPut.registrationName,listenerToPut.listener)}function inputPostMount(){var inst=this;ReactDOMInput.postMountWrapper(inst)}function textareaPostMount(){var inst=this;ReactDOMTextarea.postMountWrapper(inst)}function optionPostMount(){var inst=this;ReactDOMOption.postMountWrapper(inst)}var setAndValidateContentChildDev=emptyFunction;if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev=function(content){var hasExistingContent=this._contentDebugID!=null;var debugID=this._debugID;var contentDebugID=-debugID;if(content==null){if(hasExistingContent){ReactInstrumentation.debugTool.onUnmountComponent(this._contentDebugID)}this._contentDebugID=null;return}validateDOMNesting(null,String(content),this,this._ancestorInfo);this._contentDebugID=contentDebugID;if(hasExistingContent){ReactInstrumentation.debugTool.onBeforeUpdateComponent(contentDebugID,content);ReactInstrumentation.debugTool.onUpdateComponent(contentDebugID)}else{ReactInstrumentation.debugTool.onBeforeMountComponent(contentDebugID,content,debugID);ReactInstrumentation.debugTool.onMountComponent(contentDebugID);ReactInstrumentation.debugTool.onSetChildren(debugID,[contentDebugID])}}}var mediaEvents={topAbort:"abort",topCanPlay:"canplay",topCanPlayThrough:"canplaythrough",topDurationChange:"durationchange",topEmptied:"emptied",topEncrypted:"encrypted",topEnded:"ended",topError:"error",topLoadedData:"loadeddata",topLoadedMetadata:"loadedmetadata",topLoadStart:"loadstart",topPause:"pause",topPlay:"play",topPlaying:"playing",topProgress:"progress",topRateChange:"ratechange",topSeeked:"seeked",topSeeking:"seeking",topStalled:"stalled",topSuspend:"suspend",topTimeUpdate:"timeupdate",topVolumeChange:"volumechange",topWaiting:"waiting"};function trackInputValue(){inputValueTracking.track(this)}function trapBubbledEventsLocal(){var inst=this;!inst._rootNodeID?process.env.NODE_ENV!=="production"?invariant(false,"Must be mounted to trap events"):_prodInvariant("63"):void 0;var node=getNode(inst);!node?process.env.NODE_ENV!=="production"?invariant(false,"trapBubbledEvent(...): Requires node to be rendered."):_prodInvariant("64"):void 0;switch(inst._tag){case"iframe":case"object":inst._wrapperState.listeners=[ReactBrowserEventEmitter.trapBubbledEvent("topLoad","load",node)];break;case"video":case"audio":inst._wrapperState.listeners=[];for(var event in mediaEvents){if(mediaEvents.hasOwnProperty(event)){inst._wrapperState.listeners.push(ReactBrowserEventEmitter.trapBubbledEvent(event,mediaEvents[event],node))}}break;case"source":inst._wrapperState.listeners=[ReactBrowserEventEmitter.trapBubbledEvent("topError","error",node)];break;case"img":inst._wrapperState.listeners=[ReactBrowserEventEmitter.trapBubbledEvent("topError","error",node),ReactBrowserEventEmitter.trapBubbledEvent("topLoad","load",node)];break;case"form":inst._wrapperState.listeners=[ReactBrowserEventEmitter.trapBubbledEvent("topReset","reset",node),ReactBrowserEventEmitter.trapBubbledEvent("topSubmit","submit",node)];break;case"input":case"select":case"textarea":inst._wrapperState.listeners=[ReactBrowserEventEmitter.trapBubbledEvent("topInvalid","invalid",node)];break}}function postUpdateSelectWrapper(){ReactDOMSelect.postUpdateWrapper(this)}var omittedCloseTags={area:true,base:true,br:true,col:true,embed:true,hr:true,img:true,input:true,keygen:true,link:true,meta:true,param:true,source:true,track:true,wbr:true};var newlineEatingTags={listing:true,pre:true,textarea:true};var voidElementTags=_assign({menuitem:true},omittedCloseTags);var VALID_TAG_REGEX=/^[a-zA-Z][a-zA-Z:_\.\-\d]*$/;var validatedTagCache={};var hasOwnProperty={}.hasOwnProperty;function validateDangerousTag(tag){if(!hasOwnProperty.call(validatedTagCache,tag)){!VALID_TAG_REGEX.test(tag)?process.env.NODE_ENV!=="production"?invariant(false,"Invalid tag: %s",tag):_prodInvariant("65",tag):void 0;validatedTagCache[tag]=true}}function isCustomComponent(tagName,props){return tagName.indexOf("-")>=0||props.is!=null}var globalIdCounter=1;function ReactDOMComponent(element){var tag=element.type;validateDangerousTag(tag);this._currentElement=element;this._tag=tag.toLowerCase();this._namespaceURI=null;this._renderedChildren=null;this._previousStyle=null;this._previousStyleCopy=null;this._hostNode=null;this._hostParent=null;this._rootNodeID=0;this._domID=0;this._hostContainerInfo=null;this._wrapperState=null;this._topLevelWrapper=null;this._flags=0;if(process.env.NODE_ENV!=="production"){this._ancestorInfo=null;setAndValidateContentChildDev.call(this,null)}}ReactDOMComponent.displayName="ReactDOMComponent";ReactDOMComponent.Mixin={mountComponent:function(transaction,hostParent,hostContainerInfo,context){this._rootNodeID=globalIdCounter++;this._domID=hostContainerInfo._idCounter++;this._hostParent=hostParent;this._hostContainerInfo=hostContainerInfo;var props=this._currentElement.props;switch(this._tag){case"audio":case"form":case"iframe":case"img":case"link":case"object":case"source":case"video":this._wrapperState={listeners:null};transaction.getReactMountReady().enqueue(trapBubbledEventsLocal,this);break;case"input":ReactDOMInput.mountWrapper(this,props,hostParent);props=ReactDOMInput.getHostProps(this,props);transaction.getReactMountReady().enqueue(trackInputValue,this);transaction.getReactMountReady().enqueue(trapBubbledEventsLocal,this);break;case"option":ReactDOMOption.mountWrapper(this,props,hostParent);props=ReactDOMOption.getHostProps(this,props);break;case"select":ReactDOMSelect.mountWrapper(this,props,hostParent);props=ReactDOMSelect.getHostProps(this,props);transaction.getReactMountReady().enqueue(trapBubbledEventsLocal,this);break;case"textarea":ReactDOMTextarea.mountWrapper(this,props,hostParent);props=ReactDOMTextarea.getHostProps(this,props);transaction.getReactMountReady().enqueue(trackInputValue,this);transaction.getReactMountReady().enqueue(trapBubbledEventsLocal,this);break}assertValidProps(this,props);var namespaceURI;var parentTag;if(hostParent!=null){namespaceURI=hostParent._namespaceURI;parentTag=hostParent._tag}else if(hostContainerInfo._tag){namespaceURI=hostContainerInfo._namespaceURI;parentTag=hostContainerInfo._tag}if(namespaceURI==null||namespaceURI===DOMNamespaces.svg&&parentTag==="foreignobject"){namespaceURI=DOMNamespaces.html}if(namespaceURI===DOMNamespaces.html){if(this._tag==="svg"){namespaceURI=DOMNamespaces.svg}else if(this._tag==="math"){namespaceURI=DOMNamespaces.mathml}}this._namespaceURI=namespaceURI;if(process.env.NODE_ENV!=="production"){var parentInfo;if(hostParent!=null){parentInfo=hostParent._ancestorInfo}else if(hostContainerInfo._tag){parentInfo=hostContainerInfo._ancestorInfo}if(parentInfo){validateDOMNesting(this._tag,null,this,parentInfo)}this._ancestorInfo=validateDOMNesting.updatedAncestorInfo(parentInfo,this._tag,this)}var mountImage;if(transaction.useCreateElement){var ownerDocument=hostContainerInfo._ownerDocument;var el;if(namespaceURI===DOMNamespaces.html){if(this._tag==="script"){var div=ownerDocument.createElement("div");var type=this._currentElement.type;div.innerHTML="<"+type+"></"+type+">";el=div.removeChild(div.firstChild)}else if(props.is){el=ownerDocument.createElement(this._currentElement.type,props.is)}else{el=ownerDocument.createElement(this._currentElement.type)}}else{el=ownerDocument.createElementNS(namespaceURI,this._currentElement.type)}ReactDOMComponentTree.precacheNode(this,el);this._flags|=Flags.hasCachedChildNodes;if(!this._hostParent){DOMPropertyOperations.setAttributeForRoot(el)}this._updateDOMProperties(null,props,transaction);var lazyTree=DOMLazyTree(el);this._createInitialChildren(transaction,props,context,lazyTree);mountImage=lazyTree}else{var tagOpen=this._createOpenTagMarkupAndPutListeners(transaction,props);var tagContent=this._createContentMarkup(transaction,props,context);if(!tagContent&&omittedCloseTags[this._tag]){mountImage=tagOpen+"/>"}else{mountImage=tagOpen+">"+tagContent+"</"+this._currentElement.type+">"}}switch(this._tag){case"input":transaction.getReactMountReady().enqueue(inputPostMount,this);if(props.autoFocus){transaction.getReactMountReady().enqueue(AutoFocusUtils.focusDOMComponent,this)}break;case"textarea":transaction.getReactMountReady().enqueue(textareaPostMount,this);if(props.autoFocus){transaction.getReactMountReady().enqueue(AutoFocusUtils.focusDOMComponent,this)}break;case"select":if(props.autoFocus){transaction.getReactMountReady().enqueue(AutoFocusUtils.focusDOMComponent,this)}break;case"button":if(props.autoFocus){transaction.getReactMountReady().enqueue(AutoFocusUtils.focusDOMComponent,this)}break;case"option":transaction.getReactMountReady().enqueue(optionPostMount,this);break}return mountImage},_createOpenTagMarkupAndPutListeners:function(transaction,props){var ret="<"+this._currentElement.type;for(var propKey in props){if(!props.hasOwnProperty(propKey)){continue}var propValue=props[propKey];if(propValue==null){continue}if(registrationNameModules.hasOwnProperty(propKey)){if(propValue){enqueuePutListener(this,propKey,propValue,transaction)}}else{if(propKey===STYLE){if(propValue){if(process.env.NODE_ENV!=="production"){this._previousStyle=propValue}propValue=this._previousStyleCopy=_assign({},props.style)}propValue=CSSPropertyOperations.createMarkupForStyles(propValue,this)}var markup=null;if(this._tag!=null&&isCustomComponent(this._tag,props)){if(!RESERVED_PROPS.hasOwnProperty(propKey)){markup=DOMPropertyOperations.createMarkupForCustomAttribute(propKey,propValue)}}else{markup=DOMPropertyOperations.createMarkupForProperty(propKey,propValue)}if(markup){ret+=" "+markup}}}if(transaction.renderToStaticMarkup){return ret}if(!this._hostParent){ret+=" "+DOMPropertyOperations.createMarkupForRoot()}ret+=" "+DOMPropertyOperations.createMarkupForID(this._domID);return ret},_createContentMarkup:function(transaction,props,context){var ret="";var innerHTML=props.dangerouslySetInnerHTML;if(innerHTML!=null){if(innerHTML.__html!=null){ret=innerHTML.__html}}else{var contentToUse=CONTENT_TYPES[typeof props.children]?props.children:null;var childrenToUse=contentToUse!=null?null:props.children;if(contentToUse!=null){ret=escapeTextContentForBrowser(contentToUse);if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev.call(this,contentToUse)}}else if(childrenToUse!=null){var mountImages=this.mountChildren(childrenToUse,transaction,context);ret=mountImages.join("")}}if(newlineEatingTags[this._tag]&&ret.charAt(0)==="\n"){return"\n"+ret}else{return ret}},_createInitialChildren:function(transaction,props,context,lazyTree){var innerHTML=props.dangerouslySetInnerHTML;if(innerHTML!=null){if(innerHTML.__html!=null){DOMLazyTree.queueHTML(lazyTree,innerHTML.__html)}}else{var contentToUse=CONTENT_TYPES[typeof props.children]?props.children:null;var childrenToUse=contentToUse!=null?null:props.children;if(contentToUse!=null){if(contentToUse!==""){if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev.call(this,contentToUse)}DOMLazyTree.queueText(lazyTree,contentToUse)}}else if(childrenToUse!=null){var mountImages=this.mountChildren(childrenToUse,transaction,context);for(var i=0;i<mountImages.length;i++){DOMLazyTree.queueChild(lazyTree,mountImages[i])}}}},receiveComponent:function(nextElement,transaction,context){var prevElement=this._currentElement;this._currentElement=nextElement;this.updateComponent(transaction,prevElement,nextElement,context)},updateComponent:function(transaction,prevElement,nextElement,context){var lastProps=prevElement.props;var nextProps=this._currentElement.props;switch(this._tag){case"input":lastProps=ReactDOMInput.getHostProps(this,lastProps);nextProps=ReactDOMInput.getHostProps(this,nextProps);break;case"option":lastProps=ReactDOMOption.getHostProps(this,lastProps);nextProps=ReactDOMOption.getHostProps(this,nextProps);break;case"select":lastProps=ReactDOMSelect.getHostProps(this,lastProps);nextProps=ReactDOMSelect.getHostProps(this,nextProps);break;case"textarea":lastProps=ReactDOMTextarea.getHostProps(this,lastProps);nextProps=ReactDOMTextarea.getHostProps(this,nextProps);break}assertValidProps(this,nextProps);this._updateDOMProperties(lastProps,nextProps,transaction);this._updateDOMChildren(lastProps,nextProps,transaction,context);switch(this._tag){case"input":ReactDOMInput.updateWrapper(this);break;case"textarea":ReactDOMTextarea.updateWrapper(this);break;case"select":transaction.getReactMountReady().enqueue(postUpdateSelectWrapper,this);break}},_updateDOMProperties:function(lastProps,nextProps,transaction){var propKey;var styleName;var styleUpdates;for(propKey in lastProps){if(nextProps.hasOwnProperty(propKey)||!lastProps.hasOwnProperty(propKey)||lastProps[propKey]==null){continue}if(propKey===STYLE){var lastStyle=this._previousStyleCopy;for(styleName in lastStyle){if(lastStyle.hasOwnProperty(styleName)){styleUpdates=styleUpdates||{};styleUpdates[styleName]=""}}this._previousStyleCopy=null}else if(registrationNameModules.hasOwnProperty(propKey)){if(lastProps[propKey]){deleteListener(this,propKey)}}else if(isCustomComponent(this._tag,lastProps)){if(!RESERVED_PROPS.hasOwnProperty(propKey)){DOMPropertyOperations.deleteValueForAttribute(getNode(this),propKey)}}else if(DOMProperty.properties[propKey]||DOMProperty.isCustomAttribute(propKey)){DOMPropertyOperations.deleteValueForProperty(getNode(this),propKey)}}for(propKey in nextProps){var nextProp=nextProps[propKey];var lastProp=propKey===STYLE?this._previousStyleCopy:lastProps!=null?lastProps[propKey]:undefined;if(!nextProps.hasOwnProperty(propKey)||nextProp===lastProp||nextProp==null&&lastProp==null){continue}if(propKey===STYLE){if(nextProp){if(process.env.NODE_ENV!=="production"){checkAndWarnForMutatedStyle(this._previousStyleCopy,this._previousStyle,this);this._previousStyle=nextProp}nextProp=this._previousStyleCopy=_assign({},nextProp)}else{this._previousStyleCopy=null}if(lastProp){for(styleName in lastProp){if(lastProp.hasOwnProperty(styleName)&&(!nextProp||!nextProp.hasOwnProperty(styleName))){styleUpdates=styleUpdates||{};styleUpdates[styleName]=""}}for(styleName in nextProp){if(nextProp.hasOwnProperty(styleName)&&lastProp[styleName]!==nextProp[styleName]){styleUpdates=styleUpdates||{};styleUpdates[styleName]=nextProp[styleName]}}}else{styleUpdates=nextProp}}else if(registrationNameModules.hasOwnProperty(propKey)){if(nextProp){enqueuePutListener(this,propKey,nextProp,transaction)}else if(lastProp){deleteListener(this,propKey)}}else if(isCustomComponent(this._tag,nextProps)){if(!RESERVED_PROPS.hasOwnProperty(propKey)){DOMPropertyOperations.setValueForAttribute(getNode(this),propKey,nextProp)}}else if(DOMProperty.properties[propKey]||DOMProperty.isCustomAttribute(propKey)){var node=getNode(this);if(nextProp!=null){DOMPropertyOperations.setValueForProperty(node,propKey,nextProp)}else{DOMPropertyOperations.deleteValueForProperty(node,propKey)}}}if(styleUpdates){CSSPropertyOperations.setValueForStyles(getNode(this),styleUpdates,this)}},_updateDOMChildren:function(lastProps,nextProps,transaction,context){var lastContent=CONTENT_TYPES[typeof lastProps.children]?lastProps.children:null;var nextContent=CONTENT_TYPES[typeof nextProps.children]?nextProps.children:null;var lastHtml=lastProps.dangerouslySetInnerHTML&&lastProps.dangerouslySetInnerHTML.__html;var nextHtml=nextProps.dangerouslySetInnerHTML&&nextProps.dangerouslySetInnerHTML.__html;var lastChildren=lastContent!=null?null:lastProps.children;var nextChildren=nextContent!=null?null:nextProps.children;var lastHasContentOrHtml=lastContent!=null||lastHtml!=null;var nextHasContentOrHtml=nextContent!=null||nextHtml!=null;if(lastChildren!=null&&nextChildren==null){this.updateChildren(null,transaction,context)}else if(lastHasContentOrHtml&&!nextHasContentOrHtml){this.updateTextContent("");if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onSetChildren(this._debugID,[])}}if(nextContent!=null){if(lastContent!==nextContent){this.updateTextContent(""+nextContent);if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev.call(this,nextContent)}}}else if(nextHtml!=null){if(lastHtml!==nextHtml){this.updateMarkup(""+nextHtml)}if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onSetChildren(this._debugID,[])}}else if(nextChildren!=null){if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev.call(this,null)}this.updateChildren(nextChildren,transaction,context)}},getHostNode:function(){return getNode(this)},unmountComponent:function(safely){switch(this._tag){case"audio":case"form":case"iframe":case"img":case"link":case"object":case"source":case"video":var listeners=this._wrapperState.listeners;if(listeners){for(var i=0;i<listeners.length;i++){listeners[i].remove()}}break;case"input":case"textarea":inputValueTracking.stopTracking(this);break;case"html":case"head":case"body":!false?process.env.NODE_ENV!=="production"?invariant(false,"<%s> tried to unmount. Because of cross-browser quirks it is impossible to unmount some top-level components (eg <html>, <head>, and <body>) reliably and efficiently. To fix this, have a single top-level component that never unmounts render these elements.",this._tag):_prodInvariant("66",this._tag):void 0;break}this.unmountChildren(safely);ReactDOMComponentTree.uncacheNode(this);EventPluginHub.deleteAllListeners(this);this._rootNodeID=0;this._domID=0;this._wrapperState=null;if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev.call(this,null)}},getPublicInstance:function(){return getNode(this)}};_assign(ReactDOMComponent.prototype,ReactDOMComponent.Mixin,ReactMultiChild.Mixin);module.exports=ReactDOMComponent}).call(this,require("_process"))},{"./AutoFocusUtils":33,"./CSSPropertyOperations":36,"./DOMLazyTree":40,"./DOMNamespaces":41,"./DOMProperty":42,"./DOMPropertyOperations":43,"./EventPluginHub":47,"./EventPluginRegistry":48,"./ReactBrowserEventEmitter":56,"./ReactDOMComponentFlags":63,"./ReactDOMComponentTree":64,"./ReactDOMInput":69,"./ReactDOMOption":72,"./ReactDOMSelect":73,"./ReactDOMTextarea":76,"./ReactInstrumentation":93,"./ReactMultiChild":97,"./ReactServerRenderingTransaction":105,"./escapeTextContentForBrowser":133,"./inputValueTracking":146,"./isEventSupported":148,"./reactProdInvariant":151,"./validateDOMNesting":157,_process:184,"fbjs/lib/emptyFunction":10,"fbjs/lib/invariant":18,"fbjs/lib/shallowEqual":24,"fbjs/lib/warning":25,"object-assign":26}],63:[function(require,module,exports){"use strict";var ReactDOMComponentFlags={hasCachedChildNodes:1<<0};module.exports=ReactDOMComponentFlags},{}],64:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var DOMProperty=require("./DOMProperty");var ReactDOMComponentFlags=require("./ReactDOMComponentFlags");var invariant=require("fbjs/lib/invariant");var ATTR_NAME=DOMProperty.ID_ATTRIBUTE_NAME;var Flags=ReactDOMComponentFlags;var internalInstanceKey="__reactInternalInstance$"+Math.random().toString(36).slice(2);function shouldPrecacheNode(node,nodeID){return node.nodeType===1&&node.getAttribute(ATTR_NAME)===String(nodeID)||node.nodeType===8&&node.nodeValue===" react-text: "+nodeID+" "||node.nodeType===8&&node.nodeValue===" react-empty: "+nodeID+" "}function getRenderedHostOrTextFromComponent(component){var rendered;while(rendered=component._renderedComponent){component=rendered}return component}function precacheNode(inst,node){var hostInst=getRenderedHostOrTextFromComponent(inst);hostInst._hostNode=node;node[internalInstanceKey]=hostInst}function uncacheNode(inst){var node=inst._hostNode;if(node){delete node[internalInstanceKey];inst._hostNode=null}}function precacheChildNodes(inst,node){if(inst._flags&Flags.hasCachedChildNodes){return}var children=inst._renderedChildren;var childNode=node.firstChild;outer:for(var name in children){if(!children.hasOwnProperty(name)){continue}var childInst=children[name];var childID=getRenderedHostOrTextFromComponent(childInst)._domID;if(childID===0){continue}for(;childNode!==null;childNode=childNode.nextSibling){if(shouldPrecacheNode(childNode,childID)){precacheNode(childInst,childNode);continue outer}}!false?process.env.NODE_ENV!=="production"?invariant(false,"Unable to find element with ID %s.",childID):_prodInvariant("32",childID):void 0}inst._flags|=Flags.hasCachedChildNodes}function getClosestInstanceFromNode(node){if(node[internalInstanceKey]){return node[internalInstanceKey]}var parents=[];while(!node[internalInstanceKey]){parents.push(node);if(node.parentNode){node=node.parentNode}else{return null}}var closest;var inst;for(;node&&(inst=node[internalInstanceKey]);node=parents.pop()){closest=inst;if(parents.length){precacheChildNodes(inst,node)}}return closest}function getInstanceFromNode(node){var inst=getClosestInstanceFromNode(node);if(inst!=null&&inst._hostNode===node){return inst}else{return null}}function getNodeFromInstance(inst){!(inst._hostNode!==undefined)?process.env.NODE_ENV!=="production"?invariant(false,"getNodeFromInstance: Invalid argument."):_prodInvariant("33"):void 0;if(inst._hostNode){return inst._hostNode}var parents=[];while(!inst._hostNode){parents.push(inst);!inst._hostParent?process.env.NODE_ENV!=="production"?invariant(false,"React DOM tree root should always have a node reference."):_prodInvariant("34"):void 0;inst=inst._hostParent}for(;parents.length;inst=parents.pop()){precacheChildNodes(inst,inst._hostNode)}return inst._hostNode}var ReactDOMComponentTree={getClosestInstanceFromNode:getClosestInstanceFromNode,getInstanceFromNode:getInstanceFromNode,getNodeFromInstance:getNodeFromInstance,precacheChildNodes:precacheChildNodes,precacheNode:precacheNode,uncacheNode:uncacheNode};module.exports=ReactDOMComponentTree}).call(this,require("_process"))},{"./DOMProperty":42,"./ReactDOMComponentFlags":63,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],65:[function(require,module,exports){(function(process){"use strict";var validateDOMNesting=require("./validateDOMNesting");var DOC_NODE_TYPE=9;function ReactDOMContainerInfo(topLevelWrapper,node){var info={_topLevelWrapper:topLevelWrapper,_idCounter:1,_ownerDocument:node?node.nodeType===DOC_NODE_TYPE?node:node.ownerDocument:null,_node:node,_tag:node?node.nodeName.toLowerCase():null,_namespaceURI:node?node.namespaceURI:null};if(process.env.NODE_ENV!=="production"){info._ancestorInfo=node?validateDOMNesting.updatedAncestorInfo(null,info._tag,null):null}return info}module.exports=ReactDOMContainerInfo}).call(this,require("_process"))},{"./validateDOMNesting":157,_process:184}],66:[function(require,module,exports){"use strict";var _assign=require("object-assign");var DOMLazyTree=require("./DOMLazyTree");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMEmptyComponent=function(instantiate){this._currentElement=null;this._hostNode=null;this._hostParent=null;this._hostContainerInfo=null;this._domID=0};_assign(ReactDOMEmptyComponent.prototype,{mountComponent:function(transaction,hostParent,hostContainerInfo,context){var domID=hostContainerInfo._idCounter++;this._domID=domID;this._hostParent=hostParent;this._hostContainerInfo=hostContainerInfo;var nodeValue=" react-empty: "+this._domID+" ";if(transaction.useCreateElement){var ownerDocument=hostContainerInfo._ownerDocument;var node=ownerDocument.createComment(nodeValue);ReactDOMComponentTree.precacheNode(this,node);return DOMLazyTree(node)}else{if(transaction.renderToStaticMarkup){return""}return"\x3c!--"+nodeValue+"--\x3e"}},receiveComponent:function(){},getHostNode:function(){return ReactDOMComponentTree.getNodeFromInstance(this)},unmountComponent:function(){ReactDOMComponentTree.uncacheNode(this)}});module.exports=ReactDOMEmptyComponent},{"./DOMLazyTree":40,"./ReactDOMComponentTree":64,"object-assign":26}],67:[function(require,module,exports){"use strict";var ReactDOMFeatureFlags={useCreateElement:true,useFiber:false};module.exports=ReactDOMFeatureFlags},{}],68:[function(require,module,exports){"use strict";var DOMChildrenOperations=require("./DOMChildrenOperations");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMIDOperations={dangerouslyProcessChildrenUpdates:function(parentInst,updates){var node=ReactDOMComponentTree.getNodeFromInstance(parentInst);DOMChildrenOperations.processUpdates(node,updates)}};module.exports=ReactDOMIDOperations},{"./DOMChildrenOperations":39,"./ReactDOMComponentTree":64}],69:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var DOMPropertyOperations=require("./DOMPropertyOperations");var LinkedValueUtils=require("./LinkedValueUtils");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactUpdates=require("./ReactUpdates");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var didWarnValueLink=false;var didWarnCheckedLink=false;var didWarnValueDefaultValue=false;var didWarnCheckedDefaultChecked=false;var didWarnControlledToUncontrolled=false;var didWarnUncontrolledToControlled=false;function forceUpdateIfMounted(){if(this._rootNodeID){ReactDOMInput.updateWrapper(this)}}function isControlled(props){var usesChecked=props.type==="checkbox"||props.type==="radio";return usesChecked?props.checked!=null:props.value!=null}var ReactDOMInput={getHostProps:function(inst,props){var value=LinkedValueUtils.getValue(props);var checked=LinkedValueUtils.getChecked(props);var hostProps=_assign({type:undefined,step:undefined,min:undefined,max:undefined},props,{defaultChecked:undefined,defaultValue:undefined,value:value!=null?value:inst._wrapperState.initialValue,checked:checked!=null?checked:inst._wrapperState.initialChecked,onChange:inst._wrapperState.onChange});return hostProps},mountWrapper:function(inst,props){if(process.env.NODE_ENV!=="production"){LinkedValueUtils.checkPropTypes("input",props,inst._currentElement._owner);var owner=inst._currentElement._owner;if(props.valueLink!==undefined&&!didWarnValueLink){process.env.NODE_ENV!=="production"?warning(false,"`valueLink` prop on `input` is deprecated; set `value` and `onChange` instead."):void 0;didWarnValueLink=true}if(props.checkedLink!==undefined&&!didWarnCheckedLink){process.env.NODE_ENV!=="production"?warning(false,"`checkedLink` prop on `input` is deprecated; set `value` and `onChange` instead."):void 0;didWarnCheckedLink=true}if(props.checked!==undefined&&props.defaultChecked!==undefined&&!didWarnCheckedDefaultChecked){process.env.NODE_ENV!=="production"?warning(false,"%s contains an input of type %s with both checked and defaultChecked props. "+"Input elements must be either controlled or uncontrolled "+"(specify either the checked prop, or the defaultChecked prop, but not "+"both). Decide between using a controlled or uncontrolled input "+"element and remove one of these props. More info: "+"https://fb.me/react-controlled-components",owner&&owner.getName()||"A component",props.type):void 0;didWarnCheckedDefaultChecked=true}if(props.value!==undefined&&props.defaultValue!==undefined&&!didWarnValueDefaultValue){process.env.NODE_ENV!=="production"?warning(false,"%s contains an input of type %s with both value and defaultValue props. "+"Input elements must be either controlled or uncontrolled "+"(specify either the value prop, or the defaultValue prop, but not "+"both). Decide between using a controlled or uncontrolled input "+"element and remove one of these props. More info: "+"https://fb.me/react-controlled-components",owner&&owner.getName()||"A component",props.type):void 0;didWarnValueDefaultValue=true}}var defaultValue=props.defaultValue;inst._wrapperState={initialChecked:props.checked!=null?props.checked:props.defaultChecked,initialValue:props.value!=null?props.value:defaultValue,listeners:null,onChange:_handleChange.bind(inst),controlled:isControlled(props)}},updateWrapper:function(inst){var props=inst._currentElement.props;if(process.env.NODE_ENV!=="production"){var controlled=isControlled(props);var owner=inst._currentElement._owner;if(!inst._wrapperState.controlled&&controlled&&!didWarnUncontrolledToControlled){process.env.NODE_ENV!=="production"?warning(false,"%s is changing an uncontrolled input of type %s to be controlled. "+"Input elements should not switch from uncontrolled to controlled (or vice versa). "+"Decide between using a controlled or uncontrolled input "+"element for the lifetime of the component. More info: https://fb.me/react-controlled-components",owner&&owner.getName()||"A component",props.type):void 0;didWarnUncontrolledToControlled=true}if(inst._wrapperState.controlled&&!controlled&&!didWarnControlledToUncontrolled){process.env.NODE_ENV!=="production"?warning(false,"%s is changing a controlled input of type %s to be uncontrolled. "+"Input elements should not switch from controlled to uncontrolled (or vice versa). "+"Decide between using a controlled or uncontrolled input "+"element for the lifetime of the component. More info: https://fb.me/react-controlled-components",owner&&owner.getName()||"A component",props.type):void 0;didWarnControlledToUncontrolled=true}}var checked=props.checked;if(checked!=null){DOMPropertyOperations.setValueForProperty(ReactDOMComponentTree.getNodeFromInstance(inst),"checked",checked||false)}var node=ReactDOMComponentTree.getNodeFromInstance(inst);var value=LinkedValueUtils.getValue(props);if(value!=null){if(value===0&&node.value===""){node.value="0"}else if(props.type==="number"){var valueAsNumber=parseFloat(node.value,10)||0;if(value!=valueAsNumber||value==valueAsNumber&&node.value!=value){node.value=""+value}}else if(node.value!==""+value){node.value=""+value}}else{if(props.value==null&&props.defaultValue!=null){if(node.defaultValue!==""+props.defaultValue){node.defaultValue=""+props.defaultValue}}if(props.checked==null&&props.defaultChecked!=null){node.defaultChecked=!!props.defaultChecked}}},postMountWrapper:function(inst){var props=inst._currentElement.props;var node=ReactDOMComponentTree.getNodeFromInstance(inst);switch(props.type){case"submit":case"reset":break;case"color":case"date":case"datetime":case"datetime-local":case"month":case"time":case"week":node.value="";node.value=node.defaultValue;break;default:node.value=node.value;break}var name=node.name;if(name!==""){node.name=""}node.defaultChecked=!node.defaultChecked;node.defaultChecked=!node.defaultChecked;if(name!==""){node.name=name}}};function _handleChange(event){var props=this._currentElement.props;var returnValue=LinkedValueUtils.executeOnChange(props,event);ReactUpdates.asap(forceUpdateIfMounted,this);var name=props.name;if(props.type==="radio"&&name!=null){var rootNode=ReactDOMComponentTree.getNodeFromInstance(this);var queryRoot=rootNode;while(queryRoot.parentNode){queryRoot=queryRoot.parentNode}var group=queryRoot.querySelectorAll("input[name="+JSON.stringify(""+name)+'][type="radio"]');for(var i=0;i<group.length;i++){var otherNode=group[i];if(otherNode===rootNode||otherNode.form!==rootNode.form){continue}var otherInstance=ReactDOMComponentTree.getInstanceFromNode(otherNode);!otherInstance?process.env.NODE_ENV!=="production"?invariant(false,"ReactDOMInput: Mixing React and non-React radio inputs with the same `name` is not supported."):_prodInvariant("90"):void 0;ReactUpdates.asap(forceUpdateIfMounted,otherInstance)}}return returnValue}module.exports=ReactDOMInput}).call(this,require("_process"))},{"./DOMPropertyOperations":43,"./LinkedValueUtils":54,"./ReactDOMComponentTree":64,"./ReactUpdates":108,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"object-assign":26}],70:[function(require,module,exports){(function(process){"use strict";var DOMProperty=require("./DOMProperty");var ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook");var warning=require("fbjs/lib/warning");var warnedProperties={};var rARIA=new RegExp("^(aria)-["+DOMProperty.ATTRIBUTE_NAME_CHAR+"]*$");function validateProperty(tagName,name,debugID){if(warnedProperties.hasOwnProperty(name)&&warnedProperties[name]){return true}if(rARIA.test(name)){var lowerCasedName=name.toLowerCase();var standardName=DOMProperty.getPossibleStandardName.hasOwnProperty(lowerCasedName)?DOMProperty.getPossibleStandardName[lowerCasedName]:null;if(standardName==null){warnedProperties[name]=true;return false}if(name!==standardName){process.env.NODE_ENV!=="production"?warning(false,"Unknown ARIA attribute %s. Did you mean %s?%s",name,standardName,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0;warnedProperties[name]=true;return true}}return true}function warnInvalidARIAProps(debugID,element){var invalidProps=[];for(var key in element.props){var isValid=validateProperty(element.type,key,debugID);if(!isValid){invalidProps.push(key)}}var unknownPropString=invalidProps.map(function(prop){return"`"+prop+"`"}).join(", ");if(invalidProps.length===1){process.env.NODE_ENV!=="production"?warning(false,"Invalid aria prop %s on <%s> tag. "+"For details, see https://fb.me/invalid-aria-prop%s",unknownPropString,element.type,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0}else if(invalidProps.length>1){process.env.NODE_ENV!=="production"?warning(false,"Invalid aria props %s on <%s> tag. "+"For details, see https://fb.me/invalid-aria-prop%s",unknownPropString,element.type,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0}}function handleElement(debugID,element){if(element==null||typeof element.type!=="string"){return}if(element.type.indexOf("-")>=0||element.props.is){return}warnInvalidARIAProps(debugID,element)}var ReactDOMInvalidARIAHook={onBeforeMountComponent:function(debugID,element){if(process.env.NODE_ENV!=="production"){handleElement(debugID,element)}},onBeforeUpdateComponent:function(debugID,element){if(process.env.NODE_ENV!=="production"){handleElement(debugID,element)}}};module.exports=ReactDOMInvalidARIAHook}).call(this,require("_process"))},{"./DOMProperty":42,_process:184,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],71:[function(require,module,exports){(function(process){"use strict";var ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook");var warning=require("fbjs/lib/warning");var didWarnValueNull=false;function handleElement(debugID,element){if(element==null){return}if(element.type!=="input"&&element.type!=="textarea"&&element.type!=="select"){return}if(element.props!=null&&element.props.value===null&&!didWarnValueNull){process.env.NODE_ENV!=="production"?warning(false,"`value` prop on `%s` should not be null. "+"Consider using the empty string to clear the component or `undefined` "+"for uncontrolled components.%s",element.type,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0;didWarnValueNull=true}}var ReactDOMNullInputValuePropHook={onBeforeMountComponent:function(debugID,element){handleElement(debugID,element)},onBeforeUpdateComponent:function(debugID,element){handleElement(debugID,element)}};module.exports=ReactDOMNullInputValuePropHook}).call(this,require("_process"))},{_process:184,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],72:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var React=require("react/lib/React");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMSelect=require("./ReactDOMSelect");var warning=require("fbjs/lib/warning");var didWarnInvalidOptionChildren=false;function flattenChildren(children){var content="";React.Children.forEach(children,function(child){if(child==null){return}if(typeof child==="string"||typeof child==="number"){content+=child}else if(!didWarnInvalidOptionChildren){didWarnInvalidOptionChildren=true;process.env.NODE_ENV!=="production"?warning(false,"Only strings and numbers are supported as <option> children."):void 0}});return content}var ReactDOMOption={mountWrapper:function(inst,props,hostParent){if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(props.selected==null,"Use the `defaultValue` or `value` props on <select> instead of "+"setting `selected` on <option>."):void 0}var selectValue=null;if(hostParent!=null){var selectParent=hostParent;if(selectParent._tag==="optgroup"){selectParent=selectParent._hostParent}if(selectParent!=null&&selectParent._tag==="select"){selectValue=ReactDOMSelect.getSelectValueContext(selectParent)}}var selected=null;if(selectValue!=null){var value;if(props.value!=null){value=props.value+""}else{value=flattenChildren(props.children)}selected=false;if(Array.isArray(selectValue)){for(var i=0;i<selectValue.length;i++){if(""+selectValue[i]===value){selected=true;break}}}else{selected=""+selectValue===value}}inst._wrapperState={selected:selected}},postMountWrapper:function(inst){var props=inst._currentElement.props;if(props.value!=null){var node=ReactDOMComponentTree.getNodeFromInstance(inst);node.setAttribute("value",props.value)}},getHostProps:function(inst,props){var hostProps=_assign({selected:undefined,children:undefined},props);if(inst._wrapperState.selected!=null){hostProps.selected=inst._wrapperState.selected}var content=flattenChildren(props.children);if(content){hostProps.children=content}return hostProps}};module.exports=ReactDOMOption}).call(this,require("_process"))},{"./ReactDOMComponentTree":64,"./ReactDOMSelect":73,_process:184,"fbjs/lib/warning":25,"object-assign":26,"react/lib/React":160}],73:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var LinkedValueUtils=require("./LinkedValueUtils");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactUpdates=require("./ReactUpdates");var warning=require("fbjs/lib/warning");var didWarnValueLink=false;var didWarnValueDefaultValue=false;function updateOptionsIfPendingUpdateAndMounted(){if(this._rootNodeID&&this._wrapperState.pendingUpdate){this._wrapperState.pendingUpdate=false;var props=this._currentElement.props;var value=LinkedValueUtils.getValue(props);if(value!=null){updateOptions(this,Boolean(props.multiple),value)}}}function getDeclarationErrorAddendum(owner){if(owner){var name=owner.getName();if(name){return" Check the render method of `"+name+"`."}}return""}var valuePropNames=["value","defaultValue"];function checkSelectPropTypes(inst,props){var owner=inst._currentElement._owner;LinkedValueUtils.checkPropTypes("select",props,owner);if(props.valueLink!==undefined&&!didWarnValueLink){process.env.NODE_ENV!=="production"?warning(false,"`valueLink` prop on `select` is deprecated; set `value` and `onChange` instead."):void 0;didWarnValueLink=true}for(var i=0;i<valuePropNames.length;i++){var propName=valuePropNames[i];if(props[propName]==null){continue}var isArray=Array.isArray(props[propName]);if(props.multiple&&!isArray){process.env.NODE_ENV!=="production"?warning(false,"The `%s` prop supplied to <select> must be an array if "+"`multiple` is true.%s",propName,getDeclarationErrorAddendum(owner)):void 0}else if(!props.multiple&&isArray){process.env.NODE_ENV!=="production"?warning(false,"The `%s` prop supplied to <select> must be a scalar "+"value if `multiple` is false.%s",propName,getDeclarationErrorAddendum(owner)):void 0}}}function updateOptions(inst,multiple,propValue){var selectedValue,i;var options=ReactDOMComponentTree.getNodeFromInstance(inst).options;if(multiple){selectedValue={};for(i=0;i<propValue.length;i++){selectedValue[""+propValue[i]]=true}for(i=0;i<options.length;i++){var selected=selectedValue.hasOwnProperty(options[i].value);if(options[i].selected!==selected){options[i].selected=selected}}}else{selectedValue=""+propValue;for(i=0;i<options.length;i++){if(options[i].value===selectedValue){options[i].selected=true;return}}if(options.length){options[0].selected=true}}}var ReactDOMSelect={getHostProps:function(inst,props){return _assign({},props,{onChange:inst._wrapperState.onChange,value:undefined})},mountWrapper:function(inst,props){if(process.env.NODE_ENV!=="production"){checkSelectPropTypes(inst,props)}var value=LinkedValueUtils.getValue(props);inst._wrapperState={pendingUpdate:false,initialValue:value!=null?value:props.defaultValue,listeners:null,onChange:_handleChange.bind(inst),wasMultiple:Boolean(props.multiple)};if(props.value!==undefined&&props.defaultValue!==undefined&&!didWarnValueDefaultValue){process.env.NODE_ENV!=="production"?warning(false,"Select elements must be either controlled or uncontrolled "+"(specify either the value prop, or the defaultValue prop, but not "+"both). Decide between using a controlled or uncontrolled select "+"element and remove one of these props. More info: "+"https://fb.me/react-controlled-components"):void 0;didWarnValueDefaultValue=true}},getSelectValueContext:function(inst){return inst._wrapperState.initialValue},postUpdateWrapper:function(inst){var props=inst._currentElement.props;inst._wrapperState.initialValue=undefined;var wasMultiple=inst._wrapperState.wasMultiple;inst._wrapperState.wasMultiple=Boolean(props.multiple);var value=LinkedValueUtils.getValue(props);if(value!=null){inst._wrapperState.pendingUpdate=false;updateOptions(inst,Boolean(props.multiple),value)}else if(wasMultiple!==Boolean(props.multiple)){if(props.defaultValue!=null){updateOptions(inst,Boolean(props.multiple),props.defaultValue)}else{updateOptions(inst,Boolean(props.multiple),props.multiple?[]:"")}}}};function _handleChange(event){var props=this._currentElement.props;var returnValue=LinkedValueUtils.executeOnChange(props,event);if(this._rootNodeID){this._wrapperState.pendingUpdate=true}ReactUpdates.asap(updateOptionsIfPendingUpdateAndMounted,this);return returnValue}module.exports=ReactDOMSelect}).call(this,require("_process"))},{"./LinkedValueUtils":54,"./ReactDOMComponentTree":64,"./ReactUpdates":108,_process:184,"fbjs/lib/warning":25,"object-assign":26}],74:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var getNodeForCharacterOffset=require("./getNodeForCharacterOffset");var getTextContentAccessor=require("./getTextContentAccessor");function isCollapsed(anchorNode,anchorOffset,focusNode,focusOffset){return anchorNode===focusNode&&anchorOffset===focusOffset}function getIEOffsets(node){var selection=document.selection;var selectedRange=selection.createRange();var selectedLength=selectedRange.text.length;var fromStart=selectedRange.duplicate();fromStart.moveToElementText(node);fromStart.setEndPoint("EndToStart",selectedRange);var startOffset=fromStart.text.length;var endOffset=startOffset+selectedLength;return{start:startOffset,end:endOffset}}function getModernOffsets(node){var selection=window.getSelection&&window.getSelection();if(!selection||selection.rangeCount===0){return null}var anchorNode=selection.anchorNode;var anchorOffset=selection.anchorOffset;var focusNode=selection.focusNode;var focusOffset=selection.focusOffset;var currentRange=selection.getRangeAt(0);try{currentRange.startContainer.nodeType;currentRange.endContainer.nodeType}catch(e){return null}var isSelectionCollapsed=isCollapsed(selection.anchorNode,selection.anchorOffset,selection.focusNode,selection.focusOffset);var rangeLength=isSelectionCollapsed?0:currentRange.toString().length;var tempRange=currentRange.cloneRange();tempRange.selectNodeContents(node);tempRange.setEnd(currentRange.startContainer,currentRange.startOffset);var isTempRangeCollapsed=isCollapsed(tempRange.startContainer,tempRange.startOffset,tempRange.endContainer,tempRange.endOffset);var start=isTempRangeCollapsed?0:tempRange.toString().length;var end=start+rangeLength;var detectionRange=document.createRange();detectionRange.setStart(anchorNode,anchorOffset);detectionRange.setEnd(focusNode,focusOffset);var isBackward=detectionRange.collapsed;return{start:isBackward?end:start,end:isBackward?start:end}}function setIEOffsets(node,offsets){var range=document.selection.createRange().duplicate();var start,end;if(offsets.end===undefined){start=offsets.start;end=start}else if(offsets.start>offsets.end){start=offsets.end;end=offsets.start}else{start=offsets.start;end=offsets.end}range.moveToElementText(node);range.moveStart("character",start);range.setEndPoint("EndToStart",range);range.moveEnd("character",end-start);range.select()}function setModernOffsets(node,offsets){if(!window.getSelection){return}var selection=window.getSelection();var length=node[getTextContentAccessor()].length;var start=Math.min(offsets.start,length);var end=offsets.end===undefined?start:Math.min(offsets.end,length);if(!selection.extend&&start>end){var temp=end;end=start;start=temp}var startMarker=getNodeForCharacterOffset(node,start);var endMarker=getNodeForCharacterOffset(node,end);if(startMarker&&endMarker){var range=document.createRange();range.setStart(startMarker.node,startMarker.offset);selection.removeAllRanges();if(start>end){selection.addRange(range);selection.extend(endMarker.node,endMarker.offset)}else{range.setEnd(endMarker.node,endMarker.offset);selection.addRange(range)}}}var useIEOffsets=ExecutionEnvironment.canUseDOM&&"selection"in document&&!("getSelection"in window);var ReactDOMSelection={getOffsets:useIEOffsets?getIEOffsets:getModernOffsets,setOffsets:useIEOffsets?setIEOffsets:setModernOffsets};module.exports=ReactDOMSelection},{"./getNodeForCharacterOffset":143,"./getTextContentAccessor":144,"fbjs/lib/ExecutionEnvironment":4}],75:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var DOMChildrenOperations=require("./DOMChildrenOperations");var DOMLazyTree=require("./DOMLazyTree");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var escapeTextContentForBrowser=require("./escapeTextContentForBrowser");var invariant=require("fbjs/lib/invariant");var validateDOMNesting=require("./validateDOMNesting");var ReactDOMTextComponent=function(text){this._currentElement=text;this._stringText=""+text;this._hostNode=null;this._hostParent=null;this._domID=0;this._mountIndex=0;this._closingComment=null;this._commentNodes=null};_assign(ReactDOMTextComponent.prototype,{mountComponent:function(transaction,hostParent,hostContainerInfo,context){if(process.env.NODE_ENV!=="production"){var parentInfo;if(hostParent!=null){parentInfo=hostParent._ancestorInfo}else if(hostContainerInfo!=null){parentInfo=hostContainerInfo._ancestorInfo}if(parentInfo){validateDOMNesting(null,this._stringText,this,parentInfo)}}var domID=hostContainerInfo._idCounter++;var openingValue=" react-text: "+domID+" ";var closingValue=" /react-text ";this._domID=domID;this._hostParent=hostParent;if(transaction.useCreateElement){var ownerDocument=hostContainerInfo._ownerDocument;var openingComment=ownerDocument.createComment(openingValue);var closingComment=ownerDocument.createComment(closingValue);var lazyTree=DOMLazyTree(ownerDocument.createDocumentFragment());DOMLazyTree.queueChild(lazyTree,DOMLazyTree(openingComment));if(this._stringText){DOMLazyTree.queueChild(lazyTree,DOMLazyTree(ownerDocument.createTextNode(this._stringText)))}DOMLazyTree.queueChild(lazyTree,DOMLazyTree(closingComment));ReactDOMComponentTree.precacheNode(this,openingComment);this._closingComment=closingComment;return lazyTree}else{var escapedText=escapeTextContentForBrowser(this._stringText);if(transaction.renderToStaticMarkup){return escapedText}return"\x3c!--"+openingValue+"--\x3e"+escapedText+"\x3c!--"+closingValue+"--\x3e"}},receiveComponent:function(nextText,transaction){if(nextText!==this._currentElement){this._currentElement=nextText;var nextStringText=""+nextText;if(nextStringText!==this._stringText){this._stringText=nextStringText;var commentNodes=this.getHostNode();DOMChildrenOperations.replaceDelimitedText(commentNodes[0],commentNodes[1],nextStringText)}}},getHostNode:function(){var hostNode=this._commentNodes;if(hostNode){return hostNode}if(!this._closingComment){var openingComment=ReactDOMComponentTree.getNodeFromInstance(this);var node=openingComment.nextSibling;while(true){!(node!=null)?process.env.NODE_ENV!=="production"?invariant(false,"Missing closing comment for text component %s",this._domID):_prodInvariant("67",this._domID):void 0;if(node.nodeType===8&&node.nodeValue===" /react-text "){this._closingComment=node;break}node=node.nextSibling}}hostNode=[this._hostNode,this._closingComment];this._commentNodes=hostNode;return hostNode},unmountComponent:function(){this._closingComment=null;this._commentNodes=null;ReactDOMComponentTree.uncacheNode(this)}});module.exports=ReactDOMTextComponent}).call(this,require("_process"))},{"./DOMChildrenOperations":39,"./DOMLazyTree":40,"./ReactDOMComponentTree":64,"./escapeTextContentForBrowser":133,"./reactProdInvariant":151,"./validateDOMNesting":157,_process:184,"fbjs/lib/invariant":18,"object-assign":26}],76:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var LinkedValueUtils=require("./LinkedValueUtils");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactUpdates=require("./ReactUpdates");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var didWarnValueLink=false;var didWarnValDefaultVal=false;function forceUpdateIfMounted(){if(this._rootNodeID){ReactDOMTextarea.updateWrapper(this)}}var ReactDOMTextarea={getHostProps:function(inst,props){!(props.dangerouslySetInnerHTML==null)?process.env.NODE_ENV!=="production"?invariant(false,"`dangerouslySetInnerHTML` does not make sense on <textarea>."):_prodInvariant("91"):void 0;var hostProps=_assign({},props,{value:undefined,defaultValue:undefined,children:""+inst._wrapperState.initialValue,onChange:inst._wrapperState.onChange});return hostProps},mountWrapper:function(inst,props){if(process.env.NODE_ENV!=="production"){LinkedValueUtils.checkPropTypes("textarea",props,inst._currentElement._owner);if(props.valueLink!==undefined&&!didWarnValueLink){process.env.NODE_ENV!=="production"?warning(false,"`valueLink` prop on `textarea` is deprecated; set `value` and `onChange` instead."):void 0;didWarnValueLink=true}if(props.value!==undefined&&props.defaultValue!==undefined&&!didWarnValDefaultVal){process.env.NODE_ENV!=="production"?warning(false,"Textarea elements must be either controlled or uncontrolled "+"(specify either the value prop, or the defaultValue prop, but not "+"both). Decide between using a controlled or uncontrolled textarea "+"and remove one of these props. More info: "+"https://fb.me/react-controlled-components"):void 0;didWarnValDefaultVal=true}}var value=LinkedValueUtils.getValue(props);var initialValue=value;if(value==null){var defaultValue=props.defaultValue;var children=props.children;if(children!=null){if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(false,"Use the `defaultValue` or `value` props instead of setting "+"children on <textarea>."):void 0}!(defaultValue==null)?process.env.NODE_ENV!=="production"?invariant(false,"If you supply `defaultValue` on a <textarea>, do not pass children."):_prodInvariant("92"):void 0;if(Array.isArray(children)){!(children.length<=1)?process.env.NODE_ENV!=="production"?invariant(false,"<textarea> can only have at most one child."):_prodInvariant("93"):void 0;children=children[0]}defaultValue=""+children}if(defaultValue==null){defaultValue=""}initialValue=defaultValue}inst._wrapperState={initialValue:""+initialValue,listeners:null,onChange:_handleChange.bind(inst)}},updateWrapper:function(inst){var props=inst._currentElement.props;var node=ReactDOMComponentTree.getNodeFromInstance(inst);var value=LinkedValueUtils.getValue(props);if(value!=null){var newValue=""+value;if(newValue!==node.value){node.value=newValue}if(props.defaultValue==null){node.defaultValue=newValue}}if(props.defaultValue!=null){node.defaultValue=props.defaultValue}},postMountWrapper:function(inst){var node=ReactDOMComponentTree.getNodeFromInstance(inst);var textContent=node.textContent;if(textContent===inst._wrapperState.initialValue){node.value=textContent}}};function _handleChange(event){var props=this._currentElement.props;var returnValue=LinkedValueUtils.executeOnChange(props,event);ReactUpdates.asap(forceUpdateIfMounted,this);return returnValue}module.exports=ReactDOMTextarea}).call(this,require("_process"))},{"./LinkedValueUtils":54,"./ReactDOMComponentTree":64,"./ReactUpdates":108,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"object-assign":26}],77:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");function getLowestCommonAncestor(instA,instB){!("_hostNode"in instA)?process.env.NODE_ENV!=="production"?invariant(false,"getNodeFromInstance: Invalid argument."):_prodInvariant("33"):void 0;!("_hostNode"in instB)?process.env.NODE_ENV!=="production"?invariant(false,"getNodeFromInstance: Invalid argument."):_prodInvariant("33"):void 0;var depthA=0;for(var tempA=instA;tempA;tempA=tempA._hostParent){depthA++}var depthB=0;for(var tempB=instB;tempB;tempB=tempB._hostParent){depthB++}while(depthA-depthB>0){instA=instA._hostParent;depthA--}while(depthB-depthA>0){instB=instB._hostParent;depthB--}var depth=depthA;while(depth--){if(instA===instB){return instA}instA=instA._hostParent;instB=instB._hostParent}return null}function isAncestor(instA,instB){!("_hostNode"in instA)?process.env.NODE_ENV!=="production"?invariant(false,"isAncestor: Invalid argument."):_prodInvariant("35"):void 0;!("_hostNode"in instB)?process.env.NODE_ENV!=="production"?invariant(false,"isAncestor: Invalid argument."):_prodInvariant("35"):void 0;while(instB){if(instB===instA){return true}instB=instB._hostParent}return false}function getParentInstance(inst){!("_hostNode"in inst)?process.env.NODE_ENV!=="production"?invariant(false,"getParentInstance: Invalid argument."):_prodInvariant("36"):void 0;return inst._hostParent}function traverseTwoPhase(inst,fn,arg){var path=[];while(inst){path.push(inst);inst=inst._hostParent}var i;for(i=path.length;i-- >0;){fn(path[i],"captured",arg)}for(i=0;i<path.length;i++){fn(path[i],"bubbled",arg)}}function traverseEnterLeave(from,to,fn,argFrom,argTo){var common=from&&to?getLowestCommonAncestor(from,to):null;var pathFrom=[];while(from&&from!==common){pathFrom.push(from);from=from._hostParent}var pathTo=[];while(to&&to!==common){pathTo.push(to);to=to._hostParent}var i;for(i=0;i<pathFrom.length;i++){fn(pathFrom[i],"bubbled",argFrom)}for(i=pathTo.length;i-- >0;){fn(pathTo[i],"captured",argTo)}}module.exports={isAncestor:isAncestor,getLowestCommonAncestor:getLowestCommonAncestor,getParentInstance:getParentInstance,traverseTwoPhase:traverseTwoPhase,traverseEnterLeave:traverseEnterLeave}}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],78:[function(require,module,exports){(function(process){"use strict";var DOMProperty=require("./DOMProperty");var EventPluginRegistry=require("./EventPluginRegistry");var ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook");var warning=require("fbjs/lib/warning");if(process.env.NODE_ENV!=="production"){var reactProps={children:true,dangerouslySetInnerHTML:true,key:true,ref:true,autoFocus:true,defaultValue:true,valueLink:true,defaultChecked:true,checkedLink:true,innerHTML:true,suppressContentEditableWarning:true,onFocusIn:true,onFocusOut:true};var warnedProperties={};var validateProperty=function(tagName,name,debugID){if(DOMProperty.properties.hasOwnProperty(name)||DOMProperty.isCustomAttribute(name)){return true}if(reactProps.hasOwnProperty(name)&&reactProps[name]||warnedProperties.hasOwnProperty(name)&&warnedProperties[name]){return true}if(EventPluginRegistry.registrationNameModules.hasOwnProperty(name)){return true}warnedProperties[name]=true;var lowerCasedName=name.toLowerCase();var standardName=DOMProperty.isCustomAttribute(lowerCasedName)?lowerCasedName:DOMProperty.getPossibleStandardName.hasOwnProperty(lowerCasedName)?DOMProperty.getPossibleStandardName[lowerCasedName]:null;var registrationName=EventPluginRegistry.possibleRegistrationNames.hasOwnProperty(lowerCasedName)?EventPluginRegistry.possibleRegistrationNames[lowerCasedName]:null;if(standardName!=null){process.env.NODE_ENV!=="production"?warning(false,"Unknown DOM property %s. Did you mean %s?%s",name,standardName,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0;return true}else if(registrationName!=null){process.env.NODE_ENV!=="production"?warning(false,"Unknown event handler property %s. Did you mean `%s`?%s",name,registrationName,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0;return true}else{return false}}}var warnUnknownProperties=function(debugID,element){var unknownProps=[];for(var key in element.props){var isValid=validateProperty(element.type,key,debugID);if(!isValid){unknownProps.push(key)}}var unknownPropString=unknownProps.map(function(prop){return"`"+prop+"`"}).join(", ");if(unknownProps.length===1){process.env.NODE_ENV!=="production"?warning(false,"Unknown prop %s on <%s> tag. Remove this prop from the element. "+"For details, see https://fb.me/react-unknown-prop%s",unknownPropString,element.type,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0}else if(unknownProps.length>1){process.env.NODE_ENV!=="production"?warning(false,"Unknown props %s on <%s> tag. Remove these props from the element. "+"For details, see https://fb.me/react-unknown-prop%s",unknownPropString,element.type,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0}};function handleElement(debugID,element){if(element==null||typeof element.type!=="string"){return}if(element.type.indexOf("-")>=0||element.props.is){return}warnUnknownProperties(debugID,element)}var ReactDOMUnknownPropertyHook={onBeforeMountComponent:function(debugID,element){handleElement(debugID,element)},onBeforeUpdateComponent:function(debugID,element){handleElement(debugID,element)}};module.exports=ReactDOMUnknownPropertyHook}).call(this,require("_process"))},{"./DOMProperty":42,"./EventPluginRegistry":48,_process:184,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],79:[function(require,module,exports){(function(process){"use strict";var ReactInvalidSetStateWarningHook=require("./ReactInvalidSetStateWarningHook");var ReactHostOperationHistoryHook=require("./ReactHostOperationHistoryHook");var ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var performanceNow=require("fbjs/lib/performanceNow");var warning=require("fbjs/lib/warning");var hooks=[];var didHookThrowForEvent={};function callHook(event,fn,context,arg1,arg2,arg3,arg4,arg5){try{fn.call(context,arg1,arg2,arg3,arg4,arg5)}catch(e){process.env.NODE_ENV!=="production"?warning(didHookThrowForEvent[event],"Exception thrown by hook while handling %s: %s",event,e+"\n"+e.stack):void 0;didHookThrowForEvent[event]=true}}function emitEvent(event,arg1,arg2,arg3,arg4,arg5){for(var i=0;i<hooks.length;i++){var hook=hooks[i];var fn=hook[event];if(fn){callHook(event,fn,hook,arg1,arg2,arg3,arg4,arg5)}}}var isProfiling=false;var flushHistory=[];var lifeCycleTimerStack=[];var currentFlushNesting=0;var currentFlushMeasurements=[];var currentFlushStartTime=0;var currentTimerDebugID=null;var currentTimerStartTime=0;var currentTimerNestedFlushDuration=0;var currentTimerType=null;var lifeCycleTimerHasWarned=false;function clearHistory(){ReactComponentTreeHook.purgeUnmountedComponents();ReactHostOperationHistoryHook.clearHistory()}function getTreeSnapshot(registeredIDs){return registeredIDs.reduce(function(tree,id){var ownerID=ReactComponentTreeHook.getOwnerID(id);var parentID=ReactComponentTreeHook.getParentID(id);tree[id]={displayName:ReactComponentTreeHook.getDisplayName(id),text:ReactComponentTreeHook.getText(id),updateCount:ReactComponentTreeHook.getUpdateCount(id),childIDs:ReactComponentTreeHook.getChildIDs(id),ownerID:ownerID||parentID&&ReactComponentTreeHook.getOwnerID(parentID)||0,parentID:parentID};return tree},{})}function resetMeasurements(){var previousStartTime=currentFlushStartTime;var previousMeasurements=currentFlushMeasurements;var previousOperations=ReactHostOperationHistoryHook.getHistory();if(currentFlushNesting===0){currentFlushStartTime=0;currentFlushMeasurements=[];clearHistory();return}if(previousMeasurements.length||previousOperations.length){var registeredIDs=ReactComponentTreeHook.getRegisteredIDs();flushHistory.push({duration:performanceNow()-previousStartTime,measurements:previousMeasurements||[],operations:previousOperations||[],treeSnapshot:getTreeSnapshot(registeredIDs)})}clearHistory();currentFlushStartTime=performanceNow();currentFlushMeasurements=[]}function checkDebugID(debugID){var allowRoot=arguments.length>1&&arguments[1]!==undefined?arguments[1]:false;if(allowRoot&&debugID===0){return}if(!debugID){process.env.NODE_ENV!=="production"?warning(false,"ReactDebugTool: debugID may not be empty."):void 0}}function beginLifeCycleTimer(debugID,timerType){if(currentFlushNesting===0){return}if(currentTimerType&&!lifeCycleTimerHasWarned){process.env.NODE_ENV!=="production"?warning(false,"There is an internal error in the React performance measurement code. "+"Did not expect %s timer to start while %s timer is still in "+"progress for %s instance.",timerType,currentTimerType||"no",debugID===currentTimerDebugID?"the same":"another"):void 0;lifeCycleTimerHasWarned=true}currentTimerStartTime=performanceNow();currentTimerNestedFlushDuration=0;currentTimerDebugID=debugID;currentTimerType=timerType}function endLifeCycleTimer(debugID,timerType){if(currentFlushNesting===0){return}if(currentTimerType!==timerType&&!lifeCycleTimerHasWarned){process.env.NODE_ENV!=="production"?warning(false,"There is an internal error in the React performance measurement code. "+"We did not expect %s timer to stop while %s timer is still in "+"progress for %s instance. Please report this as a bug in React.",timerType,currentTimerType||"no",debugID===currentTimerDebugID?"the same":"another"):void 0;lifeCycleTimerHasWarned=true}if(isProfiling){currentFlushMeasurements.push({timerType:timerType,instanceID:debugID,duration:performanceNow()-currentTimerStartTime-currentTimerNestedFlushDuration})}currentTimerStartTime=0;currentTimerNestedFlushDuration=0;currentTimerDebugID=null;currentTimerType=null}function pauseCurrentLifeCycleTimer(){var currentTimer={startTime:currentTimerStartTime,nestedFlushStartTime:performanceNow(),debugID:currentTimerDebugID,timerType:currentTimerType};lifeCycleTimerStack.push(currentTimer);currentTimerStartTime=0;currentTimerNestedFlushDuration=0;currentTimerDebugID=null;currentTimerType=null}function resumeCurrentLifeCycleTimer(){var _lifeCycleTimerStack$=lifeCycleTimerStack.pop(),startTime=_lifeCycleTimerStack$.startTime,nestedFlushStartTime=_lifeCycleTimerStack$.nestedFlushStartTime,debugID=_lifeCycleTimerStack$.debugID,timerType=_lifeCycleTimerStack$.timerType;var nestedFlushDuration=performanceNow()-nestedFlushStartTime;currentTimerStartTime=startTime;currentTimerNestedFlushDuration+=nestedFlushDuration;currentTimerDebugID=debugID;currentTimerType=timerType}var lastMarkTimeStamp=0;var canUsePerformanceMeasure=typeof performance!=="undefined"&&typeof performance.mark==="function"&&typeof performance.clearMarks==="function"&&typeof performance.measure==="function"&&typeof performance.clearMeasures==="function";function shouldMark(debugID){if(!isProfiling||!canUsePerformanceMeasure){return false}var element=ReactComponentTreeHook.getElement(debugID);if(element==null||typeof element!=="object"){return false}var isHostElement=typeof element.type==="string";if(isHostElement){return false}return true}function markBegin(debugID,markType){if(!shouldMark(debugID)){return}var markName=debugID+"::"+markType;lastMarkTimeStamp=performanceNow();performance.mark(markName)}function markEnd(debugID,markType){if(!shouldMark(debugID)){return}var markName=debugID+"::"+markType;var displayName=ReactComponentTreeHook.getDisplayName(debugID)||"Unknown";var timeStamp=performanceNow();if(timeStamp-lastMarkTimeStamp>.1){var measurementName=displayName+" ["+markType+"]";performance.measure(measurementName,markName)}performance.clearMarks(markName);if(measurementName){performance.clearMeasures(measurementName)}}var ReactDebugTool={addHook:function(hook){hooks.push(hook)},removeHook:function(hook){for(var i=0;i<hooks.length;i++){if(hooks[i]===hook){hooks.splice(i,1);i--}}},isProfiling:function(){return isProfiling},beginProfiling:function(){if(isProfiling){return}isProfiling=true;flushHistory.length=0;resetMeasurements();ReactDebugTool.addHook(ReactHostOperationHistoryHook)},endProfiling:function(){if(!isProfiling){return}isProfiling=false;resetMeasurements();ReactDebugTool.removeHook(ReactHostOperationHistoryHook)},getFlushHistory:function(){return flushHistory},onBeginFlush:function(){currentFlushNesting++;resetMeasurements();pauseCurrentLifeCycleTimer();emitEvent("onBeginFlush")},onEndFlush:function(){resetMeasurements();currentFlushNesting--;resumeCurrentLifeCycleTimer();emitEvent("onEndFlush")},onBeginLifeCycleTimer:function(debugID,timerType){checkDebugID(debugID);emitEvent("onBeginLifeCycleTimer",debugID,timerType);markBegin(debugID,timerType);beginLifeCycleTimer(debugID,timerType)},onEndLifeCycleTimer:function(debugID,timerType){checkDebugID(debugID);endLifeCycleTimer(debugID,timerType);markEnd(debugID,timerType);emitEvent("onEndLifeCycleTimer",debugID,timerType)},onBeginProcessingChildContext:function(){emitEvent("onBeginProcessingChildContext")},onEndProcessingChildContext:function(){emitEvent("onEndProcessingChildContext")},onHostOperation:function(operation){checkDebugID(operation.instanceID);emitEvent("onHostOperation",operation)},onSetState:function(){emitEvent("onSetState")},onSetChildren:function(debugID,childDebugIDs){checkDebugID(debugID);childDebugIDs.forEach(checkDebugID);emitEvent("onSetChildren",debugID,childDebugIDs)},onBeforeMountComponent:function(debugID,element,parentDebugID){checkDebugID(debugID);checkDebugID(parentDebugID,true);emitEvent("onBeforeMountComponent",debugID,element,parentDebugID);markBegin(debugID,"mount")},onMountComponent:function(debugID){checkDebugID(debugID);markEnd(debugID,"mount");emitEvent("onMountComponent",debugID)},onBeforeUpdateComponent:function(debugID,element){checkDebugID(debugID);emitEvent("onBeforeUpdateComponent",debugID,element);markBegin(debugID,"update")},onUpdateComponent:function(debugID){checkDebugID(debugID);markEnd(debugID,"update");emitEvent("onUpdateComponent",debugID)},onBeforeUnmountComponent:function(debugID){checkDebugID(debugID);emitEvent("onBeforeUnmountComponent",debugID);markBegin(debugID,"unmount")},onUnmountComponent:function(debugID){checkDebugID(debugID);markEnd(debugID,"unmount");emitEvent("onUnmountComponent",debugID)},onTestEvent:function(){emitEvent("onTestEvent")}};ReactDebugTool.addDevtool=ReactDebugTool.addHook;ReactDebugTool.removeDevtool=ReactDebugTool.removeHook;ReactDebugTool.addHook(ReactInvalidSetStateWarningHook);ReactDebugTool.addHook(ReactComponentTreeHook);var url=ExecutionEnvironment.canUseDOM&&window.location.href||"";if(/[?&]react_perf\b/.test(url)){ReactDebugTool.beginProfiling()}module.exports=ReactDebugTool}).call(this,require("_process"))},{"./ReactHostOperationHistoryHook":89,"./ReactInvalidSetStateWarningHook":94,_process:184,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/performanceNow":23,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],80:[function(require,module,exports){"use strict";var _assign=require("object-assign");var ReactUpdates=require("./ReactUpdates");var Transaction=require("./Transaction");var emptyFunction=require("fbjs/lib/emptyFunction");var RESET_BATCHED_UPDATES={initialize:emptyFunction,close:function(){ReactDefaultBatchingStrategy.isBatchingUpdates=false}};var FLUSH_BATCHED_UPDATES={initialize:emptyFunction,close:ReactUpdates.flushBatchedUpdates.bind(ReactUpdates)};var TRANSACTION_WRAPPERS=[FLUSH_BATCHED_UPDATES,RESET_BATCHED_UPDATES];function ReactDefaultBatchingStrategyTransaction(){this.reinitializeTransaction()}_assign(ReactDefaultBatchingStrategyTransaction.prototype,Transaction,{getTransactionWrappers:function(){return TRANSACTION_WRAPPERS}});var transaction=new ReactDefaultBatchingStrategyTransaction;var ReactDefaultBatchingStrategy={isBatchingUpdates:false,batchedUpdates:function(callback,a,b,c,d,e){var alreadyBatchingUpdates=ReactDefaultBatchingStrategy.isBatchingUpdates;ReactDefaultBatchingStrategy.isBatchingUpdates=true;if(alreadyBatchingUpdates){return callback(a,b,c,d,e)}else{return transaction.perform(callback,null,a,b,c,d,e)}}};module.exports=ReactDefaultBatchingStrategy},{"./ReactUpdates":108,"./Transaction":126,"fbjs/lib/emptyFunction":10,"object-assign":26}],81:[function(require,module,exports){"use strict";var ARIADOMPropertyConfig=require("./ARIADOMPropertyConfig");var BeforeInputEventPlugin=require("./BeforeInputEventPlugin");var ChangeEventPlugin=require("./ChangeEventPlugin");var DefaultEventPluginOrder=require("./DefaultEventPluginOrder");var EnterLeaveEventPlugin=require("./EnterLeaveEventPlugin");var HTMLDOMPropertyConfig=require("./HTMLDOMPropertyConfig");var ReactComponentBrowserEnvironment=require("./ReactComponentBrowserEnvironment");var ReactDOMComponent=require("./ReactDOMComponent");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMEmptyComponent=require("./ReactDOMEmptyComponent");var ReactDOMTreeTraversal=require("./ReactDOMTreeTraversal");var ReactDOMTextComponent=require("./ReactDOMTextComponent");var ReactDefaultBatchingStrategy=require("./ReactDefaultBatchingStrategy");var ReactEventListener=require("./ReactEventListener");var ReactInjection=require("./ReactInjection");var ReactReconcileTransaction=require("./ReactReconcileTransaction");var SVGDOMPropertyConfig=require("./SVGDOMPropertyConfig");var SelectEventPlugin=require("./SelectEventPlugin");var SimpleEventPlugin=require("./SimpleEventPlugin");var alreadyInjected=false;function inject(){if(alreadyInjected){return}alreadyInjected=true;ReactInjection.EventEmitter.injectReactEventListener(ReactEventListener);ReactInjection.EventPluginHub.injectEventPluginOrder(DefaultEventPluginOrder);ReactInjection.EventPluginUtils.injectComponentTree(ReactDOMComponentTree);ReactInjection.EventPluginUtils.injectTreeTraversal(ReactDOMTreeTraversal);ReactInjection.EventPluginHub.injectEventPluginsByName({SimpleEventPlugin:SimpleEventPlugin,EnterLeaveEventPlugin:EnterLeaveEventPlugin,ChangeEventPlugin:ChangeEventPlugin,SelectEventPlugin:SelectEventPlugin,BeforeInputEventPlugin:BeforeInputEventPlugin});ReactInjection.HostComponent.injectGenericComponentClass(ReactDOMComponent);ReactInjection.HostComponent.injectTextComponentClass(ReactDOMTextComponent);ReactInjection.DOMProperty.injectDOMPropertyConfig(ARIADOMPropertyConfig);ReactInjection.DOMProperty.injectDOMPropertyConfig(HTMLDOMPropertyConfig);ReactInjection.DOMProperty.injectDOMPropertyConfig(SVGDOMPropertyConfig);ReactInjection.EmptyComponent.injectEmptyComponentFactory(function(instantiate){return new ReactDOMEmptyComponent(instantiate)});ReactInjection.Updates.injectReconcileTransaction(ReactReconcileTransaction);ReactInjection.Updates.injectBatchingStrategy(ReactDefaultBatchingStrategy);ReactInjection.Component.injectEnvironment(ReactComponentBrowserEnvironment)}module.exports={inject:inject}},{"./ARIADOMPropertyConfig":32,"./BeforeInputEventPlugin":34,"./ChangeEventPlugin":38,"./DefaultEventPluginOrder":45,"./EnterLeaveEventPlugin":46,"./HTMLDOMPropertyConfig":52,"./ReactComponentBrowserEnvironment":58,"./ReactDOMComponent":62,"./ReactDOMComponentTree":64,"./ReactDOMEmptyComponent":66,"./ReactDOMTextComponent":75,"./ReactDOMTreeTraversal":77,"./ReactDefaultBatchingStrategy":80,"./ReactEventListener":86,"./ReactInjection":90,"./ReactReconcileTransaction":102,"./SVGDOMPropertyConfig":110,"./SelectEventPlugin":111,"./SimpleEventPlugin":112}],82:[function(require,module,exports){"use strict";var REACT_ELEMENT_TYPE=typeof Symbol==="function"&&Symbol["for"]&&Symbol["for"]("react.element")||60103;module.exports=REACT_ELEMENT_TYPE},{}],83:[function(require,module,exports){"use strict";var emptyComponentFactory;var ReactEmptyComponentInjection={injectEmptyComponentFactory:function(factory){emptyComponentFactory=factory}};var ReactEmptyComponent={create:function(instantiate){return emptyComponentFactory(instantiate)}};ReactEmptyComponent.injection=ReactEmptyComponentInjection;module.exports=ReactEmptyComponent},{}],84:[function(require,module,exports){(function(process){"use strict";var caughtError=null;function invokeGuardedCallback(name,func,a){try{func(a)}catch(x){if(caughtError===null){caughtError=x}}}var ReactErrorUtils={invokeGuardedCallback:invokeGuardedCallback,invokeGuardedCallbackWithCatch:invokeGuardedCallback,rethrowCaughtError:function(){if(caughtError){var error=caughtError;caughtError=null;throw error}}};if(process.env.NODE_ENV!=="production"){if(typeof window!=="undefined"&&typeof window.dispatchEvent==="function"&&typeof document!=="undefined"&&typeof document.createEvent==="function"){var fakeNode=document.createElement("react");ReactErrorUtils.invokeGuardedCallback=function(name,func,a){var boundFunc=func.bind(null,a);var evtType="react-"+name;fakeNode.addEventListener(evtType,boundFunc,false);var evt=document.createEvent("Event");evt.initEvent(evtType,false,false);fakeNode.dispatchEvent(evt);fakeNode.removeEventListener(evtType,boundFunc,false)}}}module.exports=ReactErrorUtils}).call(this,require("_process"))},{_process:184}],85:[function(require,module,exports){"use strict";var EventPluginHub=require("./EventPluginHub");function runEventQueueInBatch(events){EventPluginHub.enqueueEvents(events);EventPluginHub.processEventQueue(false)}var ReactEventEmitterMixin={handleTopLevel:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){var events=EventPluginHub.extractEvents(topLevelType,targetInst,nativeEvent,nativeEventTarget);runEventQueueInBatch(events)}};module.exports=ReactEventEmitterMixin},{"./EventPluginHub":47}],86:[function(require,module,exports){"use strict";var _assign=require("object-assign");var EventListener=require("fbjs/lib/EventListener");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var PooledClass=require("./PooledClass");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactUpdates=require("./ReactUpdates");var getEventTarget=require("./getEventTarget");var getUnboundedScrollPosition=require("fbjs/lib/getUnboundedScrollPosition");function findParent(inst){while(inst._hostParent){inst=inst._hostParent}var rootNode=ReactDOMComponentTree.getNodeFromInstance(inst);var container=rootNode.parentNode;return ReactDOMComponentTree.getClosestInstanceFromNode(container)}function TopLevelCallbackBookKeeping(topLevelType,nativeEvent){this.topLevelType=topLevelType;this.nativeEvent=nativeEvent;this.ancestors=[]}_assign(TopLevelCallbackBookKeeping.prototype,{destructor:function(){this.topLevelType=null;this.nativeEvent=null;this.ancestors.length=0}});PooledClass.addPoolingTo(TopLevelCallbackBookKeeping,PooledClass.twoArgumentPooler);function handleTopLevelImpl(bookKeeping){var nativeEventTarget=getEventTarget(bookKeeping.nativeEvent);var targetInst=ReactDOMComponentTree.getClosestInstanceFromNode(nativeEventTarget);var ancestor=targetInst;do{bookKeeping.ancestors.push(ancestor);ancestor=ancestor&&findParent(ancestor)}while(ancestor);for(var i=0;i<bookKeeping.ancestors.length;i++){targetInst=bookKeeping.ancestors[i];ReactEventListener._handleTopLevel(bookKeeping.topLevelType,targetInst,bookKeeping.nativeEvent,getEventTarget(bookKeeping.nativeEvent))}}function scrollValueMonitor(cb){var scrollPosition=getUnboundedScrollPosition(window);cb(scrollPosition)}var ReactEventListener={_enabled:true,_handleTopLevel:null,WINDOW_HANDLE:ExecutionEnvironment.canUseDOM?window:null,setHandleTopLevel:function(handleTopLevel){ReactEventListener._handleTopLevel=handleTopLevel},setEnabled:function(enabled){ReactEventListener._enabled=!!enabled},isEnabled:function(){return ReactEventListener._enabled},trapBubbledEvent:function(topLevelType,handlerBaseName,element){if(!element){return null}return EventListener.listen(element,handlerBaseName,ReactEventListener.dispatchEvent.bind(null,topLevelType))},trapCapturedEvent:function(topLevelType,handlerBaseName,element){if(!element){return null}return EventListener.capture(element,handlerBaseName,ReactEventListener.dispatchEvent.bind(null,topLevelType))},monitorScrollValue:function(refresh){var callback=scrollValueMonitor.bind(null,refresh);EventListener.listen(window,"scroll",callback)},dispatchEvent:function(topLevelType,nativeEvent){if(!ReactEventListener._enabled){return}var bookKeeping=TopLevelCallbackBookKeeping.getPooled(topLevelType,nativeEvent);try{ReactUpdates.batchedUpdates(handleTopLevelImpl,bookKeeping)}finally{TopLevelCallbackBookKeeping.release(bookKeeping)}}};module.exports=ReactEventListener},{"./PooledClass":55,"./ReactDOMComponentTree":64,"./ReactUpdates":108,"./getEventTarget":140,"fbjs/lib/EventListener":3,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/getUnboundedScrollPosition":15,"object-assign":26}],87:[function(require,module,exports){"use strict";var ReactFeatureFlags={logTopLevelRenders:false};module.exports=ReactFeatureFlags},{}],88:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");var genericComponentClass=null;var textComponentClass=null;var ReactHostComponentInjection={injectGenericComponentClass:function(componentClass){genericComponentClass=componentClass},injectTextComponentClass:function(componentClass){textComponentClass=componentClass}};function createInternalComponent(element){!genericComponentClass?process.env.NODE_ENV!=="production"?invariant(false,"There is no registered component for the tag %s",element.type):_prodInvariant("111",element.type):void 0;return new genericComponentClass(element)}function createInstanceForText(text){return new textComponentClass(text)}function isTextComponent(component){return component instanceof textComponentClass}var ReactHostComponent={createInternalComponent:createInternalComponent,createInstanceForText:createInstanceForText,isTextComponent:isTextComponent,injection:ReactHostComponentInjection};module.exports=ReactHostComponent}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],89:[function(require,module,exports){"use strict";var history=[];var ReactHostOperationHistoryHook={onHostOperation:function(operation){history.push(operation)},clearHistory:function(){if(ReactHostOperationHistoryHook._preventClearing){return}history=[]},getHistory:function(){return history}};module.exports=ReactHostOperationHistoryHook},{}],90:[function(require,module,exports){"use strict";var DOMProperty=require("./DOMProperty");var EventPluginHub=require("./EventPluginHub");var EventPluginUtils=require("./EventPluginUtils");var ReactComponentEnvironment=require("./ReactComponentEnvironment");var ReactEmptyComponent=require("./ReactEmptyComponent");var ReactBrowserEventEmitter=require("./ReactBrowserEventEmitter");var ReactHostComponent=require("./ReactHostComponent");var ReactUpdates=require("./ReactUpdates");var ReactInjection={Component:ReactComponentEnvironment.injection,DOMProperty:DOMProperty.injection,EmptyComponent:ReactEmptyComponent.injection,EventPluginHub:EventPluginHub.injection,EventPluginUtils:EventPluginUtils.injection,EventEmitter:ReactBrowserEventEmitter.injection,HostComponent:ReactHostComponent.injection,Updates:ReactUpdates.injection};module.exports=ReactInjection},{"./DOMProperty":42,"./EventPluginHub":47,"./EventPluginUtils":49,"./ReactBrowserEventEmitter":56,"./ReactComponentEnvironment":59,"./ReactEmptyComponent":83,"./ReactHostComponent":88,"./ReactUpdates":108}],91:[function(require,module,exports){"use strict";var ReactDOMSelection=require("./ReactDOMSelection");var containsNode=require("fbjs/lib/containsNode");var focusNode=require("fbjs/lib/focusNode");var getActiveElement=require("fbjs/lib/getActiveElement");function isInDocument(node){return containsNode(document.documentElement,node)}var ReactInputSelection={hasSelectionCapabilities:function(elem){var nodeName=elem&&elem.nodeName&&elem.nodeName.toLowerCase();return nodeName&&(nodeName==="input"&&elem.type==="text"||nodeName==="textarea"||elem.contentEditable==="true")},getSelectionInformation:function(){var focusedElem=getActiveElement();return{focusedElem:focusedElem,selectionRange:ReactInputSelection.hasSelectionCapabilities(focusedElem)?ReactInputSelection.getSelection(focusedElem):null}},restoreSelection:function(priorSelectionInformation){var curFocusedElem=getActiveElement();var priorFocusedElem=priorSelectionInformation.focusedElem;var priorSelectionRange=priorSelectionInformation.selectionRange;if(curFocusedElem!==priorFocusedElem&&isInDocument(priorFocusedElem)){if(ReactInputSelection.hasSelectionCapabilities(priorFocusedElem)){ReactInputSelection.setSelection(priorFocusedElem,priorSelectionRange)}focusNode(priorFocusedElem)}},getSelection:function(input){var selection;if("selectionStart"in input){selection={start:input.selectionStart,end:input.selectionEnd}}else if(document.selection&&input.nodeName&&input.nodeName.toLowerCase()==="input"){var range=document.selection.createRange();if(range.parentElement()===input){selection={start:-range.moveStart("character",-input.value.length),end:-range.moveEnd("character",-input.value.length)}}}else{selection=ReactDOMSelection.getOffsets(input)}return selection||{start:0,end:0}},setSelection:function(input,offsets){var start=offsets.start;var end=offsets.end;if(end===undefined){end=start}if("selectionStart"in input){input.selectionStart=start;input.selectionEnd=Math.min(end,input.value.length)}else if(document.selection&&input.nodeName&&input.nodeName.toLowerCase()==="input"){var range=input.createTextRange();range.collapse(true);range.moveStart("character",start);range.moveEnd("character",end-start);range.select()}else{ReactDOMSelection.setOffsets(input,offsets)}}};module.exports=ReactInputSelection},{"./ReactDOMSelection":74,"fbjs/lib/containsNode":7,"fbjs/lib/focusNode":12,"fbjs/lib/getActiveElement":13}],92:[function(require,module,exports){"use strict";var ReactInstanceMap={remove:function(key){key._reactInternalInstance=undefined},get:function(key){return key._reactInternalInstance},has:function(key){return key._reactInternalInstance!==undefined},set:function(key,value){key._reactInternalInstance=value}};module.exports=ReactInstanceMap},{}],93:[function(require,module,exports){(function(process){"use strict";var debugTool=null;if(process.env.NODE_ENV!=="production"){var ReactDebugTool=require("./ReactDebugTool");debugTool=ReactDebugTool}module.exports={debugTool:debugTool}}).call(this,require("_process"))},{"./ReactDebugTool":79,_process:184}],94:[function(require,module,exports){(function(process){"use strict";var warning=require("fbjs/lib/warning");if(process.env.NODE_ENV!=="production"){var processingChildContext=false;var warnInvalidSetState=function(){process.env.NODE_ENV!=="production"?warning(!processingChildContext,"setState(...): Cannot call setState() inside getChildContext()"):void 0}}var ReactInvalidSetStateWarningHook={onBeginProcessingChildContext:function(){processingChildContext=true},onEndProcessingChildContext:function(){processingChildContext=false},onSetState:function(){warnInvalidSetState()}};module.exports=ReactInvalidSetStateWarningHook}).call(this,require("_process"))},{_process:184,"fbjs/lib/warning":25}],95:[function(require,module,exports){"use strict";var adler32=require("./adler32");var TAG_END=/\/?>/;var COMMENT_START=/^<\!\-\-/;var ReactMarkupChecksum={CHECKSUM_ATTR_NAME:"data-react-checksum",addChecksumToMarkup:function(markup){var checksum=adler32(markup);if(COMMENT_START.test(markup)){return markup}else{return markup.replace(TAG_END," "+ReactMarkupChecksum.CHECKSUM_ATTR_NAME+'="'+checksum+'"$&')}},canReuseMarkup:function(markup,element){var existingChecksum=element.getAttribute(ReactMarkupChecksum.CHECKSUM_ATTR_NAME);existingChecksum=existingChecksum&&parseInt(existingChecksum,10);var markupChecksum=adler32(markup);return markupChecksum===existingChecksum}};module.exports=ReactMarkupChecksum},{"./adler32":129}],96:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var DOMLazyTree=require("./DOMLazyTree");var DOMProperty=require("./DOMProperty");var React=require("react/lib/React");var ReactBrowserEventEmitter=require("./ReactBrowserEventEmitter");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMContainerInfo=require("./ReactDOMContainerInfo");var ReactDOMFeatureFlags=require("./ReactDOMFeatureFlags");var ReactFeatureFlags=require("./ReactFeatureFlags");var ReactInstanceMap=require("./ReactInstanceMap");var ReactInstrumentation=require("./ReactInstrumentation");var ReactMarkupChecksum=require("./ReactMarkupChecksum");var ReactReconciler=require("./ReactReconciler");var ReactUpdateQueue=require("./ReactUpdateQueue");var ReactUpdates=require("./ReactUpdates");var emptyObject=require("fbjs/lib/emptyObject");var instantiateReactComponent=require("./instantiateReactComponent");var invariant=require("fbjs/lib/invariant");var setInnerHTML=require("./setInnerHTML");var shouldUpdateReactComponent=require("./shouldUpdateReactComponent");var warning=require("fbjs/lib/warning");var ATTR_NAME=DOMProperty.ID_ATTRIBUTE_NAME;var ROOT_ATTR_NAME=DOMProperty.ROOT_ATTRIBUTE_NAME;var ELEMENT_NODE_TYPE=1;var DOC_NODE_TYPE=9;var DOCUMENT_FRAGMENT_NODE_TYPE=11;var instancesByReactRootID={};function firstDifferenceIndex(string1,string2){var minLen=Math.min(string1.length,string2.length);for(var i=0;i<minLen;i++){if(string1.charAt(i)!==string2.charAt(i)){return i}}return string1.length===string2.length?-1:minLen}function getReactRootElementInContainer(container){if(!container){return null}if(container.nodeType===DOC_NODE_TYPE){return container.documentElement}else{return container.firstChild}}function internalGetID(node){return node.getAttribute&&node.getAttribute(ATTR_NAME)||""}function mountComponentIntoNode(wrapperInstance,container,transaction,shouldReuseMarkup,context){var markerName;if(ReactFeatureFlags.logTopLevelRenders){var wrappedElement=wrapperInstance._currentElement.props.child;var type=wrappedElement.type;markerName="React mount: "+(typeof type==="string"?type:type.displayName||type.name);console.time(markerName)}var markup=ReactReconciler.mountComponent(wrapperInstance,transaction,null,ReactDOMContainerInfo(wrapperInstance,container),context,0);if(markerName){console.timeEnd(markerName)}wrapperInstance._renderedComponent._topLevelWrapper=wrapperInstance;ReactMount._mountImageIntoNode(markup,container,wrapperInstance,shouldReuseMarkup,transaction)}function batchedMountComponentIntoNode(componentInstance,container,shouldReuseMarkup,context){var transaction=ReactUpdates.ReactReconcileTransaction.getPooled(!shouldReuseMarkup&&ReactDOMFeatureFlags.useCreateElement);transaction.perform(mountComponentIntoNode,null,componentInstance,container,transaction,shouldReuseMarkup,context);ReactUpdates.ReactReconcileTransaction.release(transaction)}function unmountComponentFromNode(instance,container,safely){if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onBeginFlush()}ReactReconciler.unmountComponent(instance,safely);if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onEndFlush()}if(container.nodeType===DOC_NODE_TYPE){container=container.documentElement}while(container.lastChild){container.removeChild(container.lastChild)}}function hasNonRootReactChild(container){var rootEl=getReactRootElementInContainer(container);if(rootEl){var inst=ReactDOMComponentTree.getInstanceFromNode(rootEl);return!!(inst&&inst._hostParent)}}function nodeIsRenderedByOtherInstance(container){var rootEl=getReactRootElementInContainer(container);return!!(rootEl&&isReactNode(rootEl)&&!ReactDOMComponentTree.getInstanceFromNode(rootEl))}function isValidContainer(node){return!!(node&&(node.nodeType===ELEMENT_NODE_TYPE||node.nodeType===DOC_NODE_TYPE||node.nodeType===DOCUMENT_FRAGMENT_NODE_TYPE))}function isReactNode(node){return isValidContainer(node)&&(node.hasAttribute(ROOT_ATTR_NAME)||node.hasAttribute(ATTR_NAME))}function getHostRootInstanceInContainer(container){var rootEl=getReactRootElementInContainer(container);var prevHostInstance=rootEl&&ReactDOMComponentTree.getInstanceFromNode(rootEl);return prevHostInstance&&!prevHostInstance._hostParent?prevHostInstance:null}function getTopLevelWrapperInContainer(container){var root=getHostRootInstanceInContainer(container);return root?root._hostContainerInfo._topLevelWrapper:null}var topLevelRootCounter=1;var TopLevelWrapper=function(){this.rootID=topLevelRootCounter++};TopLevelWrapper.prototype.isReactComponent={};if(process.env.NODE_ENV!=="production"){TopLevelWrapper.displayName="TopLevelWrapper"}TopLevelWrapper.prototype.render=function(){return this.props.child};TopLevelWrapper.isReactTopLevelWrapper=true;var ReactMount={TopLevelWrapper:TopLevelWrapper,_instancesByReactRootID:instancesByReactRootID,scrollMonitor:function(container,renderCallback){renderCallback()},_updateRootComponent:function(prevComponent,nextElement,nextContext,container,callback){ReactMount.scrollMonitor(container,function(){ReactUpdateQueue.enqueueElementInternal(prevComponent,nextElement,nextContext);if(callback){ReactUpdateQueue.enqueueCallbackInternal(prevComponent,callback)}});return prevComponent},_renderNewRootComponent:function(nextElement,container,shouldReuseMarkup,context){process.env.NODE_ENV!=="production"?warning(ReactCurrentOwner.current==null,"_renderNewRootComponent(): Render methods should be a pure function "+"of props and state; triggering nested component updates from "+"render is not allowed. If necessary, trigger nested updates in "+"componentDidUpdate. Check the render method of %s.",ReactCurrentOwner.current&&ReactCurrentOwner.current.getName()||"ReactCompositeComponent"):void 0;!isValidContainer(container)?process.env.NODE_ENV!=="production"?invariant(false,"_registerComponent(...): Target container is not a DOM element."):_prodInvariant("37"):void 0;ReactBrowserEventEmitter.ensureScrollValueMonitoring();var componentInstance=instantiateReactComponent(nextElement,false);ReactUpdates.batchedUpdates(batchedMountComponentIntoNode,componentInstance,container,shouldReuseMarkup,context);var wrapperID=componentInstance._instance.rootID;instancesByReactRootID[wrapperID]=componentInstance;return componentInstance},renderSubtreeIntoContainer:function(parentComponent,nextElement,container,callback){!(parentComponent!=null&&ReactInstanceMap.has(parentComponent))?process.env.NODE_ENV!=="production"?invariant(false,"parentComponent must be a valid React Component"):_prodInvariant("38"):void 0;return ReactMount._renderSubtreeIntoContainer(parentComponent,nextElement,container,callback)},_renderSubtreeIntoContainer:function(parentComponent,nextElement,container,callback){ReactUpdateQueue.validateCallback(callback,"ReactDOM.render");!React.isValidElement(nextElement)?process.env.NODE_ENV!=="production"?invariant(false,"ReactDOM.render(): Invalid component element.%s",typeof nextElement==="string"?" Instead of passing a string like 'div', pass "+"React.createElement('div') or <div />.":typeof nextElement==="function"?" Instead of passing a class like Foo, pass "+"React.createElement(Foo) or <Foo />.":nextElement!=null&&nextElement.props!==undefined?" This may be caused by unintentionally loading two independent "+"copies of React.":""):_prodInvariant("39",typeof nextElement==="string"?" Instead of passing a string like 'div', pass "+"React.createElement('div') or <div />.":typeof nextElement==="function"?" Instead of passing a class like Foo, pass "+"React.createElement(Foo) or <Foo />.":nextElement!=null&&nextElement.props!==undefined?" This may be caused by unintentionally loading two independent "+"copies of React.":""):void 0;process.env.NODE_ENV!=="production"?warning(!container||!container.tagName||container.tagName.toUpperCase()!=="BODY","render(): Rendering components directly into document.body is "+"discouraged, since its children are often manipulated by third-party "+"scripts and browser extensions. This may lead to subtle "+"reconciliation issues. Try rendering into a container element created "+"for your app."):void 0;var nextWrappedElement=React.createElement(TopLevelWrapper,{child:nextElement});var nextContext;if(parentComponent){var parentInst=ReactInstanceMap.get(parentComponent);nextContext=parentInst._processChildContext(parentInst._context)}else{nextContext=emptyObject}var prevComponent=getTopLevelWrapperInContainer(container);if(prevComponent){var prevWrappedElement=prevComponent._currentElement;var prevElement=prevWrappedElement.props.child;if(shouldUpdateReactComponent(prevElement,nextElement)){var publicInst=prevComponent._renderedComponent.getPublicInstance();var updatedCallback=callback&&function(){callback.call(publicInst)};ReactMount._updateRootComponent(prevComponent,nextWrappedElement,nextContext,container,updatedCallback);return publicInst}else{ReactMount.unmountComponentAtNode(container)}}var reactRootElement=getReactRootElementInContainer(container);var containerHasReactMarkup=reactRootElement&&!!internalGetID(reactRootElement);var containerHasNonRootReactChild=hasNonRootReactChild(container);if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(!containerHasNonRootReactChild,"render(...): Replacing React-rendered children with a new root "+"component. If you intended to update the children of this node, "+"you should instead have the existing children update their state "+"and render the new components instead of calling ReactDOM.render."):void 0;if(!containerHasReactMarkup||reactRootElement.nextSibling){var rootElementSibling=reactRootElement;while(rootElementSibling){if(internalGetID(rootElementSibling)){process.env.NODE_ENV!=="production"?warning(false,"render(): Target node has markup rendered by React, but there "+"are unrelated nodes as well. This is most commonly caused by "+"white-space inserted around server-rendered markup."):void 0;break}rootElementSibling=rootElementSibling.nextSibling}}}var shouldReuseMarkup=containerHasReactMarkup&&!prevComponent&&!containerHasNonRootReactChild;var component=ReactMount._renderNewRootComponent(nextWrappedElement,container,shouldReuseMarkup,nextContext)._renderedComponent.getPublicInstance();if(callback){callback.call(component)}return component},render:function(nextElement,container,callback){return ReactMount._renderSubtreeIntoContainer(null,nextElement,container,callback)},unmountComponentAtNode:function(container){process.env.NODE_ENV!=="production"?warning(ReactCurrentOwner.current==null,"unmountComponentAtNode(): Render methods should be a pure function "+"of props and state; triggering nested component updates from render "+"is not allowed. If necessary, trigger nested updates in "+"componentDidUpdate. Check the render method of %s.",ReactCurrentOwner.current&&ReactCurrentOwner.current.getName()||"ReactCompositeComponent"):void 0;!isValidContainer(container)?process.env.NODE_ENV!=="production"?invariant(false,"unmountComponentAtNode(...): Target container is not a DOM element."):_prodInvariant("40"):void 0;if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(!nodeIsRenderedByOtherInstance(container),"unmountComponentAtNode(): The node you're attempting to unmount "+"was rendered by another copy of React."):void 0}var prevComponent=getTopLevelWrapperInContainer(container);if(!prevComponent){var containerHasNonRootReactChild=hasNonRootReactChild(container);var isContainerReactRoot=container.nodeType===1&&container.hasAttribute(ROOT_ATTR_NAME);if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(!containerHasNonRootReactChild,"unmountComponentAtNode(): The node you're attempting to unmount "+"was rendered by React and is not a top-level container. %s",isContainerReactRoot?"You may have accidentally passed in a React root node instead "+"of its container.":"Instead, have the parent component update its state and "+"rerender in order to remove this component."):void 0}return false}delete instancesByReactRootID[prevComponent._instance.rootID];ReactUpdates.batchedUpdates(unmountComponentFromNode,prevComponent,container,false);return true},_mountImageIntoNode:function(markup,container,instance,shouldReuseMarkup,transaction){!isValidContainer(container)?process.env.NODE_ENV!=="production"?invariant(false,"mountComponentIntoNode(...): Target container is not valid."):_prodInvariant("41"):void 0;if(shouldReuseMarkup){var rootElement=getReactRootElementInContainer(container);if(ReactMarkupChecksum.canReuseMarkup(markup,rootElement)){ReactDOMComponentTree.precacheNode(instance,rootElement);return}else{var checksum=rootElement.getAttribute(ReactMarkupChecksum.CHECKSUM_ATTR_NAME);rootElement.removeAttribute(ReactMarkupChecksum.CHECKSUM_ATTR_NAME);var rootMarkup=rootElement.outerHTML;rootElement.setAttribute(ReactMarkupChecksum.CHECKSUM_ATTR_NAME,checksum);var normalizedMarkup=markup;if(process.env.NODE_ENV!=="production"){var normalizer;if(container.nodeType===ELEMENT_NODE_TYPE){normalizer=document.createElement("div");normalizer.innerHTML=markup;normalizedMarkup=normalizer.innerHTML}else{normalizer=document.createElement("iframe");document.body.appendChild(normalizer);normalizer.contentDocument.write(markup);normalizedMarkup=normalizer.contentDocument.documentElement.outerHTML;document.body.removeChild(normalizer)}}var diffIndex=firstDifferenceIndex(normalizedMarkup,rootMarkup);var difference=" (client) "+normalizedMarkup.substring(diffIndex-20,diffIndex+20)+"\n (server) "+rootMarkup.substring(diffIndex-20,diffIndex+20);!(container.nodeType!==DOC_NODE_TYPE)?process.env.NODE_ENV!=="production"?invariant(false,"You're trying to render a component to the document using server rendering but the checksum was invalid. This usually means you rendered a different component type or props on the client from the one on the server, or your render() methods are impure. React cannot handle this case due to cross-browser quirks by rendering at the document root. You should look for environment dependent code in your components and ensure the props are the same client and server side:\n%s",difference):_prodInvariant("42",difference):void 0;if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(false,"React attempted to reuse markup in a container but the "+"checksum was invalid. This generally means that you are "+"using server rendering and the markup generated on the "+"server was not what the client was expecting. React injected "+"new markup to compensate which works but you have lost many "+"of the benefits of server rendering. Instead, figure out "+"why the markup being generated is different on the client "+"or server:\n%s",difference):void 0}}}!(container.nodeType!==DOC_NODE_TYPE)?process.env.NODE_ENV!=="production"?invariant(false,"You're trying to render a component to the document but you didn't use server rendering. We can't do this without using server rendering due to cross-browser quirks. See ReactDOMServer.renderToString() for server rendering."):_prodInvariant("43"):void 0;if(transaction.useCreateElement){while(container.lastChild){container.removeChild(container.lastChild)}DOMLazyTree.insertTreeBefore(container,markup,null)}else{setInnerHTML(container,markup);ReactDOMComponentTree.precacheNode(instance,container.firstChild)}if(process.env.NODE_ENV!=="production"){var hostNode=ReactDOMComponentTree.getInstanceFromNode(container.firstChild);if(hostNode._debugID!==0){ReactInstrumentation.debugTool.onHostOperation({instanceID:hostNode._debugID,type:"mount",payload:markup.toString()})}}}};module.exports=ReactMount}).call(this,require("_process"))},{"./DOMLazyTree":40,"./DOMProperty":42,"./ReactBrowserEventEmitter":56,"./ReactDOMComponentTree":64,"./ReactDOMContainerInfo":65,"./ReactDOMFeatureFlags":67,"./ReactFeatureFlags":87,"./ReactInstanceMap":92,"./ReactInstrumentation":93,"./ReactMarkupChecksum":95,"./ReactReconciler":103,"./ReactUpdateQueue":107,"./ReactUpdates":108,"./instantiateReactComponent":147,"./reactProdInvariant":151,"./setInnerHTML":153,"./shouldUpdateReactComponent":155,_process:184,"fbjs/lib/emptyObject":11,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"react/lib/React":160,"react/lib/ReactCurrentOwner":164}],97:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactComponentEnvironment=require("./ReactComponentEnvironment");var ReactInstanceMap=require("./ReactInstanceMap");var ReactInstrumentation=require("./ReactInstrumentation");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var ReactReconciler=require("./ReactReconciler");var ReactChildReconciler=require("./ReactChildReconciler");var emptyFunction=require("fbjs/lib/emptyFunction");var flattenChildren=require("./flattenChildren");var invariant=require("fbjs/lib/invariant");function makeInsertMarkup(markup,afterNode,toIndex){return{type:"INSERT_MARKUP",content:markup,fromIndex:null,fromNode:null,toIndex:toIndex,afterNode:afterNode}}function makeMove(child,afterNode,toIndex){return{type:"MOVE_EXISTING",content:null,fromIndex:child._mountIndex,fromNode:ReactReconciler.getHostNode(child),toIndex:toIndex,afterNode:afterNode}}function makeRemove(child,node){return{type:"REMOVE_NODE",content:null,fromIndex:child._mountIndex,fromNode:node,toIndex:null,afterNode:null}}function makeSetMarkup(markup){return{type:"SET_MARKUP",content:markup,fromIndex:null,fromNode:null,toIndex:null,afterNode:null}}function makeTextContent(textContent){return{type:"TEXT_CONTENT",content:textContent,fromIndex:null,fromNode:null,toIndex:null,afterNode:null}}function enqueue(queue,update){if(update){queue=queue||[];queue.push(update)}return queue}function processQueue(inst,updateQueue){ReactComponentEnvironment.processChildrenUpdates(inst,updateQueue)}var setChildrenForInstrumentation=emptyFunction;if(process.env.NODE_ENV!=="production"){var getDebugID=function(inst){if(!inst._debugID){var internal;if(internal=ReactInstanceMap.get(inst)){inst=internal}}return inst._debugID};setChildrenForInstrumentation=function(children){var debugID=getDebugID(this);if(debugID!==0){ReactInstrumentation.debugTool.onSetChildren(debugID,children?Object.keys(children).map(function(key){return children[key]._debugID}):[])}}}var ReactMultiChild={Mixin:{_reconcilerInstantiateChildren:function(nestedChildren,transaction,context){if(process.env.NODE_ENV!=="production"){var selfDebugID=getDebugID(this);if(this._currentElement){try{ReactCurrentOwner.current=this._currentElement._owner;return ReactChildReconciler.instantiateChildren(nestedChildren,transaction,context,selfDebugID)}finally{ReactCurrentOwner.current=null}}}return ReactChildReconciler.instantiateChildren(nestedChildren,transaction,context)},_reconcilerUpdateChildren:function(prevChildren,nextNestedChildrenElements,mountImages,removedNodes,transaction,context){var nextChildren;var selfDebugID=0;if(process.env.NODE_ENV!=="production"){selfDebugID=getDebugID(this);if(this._currentElement){try{ReactCurrentOwner.current=this._currentElement._owner;nextChildren=flattenChildren(nextNestedChildrenElements,selfDebugID)}finally{ReactCurrentOwner.current=null}ReactChildReconciler.updateChildren(prevChildren,nextChildren,mountImages,removedNodes,transaction,this,this._hostContainerInfo,context,selfDebugID);return nextChildren}}nextChildren=flattenChildren(nextNestedChildrenElements,selfDebugID);ReactChildReconciler.updateChildren(prevChildren,nextChildren,mountImages,removedNodes,transaction,this,this._hostContainerInfo,context,selfDebugID);return nextChildren},mountChildren:function(nestedChildren,transaction,context){var children=this._reconcilerInstantiateChildren(nestedChildren,transaction,context);this._renderedChildren=children;var mountImages=[];var index=0;for(var name in children){if(children.hasOwnProperty(name)){var child=children[name];var selfDebugID=0;if(process.env.NODE_ENV!=="production"){selfDebugID=getDebugID(this)}var mountImage=ReactReconciler.mountComponent(child,transaction,this,this._hostContainerInfo,context,selfDebugID);child._mountIndex=index++;mountImages.push(mountImage)}}if(process.env.NODE_ENV!=="production"){setChildrenForInstrumentation.call(this,children)}return mountImages},updateTextContent:function(nextContent){var prevChildren=this._renderedChildren;ReactChildReconciler.unmountChildren(prevChildren,false);for(var name in prevChildren){if(prevChildren.hasOwnProperty(name)){!false?process.env.NODE_ENV!=="production"?invariant(false,"updateTextContent called on non-empty component."):_prodInvariant("118"):void 0}}var updates=[makeTextContent(nextContent)];processQueue(this,updates)},updateMarkup:function(nextMarkup){var prevChildren=this._renderedChildren;ReactChildReconciler.unmountChildren(prevChildren,false);for(var name in prevChildren){if(prevChildren.hasOwnProperty(name)){!false?process.env.NODE_ENV!=="production"?invariant(false,"updateTextContent called on non-empty component."):_prodInvariant("118"):void 0}}var updates=[makeSetMarkup(nextMarkup)];processQueue(this,updates)},updateChildren:function(nextNestedChildrenElements,transaction,context){this._updateChildren(nextNestedChildrenElements,transaction,context)},_updateChildren:function(nextNestedChildrenElements,transaction,context){var prevChildren=this._renderedChildren;var removedNodes={};var mountImages=[];var nextChildren=this._reconcilerUpdateChildren(prevChildren,nextNestedChildrenElements,mountImages,removedNodes,transaction,context);if(!nextChildren&&!prevChildren){return}var updates=null;var name;var nextIndex=0;var lastIndex=0;var nextMountIndex=0;var lastPlacedNode=null;for(name in nextChildren){if(!nextChildren.hasOwnProperty(name)){continue}var prevChild=prevChildren&&prevChildren[name];var nextChild=nextChildren[name];if(prevChild===nextChild){updates=enqueue(updates,this.moveChild(prevChild,lastPlacedNode,nextIndex,lastIndex));lastIndex=Math.max(prevChild._mountIndex,lastIndex);prevChild._mountIndex=nextIndex}else{if(prevChild){lastIndex=Math.max(prevChild._mountIndex,lastIndex)}updates=enqueue(updates,this._mountChildAtIndex(nextChild,mountImages[nextMountIndex],lastPlacedNode,nextIndex,transaction,context));nextMountIndex++}nextIndex++;lastPlacedNode=ReactReconciler.getHostNode(nextChild)}for(name in removedNodes){if(removedNodes.hasOwnProperty(name)){updates=enqueue(updates,this._unmountChild(prevChildren[name],removedNodes[name]))}}if(updates){processQueue(this,updates)}this._renderedChildren=nextChildren;if(process.env.NODE_ENV!=="production"){setChildrenForInstrumentation.call(this,nextChildren)}},unmountChildren:function(safely){var renderedChildren=this._renderedChildren;ReactChildReconciler.unmountChildren(renderedChildren,safely);this._renderedChildren=null},moveChild:function(child,afterNode,toIndex,lastIndex){if(child._mountIndex<lastIndex){return makeMove(child,afterNode,toIndex)}},createChild:function(child,afterNode,mountImage){return makeInsertMarkup(mountImage,afterNode,child._mountIndex)},removeChild:function(child,node){return makeRemove(child,node)},_mountChildAtIndex:function(child,mountImage,afterNode,index,transaction,context){child._mountIndex=index;return this.createChild(child,afterNode,mountImage)},_unmountChild:function(child,node){var update=this.removeChild(child,node);child._mountIndex=null;return update}}};module.exports=ReactMultiChild}).call(this,require("_process"))},{"./ReactChildReconciler":57,"./ReactComponentEnvironment":59,"./ReactInstanceMap":92,"./ReactInstrumentation":93,"./ReactReconciler":103,"./flattenChildren":135,"./reactProdInvariant":151,_process:184,"fbjs/lib/emptyFunction":10,"fbjs/lib/invariant":18,"react/lib/ReactCurrentOwner":164}],98:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var React=require("react/lib/React");var invariant=require("fbjs/lib/invariant");var ReactNodeTypes={HOST:0,COMPOSITE:1,EMPTY:2,getType:function(node){if(node===null||node===false){return ReactNodeTypes.EMPTY}else if(React.isValidElement(node)){if(typeof node.type==="function"){return ReactNodeTypes.COMPOSITE}else{return ReactNodeTypes.HOST}}!false?process.env.NODE_ENV!=="production"?invariant(false,"Unexpected node: %s",node):_prodInvariant("26",node):void 0}};module.exports=ReactNodeTypes}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"react/lib/React":160}],99:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");function isValidOwner(object){return!!(object&&typeof object.attachRef==="function"&&typeof object.detachRef==="function")}var ReactOwner={addComponentAsRefTo:function(component,ref,owner){!isValidOwner(owner)?process.env.NODE_ENV!=="production"?invariant(false,"addComponentAsRefTo(...): Only a ReactOwner can have refs. You might be adding a ref to a component that was not created inside a component's `render` method, or you have multiple copies of React loaded (details: https://fb.me/react-refs-must-have-owner)."):_prodInvariant("119"):void 0;owner.attachRef(ref,component)},removeComponentAsRefFrom:function(component,ref,owner){!isValidOwner(owner)?process.env.NODE_ENV!=="production"?invariant(false,"removeComponentAsRefFrom(...): Only a ReactOwner can have refs. You might be removing a ref to a component that was not created inside a component's `render` method, or you have multiple copies of React loaded (details: https://fb.me/react-refs-must-have-owner)."):_prodInvariant("120"):void 0;var ownerPublicInstance=owner.getPublicInstance();if(ownerPublicInstance&&ownerPublicInstance.refs[ref]===component.getPublicInstance()){owner.detachRef(ref)}}};module.exports=ReactOwner}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],100:[function(require,module,exports){(function(process){"use strict";var ReactPropTypeLocationNames={};if(process.env.NODE_ENV!=="production"){ReactPropTypeLocationNames={prop:"prop",context:"context",childContext:"child context"}}module.exports=ReactPropTypeLocationNames}).call(this,require("_process"))},{_process:184}],101:[function(require,module,exports){"use strict";var ReactPropTypesSecret="SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED";module.exports=ReactPropTypesSecret},{}],102:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var CallbackQueue=require("./CallbackQueue");var PooledClass=require("./PooledClass");var ReactBrowserEventEmitter=require("./ReactBrowserEventEmitter");var ReactInputSelection=require("./ReactInputSelection");var ReactInstrumentation=require("./ReactInstrumentation");var Transaction=require("./Transaction");var ReactUpdateQueue=require("./ReactUpdateQueue");var SELECTION_RESTORATION={initialize:ReactInputSelection.getSelectionInformation,close:ReactInputSelection.restoreSelection};var EVENT_SUPPRESSION={initialize:function(){var currentlyEnabled=ReactBrowserEventEmitter.isEnabled();ReactBrowserEventEmitter.setEnabled(false);return currentlyEnabled},close:function(previouslyEnabled){ReactBrowserEventEmitter.setEnabled(previouslyEnabled)}};var ON_DOM_READY_QUEUEING={initialize:function(){this.reactMountReady.reset()},close:function(){this.reactMountReady.notifyAll()}};var TRANSACTION_WRAPPERS=[SELECTION_RESTORATION,EVENT_SUPPRESSION,ON_DOM_READY_QUEUEING];if(process.env.NODE_ENV!=="production"){TRANSACTION_WRAPPERS.push({initialize:ReactInstrumentation.debugTool.onBeginFlush,close:ReactInstrumentation.debugTool.onEndFlush})}function ReactReconcileTransaction(useCreateElement){this.reinitializeTransaction();this.renderToStaticMarkup=false;this.reactMountReady=CallbackQueue.getPooled(null);this.useCreateElement=useCreateElement}var Mixin={getTransactionWrappers:function(){return TRANSACTION_WRAPPERS},getReactMountReady:function(){return this.reactMountReady},getUpdateQueue:function(){return ReactUpdateQueue},checkpoint:function(){return this.reactMountReady.checkpoint()},rollback:function(checkpoint){this.reactMountReady.rollback(checkpoint)},destructor:function(){CallbackQueue.release(this.reactMountReady);this.reactMountReady=null}};_assign(ReactReconcileTransaction.prototype,Transaction,Mixin);PooledClass.addPoolingTo(ReactReconcileTransaction);module.exports=ReactReconcileTransaction}).call(this,require("_process"))},{"./CallbackQueue":37,"./PooledClass":55,"./ReactBrowserEventEmitter":56,"./ReactInputSelection":91,"./ReactInstrumentation":93,"./ReactUpdateQueue":107,"./Transaction":126,_process:184,"object-assign":26}],103:[function(require,module,exports){(function(process){"use strict";var ReactRef=require("./ReactRef");var ReactInstrumentation=require("./ReactInstrumentation");var warning=require("fbjs/lib/warning");function attachRefs(){ReactRef.attachRefs(this,this._currentElement)}var ReactReconciler={mountComponent:function(internalInstance,transaction,hostParent,hostContainerInfo,context,parentDebugID){if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onBeforeMountComponent(internalInstance._debugID,internalInstance._currentElement,parentDebugID)}}var markup=internalInstance.mountComponent(transaction,hostParent,hostContainerInfo,context,parentDebugID);if(internalInstance._currentElement&&internalInstance._currentElement.ref!=null){transaction.getReactMountReady().enqueue(attachRefs,internalInstance)}if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onMountComponent(internalInstance._debugID)}}return markup},getHostNode:function(internalInstance){return internalInstance.getHostNode()},unmountComponent:function(internalInstance,safely){if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onBeforeUnmountComponent(internalInstance._debugID)}}ReactRef.detachRefs(internalInstance,internalInstance._currentElement);internalInstance.unmountComponent(safely);if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onUnmountComponent(internalInstance._debugID)}}},receiveComponent:function(internalInstance,nextElement,transaction,context){var prevElement=internalInstance._currentElement;if(nextElement===prevElement&&context===internalInstance._context){return}if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onBeforeUpdateComponent(internalInstance._debugID,nextElement)}}var refsChanged=ReactRef.shouldUpdateRefs(prevElement,nextElement);if(refsChanged){ReactRef.detachRefs(internalInstance,prevElement)}internalInstance.receiveComponent(nextElement,transaction,context);if(refsChanged&&internalInstance._currentElement&&internalInstance._currentElement.ref!=null){transaction.getReactMountReady().enqueue(attachRefs,internalInstance)}if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onUpdateComponent(internalInstance._debugID)}}},performUpdateIfNecessary:function(internalInstance,transaction,updateBatchNumber){if(internalInstance._updateBatchNumber!==updateBatchNumber){process.env.NODE_ENV!=="production"?warning(internalInstance._updateBatchNumber==null||internalInstance._updateBatchNumber===updateBatchNumber+1,"performUpdateIfNecessary: Unexpected batch number (current %s, "+"pending %s)",updateBatchNumber,internalInstance._updateBatchNumber):void 0;return}if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onBeforeUpdateComponent(internalInstance._debugID,internalInstance._currentElement)}}internalInstance.performUpdateIfNecessary(transaction);if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onUpdateComponent(internalInstance._debugID)}}}};module.exports=ReactReconciler}).call(this,require("_process"))},{"./ReactInstrumentation":93,"./ReactRef":104,_process:184,"fbjs/lib/warning":25}],104:[function(require,module,exports){"use strict";var ReactOwner=require("./ReactOwner");var ReactRef={};function attachRef(ref,component,owner){if(typeof ref==="function"){ref(component.getPublicInstance())}else{ReactOwner.addComponentAsRefTo(component,ref,owner)}}function detachRef(ref,component,owner){if(typeof ref==="function"){ref(null)}else{ReactOwner.removeComponentAsRefFrom(component,ref,owner)}}ReactRef.attachRefs=function(instance,element){if(element===null||typeof element!=="object"){return}var ref=element.ref;if(ref!=null){attachRef(ref,instance,element._owner)}};ReactRef.shouldUpdateRefs=function(prevElement,nextElement){var prevRef=null;var prevOwner=null;if(prevElement!==null&&typeof prevElement==="object"){prevRef=prevElement.ref;prevOwner=prevElement._owner}var nextRef=null;var nextOwner=null;if(nextElement!==null&&typeof nextElement==="object"){nextRef=nextElement.ref;nextOwner=nextElement._owner}return prevRef!==nextRef||typeof nextRef==="string"&&nextOwner!==prevOwner};ReactRef.detachRefs=function(instance,element){if(element===null||typeof element!=="object"){return}var ref=element.ref;if(ref!=null){detachRef(ref,instance,element._owner)}};module.exports=ReactRef},{"./ReactOwner":99}],105:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var PooledClass=require("./PooledClass");var Transaction=require("./Transaction");var ReactInstrumentation=require("./ReactInstrumentation");var ReactServerUpdateQueue=require("./ReactServerUpdateQueue");var TRANSACTION_WRAPPERS=[];if(process.env.NODE_ENV!=="production"){TRANSACTION_WRAPPERS.push({initialize:ReactInstrumentation.debugTool.onBeginFlush,close:ReactInstrumentation.debugTool.onEndFlush})}var noopCallbackQueue={enqueue:function(){}};function ReactServerRenderingTransaction(renderToStaticMarkup){this.reinitializeTransaction();this.renderToStaticMarkup=renderToStaticMarkup;this.useCreateElement=false;this.updateQueue=new ReactServerUpdateQueue(this)}var Mixin={getTransactionWrappers:function(){return TRANSACTION_WRAPPERS},getReactMountReady:function(){return noopCallbackQueue},getUpdateQueue:function(){return this.updateQueue},destructor:function(){},checkpoint:function(){},rollback:function(){}};_assign(ReactServerRenderingTransaction.prototype,Transaction,Mixin);PooledClass.addPoolingTo(ReactServerRenderingTransaction);module.exports=ReactServerRenderingTransaction}).call(this,require("_process"))},{"./PooledClass":55,"./ReactInstrumentation":93,"./ReactServerUpdateQueue":106,"./Transaction":126,_process:184,"object-assign":26}],106:[function(require,module,exports){(function(process){"use strict";function _classCallCheck(instance,Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function")}}var ReactUpdateQueue=require("./ReactUpdateQueue");var warning=require("fbjs/lib/warning");function warnNoop(publicInstance,callerName){if(process.env.NODE_ENV!=="production"){var constructor=publicInstance.constructor;process.env.NODE_ENV!=="production"?warning(false,"%s(...): Can only update a mounting component. "+"This usually means you called %s() outside componentWillMount() on the server. "+"This is a no-op. Please check the code for the %s component.",callerName,callerName,constructor&&(constructor.displayName||constructor.name)||"ReactClass"):void 0}}var ReactServerUpdateQueue=function(){function ReactServerUpdateQueue(transaction){_classCallCheck(this,ReactServerUpdateQueue);this.transaction=transaction}ReactServerUpdateQueue.prototype.isMounted=function isMounted(publicInstance){return false};ReactServerUpdateQueue.prototype.enqueueCallback=function enqueueCallback(publicInstance,callback,callerName){if(this.transaction.isInTransaction()){ReactUpdateQueue.enqueueCallback(publicInstance,callback,callerName)}};ReactServerUpdateQueue.prototype.enqueueForceUpdate=function enqueueForceUpdate(publicInstance){if(this.transaction.isInTransaction()){ReactUpdateQueue.enqueueForceUpdate(publicInstance)}else{warnNoop(publicInstance,"forceUpdate")}};ReactServerUpdateQueue.prototype.enqueueReplaceState=function enqueueReplaceState(publicInstance,completeState){if(this.transaction.isInTransaction()){ReactUpdateQueue.enqueueReplaceState(publicInstance,completeState)}else{warnNoop(publicInstance,"replaceState")}};ReactServerUpdateQueue.prototype.enqueueSetState=function enqueueSetState(publicInstance,partialState){if(this.transaction.isInTransaction()){ReactUpdateQueue.enqueueSetState(publicInstance,partialState)}else{warnNoop(publicInstance,"setState")}};return ReactServerUpdateQueue}();module.exports=ReactServerUpdateQueue}).call(this,require("_process"))},{"./ReactUpdateQueue":107,_process:184,"fbjs/lib/warning":25}],107:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var ReactInstanceMap=require("./ReactInstanceMap");var ReactInstrumentation=require("./ReactInstrumentation");var ReactUpdates=require("./ReactUpdates");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");function enqueueUpdate(internalInstance){ReactUpdates.enqueueUpdate(internalInstance)}function formatUnexpectedArgument(arg){var type=typeof arg;if(type!=="object"){return type}var displayName=arg.constructor&&arg.constructor.name||type;var keys=Object.keys(arg);if(keys.length>0&&keys.length<20){return displayName+" (keys: "+keys.join(", ")+")"}return displayName}function getInternalInstanceReadyForUpdate(publicInstance,callerName){var internalInstance=ReactInstanceMap.get(publicInstance);if(!internalInstance){if(process.env.NODE_ENV!=="production"){var ctor=publicInstance.constructor;process.env.NODE_ENV!=="production"?warning(!callerName,"%s(...): Can only update a mounted or mounting component. "+"This usually means you called %s() on an unmounted component. "+"This is a no-op. Please check the code for the %s component.",callerName,callerName,ctor&&(ctor.displayName||ctor.name)||"ReactClass"):void 0}return null}if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(ReactCurrentOwner.current==null,"%s(...): Cannot update during an existing state transition (such as "+"within `render` or another component's constructor). Render methods "+"should be a pure function of props and state; constructor "+"side-effects are an anti-pattern, but can be moved to "+"`componentWillMount`.",callerName):void 0}return internalInstance}var ReactUpdateQueue={isMounted:function(publicInstance){if(process.env.NODE_ENV!=="production"){var owner=ReactCurrentOwner.current;if(owner!==null){process.env.NODE_ENV!=="production"?warning(owner._warnedAboutRefsInRender,"%s is accessing isMounted inside its render() function. "+"render() should be a pure function of props and state. It should "+"never access something that requires stale data from the previous "+"render, such as refs. Move this logic to componentDidMount and "+"componentDidUpdate instead.",owner.getName()||"A component"):void 0;owner._warnedAboutRefsInRender=true}}var internalInstance=ReactInstanceMap.get(publicInstance);if(internalInstance){return!!internalInstance._renderedComponent}else{return false}},enqueueCallback:function(publicInstance,callback,callerName){ReactUpdateQueue.validateCallback(callback,callerName);var internalInstance=getInternalInstanceReadyForUpdate(publicInstance);if(!internalInstance){return null}if(internalInstance._pendingCallbacks){internalInstance._pendingCallbacks.push(callback)}else{internalInstance._pendingCallbacks=[callback]}enqueueUpdate(internalInstance)},enqueueCallbackInternal:function(internalInstance,callback){if(internalInstance._pendingCallbacks){internalInstance._pendingCallbacks.push(callback)}else{internalInstance._pendingCallbacks=[callback]}enqueueUpdate(internalInstance)},enqueueForceUpdate:function(publicInstance){var internalInstance=getInternalInstanceReadyForUpdate(publicInstance,"forceUpdate");if(!internalInstance){return}internalInstance._pendingForceUpdate=true;enqueueUpdate(internalInstance)},enqueueReplaceState:function(publicInstance,completeState,callback){var internalInstance=getInternalInstanceReadyForUpdate(publicInstance,"replaceState");if(!internalInstance){return}internalInstance._pendingStateQueue=[completeState];internalInstance._pendingReplaceState=true;if(callback!==undefined&&callback!==null){ReactUpdateQueue.validateCallback(callback,"replaceState");if(internalInstance._pendingCallbacks){internalInstance._pendingCallbacks.push(callback)}else{internalInstance._pendingCallbacks=[callback]}}enqueueUpdate(internalInstance)},enqueueSetState:function(publicInstance,partialState){if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onSetState();process.env.NODE_ENV!=="production"?warning(partialState!=null,"setState(...): You passed an undefined or null state object; "+"instead, use forceUpdate()."):void 0}var internalInstance=getInternalInstanceReadyForUpdate(publicInstance,"setState");if(!internalInstance){return}var queue=internalInstance._pendingStateQueue||(internalInstance._pendingStateQueue=[]);queue.push(partialState);enqueueUpdate(internalInstance)},enqueueElementInternal:function(internalInstance,nextElement,nextContext){internalInstance._pendingElement=nextElement;internalInstance._context=nextContext;enqueueUpdate(internalInstance)},validateCallback:function(callback,callerName){!(!callback||typeof callback==="function")?process.env.NODE_ENV!=="production"?invariant(false,"%s(...): Expected the last optional `callback` argument to be a function. Instead received: %s.",callerName,formatUnexpectedArgument(callback)):_prodInvariant("122",callerName,formatUnexpectedArgument(callback)):void 0}};module.exports=ReactUpdateQueue}).call(this,require("_process"))},{"./ReactInstanceMap":92,"./ReactInstrumentation":93,"./ReactUpdates":108,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"react/lib/ReactCurrentOwner":164}],108:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var CallbackQueue=require("./CallbackQueue");var PooledClass=require("./PooledClass");var ReactFeatureFlags=require("./ReactFeatureFlags");var ReactReconciler=require("./ReactReconciler");var Transaction=require("./Transaction");var invariant=require("fbjs/lib/invariant");var dirtyComponents=[];var updateBatchNumber=0;var asapCallbackQueue=CallbackQueue.getPooled();var asapEnqueued=false;var batchingStrategy=null;function ensureInjected(){!(ReactUpdates.ReactReconcileTransaction&&batchingStrategy)?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates: must inject a reconcile transaction class and batching strategy"):_prodInvariant("123"):void 0}var NESTED_UPDATES={initialize:function(){this.dirtyComponentsLength=dirtyComponents.length},close:function(){if(this.dirtyComponentsLength!==dirtyComponents.length){dirtyComponents.splice(0,this.dirtyComponentsLength);flushBatchedUpdates()}else{dirtyComponents.length=0}}};var UPDATE_QUEUEING={initialize:function(){this.callbackQueue.reset()},close:function(){this.callbackQueue.notifyAll()}};var TRANSACTION_WRAPPERS=[NESTED_UPDATES,UPDATE_QUEUEING];function ReactUpdatesFlushTransaction(){this.reinitializeTransaction();this.dirtyComponentsLength=null;this.callbackQueue=CallbackQueue.getPooled();this.reconcileTransaction=ReactUpdates.ReactReconcileTransaction.getPooled(true)}_assign(ReactUpdatesFlushTransaction.prototype,Transaction,{getTransactionWrappers:function(){return TRANSACTION_WRAPPERS},destructor:function(){this.dirtyComponentsLength=null;CallbackQueue.release(this.callbackQueue);this.callbackQueue=null;ReactUpdates.ReactReconcileTransaction.release(this.reconcileTransaction);this.reconcileTransaction=null},perform:function(method,scope,a){return Transaction.perform.call(this,this.reconcileTransaction.perform,this.reconcileTransaction,method,scope,a)}});PooledClass.addPoolingTo(ReactUpdatesFlushTransaction);function batchedUpdates(callback,a,b,c,d,e){ensureInjected();return batchingStrategy.batchedUpdates(callback,a,b,c,d,e)}function mountOrderComparator(c1,c2){return c1._mountOrder-c2._mountOrder}function runBatchedUpdates(transaction){var len=transaction.dirtyComponentsLength;!(len===dirtyComponents.length)?process.env.NODE_ENV!=="production"?invariant(false,"Expected flush transaction's stored dirty-components length (%s) to match dirty-components array length (%s).",len,dirtyComponents.length):_prodInvariant("124",len,dirtyComponents.length):void 0;dirtyComponents.sort(mountOrderComparator);updateBatchNumber++;for(var i=0;i<len;i++){var component=dirtyComponents[i];var callbacks=component._pendingCallbacks;component._pendingCallbacks=null;var markerName;if(ReactFeatureFlags.logTopLevelRenders){var namedComponent=component;if(component._currentElement.type.isReactTopLevelWrapper){namedComponent=component._renderedComponent}markerName="React update: "+namedComponent.getName();console.time(markerName)}ReactReconciler.performUpdateIfNecessary(component,transaction.reconcileTransaction,updateBatchNumber);if(markerName){console.timeEnd(markerName)}if(callbacks){for(var j=0;j<callbacks.length;j++){transaction.callbackQueue.enqueue(callbacks[j],component.getPublicInstance())}}}}var flushBatchedUpdates=function(){while(dirtyComponents.length||asapEnqueued){if(dirtyComponents.length){var transaction=ReactUpdatesFlushTransaction.getPooled();transaction.perform(runBatchedUpdates,null,transaction);ReactUpdatesFlushTransaction.release(transaction)}if(asapEnqueued){asapEnqueued=false;var queue=asapCallbackQueue;asapCallbackQueue=CallbackQueue.getPooled();queue.notifyAll();CallbackQueue.release(queue)}}};function enqueueUpdate(component){ensureInjected();if(!batchingStrategy.isBatchingUpdates){batchingStrategy.batchedUpdates(enqueueUpdate,component);return}dirtyComponents.push(component);if(component._updateBatchNumber==null){component._updateBatchNumber=updateBatchNumber+1}}function asap(callback,context){!batchingStrategy.isBatchingUpdates?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates.asap: Can't enqueue an asap callback in a context whereupdates are not being batched."):_prodInvariant("125"):void 0;asapCallbackQueue.enqueue(callback,context);asapEnqueued=true}var ReactUpdatesInjection={injectReconcileTransaction:function(ReconcileTransaction){!ReconcileTransaction?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates: must provide a reconcile transaction class"):_prodInvariant("126"):void 0;ReactUpdates.ReactReconcileTransaction=ReconcileTransaction},injectBatchingStrategy:function(_batchingStrategy){!_batchingStrategy?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates: must provide a batching strategy"):_prodInvariant("127"):void 0;!(typeof _batchingStrategy.batchedUpdates==="function")?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates: must provide a batchedUpdates() function"):_prodInvariant("128"):void 0;!(typeof _batchingStrategy.isBatchingUpdates==="boolean")?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates: must provide an isBatchingUpdates boolean attribute"):_prodInvariant("129"):void 0;batchingStrategy=_batchingStrategy}};var ReactUpdates={ReactReconcileTransaction:null,batchedUpdates:batchedUpdates,enqueueUpdate:enqueueUpdate,flushBatchedUpdates:flushBatchedUpdates,injection:ReactUpdatesInjection,asap:asap};module.exports=ReactUpdates}).call(this,require("_process"))},{"./CallbackQueue":37,"./PooledClass":55,"./ReactFeatureFlags":87,"./ReactReconciler":103,"./Transaction":126,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"object-assign":26}],109:[function(require,module,exports){"use strict";module.exports="15.6.1"},{}],110:[function(require,module,exports){"use strict";var NS={xlink:"http://www.w3.org/1999/xlink",xml:"http://www.w3.org/XML/1998/namespace"};var ATTRS={accentHeight:"accent-height",accumulate:0,additive:0,alignmentBaseline:"alignment-baseline",allowReorder:"allowReorder",alphabetic:0,amplitude:0,arabicForm:"arabic-form",ascent:0,attributeName:"attributeName",attributeType:"attributeType",autoReverse:"autoReverse",azimuth:0,baseFrequency:"baseFrequency",baseProfile:"baseProfile",baselineShift:"baseline-shift",bbox:0,begin:0,bias:0,by:0,calcMode:"calcMode",capHeight:"cap-height",clip:0,clipPath:"clip-path",clipRule:"clip-rule",clipPathUnits:"clipPathUnits",colorInterpolation:"color-interpolation",colorInterpolationFilters:"color-interpolation-filters",colorProfile:"color-profile",colorRendering:"color-rendering",contentScriptType:"contentScriptType",contentStyleType:"contentStyleType",cursor:0,cx:0,cy:0,d:0,decelerate:0,descent:0,diffuseConstant:"diffuseConstant",direction:0,display:0,divisor:0,dominantBaseline:"dominant-baseline",dur:0,dx:0,dy:0,edgeMode:"edgeMode",elevation:0,enableBackground:"enable-background",end:0,exponent:0,externalResourcesRequired:"externalResourcesRequired",fill:0,fillOpacity:"fill-opacity",fillRule:"fill-rule",filter:0,filterRes:"filterRes",filterUnits:"filterUnits",floodColor:"flood-color",floodOpacity:"flood-opacity",focusable:0,fontFamily:"font-family",fontSize:"font-size",fontSizeAdjust:"font-size-adjust",fontStretch:"font-stretch",fontStyle:"font-style",fontVariant:"font-variant",fontWeight:"font-weight",format:0,from:0,fx:0,fy:0,g1:0,g2:0,glyphName:"glyph-name",glyphOrientationHorizontal:"glyph-orientation-horizontal",glyphOrientationVertical:"glyph-orientation-vertical",glyphRef:"glyphRef",gradientTransform:"gradientTransform",gradientUnits:"gradientUnits",hanging:0,horizAdvX:"horiz-adv-x",horizOriginX:"horiz-origin-x",ideographic:0,imageRendering:"image-rendering",in:0,in2:0,intercept:0,k:0,k1:0,k2:0,k3:0,k4:0,kernelMatrix:"kernelMatrix",kernelUnitLength:"kernelUnitLength",kerning:0,keyPoints:"keyPoints",keySplines:"keySplines",keyTimes:"keyTimes",lengthAdjust:"lengthAdjust",letterSpacing:"letter-spacing",lightingColor:"lighting-color",limitingConeAngle:"limitingConeAngle",local:0,markerEnd:"marker-end",markerMid:"marker-mid",markerStart:"marker-start",markerHeight:"markerHeight",markerUnits:"markerUnits",markerWidth:"markerWidth",mask:0,maskContentUnits:"maskContentUnits",maskUnits:"maskUnits",mathematical:0,mode:0,numOctaves:"numOctaves",offset:0,opacity:0,operator:0,order:0,orient:0,orientation:0,origin:0,overflow:0,overlinePosition:"overline-position",overlineThickness:"overline-thickness",paintOrder:"paint-order",panose1:"panose-1",pathLength:"pathLength",patternContentUnits:"patternContentUnits",patternTransform:"patternTransform",patternUnits:"patternUnits",pointerEvents:"pointer-events",points:0,pointsAtX:"pointsAtX",pointsAtY:"pointsAtY",pointsAtZ:"pointsAtZ",preserveAlpha:"preserveAlpha",preserveAspectRatio:"preserveAspectRatio",primitiveUnits:"primitiveUnits",r:0,radius:0,refX:"refX",refY:"refY",renderingIntent:"rendering-intent",repeatCount:"repeatCount",repeatDur:"repeatDur",requiredExtensions:"requiredExtensions",requiredFeatures:"requiredFeatures",restart:0,result:0,rotate:0,rx:0,ry:0,scale:0,seed:0,shapeRendering:"shape-rendering",slope:0,spacing:0,specularConstant:"specularConstant",specularExponent:"specularExponent",speed:0,spreadMethod:"spreadMethod",startOffset:"startOffset",stdDeviation:"stdDeviation",stemh:0,stemv:0,stitchTiles:"stitchTiles",stopColor:"stop-color",stopOpacity:"stop-opacity",strikethroughPosition:"strikethrough-position",strikethroughThickness:"strikethrough-thickness",string:0,stroke:0,strokeDasharray:"stroke-dasharray",strokeDashoffset:"stroke-dashoffset",strokeLinecap:"stroke-linecap",strokeLinejoin:"stroke-linejoin",strokeMiterlimit:"stroke-miterlimit",strokeOpacity:"stroke-opacity",strokeWidth:"stroke-width",surfaceScale:"surfaceScale",systemLanguage:"systemLanguage",tableValues:"tableValues",targetX:"targetX",targetY:"targetY",textAnchor:"text-anchor",textDecoration:"text-decoration",textRendering:"text-rendering",textLength:"textLength",to:0,transform:0,u1:0,u2:0,underlinePosition:"underline-position",underlineThickness:"underline-thickness",unicode:0,unicodeBidi:"unicode-bidi",unicodeRange:"unicode-range",unitsPerEm:"units-per-em",vAlphabetic:"v-alphabetic",vHanging:"v-hanging",vIdeographic:"v-ideographic",vMathematical:"v-mathematical",values:0,vectorEffect:"vector-effect",version:0,vertAdvY:"vert-adv-y",vertOriginX:"vert-origin-x",vertOriginY:"vert-origin-y",viewBox:"viewBox",viewTarget:"viewTarget",visibility:0,widths:0,wordSpacing:"word-spacing",writingMode:"writing-mode",x:0,xHeight:"x-height",x1:0,x2:0,xChannelSelector:"xChannelSelector",xlinkActuate:"xlink:actuate",xlinkArcrole:"xlink:arcrole",xlinkHref:"xlink:href",xlinkRole:"xlink:role",xlinkShow:"xlink:show",xlinkTitle:"xlink:title",xlinkType:"xlink:type",xmlBase:"xml:base",xmlns:0,xmlnsXlink:"xmlns:xlink",xmlLang:"xml:lang",xmlSpace:"xml:space",y:0,y1:0,y2:0,yChannelSelector:"yChannelSelector",z:0,zoomAndPan:"zoomAndPan"};var SVGDOMPropertyConfig={Properties:{},DOMAttributeNamespaces:{xlinkActuate:NS.xlink,xlinkArcrole:NS.xlink,xlinkHref:NS.xlink,xlinkRole:NS.xlink,xlinkShow:NS.xlink,xlinkTitle:NS.xlink,xlinkType:NS.xlink,xmlBase:NS.xml,xmlLang:NS.xml,xmlSpace:NS.xml},DOMAttributeNames:{}};Object.keys(ATTRS).forEach(function(key){SVGDOMPropertyConfig.Properties[key]=0;if(ATTRS[key]){SVGDOMPropertyConfig.DOMAttributeNames[key]=ATTRS[key]}});module.exports=SVGDOMPropertyConfig},{}],111:[function(require,module,exports){"use strict";var EventPropagators=require("./EventPropagators");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactInputSelection=require("./ReactInputSelection");var SyntheticEvent=require("./SyntheticEvent");var getActiveElement=require("fbjs/lib/getActiveElement");var isTextInputElement=require("./isTextInputElement");var shallowEqual=require("fbjs/lib/shallowEqual");var skipSelectionChangeEvent=ExecutionEnvironment.canUseDOM&&"documentMode"in document&&document.documentMode<=11;var eventTypes={select:{phasedRegistrationNames:{bubbled:"onSelect",captured:"onSelectCapture"},dependencies:["topBlur","topContextMenu","topFocus","topKeyDown","topKeyUp","topMouseDown","topMouseUp","topSelectionChange"]}};var activeElement=null;var activeElementInst=null;var lastSelection=null;var mouseDown=false;var hasListener=false;function getSelection(node){if("selectionStart"in node&&ReactInputSelection.hasSelectionCapabilities(node)){return{start:node.selectionStart,end:node.selectionEnd}}else if(window.getSelection){var selection=window.getSelection();return{anchorNode:selection.anchorNode,anchorOffset:selection.anchorOffset,focusNode:selection.focusNode,focusOffset:selection.focusOffset}}else if(document.selection){var range=document.selection.createRange();return{parentElement:range.parentElement(),text:range.text,top:range.boundingTop,left:range.boundingLeft}}}function constructSelectEvent(nativeEvent,nativeEventTarget){if(mouseDown||activeElement==null||activeElement!==getActiveElement()){return null}var currentSelection=getSelection(activeElement);if(!lastSelection||!shallowEqual(lastSelection,currentSelection)){lastSelection=currentSelection;var syntheticEvent=SyntheticEvent.getPooled(eventTypes.select,activeElementInst,nativeEvent,nativeEventTarget);syntheticEvent.type="select";syntheticEvent.target=activeElement;EventPropagators.accumulateTwoPhaseDispatches(syntheticEvent);return syntheticEvent}return null}var SelectEventPlugin={eventTypes:eventTypes,extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){if(!hasListener){return null}var targetNode=targetInst?ReactDOMComponentTree.getNodeFromInstance(targetInst):window;switch(topLevelType){case"topFocus":if(isTextInputElement(targetNode)||targetNode.contentEditable==="true"){activeElement=targetNode;activeElementInst=targetInst;lastSelection=null}break;case"topBlur":activeElement=null;activeElementInst=null;lastSelection=null;break;case"topMouseDown":mouseDown=true;break;case"topContextMenu":case"topMouseUp":mouseDown=false;return constructSelectEvent(nativeEvent,nativeEventTarget);case"topSelectionChange":if(skipSelectionChangeEvent){break}case"topKeyDown":case"topKeyUp":return constructSelectEvent(nativeEvent,nativeEventTarget)}return null},didPutListener:function(inst,registrationName,listener){if(registrationName==="onSelect"){hasListener=true}}};module.exports=SelectEventPlugin},{"./EventPropagators":50,"./ReactDOMComponentTree":64,"./ReactInputSelection":91,"./SyntheticEvent":117,"./isTextInputElement":149,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/getActiveElement":13,"fbjs/lib/shallowEqual":24}],112:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var EventListener=require("fbjs/lib/EventListener");var EventPropagators=require("./EventPropagators");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var SyntheticAnimationEvent=require("./SyntheticAnimationEvent");var SyntheticClipboardEvent=require("./SyntheticClipboardEvent");var SyntheticEvent=require("./SyntheticEvent");var SyntheticFocusEvent=require("./SyntheticFocusEvent");var SyntheticKeyboardEvent=require("./SyntheticKeyboardEvent");var SyntheticMouseEvent=require("./SyntheticMouseEvent");var SyntheticDragEvent=require("./SyntheticDragEvent");var SyntheticTouchEvent=require("./SyntheticTouchEvent");var SyntheticTransitionEvent=require("./SyntheticTransitionEvent");var SyntheticUIEvent=require("./SyntheticUIEvent");var SyntheticWheelEvent=require("./SyntheticWheelEvent");var emptyFunction=require("fbjs/lib/emptyFunction");var getEventCharCode=require("./getEventCharCode");var invariant=require("fbjs/lib/invariant");var eventTypes={};var topLevelEventsToDispatchConfig={};["abort","animationEnd","animationIteration","animationStart","blur","canPlay","canPlayThrough","click","contextMenu","copy","cut","doubleClick","drag","dragEnd","dragEnter","dragExit","dragLeave","dragOver","dragStart","drop","durationChange","emptied","encrypted","ended","error","focus","input","invalid","keyDown","keyPress","keyUp","load","loadedData","loadedMetadata","loadStart","mouseDown","mouseMove","mouseOut","mouseOver","mouseUp","paste","pause","play","playing","progress","rateChange","reset","scroll","seeked","seeking","stalled","submit","suspend","timeUpdate","touchCancel","touchEnd","touchMove","touchStart","transitionEnd","volumeChange","waiting","wheel"].forEach(function(event){var capitalizedEvent=event[0].toUpperCase()+event.slice(1);var onEvent="on"+capitalizedEvent;var topEvent="top"+capitalizedEvent;var type={phasedRegistrationNames:{bubbled:onEvent,captured:onEvent+"Capture"},dependencies:[topEvent]};eventTypes[event]=type;topLevelEventsToDispatchConfig[topEvent]=type});var onClickListeners={};function getDictionaryKey(inst){return"."+inst._rootNodeID}function isInteractive(tag){return tag==="button"||tag==="input"||tag==="select"||tag==="textarea"}var SimpleEventPlugin={eventTypes:eventTypes,extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){var dispatchConfig=topLevelEventsToDispatchConfig[topLevelType];if(!dispatchConfig){return null}var EventConstructor;switch(topLevelType){case"topAbort":case"topCanPlay":case"topCanPlayThrough":case"topDurationChange":case"topEmptied":case"topEncrypted":case"topEnded":case"topError":case"topInput":case"topInvalid":case"topLoad":case"topLoadedData":case"topLoadedMetadata":case"topLoadStart":case"topPause":case"topPlay":case"topPlaying":case"topProgress":case"topRateChange":case"topReset":case"topSeeked":case"topSeeking":case"topStalled":case"topSubmit":case"topSuspend":case"topTimeUpdate":case"topVolumeChange":case"topWaiting":EventConstructor=SyntheticEvent;break;case"topKeyPress":if(getEventCharCode(nativeEvent)===0){return null}case"topKeyDown":case"topKeyUp":EventConstructor=SyntheticKeyboardEvent;break;case"topBlur":case"topFocus":EventConstructor=SyntheticFocusEvent;break;case"topClick":if(nativeEvent.button===2){return null}case"topDoubleClick":case"topMouseDown":case"topMouseMove":case"topMouseUp":case"topMouseOut":case"topMouseOver":case"topContextMenu":EventConstructor=SyntheticMouseEvent;break;case"topDrag":case"topDragEnd":case"topDragEnter":case"topDragExit":case"topDragLeave":case"topDragOver":case"topDragStart":case"topDrop":EventConstructor=SyntheticDragEvent;break;case"topTouchCancel":case"topTouchEnd":case"topTouchMove":case"topTouchStart":EventConstructor=SyntheticTouchEvent;break;case"topAnimationEnd":case"topAnimationIteration":case"topAnimationStart":EventConstructor=SyntheticAnimationEvent;break;case"topTransitionEnd":EventConstructor=SyntheticTransitionEvent;break;case"topScroll":EventConstructor=SyntheticUIEvent;break;case"topWheel":EventConstructor=SyntheticWheelEvent;break;case"topCopy":case"topCut":case"topPaste":EventConstructor=SyntheticClipboardEvent;break}!EventConstructor?process.env.NODE_ENV!=="production"?invariant(false,"SimpleEventPlugin: Unhandled event type, `%s`.",topLevelType):_prodInvariant("86",topLevelType):void 0;var event=EventConstructor.getPooled(dispatchConfig,targetInst,nativeEvent,nativeEventTarget);EventPropagators.accumulateTwoPhaseDispatches(event);return event},didPutListener:function(inst,registrationName,listener){if(registrationName==="onClick"&&!isInteractive(inst._tag)){var key=getDictionaryKey(inst);var node=ReactDOMComponentTree.getNodeFromInstance(inst);if(!onClickListeners[key]){onClickListeners[key]=EventListener.listen(node,"click",emptyFunction)}}},willDeleteListener:function(inst,registrationName){if(registrationName==="onClick"&&!isInteractive(inst._tag)){var key=getDictionaryKey(inst);onClickListeners[key].remove();delete onClickListeners[key]}}};module.exports=SimpleEventPlugin}).call(this,require("_process"))},{"./EventPropagators":50,"./ReactDOMComponentTree":64,"./SyntheticAnimationEvent":113,"./SyntheticClipboardEvent":114,"./SyntheticDragEvent":116,"./SyntheticEvent":117,"./SyntheticFocusEvent":118,"./SyntheticKeyboardEvent":120,"./SyntheticMouseEvent":121,"./SyntheticTouchEvent":122,"./SyntheticTransitionEvent":123,"./SyntheticUIEvent":124,"./SyntheticWheelEvent":125,"./getEventCharCode":137,"./reactProdInvariant":151,_process:184,"fbjs/lib/EventListener":3,"fbjs/lib/emptyFunction":10,"fbjs/lib/invariant":18}],113:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var AnimationEventInterface={animationName:null,elapsedTime:null,pseudoElement:null};function SyntheticAnimationEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticAnimationEvent,AnimationEventInterface);module.exports=SyntheticAnimationEvent},{"./SyntheticEvent":117}],114:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var ClipboardEventInterface={clipboardData:function(event){return"clipboardData"in event?event.clipboardData:window.clipboardData}};function SyntheticClipboardEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticClipboardEvent,ClipboardEventInterface);module.exports=SyntheticClipboardEvent},{"./SyntheticEvent":117}],115:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var CompositionEventInterface={data:null};function SyntheticCompositionEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticCompositionEvent,CompositionEventInterface);module.exports=SyntheticCompositionEvent},{"./SyntheticEvent":117}],116:[function(require,module,exports){"use strict";var SyntheticMouseEvent=require("./SyntheticMouseEvent");var DragEventInterface={dataTransfer:null};function SyntheticDragEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticMouseEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticMouseEvent.augmentClass(SyntheticDragEvent,DragEventInterface);module.exports=SyntheticDragEvent},{"./SyntheticMouseEvent":121}],117:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var PooledClass=require("./PooledClass");var emptyFunction=require("fbjs/lib/emptyFunction");var warning=require("fbjs/lib/warning");var didWarnForAddedNewProperty=false;var isProxySupported=typeof Proxy==="function";var shouldBeReleasedProperties=["dispatchConfig","_targetInst","nativeEvent","isDefaultPrevented","isPropagationStopped","_dispatchListeners","_dispatchInstances"];var EventInterface={type:null,target:null,currentTarget:emptyFunction.thatReturnsNull,eventPhase:null,bubbles:null,cancelable:null,timeStamp:function(event){return event.timeStamp||Date.now()},defaultPrevented:null,isTrusted:null};function SyntheticEvent(dispatchConfig,targetInst,nativeEvent,nativeEventTarget){if(process.env.NODE_ENV!=="production"){delete this.nativeEvent;delete this.preventDefault;delete this.stopPropagation}this.dispatchConfig=dispatchConfig;this._targetInst=targetInst;this.nativeEvent=nativeEvent;var Interface=this.constructor.Interface;for(var propName in Interface){if(!Interface.hasOwnProperty(propName)){continue}if(process.env.NODE_ENV!=="production"){delete this[propName]}var normalize=Interface[propName];if(normalize){this[propName]=normalize(nativeEvent)}else{if(propName==="target"){this.target=nativeEventTarget}else{this[propName]=nativeEvent[propName]}}}var defaultPrevented=nativeEvent.defaultPrevented!=null?nativeEvent.defaultPrevented:nativeEvent.returnValue===false;if(defaultPrevented){this.isDefaultPrevented=emptyFunction.thatReturnsTrue}else{this.isDefaultPrevented=emptyFunction.thatReturnsFalse}this.isPropagationStopped=emptyFunction.thatReturnsFalse;return this}_assign(SyntheticEvent.prototype,{preventDefault:function(){this.defaultPrevented=true;var event=this.nativeEvent;if(!event){return}if(event.preventDefault){event.preventDefault()}else if(typeof event.returnValue!=="unknown"){event.returnValue=false}this.isDefaultPrevented=emptyFunction.thatReturnsTrue},stopPropagation:function(){var event=this.nativeEvent;if(!event){return}if(event.stopPropagation){event.stopPropagation()}else if(typeof event.cancelBubble!=="unknown"){event.cancelBubble=true}this.isPropagationStopped=emptyFunction.thatReturnsTrue},persist:function(){this.isPersistent=emptyFunction.thatReturnsTrue},isPersistent:emptyFunction.thatReturnsFalse,destructor:function(){var Interface=this.constructor.Interface;for(var propName in Interface){if(process.env.NODE_ENV!=="production"){Object.defineProperty(this,propName,getPooledWarningPropertyDefinition(propName,Interface[propName]))}else{this[propName]=null}}for(var i=0;i<shouldBeReleasedProperties.length;i++){this[shouldBeReleasedProperties[i]]=null}if(process.env.NODE_ENV!=="production"){Object.defineProperty(this,"nativeEvent",getPooledWarningPropertyDefinition("nativeEvent",null));Object.defineProperty(this,"preventDefault",getPooledWarningPropertyDefinition("preventDefault",emptyFunction));Object.defineProperty(this,"stopPropagation",getPooledWarningPropertyDefinition("stopPropagation",emptyFunction))}}});SyntheticEvent.Interface=EventInterface;if(process.env.NODE_ENV!=="production"){if(isProxySupported){SyntheticEvent=new Proxy(SyntheticEvent,{construct:function(target,args){return this.apply(target,Object.create(target.prototype),args)},apply:function(constructor,that,args){return new Proxy(constructor.apply(that,args),{set:function(target,prop,value){if(prop!=="isPersistent"&&!target.constructor.Interface.hasOwnProperty(prop)&&shouldBeReleasedProperties.indexOf(prop)===-1){process.env.NODE_ENV!=="production"?warning(didWarnForAddedNewProperty||target.isPersistent(),"This synthetic event is reused for performance reasons. If you're "+"seeing this, you're adding a new property in the synthetic event object. "+"The property is never released. See "+"https://fb.me/react-event-pooling for more information."):void 0;didWarnForAddedNewProperty=true}target[prop]=value;return true}})}})}}SyntheticEvent.augmentClass=function(Class,Interface){var Super=this;var E=function(){};E.prototype=Super.prototype;var prototype=new E;_assign(prototype,Class.prototype);Class.prototype=prototype;Class.prototype.constructor=Class;Class.Interface=_assign({},Super.Interface,Interface);Class.augmentClass=Super.augmentClass;PooledClass.addPoolingTo(Class,PooledClass.fourArgumentPooler)};PooledClass.addPoolingTo(SyntheticEvent,PooledClass.fourArgumentPooler);module.exports=SyntheticEvent;function getPooledWarningPropertyDefinition(propName,getVal){var isFunction=typeof getVal==="function";return{configurable:true,set:set,get:get};function set(val){var action=isFunction?"setting the method":"setting the property";warn(action,"This is effectively a no-op");return val}function get(){var action=isFunction?"accessing the method":"accessing the property";var result=isFunction?"This is a no-op function":"This is set to null";warn(action,result);return getVal}function warn(action,result){var warningCondition=false;process.env.NODE_ENV!=="production"?warning(warningCondition,"This synthetic event is reused for performance reasons. If you're seeing this, "+"you're %s `%s` on a released/nullified synthetic event. %s. "+"If you must keep the original synthetic event around, use event.persist(). "+"See https://fb.me/react-event-pooling for more information.",action,propName,result):void 0}}}).call(this,require("_process"))},{"./PooledClass":55,_process:184,"fbjs/lib/emptyFunction":10,"fbjs/lib/warning":25,"object-assign":26}],118:[function(require,module,exports){"use strict";var SyntheticUIEvent=require("./SyntheticUIEvent");var FocusEventInterface={relatedTarget:null};function SyntheticFocusEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticUIEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticUIEvent.augmentClass(SyntheticFocusEvent,FocusEventInterface);module.exports=SyntheticFocusEvent},{"./SyntheticUIEvent":124}],119:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var InputEventInterface={data:null};function SyntheticInputEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticInputEvent,InputEventInterface);module.exports=SyntheticInputEvent},{"./SyntheticEvent":117}],120:[function(require,module,exports){"use strict";var SyntheticUIEvent=require("./SyntheticUIEvent");var getEventCharCode=require("./getEventCharCode");var getEventKey=require("./getEventKey");var getEventModifierState=require("./getEventModifierState");var KeyboardEventInterface={key:getEventKey,location:null,ctrlKey:null,shiftKey:null,altKey:null,metaKey:null,repeat:null,locale:null,getModifierState:getEventModifierState,charCode:function(event){if(event.type==="keypress"){return getEventCharCode(event)}return 0},keyCode:function(event){if(event.type==="keydown"||event.type==="keyup"){return event.keyCode}return 0},which:function(event){if(event.type==="keypress"){return getEventCharCode(event)}if(event.type==="keydown"||event.type==="keyup"){return event.keyCode}return 0}};function SyntheticKeyboardEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticUIEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticUIEvent.augmentClass(SyntheticKeyboardEvent,KeyboardEventInterface);module.exports=SyntheticKeyboardEvent},{"./SyntheticUIEvent":124,"./getEventCharCode":137,"./getEventKey":138,"./getEventModifierState":139}],121:[function(require,module,exports){"use strict";var SyntheticUIEvent=require("./SyntheticUIEvent");var ViewportMetrics=require("./ViewportMetrics");var getEventModifierState=require("./getEventModifierState");var MouseEventInterface={screenX:null,screenY:null,clientX:null,clientY:null,ctrlKey:null,shiftKey:null,altKey:null,metaKey:null,getModifierState:getEventModifierState,button:function(event){var button=event.button;if("which"in event){return button}return button===2?2:button===4?1:0},buttons:null,relatedTarget:function(event){return event.relatedTarget||(event.fromElement===event.srcElement?event.toElement:event.fromElement)},pageX:function(event){return"pageX"in event?event.pageX:event.clientX+ViewportMetrics.currentScrollLeft},pageY:function(event){return"pageY"in event?event.pageY:event.clientY+ViewportMetrics.currentScrollTop}};function SyntheticMouseEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticUIEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticUIEvent.augmentClass(SyntheticMouseEvent,MouseEventInterface);module.exports=SyntheticMouseEvent},{"./SyntheticUIEvent":124,"./ViewportMetrics":127,"./getEventModifierState":139}],122:[function(require,module,exports){"use strict";var SyntheticUIEvent=require("./SyntheticUIEvent");var getEventModifierState=require("./getEventModifierState");var TouchEventInterface={touches:null,targetTouches:null,changedTouches:null,altKey:null,metaKey:null,ctrlKey:null,shiftKey:null,getModifierState:getEventModifierState};function SyntheticTouchEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticUIEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticUIEvent.augmentClass(SyntheticTouchEvent,TouchEventInterface);module.exports=SyntheticTouchEvent},{"./SyntheticUIEvent":124,"./getEventModifierState":139}],123:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var TransitionEventInterface={propertyName:null,elapsedTime:null,pseudoElement:null};function SyntheticTransitionEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticTransitionEvent,TransitionEventInterface);module.exports=SyntheticTransitionEvent},{"./SyntheticEvent":117}],124:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var getEventTarget=require("./getEventTarget");var UIEventInterface={view:function(event){if(event.view){return event.view}var target=getEventTarget(event);if(target.window===target){return target}var doc=target.ownerDocument;if(doc){return doc.defaultView||doc.parentWindow}else{return window}},detail:function(event){return event.detail||0}};function SyntheticUIEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticUIEvent,UIEventInterface);module.exports=SyntheticUIEvent},{"./SyntheticEvent":117,"./getEventTarget":140}],125:[function(require,module,exports){"use strict";var SyntheticMouseEvent=require("./SyntheticMouseEvent");var WheelEventInterface={deltaX:function(event){return"deltaX"in event?event.deltaX:"wheelDeltaX"in event?-event.wheelDeltaX:0},deltaY:function(event){return"deltaY"in event?event.deltaY:"wheelDeltaY"in event?-event.wheelDeltaY:"wheelDelta"in event?-event.wheelDelta:0},deltaZ:null,deltaMode:null};function SyntheticWheelEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticMouseEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticMouseEvent.augmentClass(SyntheticWheelEvent,WheelEventInterface);module.exports=SyntheticWheelEvent},{"./SyntheticMouseEvent":121}],126:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");var OBSERVED_ERROR={};var TransactionImpl={reinitializeTransaction:function(){this.transactionWrappers=this.getTransactionWrappers();if(this.wrapperInitData){this.wrapperInitData.length=0}else{this.wrapperInitData=[]}this._isInTransaction=false},_isInTransaction:false,getTransactionWrappers:null,isInTransaction:function(){return!!this._isInTransaction},perform:function(method,scope,a,b,c,d,e,f){!!this.isInTransaction()?process.env.NODE_ENV!=="production"?invariant(false,"Transaction.perform(...): Cannot initialize a transaction when there is already an outstanding transaction."):_prodInvariant("27"):void 0;var errorThrown;var ret;try{this._isInTransaction=true;errorThrown=true;this.initializeAll(0);ret=method.call(scope,a,b,c,d,e,f);errorThrown=false}finally{try{if(errorThrown){try{this.closeAll(0)}catch(err){}}else{this.closeAll(0)}}finally{this._isInTransaction=false}}return ret},initializeAll:function(startIndex){var transactionWrappers=this.transactionWrappers;for(var i=startIndex;i<transactionWrappers.length;i++){var wrapper=transactionWrappers[i];try{this.wrapperInitData[i]=OBSERVED_ERROR;this.wrapperInitData[i]=wrapper.initialize?wrapper.initialize.call(this):null}finally{if(this.wrapperInitData[i]===OBSERVED_ERROR){try{this.initializeAll(i+1)}catch(err){}}}}},closeAll:function(startIndex){!this.isInTransaction()?process.env.NODE_ENV!=="production"?invariant(false,"Transaction.closeAll(): Cannot close transaction when none are open."):_prodInvariant("28"):void 0;var transactionWrappers=this.transactionWrappers;for(var i=startIndex;i<transactionWrappers.length;i++){var wrapper=transactionWrappers[i];var initData=this.wrapperInitData[i];var errorThrown;try{errorThrown=true;if(initData!==OBSERVED_ERROR&&wrapper.close){wrapper.close.call(this,initData)}errorThrown=false}finally{if(errorThrown){try{this.closeAll(i+1)}catch(e){}}}}this.wrapperInitData.length=0}};module.exports=TransactionImpl}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],127:[function(require,module,exports){"use strict";var ViewportMetrics={currentScrollLeft:0,currentScrollTop:0,refreshScrollValues:function(scrollPosition){ViewportMetrics.currentScrollLeft=scrollPosition.x;ViewportMetrics.currentScrollTop=scrollPosition.y}};module.exports=ViewportMetrics},{}],128:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");function accumulateInto(current,next){!(next!=null)?process.env.NODE_ENV!=="production"?invariant(false,"accumulateInto(...): Accumulated items must not be null or undefined."):_prodInvariant("30"):void 0;if(current==null){return next}if(Array.isArray(current)){if(Array.isArray(next)){current.push.apply(current,next);return current}current.push(next);return current}if(Array.isArray(next)){return[current].concat(next)}return[current,next]}module.exports=accumulateInto}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],129:[function(require,module,exports){"use strict";var MOD=65521;function adler32(data){var a=1;var b=0;var i=0;var l=data.length;var m=l&~3;while(i<m){var n=Math.min(i+4096,m);for(;i<n;i+=4){b+=(a+=data.charCodeAt(i))+(a+=data.charCodeAt(i+1))+(a+=data.charCodeAt(i+2))+(a+=data.charCodeAt(i+3))}a%=MOD;b%=MOD}for(;i<l;i++){b+=a+=data.charCodeAt(i)}a%=MOD;b%=MOD;return a|b<<16}module.exports=adler32},{}],130:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactPropTypeLocationNames=require("./ReactPropTypeLocationNames");var ReactPropTypesSecret=require("./ReactPropTypesSecret");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ReactComponentTreeHook;if(typeof process!=="undefined"&&process.env&&process.env.NODE_ENV==="test"){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}var loggedTypeFailures={};function checkReactTypeSpec(typeSpecs,values,location,componentName,element,debugID){for(var typeSpecName in typeSpecs){if(typeSpecs.hasOwnProperty(typeSpecName)){var error;try{!(typeof typeSpecs[typeSpecName]==="function")?process.env.NODE_ENV!=="production"?invariant(false,"%s: %s type `%s` is invalid; it must be a function, usually from React.PropTypes.",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName):_prodInvariant("84",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName):void 0;error=typeSpecs[typeSpecName](values,typeSpecName,componentName,location,null,ReactPropTypesSecret)}catch(ex){error=ex}process.env.NODE_ENV!=="production"?warning(!error||error instanceof Error,"%s: type specification of %s `%s` is invalid; the type checker "+"function must return `null` or an `Error` but returned a %s. "+"You may have forgotten to pass an argument to the type checker "+"creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and "+"shape all require an argument).",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName,typeof error):void 0;if(error instanceof Error&&!(error.message in loggedTypeFailures)){loggedTypeFailures[error.message]=true;var componentStackInfo="";if(process.env.NODE_ENV!=="production"){if(!ReactComponentTreeHook){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}if(debugID!==null){componentStackInfo=ReactComponentTreeHook.getStackAddendumByID(debugID)}else if(element!==null){componentStackInfo=ReactComponentTreeHook.getCurrentStackAddendum(element)}}process.env.NODE_ENV!=="production"?warning(false,"Failed %s type: %s%s",location,error.message,componentStackInfo):void 0}}}}module.exports=checkReactTypeSpec}).call(this,require("_process"))},{"./ReactPropTypeLocationNames":100,"./ReactPropTypesSecret":101,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],131:[function(require,module,exports){"use strict";var createMicrosoftUnsafeLocalFunction=function(func){if(typeof MSApp!=="undefined"&&MSApp.execUnsafeLocalFunction){return function(arg0,arg1,arg2,arg3){MSApp.execUnsafeLocalFunction(function(){return func(arg0,arg1,arg2,arg3)})}}else{return func}};module.exports=createMicrosoftUnsafeLocalFunction},{}],132:[function(require,module,exports){(function(process){"use strict";var CSSProperty=require("./CSSProperty");var warning=require("fbjs/lib/warning");var isUnitlessNumber=CSSProperty.isUnitlessNumber;var styleWarnings={};function dangerousStyleValue(name,value,component,isCustomProperty){var isEmpty=value==null||typeof value==="boolean"||value==="";if(isEmpty){return""}var isNonNumeric=isNaN(value);if(isCustomProperty||isNonNumeric||value===0||isUnitlessNumber.hasOwnProperty(name)&&isUnitlessNumber[name]){return""+value}if(typeof value==="string"){if(process.env.NODE_ENV!=="production"){if(component&&value!=="0"){var owner=component._currentElement._owner;var ownerName=owner?owner.getName():null;if(ownerName&&!styleWarnings[ownerName]){styleWarnings[ownerName]={}}var warned=false;if(ownerName){var warnings=styleWarnings[ownerName];warned=warnings[name];if(!warned){warnings[name]=true}}if(!warned){process.env.NODE_ENV!=="production"?warning(false,"a `%s` tag (owner: `%s`) was passed a numeric string value "+"for CSS property `%s` (value: `%s`) which will be treated "+"as a unitless number in a future version of React.",component._currentElement.type,ownerName||"unknown",name,value):void 0}}}value=value.trim()}return value+"px"}module.exports=dangerousStyleValue}).call(this,require("_process"))},{"./CSSProperty":35,_process:184,"fbjs/lib/warning":25}],133:[function(require,module,exports){"use strict";var matchHtmlRegExp=/["'&<>]/;function escapeHtml(string){var str=""+string;var match=matchHtmlRegExp.exec(str);if(!match){return str}var escape;var html="";var index=0;var lastIndex=0;for(index=match.index;index<str.length;index++){switch(str.charCodeAt(index)){case 34:escape="&quot;";break;case 38:escape="&amp;";break;case 39:escape="&#x27;";break;case 60:escape="&lt;";break;case 62:escape="&gt;";break;default:continue}if(lastIndex!==index){html+=str.substring(lastIndex,index)}lastIndex=index+1;html+=escape}return lastIndex!==index?html+str.substring(lastIndex,index):html}function escapeTextContentForBrowser(text){if(typeof text==="boolean"||typeof text==="number"){return""+text}return escapeHtml(text)}module.exports=escapeTextContentForBrowser},{}],134:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactInstanceMap=require("./ReactInstanceMap");var getHostComponentFromComposite=require("./getHostComponentFromComposite");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");function findDOMNode(componentOrElement){if(process.env.NODE_ENV!=="production"){var owner=ReactCurrentOwner.current;if(owner!==null){process.env.NODE_ENV!=="production"?warning(owner._warnedAboutRefsInRender,"%s is accessing findDOMNode inside its render(). "+"render() should be a pure function of props and state. It should "+"never access something that requires stale data from the previous "+"render, such as refs. Move this logic to componentDidMount and "+"componentDidUpdate instead.",owner.getName()||"A component"):void 0;owner._warnedAboutRefsInRender=true}}if(componentOrElement==null){return null}if(componentOrElement.nodeType===1){return componentOrElement}var inst=ReactInstanceMap.get(componentOrElement);if(inst){inst=getHostComponentFromComposite(inst);return inst?ReactDOMComponentTree.getNodeFromInstance(inst):null}if(typeof componentOrElement.render==="function"){!false?process.env.NODE_ENV!=="production"?invariant(false,"findDOMNode was called on an unmounted component."):_prodInvariant("44"):void 0}else{!false?process.env.NODE_ENV!=="production"?invariant(false,"Element appears to be neither ReactComponent nor DOMNode (keys: %s)",Object.keys(componentOrElement)):_prodInvariant("45",Object.keys(componentOrElement)):void 0}}module.exports=findDOMNode}).call(this,require("_process"))},{"./ReactDOMComponentTree":64,"./ReactInstanceMap":92,"./getHostComponentFromComposite":141,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"react/lib/ReactCurrentOwner":164}],135:[function(require,module,exports){(function(process){"use strict";var KeyEscapeUtils=require("./KeyEscapeUtils");var traverseAllChildren=require("./traverseAllChildren");var warning=require("fbjs/lib/warning");var ReactComponentTreeHook;if(typeof process!=="undefined"&&process.env&&process.env.NODE_ENV==="test"){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}function flattenSingleChildIntoContext(traverseContext,child,name,selfDebugID){if(traverseContext&&typeof traverseContext==="object"){var result=traverseContext;var keyUnique=result[name]===undefined;if(process.env.NODE_ENV!=="production"){if(!ReactComponentTreeHook){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}if(!keyUnique){process.env.NODE_ENV!=="production"?warning(false,"flattenChildren(...): Encountered two children with the same key, "+"`%s`. Child keys must be unique; when two children share a key, only "+"the first child will be used.%s",KeyEscapeUtils.unescape(name),ReactComponentTreeHook.getStackAddendumByID(selfDebugID)):void 0}}if(keyUnique&&child!=null){result[name]=child}}}function flattenChildren(children,selfDebugID){if(children==null){return children}var result={};if(process.env.NODE_ENV!=="production"){traverseAllChildren(children,function(traverseContext,child,name){return flattenSingleChildIntoContext(traverseContext,child,name,selfDebugID)},result)}else{traverseAllChildren(children,flattenSingleChildIntoContext,result)}return result}module.exports=flattenChildren}).call(this,require("_process"))},{"./KeyEscapeUtils":53,"./traverseAllChildren":156,_process:184,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],136:[function(require,module,exports){"use strict";function forEachAccumulated(arr,cb,scope){if(Array.isArray(arr)){arr.forEach(cb,scope)}else if(arr){cb.call(scope,arr)}}module.exports=forEachAccumulated},{}],137:[function(require,module,exports){"use strict";function getEventCharCode(nativeEvent){var charCode;var keyCode=nativeEvent.keyCode;if("charCode"in nativeEvent){charCode=nativeEvent.charCode;if(charCode===0&&keyCode===13){charCode=13}}else{charCode=keyCode}if(charCode>=32||charCode===13){return charCode}return 0}module.exports=getEventCharCode},{}],138:[function(require,module,exports){"use strict";var getEventCharCode=require("./getEventCharCode");var normalizeKey={Esc:"Escape",Spacebar:" ",Left:"ArrowLeft",Up:"ArrowUp",Right:"ArrowRight",Down:"ArrowDown",Del:"Delete",Win:"OS",Menu:"ContextMenu",Apps:"ContextMenu",Scroll:"ScrollLock",MozPrintableKey:"Unidentified"};var translateToKey={8:"Backspace",9:"Tab",12:"Clear",13:"Enter",16:"Shift",17:"Control",18:"Alt",19:"Pause",20:"CapsLock",27:"Escape",32:" ",33:"PageUp",34:"PageDown",35:"End",36:"Home",37:"ArrowLeft",38:"ArrowUp",39:"ArrowRight",40:"ArrowDown",45:"Insert",46:"Delete",112:"F1",113:"F2",114:"F3",115:"F4",116:"F5",117:"F6",118:"F7",119:"F8",120:"F9",121:"F10",122:"F11",123:"F12",144:"NumLock",145:"ScrollLock",224:"Meta"};function getEventKey(nativeEvent){if(nativeEvent.key){var key=normalizeKey[nativeEvent.key]||nativeEvent.key;if(key!=="Unidentified"){return key}}if(nativeEvent.type==="keypress"){var charCode=getEventCharCode(nativeEvent);return charCode===13?"Enter":String.fromCharCode(charCode)}if(nativeEvent.type==="keydown"||nativeEvent.type==="keyup"){return translateToKey[nativeEvent.keyCode]||"Unidentified"}return""}module.exports=getEventKey},{"./getEventCharCode":137}],139:[function(require,module,exports){"use strict";var modifierKeyToProp={Alt:"altKey",Control:"ctrlKey",Meta:"metaKey",Shift:"shiftKey"};function modifierStateGetter(keyArg){var syntheticEvent=this;var nativeEvent=syntheticEvent.nativeEvent;if(nativeEvent.getModifierState){return nativeEvent.getModifierState(keyArg)}var keyProp=modifierKeyToProp[keyArg];return keyProp?!!nativeEvent[keyProp]:false}function getEventModifierState(nativeEvent){return modifierStateGetter}module.exports=getEventModifierState},{}],140:[function(require,module,exports){"use strict";function getEventTarget(nativeEvent){var target=nativeEvent.target||nativeEvent.srcElement||window;if(target.correspondingUseElement){target=target.correspondingUseElement}return target.nodeType===3?target.parentNode:target}module.exports=getEventTarget},{}],141:[function(require,module,exports){"use strict";var ReactNodeTypes=require("./ReactNodeTypes");function getHostComponentFromComposite(inst){var type;while((type=inst._renderedNodeType)===ReactNodeTypes.COMPOSITE){inst=inst._renderedComponent}if(type===ReactNodeTypes.HOST){return inst._renderedComponent}else if(type===ReactNodeTypes.EMPTY){return null}}module.exports=getHostComponentFromComposite},{"./ReactNodeTypes":98}],142:[function(require,module,exports){"use strict";var ITERATOR_SYMBOL=typeof Symbol==="function"&&Symbol.iterator;var FAUX_ITERATOR_SYMBOL="@@iterator";function getIteratorFn(maybeIterable){var iteratorFn=maybeIterable&&(ITERATOR_SYMBOL&&maybeIterable[ITERATOR_SYMBOL]||maybeIterable[FAUX_ITERATOR_SYMBOL]);if(typeof iteratorFn==="function"){return iteratorFn}}module.exports=getIteratorFn},{}],143:[function(require,module,exports){"use strict";function getLeafNode(node){while(node&&node.firstChild){node=node.firstChild}return node}function getSiblingNode(node){while(node){if(node.nextSibling){return node.nextSibling}node=node.parentNode}}function getNodeForCharacterOffset(root,offset){var node=getLeafNode(root);var nodeStart=0;var nodeEnd=0;while(node){if(node.nodeType===3){nodeEnd=nodeStart+node.textContent.length;if(nodeStart<=offset&&nodeEnd>=offset){return{node:node,offset:offset-nodeStart}}nodeStart=nodeEnd}node=getLeafNode(getSiblingNode(node))}}module.exports=getNodeForCharacterOffset},{}],144:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var contentKey=null;function getTextContentAccessor(){if(!contentKey&&ExecutionEnvironment.canUseDOM){contentKey="textContent"in document.documentElement?"textContent":"innerText"}return contentKey}module.exports=getTextContentAccessor},{"fbjs/lib/ExecutionEnvironment":4}],145:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");function makePrefixMap(styleProp,eventName){var prefixes={};prefixes[styleProp.toLowerCase()]=eventName.toLowerCase();prefixes["Webkit"+styleProp]="webkit"+eventName;prefixes["Moz"+styleProp]="moz"+eventName;prefixes["ms"+styleProp]="MS"+eventName;prefixes["O"+styleProp]="o"+eventName.toLowerCase();return prefixes}var vendorPrefixes={animationend:makePrefixMap("Animation","AnimationEnd"),animationiteration:makePrefixMap("Animation","AnimationIteration"),animationstart:makePrefixMap("Animation","AnimationStart"),transitionend:makePrefixMap("Transition","TransitionEnd")};var prefixedEventNames={};var style={};if(ExecutionEnvironment.canUseDOM){style=document.createElement("div").style;if(!("AnimationEvent"in window)){delete vendorPrefixes.animationend.animation;delete vendorPrefixes.animationiteration.animation;delete vendorPrefixes.animationstart.animation}if(!("TransitionEvent"in window)){delete vendorPrefixes.transitionend.transition}}function getVendorPrefixedEventName(eventName){if(prefixedEventNames[eventName]){return prefixedEventNames[eventName]}else if(!vendorPrefixes[eventName]){return eventName}var prefixMap=vendorPrefixes[eventName];for(var styleProp in prefixMap){if(prefixMap.hasOwnProperty(styleProp)&&styleProp in style){return prefixedEventNames[eventName]=prefixMap[styleProp]}}return""}module.exports=getVendorPrefixedEventName},{"fbjs/lib/ExecutionEnvironment":4}],146:[function(require,module,exports){"use strict";var ReactDOMComponentTree=require("./ReactDOMComponentTree");function isCheckable(elem){var type=elem.type;var nodeName=elem.nodeName;return nodeName&&nodeName.toLowerCase()==="input"&&(type==="checkbox"||type==="radio")}function getTracker(inst){return inst._wrapperState.valueTracker}function attachTracker(inst,tracker){inst._wrapperState.valueTracker=tracker}function detachTracker(inst){delete inst._wrapperState.valueTracker}function getValueFromNode(node){var value;if(node){value=isCheckable(node)?""+node.checked:node.value}return value}var inputValueTracking={_getTrackerFromNode:function(node){return getTracker(ReactDOMComponentTree.getInstanceFromNode(node))},track:function(inst){if(getTracker(inst)){return}var node=ReactDOMComponentTree.getNodeFromInstance(inst);var valueField=isCheckable(node)?"checked":"value";var descriptor=Object.getOwnPropertyDescriptor(node.constructor.prototype,valueField);var currentValue=""+node[valueField];if(node.hasOwnProperty(valueField)||typeof descriptor.get!=="function"||typeof descriptor.set!=="function"){return}Object.defineProperty(node,valueField,{enumerable:descriptor.enumerable,configurable:true,get:function(){return descriptor.get.call(this)},set:function(value){currentValue=""+value;descriptor.set.call(this,value)}});attachTracker(inst,{getValue:function(){return currentValue},setValue:function(value){currentValue=""+value},stopTracking:function(){detachTracker(inst);delete node[valueField]}})},updateValueIfChanged:function(inst){if(!inst){return false}var tracker=getTracker(inst);if(!tracker){inputValueTracking.track(inst);return true}var lastValue=tracker.getValue();var nextValue=getValueFromNode(ReactDOMComponentTree.getNodeFromInstance(inst));if(nextValue!==lastValue){tracker.setValue(nextValue);return true}return false},stopTracking:function(inst){var tracker=getTracker(inst);if(tracker){tracker.stopTracking()}}};module.exports=inputValueTracking},{"./ReactDOMComponentTree":64}],147:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var ReactCompositeComponent=require("./ReactCompositeComponent");var ReactEmptyComponent=require("./ReactEmptyComponent");var ReactHostComponent=require("./ReactHostComponent");var getNextDebugID=require("react/lib/getNextDebugID");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ReactCompositeComponentWrapper=function(element){this.construct(element)};function getDeclarationErrorAddendum(owner){if(owner){var name=owner.getName();if(name){return" Check the render method of `"+name+"`."}}return""}function isInternalComponentType(type){return typeof type==="function"&&typeof type.prototype!=="undefined"&&typeof type.prototype.mountComponent==="function"&&typeof type.prototype.receiveComponent==="function"}function instantiateReactComponent(node,shouldHaveDebugID){var instance;if(node===null||node===false){instance=ReactEmptyComponent.create(instantiateReactComponent)}else if(typeof node==="object"){var element=node;var type=element.type;if(typeof type!=="function"&&typeof type!=="string"){var info="";if(process.env.NODE_ENV!=="production"){if(type===undefined||typeof type==="object"&&type!==null&&Object.keys(type).length===0){info+=" You likely forgot to export your component from the file "+"it's defined in."}}info+=getDeclarationErrorAddendum(element._owner);!false?process.env.NODE_ENV!=="production"?invariant(false,"Element type is invalid: expected a string (for built-in components) or a class/function (for composite components) but got: %s.%s",type==null?type:typeof type,info):_prodInvariant("130",type==null?type:typeof type,info):void 0}if(typeof element.type==="string"){instance=ReactHostComponent.createInternalComponent(element)}else if(isInternalComponentType(element.type)){instance=new element.type(element);if(!instance.getHostNode){instance.getHostNode=instance.getNativeNode}}else{instance=new ReactCompositeComponentWrapper(element)}}else if(typeof node==="string"||typeof node==="number"){instance=ReactHostComponent.createInstanceForText(node)}else{!false?process.env.NODE_ENV!=="production"?invariant(false,"Encountered invalid React node of type %s",typeof node):_prodInvariant("131",typeof node):void 0}if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(typeof instance.mountComponent==="function"&&typeof instance.receiveComponent==="function"&&typeof instance.getHostNode==="function"&&typeof instance.unmountComponent==="function","Only React Components can be mounted."):void 0}instance._mountIndex=0;instance._mountImage=null;if(process.env.NODE_ENV!=="production"){instance._debugID=shouldHaveDebugID?getNextDebugID():0}if(process.env.NODE_ENV!=="production"){if(Object.preventExtensions){Object.preventExtensions(instance)}}return instance}_assign(ReactCompositeComponentWrapper.prototype,ReactCompositeComponent,{_instantiateReactComponent:instantiateReactComponent});module.exports=instantiateReactComponent}).call(this,require("_process"))},{"./ReactCompositeComponent":60,"./ReactEmptyComponent":83,"./ReactHostComponent":88,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"object-assign":26,"react/lib/getNextDebugID":178}],148:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var useHasFeature;if(ExecutionEnvironment.canUseDOM){useHasFeature=document.implementation&&document.implementation.hasFeature&&document.implementation.hasFeature("","")!==true}function isEventSupported(eventNameSuffix,capture){if(!ExecutionEnvironment.canUseDOM||capture&&!("addEventListener"in document)){return false}var eventName="on"+eventNameSuffix;var isSupported=eventName in document;if(!isSupported){var element=document.createElement("div");element.setAttribute(eventName,"return;");isSupported=typeof element[eventName]==="function"}if(!isSupported&&useHasFeature&&eventNameSuffix==="wheel"){isSupported=document.implementation.hasFeature("Events.wheel","3.0")}return isSupported}module.exports=isEventSupported},{"fbjs/lib/ExecutionEnvironment":4}],149:[function(require,module,exports){"use strict";var supportedInputTypes={color:true,date:true,datetime:true,"datetime-local":true,email:true,month:true,number:true,password:true,range:true,search:true,tel:true,text:true,time:true,url:true,week:true};function isTextInputElement(elem){var nodeName=elem&&elem.nodeName&&elem.nodeName.toLowerCase();if(nodeName==="input"){return!!supportedInputTypes[elem.type]}if(nodeName==="textarea"){return true}return false}module.exports=isTextInputElement},{}],150:[function(require,module,exports){"use strict";var escapeTextContentForBrowser=require("./escapeTextContentForBrowser");function quoteAttributeValueForBrowser(value){return'"'+escapeTextContentForBrowser(value)+'"'}module.exports=quoteAttributeValueForBrowser},{"./escapeTextContentForBrowser":133}],151:[function(require,module,exports){"use strict";function reactProdInvariant(code){var argCount=arguments.length-1;var message="Minified React error #"+code+"; visit "+"http://facebook.github.io/react/docs/error-decoder.html?invariant="+code;for(var argIdx=0;argIdx<argCount;argIdx++){message+="&args[]="+encodeURIComponent(arguments[argIdx+1])}message+=" for the full message or use the non-minified dev environment"+" for full errors and additional helpful warnings.";var error=new Error(message);error.name="Invariant Violation";error.framesToPop=1;throw error}module.exports=reactProdInvariant},{}],152:[function(require,module,exports){"use strict";var ReactMount=require("./ReactMount");module.exports=ReactMount.renderSubtreeIntoContainer},{"./ReactMount":96}],153:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var DOMNamespaces=require("./DOMNamespaces");var WHITESPACE_TEST=/^[ \r\n\t\f]/;var NONVISIBLE_TEST=/<(!--|link|noscript|meta|script|style)[ \r\n\t\f\/>]/;var createMicrosoftUnsafeLocalFunction=require("./createMicrosoftUnsafeLocalFunction");var reusableSVGContainer;var setInnerHTML=createMicrosoftUnsafeLocalFunction(function(node,html){if(node.namespaceURI===DOMNamespaces.svg&&!("innerHTML"in node)){reusableSVGContainer=reusableSVGContainer||document.createElement("div");reusableSVGContainer.innerHTML="<svg>"+html+"</svg>";var svgNode=reusableSVGContainer.firstChild;while(svgNode.firstChild){node.appendChild(svgNode.firstChild)}}else{node.innerHTML=html}});if(ExecutionEnvironment.canUseDOM){var testElement=document.createElement("div");testElement.innerHTML=" ";if(testElement.innerHTML===""){setInnerHTML=function(node,html){if(node.parentNode){node.parentNode.replaceChild(node,node)}if(WHITESPACE_TEST.test(html)||html[0]==="<"&&NONVISIBLE_TEST.test(html)){node.innerHTML=String.fromCharCode(65279)+html;var textNode=node.firstChild;if(textNode.data.length===1){node.removeChild(textNode)}else{textNode.deleteData(0,1)}}else{node.innerHTML=html}}}testElement=null}module.exports=setInnerHTML},{"./DOMNamespaces":41,"./createMicrosoftUnsafeLocalFunction":131,"fbjs/lib/ExecutionEnvironment":4}],154:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var escapeTextContentForBrowser=require("./escapeTextContentForBrowser");var setInnerHTML=require("./setInnerHTML");var setTextContent=function(node,text){if(text){var firstChild=node.firstChild;if(firstChild&&firstChild===node.lastChild&&firstChild.nodeType===3){firstChild.nodeValue=text;return}}node.textContent=text};if(ExecutionEnvironment.canUseDOM){if(!("textContent"in document.documentElement)){setTextContent=function(node,text){if(node.nodeType===3){node.nodeValue=text;return}setInnerHTML(node,escapeTextContentForBrowser(text))}}}module.exports=setTextContent},{"./escapeTextContentForBrowser":133,"./setInnerHTML":153,"fbjs/lib/ExecutionEnvironment":4}],155:[function(require,module,exports){"use strict";function shouldUpdateReactComponent(prevElement,nextElement){var prevEmpty=prevElement===null||prevElement===false;var nextEmpty=nextElement===null||nextElement===false;if(prevEmpty||nextEmpty){return prevEmpty===nextEmpty}var prevType=typeof prevElement;var nextType=typeof nextElement;if(prevType==="string"||prevType==="number"){return nextType==="string"||nextType==="number"}else{return nextType==="object"&&prevElement.type===nextElement.type&&prevElement.key===nextElement.key}}module.exports=shouldUpdateReactComponent},{}],156:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var REACT_ELEMENT_TYPE=require("./ReactElementSymbol");var getIteratorFn=require("./getIteratorFn");var invariant=require("fbjs/lib/invariant");var KeyEscapeUtils=require("./KeyEscapeUtils");var warning=require("fbjs/lib/warning");var SEPARATOR=".";var SUBSEPARATOR=":";var didWarnAboutMaps=false;function getComponentKey(component,index){if(component&&typeof component==="object"&&component.key!=null){return KeyEscapeUtils.escape(component.key)}return index.toString(36)}function traverseAllChildrenImpl(children,nameSoFar,callback,traverseContext){var type=typeof children;if(type==="undefined"||type==="boolean"){children=null}if(children===null||type==="string"||type==="number"||type==="object"&&children.$$typeof===REACT_ELEMENT_TYPE){callback(traverseContext,children,nameSoFar===""?SEPARATOR+getComponentKey(children,0):nameSoFar);return 1}var child;var nextName;var subtreeCount=0;var nextNamePrefix=nameSoFar===""?SEPARATOR:nameSoFar+SUBSEPARATOR;if(Array.isArray(children)){for(var i=0;i<children.length;i++){child=children[i];nextName=nextNamePrefix+getComponentKey(child,i);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}else{var iteratorFn=getIteratorFn(children);if(iteratorFn){var iterator=iteratorFn.call(children);var step;if(iteratorFn!==children.entries){var ii=0;while(!(step=iterator.next()).done){child=step.value;nextName=nextNamePrefix+getComponentKey(child,ii++);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}else{if(process.env.NODE_ENV!=="production"){var mapsAsChildrenAddendum="";if(ReactCurrentOwner.current){var mapsAsChildrenOwnerName=ReactCurrentOwner.current.getName();if(mapsAsChildrenOwnerName){mapsAsChildrenAddendum=" Check the render method of `"+mapsAsChildrenOwnerName+"`."}}process.env.NODE_ENV!=="production"?warning(didWarnAboutMaps,"Using Maps as children is not yet fully supported. It is an "+"experimental feature that might be removed. Convert it to a "+"sequence / iterable of keyed ReactElements instead.%s",mapsAsChildrenAddendum):void 0;didWarnAboutMaps=true}while(!(step=iterator.next()).done){var entry=step.value;if(entry){child=entry[1];nextName=nextNamePrefix+KeyEscapeUtils.escape(entry[0])+SUBSEPARATOR+getComponentKey(child,0);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}}}else if(type==="object"){var addendum="";if(process.env.NODE_ENV!=="production"){addendum=" If you meant to render a collection of children, use an array "+"instead or wrap the object using createFragment(object) from the "+"React add-ons.";if(children._isReactElement){addendum=" It looks like you're using an element created by a different "+"version of React. Make sure to use only one copy of React."}if(ReactCurrentOwner.current){var name=ReactCurrentOwner.current.getName();if(name){addendum+=" Check the render method of `"+name+"`."}}}var childrenString=String(children);!false?process.env.NODE_ENV!=="production"?invariant(false,"Objects are not valid as a React child (found: %s).%s",childrenString==="[object Object]"?"object with keys {"+Object.keys(children).join(", ")+"}":childrenString,addendum):_prodInvariant("31",childrenString==="[object Object]"?"object with keys {"+Object.keys(children).join(", ")+"}":childrenString,addendum):void 0}}return subtreeCount}function traverseAllChildren(children,callback,traverseContext){if(children==null){return 0}return traverseAllChildrenImpl(children,"",callback,traverseContext)}module.exports=traverseAllChildren}).call(this,require("_process"))},{"./KeyEscapeUtils":53,"./ReactElementSymbol":82,"./getIteratorFn":142,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"react/lib/ReactCurrentOwner":164}],157:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var emptyFunction=require("fbjs/lib/emptyFunction");var warning=require("fbjs/lib/warning");var validateDOMNesting=emptyFunction;if(process.env.NODE_ENV!=="production"){var specialTags=["address","applet","area","article","aside","base","basefont","bgsound","blockquote","body","br","button","caption","center","col","colgroup","dd","details","dir","div","dl","dt","embed","fieldset","figcaption","figure","footer","form","frame","frameset","h1","h2","h3","h4","h5","h6","head","header","hgroup","hr","html","iframe","img","input","isindex","li","link","listing","main","marquee","menu","menuitem","meta","nav","noembed","noframes","noscript","object","ol","p","param","plaintext","pre","script","section","select","source","style","summary","table","tbody","td","template","textarea","tfoot","th","thead","title","tr","track","ul","wbr","xmp"];var inScopeTags=["applet","caption","html","table","td","th","marquee","object","template","foreignObject","desc","title"];var buttonScopeTags=inScopeTags.concat(["button"]);var impliedEndTags=["dd","dt","li","option","optgroup","p","rp","rt"];var emptyAncestorInfo={current:null,formTag:null,aTagInScope:null,buttonTagInScope:null,nobrTagInScope:null,pTagInButtonScope:null,listItemTagAutoclosing:null,dlItemTagAutoclosing:null};var updatedAncestorInfo=function(oldInfo,tag,instance){var ancestorInfo=_assign({},oldInfo||emptyAncestorInfo);var info={tag:tag,instance:instance};if(inScopeTags.indexOf(tag)!==-1){ancestorInfo.aTagInScope=null;ancestorInfo.buttonTagInScope=null;ancestorInfo.nobrTagInScope=null}if(buttonScopeTags.indexOf(tag)!==-1){ancestorInfo.pTagInButtonScope=null}if(specialTags.indexOf(tag)!==-1&&tag!=="address"&&tag!=="div"&&tag!=="p"){ancestorInfo.listItemTagAutoclosing=null;ancestorInfo.dlItemTagAutoclosing=null}ancestorInfo.current=info;if(tag==="form"){ancestorInfo.formTag=info}if(tag==="a"){ancestorInfo.aTagInScope=info}if(tag==="button"){ancestorInfo.buttonTagInScope=info}if(tag==="nobr"){ancestorInfo.nobrTagInScope=info}if(tag==="p"){ancestorInfo.pTagInButtonScope=info}if(tag==="li"){ancestorInfo.listItemTagAutoclosing=info}if(tag==="dd"||tag==="dt"){ancestorInfo.dlItemTagAutoclosing=info}return ancestorInfo};var isTagValidWithParent=function(tag,parentTag){switch(parentTag){case"select":return tag==="option"||tag==="optgroup"||tag==="#text";case"optgroup":return tag==="option"||tag==="#text";case"option":return tag==="#text";case"tr":return tag==="th"||tag==="td"||tag==="style"||tag==="script"||tag==="template";case"tbody":case"thead":case"tfoot":return tag==="tr"||tag==="style"||tag==="script"||tag==="template";case"colgroup":return tag==="col"||tag==="template";case"table":return tag==="caption"||tag==="colgroup"||tag==="tbody"||tag==="tfoot"||tag==="thead"||tag==="style"||tag==="script"||tag==="template";case"head":return tag==="base"||tag==="basefont"||tag==="bgsound"||tag==="link"||tag==="meta"||tag==="title"||tag==="noscript"||tag==="noframes"||tag==="style"||tag==="script"||tag==="template";case"html":return tag==="head"||tag==="body";case"#document":return tag==="html"}switch(tag){case"h1":case"h2":case"h3":case"h4":case"h5":case"h6":return parentTag!=="h1"&&parentTag!=="h2"&&parentTag!=="h3"&&parentTag!=="h4"&&parentTag!=="h5"&&parentTag!=="h6";case"rp":case"rt":return impliedEndTags.indexOf(parentTag)===-1;case"body":case"caption":case"col":case"colgroup":case"frame":case"head":case"html":case"tbody":case"td":case"tfoot":case"th":case"thead":case"tr":return parentTag==null}return true};var findInvalidAncestorForTag=function(tag,ancestorInfo){switch(tag){case"address":case"article":case"aside":case"blockquote":case"center":case"details":case"dialog":case"dir":case"div":case"dl":case"fieldset":case"figcaption":case"figure":case"footer":case"header":case"hgroup":case"main":case"menu":case"nav":case"ol":case"p":case"section":case"summary":case"ul":case"pre":case"listing":case"table":case"hr":case"xmp":case"h1":case"h2":case"h3":case"h4":case"h5":case"h6":return ancestorInfo.pTagInButtonScope;case"form":return ancestorInfo.formTag||ancestorInfo.pTagInButtonScope;case"li":return ancestorInfo.listItemTagAutoclosing;case"dd":case"dt":return ancestorInfo.dlItemTagAutoclosing;case"button":return ancestorInfo.buttonTagInScope;case"a":return ancestorInfo.aTagInScope;case"nobr":return ancestorInfo.nobrTagInScope}return null};var findOwnerStack=function(instance){if(!instance){return[]}var stack=[];do{stack.push(instance)}while(instance=instance._currentElement._owner);stack.reverse();return stack};var didWarn={};validateDOMNesting=function(childTag,childText,childInstance,ancestorInfo){ancestorInfo=ancestorInfo||emptyAncestorInfo;var parentInfo=ancestorInfo.current;var parentTag=parentInfo&&parentInfo.tag;if(childText!=null){process.env.NODE_ENV!=="production"?warning(childTag==null,"validateDOMNesting: when childText is passed, childTag should be null"):void 0;childTag="#text"}var invalidParent=isTagValidWithParent(childTag,parentTag)?null:parentInfo;var invalidAncestor=invalidParent?null:findInvalidAncestorForTag(childTag,ancestorInfo);var problematic=invalidParent||invalidAncestor;if(problematic){var ancestorTag=problematic.tag;var ancestorInstance=problematic.instance;var childOwner=childInstance&&childInstance._currentElement._owner;var ancestorOwner=ancestorInstance&&ancestorInstance._currentElement._owner;var childOwners=findOwnerStack(childOwner);var ancestorOwners=findOwnerStack(ancestorOwner);var minStackLen=Math.min(childOwners.length,ancestorOwners.length);var i;var deepestCommon=-1;for(i=0;i<minStackLen;i++){if(childOwners[i]===ancestorOwners[i]){deepestCommon=i}else{break}}var UNKNOWN="(unknown)";var childOwnerNames=childOwners.slice(deepestCommon+1).map(function(inst){return inst.getName()||UNKNOWN});var ancestorOwnerNames=ancestorOwners.slice(deepestCommon+1).map(function(inst){return inst.getName()||UNKNOWN});var ownerInfo=[].concat(deepestCommon!==-1?childOwners[deepestCommon].getName()||UNKNOWN:[],ancestorOwnerNames,ancestorTag,invalidAncestor?["..."]:[],childOwnerNames,childTag).join(" > ");var warnKey=!!invalidParent+"|"+childTag+"|"+ancestorTag+"|"+ownerInfo;if(didWarn[warnKey]){return}didWarn[warnKey]=true;var tagDisplayName=childTag;var whitespaceInfo="";if(childTag==="#text"){if(/\S/.test(childText)){tagDisplayName="Text nodes"}else{tagDisplayName="Whitespace text nodes";whitespaceInfo=" Make sure you don't have any extra whitespace between tags on "+"each line of your source code."}}else{tagDisplayName="<"+childTag+">"}if(invalidParent){var info="";if(ancestorTag==="table"&&childTag==="tr"){info+=" Add a <tbody> to your code to match the DOM tree generated by "+"the browser."}process.env.NODE_ENV!=="production"?warning(false,"validateDOMNesting(...): %s cannot appear as a child of <%s>.%s "+"See %s.%s",tagDisplayName,ancestorTag,whitespaceInfo,ownerInfo,info):void 0}else{process.env.NODE_ENV!=="production"?warning(false,"validateDOMNesting(...): %s cannot appear as a descendant of "+"<%s>. See %s.",tagDisplayName,ancestorTag,ownerInfo):void 0}}};validateDOMNesting.updatedAncestorInfo=updatedAncestorInfo;validateDOMNesting.isTagValidInContext=function(tag,ancestorInfo){ancestorInfo=ancestorInfo||emptyAncestorInfo;var parentInfo=ancestorInfo.current;var parentTag=parentInfo&&parentInfo.tag;return isTagValidWithParent(tag,parentTag)&&!findInvalidAncestorForTag(tag,ancestorInfo)}}module.exports=validateDOMNesting}).call(this,require("_process"))},{_process:184,"fbjs/lib/emptyFunction":10,"fbjs/lib/warning":25,"object-assign":26}],158:[function(require,module,exports){arguments[4][53][0].apply(exports,arguments)},{dup:53}],159:[function(require,module,exports){arguments[4][55][0].apply(exports,arguments)},{"./reactProdInvariant":181,_process:184,dup:55,"fbjs/lib/invariant":18}],160:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var ReactBaseClasses=require("./ReactBaseClasses");var ReactChildren=require("./ReactChildren");var ReactDOMFactories=require("./ReactDOMFactories");var ReactElement=require("./ReactElement");var ReactPropTypes=require("./ReactPropTypes");var ReactVersion=require("./ReactVersion");var createReactClass=require("./createClass");var onlyChild=require("./onlyChild");var createElement=ReactElement.createElement;var createFactory=ReactElement.createFactory;var cloneElement=ReactElement.cloneElement;if(process.env.NODE_ENV!=="production"){var lowPriorityWarning=require("./lowPriorityWarning");var canDefineProperty=require("./canDefineProperty");var ReactElementValidator=require("./ReactElementValidator");var didWarnPropTypesDeprecated=false;createElement=ReactElementValidator.createElement;createFactory=ReactElementValidator.createFactory;cloneElement=ReactElementValidator.cloneElement}var __spread=_assign;var createMixin=function(mixin){return mixin};if(process.env.NODE_ENV!=="production"){var warnedForSpread=false;var warnedForCreateMixin=false;__spread=function(){lowPriorityWarning(warnedForSpread,"React.__spread is deprecated and should not be used. Use "+"Object.assign directly or another helper function with similar "+"semantics. You may be seeing this warning due to your compiler. "+"See https://fb.me/react-spread-deprecation for more details.");warnedForSpread=true;return _assign.apply(null,arguments)};createMixin=function(mixin){lowPriorityWarning(warnedForCreateMixin,"React.createMixin is deprecated and should not be used. "+"In React v16.0, it will be removed. "+"You can use this mixin directly instead. "+"See https://fb.me/createmixin-was-never-implemented for more info.");warnedForCreateMixin=true;return mixin}}var React={Children:{map:ReactChildren.map,forEach:ReactChildren.forEach,count:ReactChildren.count,toArray:ReactChildren.toArray,only:onlyChild},Component:ReactBaseClasses.Component,PureComponent:ReactBaseClasses.PureComponent,createElement:createElement,cloneElement:cloneElement,isValidElement:ReactElement.isValidElement,PropTypes:ReactPropTypes,createClass:createReactClass,createFactory:createFactory,createMixin:createMixin,DOM:ReactDOMFactories,version:ReactVersion,__spread:__spread};if(process.env.NODE_ENV!=="production"){var warnedForCreateClass=false;if(canDefineProperty){Object.defineProperty(React,"PropTypes",{get:function(){lowPriorityWarning(didWarnPropTypesDeprecated,"Accessing PropTypes via the main React package is deprecated,"+" and will be removed in  React v16.0."+" Use the latest available v15.* prop-types package from npm instead."+" For info on usage, compatibility, migration and more, see "+"https://fb.me/prop-types-docs");didWarnPropTypesDeprecated=true;return ReactPropTypes}});Object.defineProperty(React,"createClass",{get:function(){lowPriorityWarning(warnedForCreateClass,"Accessing createClass via the main React package is deprecated,"+" and will be removed in React v16.0."+" Use a plain JavaScript class instead. If you're not yet "+"ready to migrate, create-react-class v15.* is available "+"on npm as a temporary, drop-in replacement. "+"For more info see https://fb.me/react-create-class");warnedForCreateClass=true;return createReactClass}})}React.DOM={};var warnedForFactories=false;Object.keys(ReactDOMFactories).forEach(function(factory){React.DOM[factory]=function(){if(!warnedForFactories){lowPriorityWarning(false,"Accessing factories like React.DOM.%s has been deprecated "+"and will be removed in v16.0+. Use the "+"react-dom-factories package instead. "+" Version 1.0 provides a drop-in replacement."+" For more info, see https://fb.me/react-dom-factories",factory);warnedForFactories=true}return ReactDOMFactories[factory].apply(ReactDOMFactories,arguments)}})}module.exports=React}).call(this,require("_process"))},{"./ReactBaseClasses":161,"./ReactChildren":162,"./ReactDOMFactories":165,"./ReactElement":166,"./ReactElementValidator":168,"./ReactPropTypes":171,"./ReactVersion":173,"./canDefineProperty":174,"./createClass":176,"./lowPriorityWarning":179,"./onlyChild":180,_process:184,"object-assign":26}],161:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var ReactNoopUpdateQueue=require("./ReactNoopUpdateQueue");var canDefineProperty=require("./canDefineProperty");var emptyObject=require("fbjs/lib/emptyObject");var invariant=require("fbjs/lib/invariant");var lowPriorityWarning=require("./lowPriorityWarning");function ReactComponent(props,context,updater){this.props=props;this.context=context;this.refs=emptyObject;this.updater=updater||ReactNoopUpdateQueue}ReactComponent.prototype.isReactComponent={};ReactComponent.prototype.setState=function(partialState,callback){!(typeof partialState==="object"||typeof partialState==="function"||partialState==null)?process.env.NODE_ENV!=="production"?invariant(false,"setState(...): takes an object of state variables to update or a function which returns an object of state variables."):_prodInvariant("85"):void 0;this.updater.enqueueSetState(this,partialState);if(callback){this.updater.enqueueCallback(this,callback,"setState")}};ReactComponent.prototype.forceUpdate=function(callback){this.updater.enqueueForceUpdate(this);if(callback){this.updater.enqueueCallback(this,callback,"forceUpdate")}};if(process.env.NODE_ENV!=="production"){var deprecatedAPIs={isMounted:["isMounted","Instead, make sure to clean up subscriptions and pending requests in "+"componentWillUnmount to prevent memory leaks."],replaceState:["replaceState","Refactor your code to use setState instead (see "+"https://github.com/facebook/react/issues/3236)."]};var defineDeprecationWarning=function(methodName,info){if(canDefineProperty){Object.defineProperty(ReactComponent.prototype,methodName,{get:function(){lowPriorityWarning(false,"%s(...) is deprecated in plain JavaScript React classes. %s",info[0],info[1]);return undefined}})}};for(var fnName in deprecatedAPIs){if(deprecatedAPIs.hasOwnProperty(fnName)){defineDeprecationWarning(fnName,deprecatedAPIs[fnName])}}}function ReactPureComponent(props,context,updater){this.props=props;this.context=context;this.refs=emptyObject;this.updater=updater||ReactNoopUpdateQueue}function ComponentDummy(){}ComponentDummy.prototype=ReactComponent.prototype;ReactPureComponent.prototype=new ComponentDummy;ReactPureComponent.prototype.constructor=ReactPureComponent;_assign(ReactPureComponent.prototype,ReactComponent.prototype);ReactPureComponent.prototype.isPureReactComponent=true;module.exports={Component:ReactComponent,PureComponent:ReactPureComponent}}).call(this,require("_process"))},{"./ReactNoopUpdateQueue":169,"./canDefineProperty":174,"./lowPriorityWarning":179,"./reactProdInvariant":181,_process:184,"fbjs/lib/emptyObject":11,"fbjs/lib/invariant":18,"object-assign":26}],162:[function(require,module,exports){"use strict";var PooledClass=require("./PooledClass");var ReactElement=require("./ReactElement");var emptyFunction=require("fbjs/lib/emptyFunction");var traverseAllChildren=require("./traverseAllChildren");var twoArgumentPooler=PooledClass.twoArgumentPooler;var fourArgumentPooler=PooledClass.fourArgumentPooler;var userProvidedKeyEscapeRegex=/\/+/g;function escapeUserProvidedKey(text){return(""+text).replace(userProvidedKeyEscapeRegex,"$&/")}function ForEachBookKeeping(forEachFunction,forEachContext){this.func=forEachFunction;this.context=forEachContext;this.count=0}ForEachBookKeeping.prototype.destructor=function(){this.func=null;this.context=null;this.count=0};PooledClass.addPoolingTo(ForEachBookKeeping,twoArgumentPooler);function forEachSingleChild(bookKeeping,child,name){var func=bookKeeping.func,context=bookKeeping.context;func.call(context,child,bookKeeping.count++)}function forEachChildren(children,forEachFunc,forEachContext){if(children==null){return children}var traverseContext=ForEachBookKeeping.getPooled(forEachFunc,forEachContext);traverseAllChildren(children,forEachSingleChild,traverseContext);ForEachBookKeeping.release(traverseContext)}function MapBookKeeping(mapResult,keyPrefix,mapFunction,mapContext){this.result=mapResult;this.keyPrefix=keyPrefix;this.func=mapFunction;this.context=mapContext;this.count=0}MapBookKeeping.prototype.destructor=function(){this.result=null;this.keyPrefix=null;this.func=null;this.context=null;this.count=0};PooledClass.addPoolingTo(MapBookKeeping,fourArgumentPooler);function mapSingleChildIntoContext(bookKeeping,child,childKey){var result=bookKeeping.result,keyPrefix=bookKeeping.keyPrefix,func=bookKeeping.func,context=bookKeeping.context;var mappedChild=func.call(context,child,bookKeeping.count++);if(Array.isArray(mappedChild)){mapIntoWithKeyPrefixInternal(mappedChild,result,childKey,emptyFunction.thatReturnsArgument)}else if(mappedChild!=null){if(ReactElement.isValidElement(mappedChild)){mappedChild=ReactElement.cloneAndReplaceKey(mappedChild,keyPrefix+(mappedChild.key&&(!child||child.key!==mappedChild.key)?escapeUserProvidedKey(mappedChild.key)+"/":"")+childKey)}result.push(mappedChild)}}function mapIntoWithKeyPrefixInternal(children,array,prefix,func,context){var escapedPrefix="";if(prefix!=null){escapedPrefix=escapeUserProvidedKey(prefix)+"/"}var traverseContext=MapBookKeeping.getPooled(array,escapedPrefix,func,context);traverseAllChildren(children,mapSingleChildIntoContext,traverseContext);MapBookKeeping.release(traverseContext)}function mapChildren(children,func,context){if(children==null){return children}var result=[];mapIntoWithKeyPrefixInternal(children,result,null,func,context);return result}function forEachSingleChildDummy(traverseContext,child,name){return null}function countChildren(children,context){return traverseAllChildren(children,forEachSingleChildDummy,null)}function toArray(children){var result=[];mapIntoWithKeyPrefixInternal(children,result,null,emptyFunction.thatReturnsArgument);return result}var ReactChildren={forEach:forEachChildren,map:mapChildren,mapIntoWithKeyPrefixInternal:mapIntoWithKeyPrefixInternal,count:countChildren,toArray:toArray};module.exports=ReactChildren},{"./PooledClass":159,"./ReactElement":166,"./traverseAllChildren":182,"fbjs/lib/emptyFunction":10}],163:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactCurrentOwner=require("./ReactCurrentOwner");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");function isNative(fn){var funcToString=Function.prototype.toString;var hasOwnProperty=Object.prototype.hasOwnProperty;var reIsNative=RegExp("^"+funcToString.call(hasOwnProperty).replace(/[\\^$.*+?()[\]{}|]/g,"\\$&").replace(/hasOwnProperty|(function).*?(?=\\\()| for .+?(?=\\\])/g,"$1.*?")+"$");try{var source=funcToString.call(fn);return reIsNative.test(source)}catch(err){return false}}var canUseCollections=typeof Array.from==="function"&&typeof Map==="function"&&isNative(Map)&&Map.prototype!=null&&typeof Map.prototype.keys==="function"&&isNative(Map.prototype.keys)&&typeof Set==="function"&&isNative(Set)&&Set.prototype!=null&&typeof Set.prototype.keys==="function"&&isNative(Set.prototype.keys);var setItem;var getItem;var removeItem;var getItemIDs;var addRoot;var removeRoot;var getRootIDs;if(canUseCollections){var itemMap=new Map;var rootIDSet=new Set;setItem=function(id,item){itemMap.set(id,item)};getItem=function(id){return itemMap.get(id)};removeItem=function(id){itemMap["delete"](id)};getItemIDs=function(){return Array.from(itemMap.keys())};addRoot=function(id){rootIDSet.add(id)};removeRoot=function(id){rootIDSet["delete"](id)};getRootIDs=function(){return Array.from(rootIDSet.keys())}}else{var itemByKey={};var rootByKey={};var getKeyFromID=function(id){return"."+id};var getIDFromKey=function(key){return parseInt(key.substr(1),10)};setItem=function(id,item){var key=getKeyFromID(id);itemByKey[key]=item};getItem=function(id){var key=getKeyFromID(id);return itemByKey[key]};removeItem=function(id){var key=getKeyFromID(id);delete itemByKey[key]};getItemIDs=function(){return Object.keys(itemByKey).map(getIDFromKey)};addRoot=function(id){var key=getKeyFromID(id);rootByKey[key]=true};removeRoot=function(id){var key=getKeyFromID(id);delete rootByKey[key]};getRootIDs=function(){return Object.keys(rootByKey).map(getIDFromKey)}}var unmountedIDs=[];function purgeDeep(id){var item=getItem(id);if(item){var childIDs=item.childIDs;removeItem(id);childIDs.forEach(purgeDeep)}}function describeComponentFrame(name,source,ownerName){return"\n    in "+(name||"Unknown")+(source?" (at "+source.fileName.replace(/^.*[\\\/]/,"")+":"+source.lineNumber+")":ownerName?" (created by "+ownerName+")":"")}function getDisplayName(element){if(element==null){return"#empty"}else if(typeof element==="string"||typeof element==="number"){return"#text"}else if(typeof element.type==="string"){return element.type}else{return element.type.displayName||element.type.name||"Unknown"}}function describeID(id){var name=ReactComponentTreeHook.getDisplayName(id);var element=ReactComponentTreeHook.getElement(id);var ownerID=ReactComponentTreeHook.getOwnerID(id);var ownerName;if(ownerID){ownerName=ReactComponentTreeHook.getDisplayName(ownerID)}process.env.NODE_ENV!=="production"?warning(element,"ReactComponentTreeHook: Missing React element for debugID %s when "+"building stack",id):void 0;return describeComponentFrame(name,element&&element._source,ownerName)}var ReactComponentTreeHook={onSetChildren:function(id,nextChildIDs){var item=getItem(id);!item?process.env.NODE_ENV!=="production"?invariant(false,"Item must have been set"):_prodInvariant("144"):void 0;item.childIDs=nextChildIDs;for(var i=0;i<nextChildIDs.length;i++){var nextChildID=nextChildIDs[i];var nextChild=getItem(nextChildID);!nextChild?process.env.NODE_ENV!=="production"?invariant(false,"Expected hook events to fire for the child before its parent includes it in onSetChildren()."):_prodInvariant("140"):void 0;!(nextChild.childIDs!=null||typeof nextChild.element!=="object"||nextChild.element==null)?process.env.NODE_ENV!=="production"?invariant(false,"Expected onSetChildren() to fire for a container child before its parent includes it in onSetChildren()."):_prodInvariant("141"):void 0;!nextChild.isMounted?process.env.NODE_ENV!=="production"?invariant(false,"Expected onMountComponent() to fire for the child before its parent includes it in onSetChildren()."):_prodInvariant("71"):void 0;if(nextChild.parentID==null){nextChild.parentID=id}!(nextChild.parentID===id)?process.env.NODE_ENV!=="production"?invariant(false,"Expected onBeforeMountComponent() parent and onSetChildren() to be consistent (%s has parents %s and %s).",nextChildID,nextChild.parentID,id):_prodInvariant("142",nextChildID,nextChild.parentID,id):void 0}},onBeforeMountComponent:function(id,element,parentID){var item={element:element,parentID:parentID,text:null,childIDs:[],isMounted:false,updateCount:0};setItem(id,item)},onBeforeUpdateComponent:function(id,element){var item=getItem(id);if(!item||!item.isMounted){return}item.element=element},onMountComponent:function(id){var item=getItem(id);!item?process.env.NODE_ENV!=="production"?invariant(false,"Item must have been set"):_prodInvariant("144"):void 0;item.isMounted=true;var isRoot=item.parentID===0;if(isRoot){addRoot(id)}},onUpdateComponent:function(id){var item=getItem(id);if(!item||!item.isMounted){return}item.updateCount++},onUnmountComponent:function(id){var item=getItem(id);if(item){item.isMounted=false;var isRoot=item.parentID===0;if(isRoot){removeRoot(id)}}unmountedIDs.push(id)},purgeUnmountedComponents:function(){if(ReactComponentTreeHook._preventPurging){return}for(var i=0;i<unmountedIDs.length;i++){var id=unmountedIDs[i];purgeDeep(id)}unmountedIDs.length=0},isMounted:function(id){var item=getItem(id);return item?item.isMounted:false},getCurrentStackAddendum:function(topElement){var info="";if(topElement){var name=getDisplayName(topElement);var owner=topElement._owner;info+=describeComponentFrame(name,topElement._source,owner&&owner.getName())}var currentOwner=ReactCurrentOwner.current;var id=currentOwner&&currentOwner._debugID;info+=ReactComponentTreeHook.getStackAddendumByID(id);return info},getStackAddendumByID:function(id){var info="";while(id){info+=describeID(id);id=ReactComponentTreeHook.getParentID(id)}return info},getChildIDs:function(id){var item=getItem(id);return item?item.childIDs:[]},getDisplayName:function(id){var element=ReactComponentTreeHook.getElement(id);if(!element){return null}return getDisplayName(element)},getElement:function(id){var item=getItem(id);return item?item.element:null},getOwnerID:function(id){var element=ReactComponentTreeHook.getElement(id);if(!element||!element._owner){return null}return element._owner._debugID},getParentID:function(id){var item=getItem(id);return item?item.parentID:null},getSource:function(id){var item=getItem(id);var element=item?item.element:null;var source=element!=null?element._source:null;return source},getText:function(id){var element=ReactComponentTreeHook.getElement(id);if(typeof element==="string"){return element}else if(typeof element==="number"){return""+element}else{return null}},getUpdateCount:function(id){var item=getItem(id);return item?item.updateCount:0},getRootIDs:getRootIDs,getRegisteredIDs:getItemIDs,pushNonStandardWarningStack:function(isCreatingElement,currentSource){if(typeof console.reactStack!=="function"){return}var stack=[];var currentOwner=ReactCurrentOwner.current;var id=currentOwner&&currentOwner._debugID;try{if(isCreatingElement){stack.push({name:id?ReactComponentTreeHook.getDisplayName(id):null,fileName:currentSource?currentSource.fileName:null,lineNumber:currentSource?currentSource.lineNumber:null})}while(id){var element=ReactComponentTreeHook.getElement(id);var parentID=ReactComponentTreeHook.getParentID(id);var ownerID=ReactComponentTreeHook.getOwnerID(id);var ownerName=ownerID?ReactComponentTreeHook.getDisplayName(ownerID):null;var source=element&&element._source;stack.push({name:ownerName,fileName:source?source.fileName:null,lineNumber:source?source.lineNumber:null});id=parentID}}catch(err){}console.reactStack(stack)},popNonStandardWarningStack:function(){if(typeof console.reactStackEnd!=="function"){return}console.reactStackEnd()}};module.exports=ReactComponentTreeHook}).call(this,require("_process"))},{"./ReactCurrentOwner":164,"./reactProdInvariant":181,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],164:[function(require,module,exports){"use strict";var ReactCurrentOwner={current:null};module.exports=ReactCurrentOwner},{}],165:[function(require,module,exports){(function(process){"use strict";var ReactElement=require("./ReactElement");var createDOMFactory=ReactElement.createFactory;if(process.env.NODE_ENV!=="production"){var ReactElementValidator=require("./ReactElementValidator");createDOMFactory=ReactElementValidator.createFactory}var ReactDOMFactories={a:createDOMFactory("a"),abbr:createDOMFactory("abbr"),address:createDOMFactory("address"),area:createDOMFactory("area"),article:createDOMFactory("article"),aside:createDOMFactory("aside"),audio:createDOMFactory("audio"),b:createDOMFactory("b"),base:createDOMFactory("base"),bdi:createDOMFactory("bdi"),bdo:createDOMFactory("bdo"),big:createDOMFactory("big"),blockquote:createDOMFactory("blockquote"),body:createDOMFactory("body"),br:createDOMFactory("br"),button:createDOMFactory("button"),canvas:createDOMFactory("canvas"),caption:createDOMFactory("caption"),cite:createDOMFactory("cite"),code:createDOMFactory("code"),col:createDOMFactory("col"),colgroup:createDOMFactory("colgroup"),data:createDOMFactory("data"),datalist:createDOMFactory("datalist"),dd:createDOMFactory("dd"),del:createDOMFactory("del"),details:createDOMFactory("details"),dfn:createDOMFactory("dfn"),dialog:createDOMFactory("dialog"),div:createDOMFactory("div"),dl:createDOMFactory("dl"),dt:createDOMFactory("dt"),em:createDOMFactory("em"),embed:createDOMFactory("embed"),fieldset:createDOMFactory("fieldset"),figcaption:createDOMFactory("figcaption"),figure:createDOMFactory("figure"),footer:createDOMFactory("footer"),form:createDOMFactory("form"),h1:createDOMFactory("h1"),h2:createDOMFactory("h2"),h3:createDOMFactory("h3"),h4:createDOMFactory("h4"),h5:createDOMFactory("h5"),h6:createDOMFactory("h6"),head:createDOMFactory("head"),header:createDOMFactory("header"),hgroup:createDOMFactory("hgroup"),hr:createDOMFactory("hr"),html:createDOMFactory("html"),i:createDOMFactory("i"),iframe:createDOMFactory("iframe"),img:createDOMFactory("img"),input:createDOMFactory("input"),ins:createDOMFactory("ins"),kbd:createDOMFactory("kbd"),keygen:createDOMFactory("keygen"),label:createDOMFactory("label"),legend:createDOMFactory("legend"),li:createDOMFactory("li"),link:createDOMFactory("link"),main:createDOMFactory("main"),map:createDOMFactory("map"),mark:createDOMFactory("mark"),menu:createDOMFactory("menu"),menuitem:createDOMFactory("menuitem"),meta:createDOMFactory("meta"),meter:createDOMFactory("meter"),nav:createDOMFactory("nav"),noscript:createDOMFactory("noscript"),object:createDOMFactory("object"),ol:createDOMFactory("ol"),optgroup:createDOMFactory("optgroup"),option:createDOMFactory("option"),output:createDOMFactory("output"),p:createDOMFactory("p"),param:createDOMFactory("param"),picture:createDOMFactory("picture"),pre:createDOMFactory("pre"),progress:createDOMFactory("progress"),q:createDOMFactory("q"),rp:createDOMFactory("rp"),rt:createDOMFactory("rt"),ruby:createDOMFactory("ruby"),s:createDOMFactory("s"),samp:createDOMFactory("samp"),script:createDOMFactory("script"),section:createDOMFactory("section"),select:createDOMFactory("select"),small:createDOMFactory("small"),source:createDOMFactory("source"),span:createDOMFactory("span"),strong:createDOMFactory("strong"),style:createDOMFactory("style"),sub:createDOMFactory("sub"),summary:createDOMFactory("summary"),sup:createDOMFactory("sup"),table:createDOMFactory("table"),tbody:createDOMFactory("tbody"),td:createDOMFactory("td"),textarea:createDOMFactory("textarea"),tfoot:createDOMFactory("tfoot"),th:createDOMFactory("th"),thead:createDOMFactory("thead"),time:createDOMFactory("time"),title:createDOMFactory("title"),tr:createDOMFactory("tr"),track:createDOMFactory("track"),u:createDOMFactory("u"),ul:createDOMFactory("ul"),var:createDOMFactory("var"),video:createDOMFactory("video"),wbr:createDOMFactory("wbr"),circle:createDOMFactory("circle"),clipPath:createDOMFactory("clipPath"),defs:createDOMFactory("defs"),ellipse:createDOMFactory("ellipse"),g:createDOMFactory("g"),image:createDOMFactory("image"),line:createDOMFactory("line"),linearGradient:createDOMFactory("linearGradient"),mask:createDOMFactory("mask"),path:createDOMFactory("path"),pattern:createDOMFactory("pattern"),polygon:createDOMFactory("polygon"),polyline:createDOMFactory("polyline"),radialGradient:createDOMFactory("radialGradient"),rect:createDOMFactory("rect"),stop:createDOMFactory("stop"),svg:createDOMFactory("svg"),text:createDOMFactory("text"),tspan:createDOMFactory("tspan")};module.exports=ReactDOMFactories}).call(this,require("_process"))},{"./ReactElement":166,"./ReactElementValidator":168,_process:184}],166:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var ReactCurrentOwner=require("./ReactCurrentOwner");var warning=require("fbjs/lib/warning");var canDefineProperty=require("./canDefineProperty");var hasOwnProperty=Object.prototype.hasOwnProperty;var REACT_ELEMENT_TYPE=require("./ReactElementSymbol");var RESERVED_PROPS={key:true,ref:true,__self:true,__source:true};var specialPropKeyWarningShown,specialPropRefWarningShown;function hasValidRef(config){if(process.env.NODE_ENV!=="production"){if(hasOwnProperty.call(config,"ref")){var getter=Object.getOwnPropertyDescriptor(config,"ref").get;if(getter&&getter.isReactWarning){return false}}}return config.ref!==undefined}function hasValidKey(config){if(process.env.NODE_ENV!=="production"){if(hasOwnProperty.call(config,"key")){var getter=Object.getOwnPropertyDescriptor(config,"key").get;if(getter&&getter.isReactWarning){return false}}}return config.key!==undefined}function defineKeyPropWarningGetter(props,displayName){var warnAboutAccessingKey=function(){if(!specialPropKeyWarningShown){specialPropKeyWarningShown=true;process.env.NODE_ENV!=="production"?warning(false,"%s: `key` is not a prop. Trying to access it will result "+"in `undefined` being returned. If you need to access the same "+"value within the child component, you should pass it as a different "+"prop. (https://fb.me/react-special-props)",displayName):void 0}};warnAboutAccessingKey.isReactWarning=true;Object.defineProperty(props,"key",{get:warnAboutAccessingKey,configurable:true})}function defineRefPropWarningGetter(props,displayName){var warnAboutAccessingRef=function(){if(!specialPropRefWarningShown){specialPropRefWarningShown=true;process.env.NODE_ENV!=="production"?warning(false,"%s: `ref` is not a prop. Trying to access it will result "+"in `undefined` being returned. If you need to access the same "+"value within the child component, you should pass it as a different "+"prop. (https://fb.me/react-special-props)",displayName):void 0}};warnAboutAccessingRef.isReactWarning=true;Object.defineProperty(props,"ref",{get:warnAboutAccessingRef,configurable:true})}var ReactElement=function(type,key,ref,self,source,owner,props){var element={$$typeof:REACT_ELEMENT_TYPE,type:type,key:key,ref:ref,props:props,_owner:owner};if(process.env.NODE_ENV!=="production"){element._store={};if(canDefineProperty){Object.defineProperty(element._store,"validated",{configurable:false,enumerable:false,writable:true,value:false});Object.defineProperty(element,"_self",{configurable:false,enumerable:false,writable:false,value:self});Object.defineProperty(element,"_source",{configurable:false,enumerable:false,writable:false,value:source})}else{element._store.validated=false;element._self=self;element._source=source}if(Object.freeze){Object.freeze(element.props);Object.freeze(element)}}return element};ReactElement.createElement=function(type,config,children){var propName;var props={};var key=null;var ref=null;var self=null;var source=null;if(config!=null){if(hasValidRef(config)){ref=config.ref}if(hasValidKey(config)){key=""+config.key}self=config.__self===undefined?null:config.__self;source=config.__source===undefined?null:config.__source;for(propName in config){if(hasOwnProperty.call(config,propName)&&!RESERVED_PROPS.hasOwnProperty(propName)){props[propName]=config[propName]}}}var childrenLength=arguments.length-2;if(childrenLength===1){props.children=children}else if(childrenLength>1){var childArray=Array(childrenLength);for(var i=0;i<childrenLength;i++){childArray[i]=arguments[i+2]}if(process.env.NODE_ENV!=="production"){if(Object.freeze){Object.freeze(childArray)}}props.children=childArray}if(type&&type.defaultProps){var defaultProps=type.defaultProps;for(propName in defaultProps){if(props[propName]===undefined){props[propName]=defaultProps[propName]}}}if(process.env.NODE_ENV!=="production"){if(key||ref){if(typeof props.$$typeof==="undefined"||props.$$typeof!==REACT_ELEMENT_TYPE){var displayName=typeof type==="function"?type.displayName||type.name||"Unknown":type;if(key){defineKeyPropWarningGetter(props,displayName)}if(ref){defineRefPropWarningGetter(props,displayName)}}}}return ReactElement(type,key,ref,self,source,ReactCurrentOwner.current,props)};ReactElement.createFactory=function(type){var factory=ReactElement.createElement.bind(null,type);factory.type=type;return factory};ReactElement.cloneAndReplaceKey=function(oldElement,newKey){var newElement=ReactElement(oldElement.type,newKey,oldElement.ref,oldElement._self,oldElement._source,oldElement._owner,oldElement.props);return newElement};ReactElement.cloneElement=function(element,config,children){var propName;var props=_assign({},element.props);var key=element.key;var ref=element.ref;var self=element._self;var source=element._source;var owner=element._owner;if(config!=null){if(hasValidRef(config)){ref=config.ref;owner=ReactCurrentOwner.current}if(hasValidKey(config)){key=""+config.key}var defaultProps;if(element.type&&element.type.defaultProps){defaultProps=element.type.defaultProps}for(propName in config){if(hasOwnProperty.call(config,propName)&&!RESERVED_PROPS.hasOwnProperty(propName)){if(config[propName]===undefined&&defaultProps!==undefined){props[propName]=defaultProps[propName]}else{props[propName]=config[propName]}}}}var childrenLength=arguments.length-2;if(childrenLength===1){props.children=children}else if(childrenLength>1){var childArray=Array(childrenLength);for(var i=0;i<childrenLength;i++){childArray[i]=arguments[i+2]}props.children=childArray}return ReactElement(element.type,key,ref,self,source,owner,props)};ReactElement.isValidElement=function(object){return typeof object==="object"&&object!==null&&object.$$typeof===REACT_ELEMENT_TYPE};module.exports=ReactElement}).call(this,require("_process"))},{"./ReactCurrentOwner":164,"./ReactElementSymbol":167,"./canDefineProperty":174,_process:184,"fbjs/lib/warning":25,"object-assign":26}],167:[function(require,module,exports){arguments[4][82][0].apply(exports,arguments)},{dup:82}],168:[function(require,module,exports){(function(process){"use strict";var ReactCurrentOwner=require("./ReactCurrentOwner");var ReactComponentTreeHook=require("./ReactComponentTreeHook");var ReactElement=require("./ReactElement");var checkReactTypeSpec=require("./checkReactTypeSpec");var canDefineProperty=require("./canDefineProperty");var getIteratorFn=require("./getIteratorFn");var warning=require("fbjs/lib/warning");var lowPriorityWarning=require("./lowPriorityWarning");function getDeclarationErrorAddendum(){if(ReactCurrentOwner.current){var name=ReactCurrentOwner.current.getName();if(name){return" Check the render method of `"+name+"`."}}return""}function getSourceInfoErrorAddendum(elementProps){if(elementProps!==null&&elementProps!==undefined&&elementProps.__source!==undefined){var source=elementProps.__source;var fileName=source.fileName.replace(/^.*[\\\/]/,"");var lineNumber=source.lineNumber;return" Check your code at "+fileName+":"+lineNumber+"."}return""}var ownerHasKeyUseWarning={};function getCurrentComponentErrorInfo(parentType){var info=getDeclarationErrorAddendum();if(!info){var parentName=typeof parentType==="string"?parentType:parentType.displayName||parentType.name;if(parentName){info=" Check the top-level render call using <"+parentName+">."}}return info}function validateExplicitKey(element,parentType){if(!element._store||element._store.validated||element.key!=null){return}element._store.validated=true;var memoizer=ownerHasKeyUseWarning.uniqueKey||(ownerHasKeyUseWarning.uniqueKey={});var currentComponentErrorInfo=getCurrentComponentErrorInfo(parentType);if(memoizer[currentComponentErrorInfo]){return}memoizer[currentComponentErrorInfo]=true;var childOwner="";if(element&&element._owner&&element._owner!==ReactCurrentOwner.current){childOwner=" It was passed a child from "+element._owner.getName()+"."}process.env.NODE_ENV!=="production"?warning(false,'Each child in an array or iterator should have a unique "key" prop.'+"%s%s See https://fb.me/react-warning-keys for more information.%s",currentComponentErrorInfo,childOwner,ReactComponentTreeHook.getCurrentStackAddendum(element)):void 0}function validateChildKeys(node,parentType){if(typeof node!=="object"){return}if(Array.isArray(node)){for(var i=0;i<node.length;i++){var child=node[i];if(ReactElement.isValidElement(child)){validateExplicitKey(child,parentType)}}}else if(ReactElement.isValidElement(node)){if(node._store){node._store.validated=true}}else if(node){var iteratorFn=getIteratorFn(node);if(iteratorFn){if(iteratorFn!==node.entries){var iterator=iteratorFn.call(node);var step;while(!(step=iterator.next()).done){if(ReactElement.isValidElement(step.value)){validateExplicitKey(step.value,parentType)}}}}}}function validatePropTypes(element){var componentClass=element.type;if(typeof componentClass!=="function"){return}var name=componentClass.displayName||componentClass.name;if(componentClass.propTypes){checkReactTypeSpec(componentClass.propTypes,element.props,"prop",name,element,null)}if(typeof componentClass.getDefaultProps==="function"){process.env.NODE_ENV!=="production"?warning(componentClass.getDefaultProps.isReactClassApproved,"getDefaultProps is only used on classic React.createClass "+"definitions. Use a static property named `defaultProps` instead."):void 0}}var ReactElementValidator={createElement:function(type,props,children){var validType=typeof type==="string"||typeof type==="function";if(!validType){if(typeof type!=="function"&&typeof type!=="string"){var info="";if(type===undefined||typeof type==="object"&&type!==null&&Object.keys(type).length===0){info+=" You likely forgot to export your component from the file "+"it's defined in."}var sourceInfo=getSourceInfoErrorAddendum(props);if(sourceInfo){info+=sourceInfo}else{info+=getDeclarationErrorAddendum()}info+=ReactComponentTreeHook.getCurrentStackAddendum();var currentSource=props!==null&&props!==undefined&&props.__source!==undefined?props.__source:null;ReactComponentTreeHook.pushNonStandardWarningStack(true,currentSource);process.env.NODE_ENV!=="production"?warning(false,"React.createElement: type is invalid -- expected a string (for "+"built-in components) or a class/function (for composite "+"components) but got: %s.%s",type==null?type:typeof type,info):void 0;ReactComponentTreeHook.popNonStandardWarningStack()}}var element=ReactElement.createElement.apply(this,arguments);if(element==null){return element}if(validType){for(var i=2;i<arguments.length;i++){validateChildKeys(arguments[i],type)}}validatePropTypes(element);return element},createFactory:function(type){var validatedFactory=ReactElementValidator.createElement.bind(null,type);validatedFactory.type=type;if(process.env.NODE_ENV!=="production"){if(canDefineProperty){Object.defineProperty(validatedFactory,"type",{enumerable:false,get:function(){lowPriorityWarning(false,"Factory.type is deprecated. Access the class directly "+"before passing it to createFactory.");Object.defineProperty(this,"type",{value:type});return type}})}}return validatedFactory},cloneElement:function(element,props,children){var newElement=ReactElement.cloneElement.apply(this,arguments);for(var i=2;i<arguments.length;i++){validateChildKeys(arguments[i],newElement.type)}validatePropTypes(newElement);return newElement}};module.exports=ReactElementValidator}).call(this,require("_process"))},{"./ReactComponentTreeHook":163,"./ReactCurrentOwner":164,"./ReactElement":166,"./canDefineProperty":174,"./checkReactTypeSpec":175,"./getIteratorFn":177,"./lowPriorityWarning":179,_process:184,"fbjs/lib/warning":25}],169:[function(require,module,exports){(function(process){"use strict";var warning=require("fbjs/lib/warning");function warnNoop(publicInstance,callerName){if(process.env.NODE_ENV!=="production"){var constructor=publicInstance.constructor;process.env.NODE_ENV!=="production"?warning(false,"%s(...): Can only update a mounted or mounting component. "+"This usually means you called %s() on an unmounted component. "+"This is a no-op. Please check the code for the %s component.",callerName,callerName,constructor&&(constructor.displayName||constructor.name)||"ReactClass"):void 0}}var ReactNoopUpdateQueue={isMounted:function(publicInstance){return false},enqueueCallback:function(publicInstance,callback){},enqueueForceUpdate:function(publicInstance){warnNoop(publicInstance,"forceUpdate")},enqueueReplaceState:function(publicInstance,completeState){warnNoop(publicInstance,"replaceState")},enqueueSetState:function(publicInstance,partialState){warnNoop(publicInstance,"setState")}};module.exports=ReactNoopUpdateQueue}).call(this,require("_process"))},{_process:184,"fbjs/lib/warning":25}],170:[function(require,module,exports){arguments[4][100][0].apply(exports,arguments)},{_process:184,dup:100}],171:[function(require,module,exports){"use strict";var _require=require("./ReactElement"),isValidElement=_require.isValidElement;var factory=require("prop-types/factory");module.exports=factory(isValidElement)},{"./ReactElement":166,"prop-types/factory":28}],172:[function(require,module,exports){arguments[4][101][0].apply(exports,arguments)},{dup:101}],173:[function(require,module,exports){arguments[4][109][0].apply(exports,arguments)},{dup:109}],174:[function(require,module,exports){(function(process){"use strict";var canDefineProperty=false;if(process.env.NODE_ENV!=="production"){try{Object.defineProperty({},"x",{get:function(){}});canDefineProperty=true}catch(x){}}module.exports=canDefineProperty}).call(this,require("_process"))},{_process:184}],175:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactPropTypeLocationNames=require("./ReactPropTypeLocationNames");var ReactPropTypesSecret=require("./ReactPropTypesSecret");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ReactComponentTreeHook;if(typeof process!=="undefined"&&process.env&&process.env.NODE_ENV==="test"){ReactComponentTreeHook=require("./ReactComponentTreeHook")}var loggedTypeFailures={};function checkReactTypeSpec(typeSpecs,values,location,componentName,element,debugID){for(var typeSpecName in typeSpecs){if(typeSpecs.hasOwnProperty(typeSpecName)){var error;try{!(typeof typeSpecs[typeSpecName]==="function")?process.env.NODE_ENV!=="production"?invariant(false,"%s: %s type `%s` is invalid; it must be a function, usually from React.PropTypes.",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName):_prodInvariant("84",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName):void 0;error=typeSpecs[typeSpecName](values,typeSpecName,componentName,location,null,ReactPropTypesSecret)}catch(ex){error=ex}process.env.NODE_ENV!=="production"?warning(!error||error instanceof Error,"%s: type specification of %s `%s` is invalid; the type checker "+"function must return `null` or an `Error` but returned a %s. "+"You may have forgotten to pass an argument to the type checker "+"creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and "+"shape all require an argument).",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName,typeof error):void 0;if(error instanceof Error&&!(error.message in loggedTypeFailures)){loggedTypeFailures[error.message]=true;var componentStackInfo="";if(process.env.NODE_ENV!=="production"){if(!ReactComponentTreeHook){ReactComponentTreeHook=require("./ReactComponentTreeHook")}if(debugID!==null){componentStackInfo=ReactComponentTreeHook.getStackAddendumByID(debugID)}else if(element!==null){componentStackInfo=ReactComponentTreeHook.getCurrentStackAddendum(element)}}process.env.NODE_ENV!=="production"?warning(false,"Failed %s type: %s%s",location,error.message,componentStackInfo):void 0}}}}module.exports=checkReactTypeSpec}).call(this,require("_process"))},{"./ReactComponentTreeHook":163,"./ReactPropTypeLocationNames":170,"./ReactPropTypesSecret":172,"./reactProdInvariant":181,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],176:[function(require,module,exports){"use strict";var _require=require("./ReactBaseClasses"),Component=_require.Component;var _require2=require("./ReactElement"),isValidElement=_require2.isValidElement;var ReactNoopUpdateQueue=require("./ReactNoopUpdateQueue");var factory=require("create-react-class/factory");module.exports=factory(Component,isValidElement,ReactNoopUpdateQueue)},{"./ReactBaseClasses":161,"./ReactElement":166,"./ReactNoopUpdateQueue":169,"create-react-class/factory":2}],177:[function(require,module,exports){arguments[4][142][0].apply(exports,arguments)},{dup:142}],178:[function(require,module,exports){"use strict";var nextDebugID=1;function getNextDebugID(){return nextDebugID++}module.exports=getNextDebugID},{}],179:[function(require,module,exports){(function(process){"use strict";var lowPriorityWarning=function(){};if(process.env.NODE_ENV!=="production"){var printWarning=function(format){for(var _len=arguments.length,args=Array(_len>1?_len-1:0),_key=1;_key<_len;_key++){args[_key-1]=arguments[_key]}var argIndex=0;var message="Warning: "+format.replace(/%s/g,function(){return args[argIndex++]});if(typeof console!=="undefined"){console.warn(message)}try{throw new Error(message)}catch(x){}};lowPriorityWarning=function(condition,format){if(format===undefined){throw new Error("`warning(condition, format, ...args)` requires a warning "+"message argument")}if(!condition){for(var _len2=arguments.length,args=Array(_len2>2?_len2-2:0),_key2=2;_key2<_len2;_key2++){args[_key2-2]=arguments[_key2]}printWarning.apply(undefined,[format].concat(args))}}}module.exports=lowPriorityWarning}).call(this,require("_process"))},{_process:184}],180:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactElement=require("./ReactElement");var invariant=require("fbjs/lib/invariant");function onlyChild(children){!ReactElement.isValidElement(children)?process.env.NODE_ENV!=="production"?invariant(false,"React.Children.only expected to receive a single React element child."):_prodInvariant("143"):void 0;return children}module.exports=onlyChild}).call(this,require("_process"))},{"./ReactElement":166,"./reactProdInvariant":181,_process:184,"fbjs/lib/invariant":18}],181:[function(require,module,exports){arguments[4][151][0].apply(exports,arguments)},{dup:151}],182:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactCurrentOwner=require("./ReactCurrentOwner");var REACT_ELEMENT_TYPE=require("./ReactElementSymbol");var getIteratorFn=require("./getIteratorFn");var invariant=require("fbjs/lib/invariant");var KeyEscapeUtils=require("./KeyEscapeUtils");var warning=require("fbjs/lib/warning");var SEPARATOR=".";var SUBSEPARATOR=":";var didWarnAboutMaps=false;function getComponentKey(component,index){if(component&&typeof component==="object"&&component.key!=null){return KeyEscapeUtils.escape(component.key)}return index.toString(36)}function traverseAllChildrenImpl(children,nameSoFar,callback,traverseContext){var type=typeof children;if(type==="undefined"||type==="boolean"){children=null}if(children===null||type==="string"||type==="number"||type==="object"&&children.$$typeof===REACT_ELEMENT_TYPE){callback(traverseContext,children,nameSoFar===""?SEPARATOR+getComponentKey(children,0):nameSoFar);return 1}var child;var nextName;var subtreeCount=0;var nextNamePrefix=nameSoFar===""?SEPARATOR:nameSoFar+SUBSEPARATOR;if(Array.isArray(children)){for(var i=0;i<children.length;i++){child=children[i];nextName=nextNamePrefix+getComponentKey(child,i);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}else{var iteratorFn=getIteratorFn(children);if(iteratorFn){var iterator=iteratorFn.call(children);var step;if(iteratorFn!==children.entries){var ii=0;while(!(step=iterator.next()).done){child=step.value;nextName=nextNamePrefix+getComponentKey(child,ii++);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}else{if(process.env.NODE_ENV!=="production"){var mapsAsChildrenAddendum="";if(ReactCurrentOwner.current){var mapsAsChildrenOwnerName=ReactCurrentOwner.current.getName();if(mapsAsChildrenOwnerName){mapsAsChildrenAddendum=" Check the render method of `"+mapsAsChildrenOwnerName+"`."}}process.env.NODE_ENV!=="production"?warning(didWarnAboutMaps,"Using Maps as children is not yet fully supported. It is an "+"experimental feature that might be removed. Convert it to a "+"sequence / iterable of keyed ReactElements instead.%s",mapsAsChildrenAddendum):void 0;didWarnAboutMaps=true}while(!(step=iterator.next()).done){var entry=step.value;if(entry){child=entry[1];nextName=nextNamePrefix+KeyEscapeUtils.escape(entry[0])+SUBSEPARATOR+getComponentKey(child,0);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}}}else if(type==="object"){var addendum="";if(process.env.NODE_ENV!=="production"){addendum=" If you meant to render a collection of children, use an array "+"instead or wrap the object using createFragment(object) from the "+"React add-ons.";if(children._isReactElement){addendum=" It looks like you're using an element created by a different "+"version of React. Make sure to use only one copy of React."}if(ReactCurrentOwner.current){var name=ReactCurrentOwner.current.getName();if(name){addendum+=" Check the render method of `"+name+"`."}}}var childrenString=String(children);!false?process.env.NODE_ENV!=="production"?invariant(false,"Objects are not valid as a React child (found: %s).%s",childrenString==="[object Object]"?"object with keys {"+Object.keys(children).join(", ")+"}":childrenString,addendum):_prodInvariant("31",childrenString==="[object Object]"?"object with keys {"+Object.keys(children).join(", ")+"}":childrenString,addendum):void 0}}return subtreeCount}function traverseAllChildren(children,callback,traverseContext){if(children==null){return 0}return traverseAllChildrenImpl(children,"",callback,traverseContext)}module.exports=traverseAllChildren}).call(this,require("_process"))},{"./KeyEscapeUtils":158,"./ReactCurrentOwner":164,"./ReactElementSymbol":167,"./getIteratorFn":177,"./reactProdInvariant":181,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],183:[function(require,module,exports){"use strict";module.exports=require("./lib/React")},{"./lib/React":160}],184:[function(require,module,exports){var process=module.exports={};var cachedSetTimeout;var cachedClearTimeout;function defaultSetTimout(){throw new Error("setTimeout has not been defined")}function defaultClearTimeout(){throw new Error("clearTimeout has not been defined")}(function(){try{if(typeof setTimeout==="function"){cachedSetTimeout=setTimeout}else{cachedSetTimeout=defaultSetTimout}}catch(e){cachedSetTimeout=defaultSetTimout}try{if(typeof clearTimeout==="function"){cachedClearTimeout=clearTimeout}else{cachedClearTimeout=defaultClearTimeout}}catch(e){cachedClearTimeout=defaultClearTimeout}})();function runTimeout(fun){if(cachedSetTimeout===setTimeout){return setTimeout(fun,0)}if((cachedSetTimeout===defaultSetTimout||!cachedSetTimeout)&&setTimeout){cachedSetTimeout=setTimeout;return setTimeout(fun,0)}try{return cachedSetTimeout(fun,0)}catch(e){try{return cachedSetTimeout.call(null,fun,0)}catch(e){return cachedSetTimeout.call(this,fun,0)}}}function runClearTimeout(marker){if(cachedClearTimeout===clearTimeout){return clearTimeout(marker)}if((cachedClearTimeout===defaultClearTimeout||!cachedClearTimeout)&&clearTimeout){cachedClearTimeout=clearTimeout;return clearTimeout(marker)}try{return cachedClearTimeout(marker)}catch(e){try{return cachedClearTimeout.call(null,marker)}catch(e){return cachedClearTimeout.call(this,marker)}}}var queue=[];var draining=false;var currentQueue;var queueIndex=-1;function cleanUpNextTick(){if(!draining||!currentQueue){return}draining=false;if(currentQueue.length){queue=currentQueue.concat(queue)}else{queueIndex=-1}if(queue.length){drainQueue()}}function drainQueue(){if(draining){return}var timeout=runTimeout(cleanUpNextTick);draining=true;var len=queue.length;while(len){currentQueue=queue;queue=[];while(++queueIndex<len){if(currentQueue){currentQueue[queueIndex].run()}}queueIndex=-1;len=queue.length}currentQueue=null;draining=false;runClearTimeout(timeout)}process.nextTick=function(fun){var args=new Array(arguments.length-1);if(arguments.length>1){for(var i=1;i<arguments.length;i++){args[i-1]=arguments[i]}}queue.push(new Item(fun,args));if(queue.length===1&&!draining){runTimeout(drainQueue)}};function Item(fun,array){this.fun=fun;this.array=array}Item.prototype.run=function(){this.fun.apply(null,this.array)};process.title="browser";process.browser=true;process.env={};process.argv=[];process.version="";process.versions={};function noop(){}process.on=noop;process.addListener=noop;process.once=noop;process.off=noop;process.removeListener=noop;process.removeAllListeners=noop;process.emit=noop;process.prependListener=noop;process.prependOnceListener=noop;process.listeners=function(name){return[]};process.binding=function(name){throw new Error("process.binding is not supported")};process.cwd=function(){return"/"};process.chdir=function(dir){throw new Error("process.chdir is not supported")};process.umask=function(){return 0}},{}]},{},[1]);






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

function h$concurEventCallback(async, action, ev) {
    var a = (h$c2(h$ap1_e,(action),((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (ev))))));
    if(async) {
        h$run(a);
    } else {
        h$runSync(a, true);
    }
}
(function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){(function(global){global.h$concur={React:require("react"),ReactDOM:require("react-dom"),makeHandler:function(action,async){var f=function(ev){return h$concurEventCallback(async,action,ev)};f.hsAction=action;return f}}}).call(this,typeof global!=="undefined"?global:typeof self!=="undefined"?self:typeof window!=="undefined"?window:{})},{react:183,"react-dom":31}],2:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var emptyObject=require("fbjs/lib/emptyObject");var _invariant=require("fbjs/lib/invariant");if(process.env.NODE_ENV!=="production"){var warning=require("fbjs/lib/warning")}var MIXINS_KEY="mixins";function identity(fn){return fn}var ReactPropTypeLocationNames;if(process.env.NODE_ENV!=="production"){ReactPropTypeLocationNames={prop:"prop",context:"context",childContext:"child context"}}else{ReactPropTypeLocationNames={}}function factory(ReactComponent,isValidElement,ReactNoopUpdateQueue){var injectedMixins=[];var ReactClassInterface={mixins:"DEFINE_MANY",statics:"DEFINE_MANY",propTypes:"DEFINE_MANY",contextTypes:"DEFINE_MANY",childContextTypes:"DEFINE_MANY",getDefaultProps:"DEFINE_MANY_MERGED",getInitialState:"DEFINE_MANY_MERGED",getChildContext:"DEFINE_MANY_MERGED",render:"DEFINE_ONCE",componentWillMount:"DEFINE_MANY",componentDidMount:"DEFINE_MANY",componentWillReceiveProps:"DEFINE_MANY",shouldComponentUpdate:"DEFINE_ONCE",componentWillUpdate:"DEFINE_MANY",componentDidUpdate:"DEFINE_MANY",componentWillUnmount:"DEFINE_MANY",updateComponent:"OVERRIDE_BASE"};var RESERVED_SPEC_KEYS={displayName:function(Constructor,displayName){Constructor.displayName=displayName},mixins:function(Constructor,mixins){if(mixins){for(var i=0;i<mixins.length;i++){mixSpecIntoComponent(Constructor,mixins[i])}}},childContextTypes:function(Constructor,childContextTypes){if(process.env.NODE_ENV!=="production"){validateTypeDef(Constructor,childContextTypes,"childContext")}Constructor.childContextTypes=_assign({},Constructor.childContextTypes,childContextTypes)},contextTypes:function(Constructor,contextTypes){if(process.env.NODE_ENV!=="production"){validateTypeDef(Constructor,contextTypes,"context")}Constructor.contextTypes=_assign({},Constructor.contextTypes,contextTypes)},getDefaultProps:function(Constructor,getDefaultProps){if(Constructor.getDefaultProps){Constructor.getDefaultProps=createMergedResultFunction(Constructor.getDefaultProps,getDefaultProps)}else{Constructor.getDefaultProps=getDefaultProps}},propTypes:function(Constructor,propTypes){if(process.env.NODE_ENV!=="production"){validateTypeDef(Constructor,propTypes,"prop")}Constructor.propTypes=_assign({},Constructor.propTypes,propTypes)},statics:function(Constructor,statics){mixStaticSpecIntoComponent(Constructor,statics)},autobind:function(){}};function validateTypeDef(Constructor,typeDef,location){for(var propName in typeDef){if(typeDef.hasOwnProperty(propName)){if(process.env.NODE_ENV!=="production"){warning(typeof typeDef[propName]==="function","%s: %s type `%s` is invalid; it must be a function, usually from "+"React.PropTypes.",Constructor.displayName||"ReactClass",ReactPropTypeLocationNames[location],propName)}}}}function validateMethodOverride(isAlreadyDefined,name){var specPolicy=ReactClassInterface.hasOwnProperty(name)?ReactClassInterface[name]:null;if(ReactClassMixin.hasOwnProperty(name)){_invariant(specPolicy==="OVERRIDE_BASE","ReactClassInterface: You are attempting to override "+"`%s` from your class specification. Ensure that your method names "+"do not overlap with React methods.",name)}if(isAlreadyDefined){_invariant(specPolicy==="DEFINE_MANY"||specPolicy==="DEFINE_MANY_MERGED","ReactClassInterface: You are attempting to define "+"`%s` on your component more than once. This conflict may be due "+"to a mixin.",name)}}function mixSpecIntoComponent(Constructor,spec){if(!spec){if(process.env.NODE_ENV!=="production"){var typeofSpec=typeof spec;var isMixinValid=typeofSpec==="object"&&spec!==null;if(process.env.NODE_ENV!=="production"){warning(isMixinValid,"%s: You're attempting to include a mixin that is either null "+"or not an object. Check the mixins included by the component, "+"as well as any mixins they include themselves. "+"Expected object but got %s.",Constructor.displayName||"ReactClass",spec===null?null:typeofSpec)}}return}_invariant(typeof spec!=="function","ReactClass: You're attempting to "+"use a component class or function as a mixin. Instead, just use a "+"regular object.");_invariant(!isValidElement(spec),"ReactClass: You're attempting to "+"use a component as a mixin. Instead, just use a regular object.");var proto=Constructor.prototype;var autoBindPairs=proto.__reactAutoBindPairs;if(spec.hasOwnProperty(MIXINS_KEY)){RESERVED_SPEC_KEYS.mixins(Constructor,spec.mixins)}for(var name in spec){if(!spec.hasOwnProperty(name)){continue}if(name===MIXINS_KEY){continue}var property=spec[name];var isAlreadyDefined=proto.hasOwnProperty(name);validateMethodOverride(isAlreadyDefined,name);if(RESERVED_SPEC_KEYS.hasOwnProperty(name)){RESERVED_SPEC_KEYS[name](Constructor,property)}else{var isReactClassMethod=ReactClassInterface.hasOwnProperty(name);var isFunction=typeof property==="function";var shouldAutoBind=isFunction&&!isReactClassMethod&&!isAlreadyDefined&&spec.autobind!==false;if(shouldAutoBind){autoBindPairs.push(name,property);proto[name]=property}else{if(isAlreadyDefined){var specPolicy=ReactClassInterface[name];_invariant(isReactClassMethod&&(specPolicy==="DEFINE_MANY_MERGED"||specPolicy==="DEFINE_MANY"),"ReactClass: Unexpected spec policy %s for key %s "+"when mixing in component specs.",specPolicy,name);if(specPolicy==="DEFINE_MANY_MERGED"){proto[name]=createMergedResultFunction(proto[name],property)}else if(specPolicy==="DEFINE_MANY"){proto[name]=createChainedFunction(proto[name],property)}}else{proto[name]=property;if(process.env.NODE_ENV!=="production"){if(typeof property==="function"&&spec.displayName){proto[name].displayName=spec.displayName+"_"+name}}}}}}}function mixStaticSpecIntoComponent(Constructor,statics){if(!statics){return}for(var name in statics){var property=statics[name];if(!statics.hasOwnProperty(name)){continue}var isReserved=name in RESERVED_SPEC_KEYS;_invariant(!isReserved,"ReactClass: You are attempting to define a reserved "+'property, `%s`, that shouldn\'t be on the "statics" key. Define it '+"as an instance property instead; it will still be accessible on the "+"constructor.",name);var isInherited=name in Constructor;_invariant(!isInherited,"ReactClass: You are attempting to define "+"`%s` on your component more than once. This conflict may be "+"due to a mixin.",name);Constructor[name]=property}}function mergeIntoWithNoDuplicateKeys(one,two){_invariant(one&&two&&typeof one==="object"&&typeof two==="object","mergeIntoWithNoDuplicateKeys(): Cannot merge non-objects.");for(var key in two){if(two.hasOwnProperty(key)){_invariant(one[key]===undefined,"mergeIntoWithNoDuplicateKeys(): "+"Tried to merge two objects with the same key: `%s`. This conflict "+"may be due to a mixin; in particular, this may be caused by two "+"getInitialState() or getDefaultProps() methods returning objects "+"with clashing keys.",key);one[key]=two[key]}}return one}function createMergedResultFunction(one,two){return function mergedResult(){var a=one.apply(this,arguments);var b=two.apply(this,arguments);if(a==null){return b}else if(b==null){return a}var c={};mergeIntoWithNoDuplicateKeys(c,a);mergeIntoWithNoDuplicateKeys(c,b);return c}}function createChainedFunction(one,two){return function chainedFunction(){one.apply(this,arguments);two.apply(this,arguments)}}function bindAutoBindMethod(component,method){var boundMethod=method.bind(component);if(process.env.NODE_ENV!=="production"){boundMethod.__reactBoundContext=component;boundMethod.__reactBoundMethod=method;boundMethod.__reactBoundArguments=null;var componentName=component.constructor.displayName;var _bind=boundMethod.bind;boundMethod.bind=function(newThis){for(var _len=arguments.length,args=Array(_len>1?_len-1:0),_key=1;_key<_len;_key++){args[_key-1]=arguments[_key]}if(newThis!==component&&newThis!==null){if(process.env.NODE_ENV!=="production"){warning(false,"bind(): React component methods may only be bound to the "+"component instance. See %s",componentName)}}else if(!args.length){if(process.env.NODE_ENV!=="production"){warning(false,"bind(): You are binding a component method to the component. "+"React does this for you automatically in a high-performance "+"way, so you can safely remove this call. See %s",componentName)}return boundMethod}var reboundMethod=_bind.apply(boundMethod,arguments);reboundMethod.__reactBoundContext=component;reboundMethod.__reactBoundMethod=method;reboundMethod.__reactBoundArguments=args;return reboundMethod}}return boundMethod}function bindAutoBindMethods(component){var pairs=component.__reactAutoBindPairs;for(var i=0;i<pairs.length;i+=2){var autoBindKey=pairs[i];var method=pairs[i+1];component[autoBindKey]=bindAutoBindMethod(component,method)}}var IsMountedPreMixin={componentDidMount:function(){this.__isMounted=true}};var IsMountedPostMixin={componentWillUnmount:function(){this.__isMounted=false}};var ReactClassMixin={replaceState:function(newState,callback){this.updater.enqueueReplaceState(this,newState,callback)},isMounted:function(){if(process.env.NODE_ENV!=="production"){warning(this.__didWarnIsMounted,"%s: isMounted is deprecated. Instead, make sure to clean up "+"subscriptions and pending requests in componentWillUnmount to "+"prevent memory leaks.",this.constructor&&this.constructor.displayName||this.name||"Component");this.__didWarnIsMounted=true}return!!this.__isMounted}};var ReactClassComponent=function(){};_assign(ReactClassComponent.prototype,ReactComponent.prototype,ReactClassMixin);function createClass(spec){var Constructor=identity(function(props,context,updater){if(process.env.NODE_ENV!=="production"){warning(this instanceof Constructor,"Something is calling a React component directly. Use a factory or "+"JSX instead. See: https://fb.me/react-legacyfactory")}if(this.__reactAutoBindPairs.length){bindAutoBindMethods(this)}this.props=props;this.context=context;this.refs=emptyObject;this.updater=updater||ReactNoopUpdateQueue;this.state=null;var initialState=this.getInitialState?this.getInitialState():null;if(process.env.NODE_ENV!=="production"){if(initialState===undefined&&this.getInitialState._isMockFunction){initialState=null}}_invariant(typeof initialState==="object"&&!Array.isArray(initialState),"%s.getInitialState(): must return an object or null",Constructor.displayName||"ReactCompositeComponent");this.state=initialState});Constructor.prototype=new ReactClassComponent;Constructor.prototype.constructor=Constructor;Constructor.prototype.__reactAutoBindPairs=[];injectedMixins.forEach(mixSpecIntoComponent.bind(null,Constructor));mixSpecIntoComponent(Constructor,IsMountedPreMixin);mixSpecIntoComponent(Constructor,spec);mixSpecIntoComponent(Constructor,IsMountedPostMixin);if(Constructor.getDefaultProps){Constructor.defaultProps=Constructor.getDefaultProps()}if(process.env.NODE_ENV!=="production"){if(Constructor.getDefaultProps){Constructor.getDefaultProps.isReactClassApproved={}}if(Constructor.prototype.getInitialState){Constructor.prototype.getInitialState.isReactClassApproved={}}}_invariant(Constructor.prototype.render,"createClass(...): Class specification must implement a `render` method.");if(process.env.NODE_ENV!=="production"){warning(!Constructor.prototype.componentShouldUpdate,"%s has a method called "+"componentShouldUpdate(). Did you mean shouldComponentUpdate()? "+"The name is phrased as a question because the function is "+"expected to return a value.",spec.displayName||"A component");warning(!Constructor.prototype.componentWillRecieveProps,"%s has a method called "+"componentWillRecieveProps(). Did you mean componentWillReceiveProps()?",spec.displayName||"A component")}for(var methodName in ReactClassInterface){if(!Constructor.prototype[methodName]){Constructor.prototype[methodName]=null}}return Constructor}return createClass}module.exports=factory}).call(this,require("_process"))},{_process:184,"fbjs/lib/emptyObject":11,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"object-assign":26}],3:[function(require,module,exports){(function(process){"use strict";var emptyFunction=require("./emptyFunction");var EventListener={listen:function listen(target,eventType,callback){if(target.addEventListener){target.addEventListener(eventType,callback,false);return{remove:function remove(){target.removeEventListener(eventType,callback,false)}}}else if(target.attachEvent){target.attachEvent("on"+eventType,callback);return{remove:function remove(){target.detachEvent("on"+eventType,callback)}}}},capture:function capture(target,eventType,callback){if(target.addEventListener){target.addEventListener(eventType,callback,true);return{remove:function remove(){target.removeEventListener(eventType,callback,true)}}}else{if(process.env.NODE_ENV!=="production"){console.error("Attempted to listen to events during the capture phase on a "+"browser that does not support the capture phase. Your application "+"will not receive some events.")}return{remove:emptyFunction}}},registerDefault:function registerDefault(){}};module.exports=EventListener}).call(this,require("_process"))},{"./emptyFunction":10,_process:184}],4:[function(require,module,exports){"use strict";var canUseDOM=!!(typeof window!=="undefined"&&window.document&&window.document.createElement);var ExecutionEnvironment={canUseDOM:canUseDOM,canUseWorkers:typeof Worker!=="undefined",canUseEventListeners:canUseDOM&&!!(window.addEventListener||window.attachEvent),canUseViewport:canUseDOM&&!!window.screen,isInWorker:!canUseDOM};module.exports=ExecutionEnvironment},{}],5:[function(require,module,exports){"use strict";var _hyphenPattern=/-(.)/g;function camelize(string){return string.replace(_hyphenPattern,function(_,character){return character.toUpperCase()})}module.exports=camelize},{}],6:[function(require,module,exports){"use strict";var camelize=require("./camelize");var msPattern=/^-ms-/;function camelizeStyleName(string){return camelize(string.replace(msPattern,"ms-"))}module.exports=camelizeStyleName},{"./camelize":5}],7:[function(require,module,exports){"use strict";var isTextNode=require("./isTextNode");function containsNode(outerNode,innerNode){if(!outerNode||!innerNode){return false}else if(outerNode===innerNode){return true}else if(isTextNode(outerNode)){return false}else if(isTextNode(innerNode)){return containsNode(outerNode,innerNode.parentNode)}else if("contains"in outerNode){return outerNode.contains(innerNode)}else if(outerNode.compareDocumentPosition){return!!(outerNode.compareDocumentPosition(innerNode)&16)}else{return false}}module.exports=containsNode},{"./isTextNode":20}],8:[function(require,module,exports){(function(process){"use strict";var invariant=require("./invariant");function toArray(obj){var length=obj.length;!(!Array.isArray(obj)&&(typeof obj==="object"||typeof obj==="function"))?process.env.NODE_ENV!=="production"?invariant(false,"toArray: Array-like object expected"):invariant(false):void 0;!(typeof length==="number")?process.env.NODE_ENV!=="production"?invariant(false,"toArray: Object needs a length property"):invariant(false):void 0;!(length===0||length-1 in obj)?process.env.NODE_ENV!=="production"?invariant(false,"toArray: Object should have keys for indices"):invariant(false):void 0;!(typeof obj.callee!=="function")?process.env.NODE_ENV!=="production"?invariant(false,"toArray: Object can't be `arguments`. Use rest params "+"(function(...args) {}) or Array.from() instead."):invariant(false):void 0;if(obj.hasOwnProperty){try{return Array.prototype.slice.call(obj)}catch(e){}}var ret=Array(length);for(var ii=0;ii<length;ii++){ret[ii]=obj[ii]}return ret}function hasArrayNature(obj){return!!obj&&(typeof obj=="object"||typeof obj=="function")&&"length"in obj&&!("setInterval"in obj)&&typeof obj.nodeType!="number"&&(Array.isArray(obj)||"callee"in obj||"item"in obj)}function createArrayFromMixed(obj){if(!hasArrayNature(obj)){return[obj]}else if(Array.isArray(obj)){return obj.slice()}else{return toArray(obj)}}module.exports=createArrayFromMixed}).call(this,require("_process"))},{"./invariant":18,_process:184}],9:[function(require,module,exports){(function(process){"use strict";var ExecutionEnvironment=require("./ExecutionEnvironment");var createArrayFromMixed=require("./createArrayFromMixed");var getMarkupWrap=require("./getMarkupWrap");var invariant=require("./invariant");var dummyNode=ExecutionEnvironment.canUseDOM?document.createElement("div"):null;var nodeNamePattern=/^\s*<(\w+)/;function getNodeName(markup){var nodeNameMatch=markup.match(nodeNamePattern);return nodeNameMatch&&nodeNameMatch[1].toLowerCase()}function createNodesFromMarkup(markup,handleScript){var node=dummyNode;!!!dummyNode?process.env.NODE_ENV!=="production"?invariant(false,"createNodesFromMarkup dummy not initialized"):invariant(false):void 0;var nodeName=getNodeName(markup);var wrap=nodeName&&getMarkupWrap(nodeName);if(wrap){node.innerHTML=wrap[1]+markup+wrap[2];var wrapDepth=wrap[0];while(wrapDepth--){node=node.lastChild}}else{node.innerHTML=markup}var scripts=node.getElementsByTagName("script");if(scripts.length){!handleScript?process.env.NODE_ENV!=="production"?invariant(false,"createNodesFromMarkup(...): Unexpected <script> element rendered."):invariant(false):void 0;createArrayFromMixed(scripts).forEach(handleScript)}var nodes=Array.from(node.childNodes);while(node.lastChild){node.removeChild(node.lastChild)}return nodes}module.exports=createNodesFromMarkup}).call(this,require("_process"))},{"./ExecutionEnvironment":4,"./createArrayFromMixed":8,"./getMarkupWrap":14,"./invariant":18,_process:184}],10:[function(require,module,exports){"use strict";function makeEmptyFunction(arg){return function(){return arg}}var emptyFunction=function emptyFunction(){};emptyFunction.thatReturns=makeEmptyFunction;emptyFunction.thatReturnsFalse=makeEmptyFunction(false);emptyFunction.thatReturnsTrue=makeEmptyFunction(true);emptyFunction.thatReturnsNull=makeEmptyFunction(null);emptyFunction.thatReturnsThis=function(){return this};emptyFunction.thatReturnsArgument=function(arg){return arg};module.exports=emptyFunction},{}],11:[function(require,module,exports){(function(process){"use strict";var emptyObject={};if(process.env.NODE_ENV!=="production"){Object.freeze(emptyObject)}module.exports=emptyObject}).call(this,require("_process"))},{_process:184}],12:[function(require,module,exports){"use strict";function focusNode(node){try{node.focus()}catch(e){}}module.exports=focusNode},{}],13:[function(require,module,exports){"use strict";function getActiveElement(doc){doc=doc||(typeof document!=="undefined"?document:undefined);if(typeof doc==="undefined"){return null}try{return doc.activeElement||doc.body}catch(e){return doc.body}}module.exports=getActiveElement},{}],14:[function(require,module,exports){(function(process){"use strict";var ExecutionEnvironment=require("./ExecutionEnvironment");var invariant=require("./invariant");var dummyNode=ExecutionEnvironment.canUseDOM?document.createElement("div"):null;var shouldWrap={};var selectWrap=[1,'<select multiple="true">',"</select>"];var tableWrap=[1,"<table>","</table>"];var trWrap=[3,"<table><tbody><tr>","</tr></tbody></table>"];var svgWrap=[1,'<svg xmlns="http://www.w3.org/2000/svg">',"</svg>"];var markupWrap={"*":[1,"?<div>","</div>"],area:[1,"<map>","</map>"],col:[2,"<table><tbody></tbody><colgroup>","</colgroup></table>"],legend:[1,"<fieldset>","</fieldset>"],param:[1,"<object>","</object>"],tr:[2,"<table><tbody>","</tbody></table>"],optgroup:selectWrap,option:selectWrap,caption:tableWrap,colgroup:tableWrap,tbody:tableWrap,tfoot:tableWrap,thead:tableWrap,td:trWrap,th:trWrap};var svgElements=["circle","clipPath","defs","ellipse","g","image","line","linearGradient","mask","path","pattern","polygon","polyline","radialGradient","rect","stop","text","tspan"];svgElements.forEach(function(nodeName){markupWrap[nodeName]=svgWrap;shouldWrap[nodeName]=true});function getMarkupWrap(nodeName){!!!dummyNode?process.env.NODE_ENV!=="production"?invariant(false,"Markup wrapping node not initialized"):invariant(false):void 0;if(!markupWrap.hasOwnProperty(nodeName)){nodeName="*"}if(!shouldWrap.hasOwnProperty(nodeName)){if(nodeName==="*"){dummyNode.innerHTML="<link />"}else{dummyNode.innerHTML="<"+nodeName+"></"+nodeName+">"}shouldWrap[nodeName]=!dummyNode.firstChild}return shouldWrap[nodeName]?markupWrap[nodeName]:null}module.exports=getMarkupWrap}).call(this,require("_process"))},{"./ExecutionEnvironment":4,"./invariant":18,_process:184}],15:[function(require,module,exports){"use strict";function getUnboundedScrollPosition(scrollable){if(scrollable.Window&&scrollable instanceof scrollable.Window){return{x:scrollable.pageXOffset||scrollable.document.documentElement.scrollLeft,y:scrollable.pageYOffset||scrollable.document.documentElement.scrollTop}}return{x:scrollable.scrollLeft,y:scrollable.scrollTop}}module.exports=getUnboundedScrollPosition},{}],16:[function(require,module,exports){"use strict";var _uppercasePattern=/([A-Z])/g;function hyphenate(string){return string.replace(_uppercasePattern,"-$1").toLowerCase()}module.exports=hyphenate},{}],17:[function(require,module,exports){"use strict";var hyphenate=require("./hyphenate");var msPattern=/^ms-/;function hyphenateStyleName(string){return hyphenate(string).replace(msPattern,"-ms-")}module.exports=hyphenateStyleName},{"./hyphenate":16}],18:[function(require,module,exports){(function(process){"use strict";var validateFormat=function validateFormat(format){};if(process.env.NODE_ENV!=="production"){validateFormat=function validateFormat(format){if(format===undefined){throw new Error("invariant requires an error message argument")}}}function invariant(condition,format,a,b,c,d,e,f){validateFormat(format);if(!condition){var error;if(format===undefined){error=new Error("Minified exception occurred; use the non-minified dev environment "+"for the full error message and additional helpful warnings.")}else{var args=[a,b,c,d,e,f];var argIndex=0;error=new Error(format.replace(/%s/g,function(){return args[argIndex++]}));error.name="Invariant Violation"}error.framesToPop=1;throw error}}module.exports=invariant}).call(this,require("_process"))},{_process:184}],19:[function(require,module,exports){"use strict";function isNode(object){var doc=object?object.ownerDocument||object:document;var defaultView=doc.defaultView||window;return!!(object&&(typeof defaultView.Node==="function"?object instanceof defaultView.Node:typeof object==="object"&&typeof object.nodeType==="number"&&typeof object.nodeName==="string"))}module.exports=isNode},{}],20:[function(require,module,exports){"use strict";var isNode=require("./isNode");function isTextNode(object){return isNode(object)&&object.nodeType==3}module.exports=isTextNode},{"./isNode":19}],21:[function(require,module,exports){"use strict";function memoizeStringOnly(callback){var cache={};return function(string){if(!cache.hasOwnProperty(string)){cache[string]=callback.call(this,string)}return cache[string]}}module.exports=memoizeStringOnly},{}],22:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("./ExecutionEnvironment");var performance;if(ExecutionEnvironment.canUseDOM){performance=window.performance||window.msPerformance||window.webkitPerformance}module.exports=performance||{}},{"./ExecutionEnvironment":4}],23:[function(require,module,exports){"use strict";var performance=require("./performance");var performanceNow;if(performance.now){performanceNow=function performanceNow(){return performance.now()}}else{performanceNow=function performanceNow(){return Date.now()}}module.exports=performanceNow},{"./performance":22}],24:[function(require,module,exports){"use strict";var hasOwnProperty=Object.prototype.hasOwnProperty;function is(x,y){if(x===y){return x!==0||y!==0||1/x===1/y}else{return x!==x&&y!==y}}function shallowEqual(objA,objB){if(is(objA,objB)){return true}if(typeof objA!=="object"||objA===null||typeof objB!=="object"||objB===null){return false}var keysA=Object.keys(objA);var keysB=Object.keys(objB);if(keysA.length!==keysB.length){return false}for(var i=0;i<keysA.length;i++){if(!hasOwnProperty.call(objB,keysA[i])||!is(objA[keysA[i]],objB[keysA[i]])){return false}}return true}module.exports=shallowEqual},{}],25:[function(require,module,exports){(function(process){"use strict";var emptyFunction=require("./emptyFunction");var warning=emptyFunction;if(process.env.NODE_ENV!=="production"){var printWarning=function printWarning(format){for(var _len=arguments.length,args=Array(_len>1?_len-1:0),_key=1;_key<_len;_key++){args[_key-1]=arguments[_key]}var argIndex=0;var message="Warning: "+format.replace(/%s/g,function(){return args[argIndex++]});if(typeof console!=="undefined"){console.error(message)}try{throw new Error(message)}catch(x){}};warning=function warning(condition,format){if(format===undefined){throw new Error("`warning(condition, format, ...args)` requires a warning "+"message argument")}if(format.indexOf("Failed Composite propType: ")===0){return}if(!condition){for(var _len2=arguments.length,args=Array(_len2>2?_len2-2:0),_key2=2;_key2<_len2;_key2++){args[_key2-2]=arguments[_key2]}printWarning.apply(undefined,[format].concat(args))}}}module.exports=warning}).call(this,require("_process"))},{"./emptyFunction":10,_process:184}],26:[function(require,module,exports){"use strict";var getOwnPropertySymbols=Object.getOwnPropertySymbols;var hasOwnProperty=Object.prototype.hasOwnProperty;var propIsEnumerable=Object.prototype.propertyIsEnumerable;function toObject(val){if(val===null||val===undefined){throw new TypeError("Object.assign cannot be called with null or undefined")}return Object(val)}function shouldUseNative(){try{if(!Object.assign){return false}var test1=new String("abc");test1[5]="de";if(Object.getOwnPropertyNames(test1)[0]==="5"){return false}var test2={};for(var i=0;i<10;i++){test2["_"+String.fromCharCode(i)]=i}var order2=Object.getOwnPropertyNames(test2).map(function(n){return test2[n]});if(order2.join("")!=="0123456789"){return false}var test3={};"abcdefghijklmnopqrst".split("").forEach(function(letter){test3[letter]=letter});if(Object.keys(Object.assign({},test3)).join("")!=="abcdefghijklmnopqrst"){return false}return true}catch(err){return false}}module.exports=shouldUseNative()?Object.assign:function(target,source){var from;var to=toObject(target);var symbols;for(var s=1;s<arguments.length;s++){from=Object(arguments[s]);for(var key in from){if(hasOwnProperty.call(from,key)){to[key]=from[key]}}if(getOwnPropertySymbols){symbols=getOwnPropertySymbols(from);for(var i=0;i<symbols.length;i++){if(propIsEnumerable.call(from,symbols[i])){to[symbols[i]]=from[symbols[i]]}}}}return to}},{}],27:[function(require,module,exports){(function(process){"use strict";if(process.env.NODE_ENV!=="production"){var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ReactPropTypesSecret=require("./lib/ReactPropTypesSecret");var loggedTypeFailures={}}function checkPropTypes(typeSpecs,values,location,componentName,getStack){if(process.env.NODE_ENV!=="production"){for(var typeSpecName in typeSpecs){if(typeSpecs.hasOwnProperty(typeSpecName)){var error;try{invariant(typeof typeSpecs[typeSpecName]==="function","%s: %s type `%s` is invalid; it must be a function, usually from "+"React.PropTypes.",componentName||"React class",location,typeSpecName);error=typeSpecs[typeSpecName](values,typeSpecName,componentName,location,null,ReactPropTypesSecret)}catch(ex){error=ex}warning(!error||error instanceof Error,"%s: type specification of %s `%s` is invalid; the type checker "+"function must return `null` or an `Error` but returned a %s. "+"You may have forgotten to pass an argument to the type checker "+"creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and "+"shape all require an argument).",componentName||"React class",location,typeSpecName,typeof error);if(error instanceof Error&&!(error.message in loggedTypeFailures)){loggedTypeFailures[error.message]=true;var stack=getStack?getStack():"";warning(false,"Failed %s type: %s%s",location,error.message,stack!=null?stack:"")}}}}}module.exports=checkPropTypes}).call(this,require("_process"))},{"./lib/ReactPropTypesSecret":30,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],28:[function(require,module,exports){"use strict";var factory=require("./factoryWithTypeCheckers");module.exports=function(isValidElement){var throwOnDirectAccess=false;return factory(isValidElement,throwOnDirectAccess)}},{"./factoryWithTypeCheckers":29}],29:[function(require,module,exports){(function(process){"use strict";var emptyFunction=require("fbjs/lib/emptyFunction");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ReactPropTypesSecret=require("./lib/ReactPropTypesSecret");var checkPropTypes=require("./checkPropTypes");module.exports=function(isValidElement,throwOnDirectAccess){var ITERATOR_SYMBOL=typeof Symbol==="function"&&Symbol.iterator;var FAUX_ITERATOR_SYMBOL="@@iterator";function getIteratorFn(maybeIterable){var iteratorFn=maybeIterable&&(ITERATOR_SYMBOL&&maybeIterable[ITERATOR_SYMBOL]||maybeIterable[FAUX_ITERATOR_SYMBOL]);if(typeof iteratorFn==="function"){return iteratorFn}}var ANONYMOUS="<<anonymous>>";var ReactPropTypes={array:createPrimitiveTypeChecker("array"),bool:createPrimitiveTypeChecker("boolean"),func:createPrimitiveTypeChecker("function"),number:createPrimitiveTypeChecker("number"),object:createPrimitiveTypeChecker("object"),string:createPrimitiveTypeChecker("string"),symbol:createPrimitiveTypeChecker("symbol"),any:createAnyTypeChecker(),arrayOf:createArrayOfTypeChecker,element:createElementTypeChecker(),instanceOf:createInstanceTypeChecker,node:createNodeChecker(),objectOf:createObjectOfTypeChecker,oneOf:createEnumTypeChecker,oneOfType:createUnionTypeChecker,shape:createShapeTypeChecker};function is(x,y){if(x===y){return x!==0||1/x===1/y}else{return x!==x&&y!==y}}function PropTypeError(message){this.message=message;this.stack=""}PropTypeError.prototype=Error.prototype;function createChainableTypeChecker(validate){if(process.env.NODE_ENV!=="production"){var manualPropTypeCallCache={};var manualPropTypeWarningCount=0}function checkType(isRequired,props,propName,componentName,location,propFullName,secret){componentName=componentName||ANONYMOUS;propFullName=propFullName||propName;if(secret!==ReactPropTypesSecret){if(throwOnDirectAccess){invariant(false,"Calling PropTypes validators directly is not supported by the `prop-types` package. "+"Use `PropTypes.checkPropTypes()` to call them. "+"Read more at http://fb.me/use-check-prop-types")}else if(process.env.NODE_ENV!=="production"&&typeof console!=="undefined"){var cacheKey=componentName+":"+propName;if(!manualPropTypeCallCache[cacheKey]&&manualPropTypeWarningCount<3){warning(false,"You are manually calling a React.PropTypes validation "+"function for the `%s` prop on `%s`. This is deprecated "+"and will throw in the standalone `prop-types` package. "+"You may be seeing this warning due to a third-party PropTypes "+"library. See https://fb.me/react-warning-dont-call-proptypes "+"for details.",propFullName,componentName);manualPropTypeCallCache[cacheKey]=true;manualPropTypeWarningCount++}}}if(props[propName]==null){if(isRequired){if(props[propName]===null){return new PropTypeError("The "+location+" `"+propFullName+"` is marked as required "+("in `"+componentName+"`, but its value is `null`."))}return new PropTypeError("The "+location+" `"+propFullName+"` is marked as required in "+("`"+componentName+"`, but its value is `undefined`."))}return null}else{return validate(props,propName,componentName,location,propFullName)}}var chainedCheckType=checkType.bind(null,false);chainedCheckType.isRequired=checkType.bind(null,true);return chainedCheckType}function createPrimitiveTypeChecker(expectedType){function validate(props,propName,componentName,location,propFullName,secret){var propValue=props[propName];var propType=getPropType(propValue);if(propType!==expectedType){var preciseType=getPreciseType(propValue);return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type "+("`"+preciseType+"` supplied to `"+componentName+"`, expected ")+("`"+expectedType+"`."))}return null}return createChainableTypeChecker(validate)}function createAnyTypeChecker(){return createChainableTypeChecker(emptyFunction.thatReturnsNull)}function createArrayOfTypeChecker(typeChecker){function validate(props,propName,componentName,location,propFullName){if(typeof typeChecker!=="function"){return new PropTypeError("Property `"+propFullName+"` of component `"+componentName+"` has invalid PropType notation inside arrayOf.")}var propValue=props[propName];if(!Array.isArray(propValue)){var propType=getPropType(propValue);return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type "+("`"+propType+"` supplied to `"+componentName+"`, expected an array."))}for(var i=0;i<propValue.length;i++){var error=typeChecker(propValue,i,componentName,location,propFullName+"["+i+"]",ReactPropTypesSecret);if(error instanceof Error){return error}}return null}return createChainableTypeChecker(validate)}function createElementTypeChecker(){function validate(props,propName,componentName,location,propFullName){var propValue=props[propName];if(!isValidElement(propValue)){var propType=getPropType(propValue);return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type "+("`"+propType+"` supplied to `"+componentName+"`, expected a single ReactElement."))}return null}return createChainableTypeChecker(validate)}function createInstanceTypeChecker(expectedClass){function validate(props,propName,componentName,location,propFullName){if(!(props[propName]instanceof expectedClass)){var expectedClassName=expectedClass.name||ANONYMOUS;var actualClassName=getClassName(props[propName]);return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type "+("`"+actualClassName+"` supplied to `"+componentName+"`, expected ")+("instance of `"+expectedClassName+"`."))}return null}return createChainableTypeChecker(validate)}function createEnumTypeChecker(expectedValues){if(!Array.isArray(expectedValues)){process.env.NODE_ENV!=="production"?warning(false,"Invalid argument supplied to oneOf, expected an instance of array."):void 0;return emptyFunction.thatReturnsNull}function validate(props,propName,componentName,location,propFullName){var propValue=props[propName];for(var i=0;i<expectedValues.length;i++){if(is(propValue,expectedValues[i])){return null}}var valuesString=JSON.stringify(expectedValues);return new PropTypeError("Invalid "+location+" `"+propFullName+"` of value `"+propValue+"` "+("supplied to `"+componentName+"`, expected one of "+valuesString+"."))}return createChainableTypeChecker(validate)}function createObjectOfTypeChecker(typeChecker){function validate(props,propName,componentName,location,propFullName){if(typeof typeChecker!=="function"){return new PropTypeError("Property `"+propFullName+"` of component `"+componentName+"` has invalid PropType notation inside objectOf.")}var propValue=props[propName];var propType=getPropType(propValue);if(propType!=="object"){return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type "+("`"+propType+"` supplied to `"+componentName+"`, expected an object."))}for(var key in propValue){if(propValue.hasOwnProperty(key)){var error=typeChecker(propValue,key,componentName,location,propFullName+"."+key,ReactPropTypesSecret);if(error instanceof Error){return error}}}return null}return createChainableTypeChecker(validate)}function createUnionTypeChecker(arrayOfTypeCheckers){if(!Array.isArray(arrayOfTypeCheckers)){process.env.NODE_ENV!=="production"?warning(false,"Invalid argument supplied to oneOfType, expected an instance of array."):void 0;return emptyFunction.thatReturnsNull}for(var i=0;i<arrayOfTypeCheckers.length;i++){var checker=arrayOfTypeCheckers[i];if(typeof checker!=="function"){warning(false,"Invalid argument supplid to oneOfType. Expected an array of check functions, but "+"received %s at index %s.",getPostfixForTypeWarning(checker),i);return emptyFunction.thatReturnsNull}}function validate(props,propName,componentName,location,propFullName){for(var i=0;i<arrayOfTypeCheckers.length;i++){var checker=arrayOfTypeCheckers[i];if(checker(props,propName,componentName,location,propFullName,ReactPropTypesSecret)==null){return null}}return new PropTypeError("Invalid "+location+" `"+propFullName+"` supplied to "+("`"+componentName+"`."))}return createChainableTypeChecker(validate)}function createNodeChecker(){function validate(props,propName,componentName,location,propFullName){if(!isNode(props[propName])){return new PropTypeError("Invalid "+location+" `"+propFullName+"` supplied to "+("`"+componentName+"`, expected a ReactNode."))}return null}return createChainableTypeChecker(validate)}function createShapeTypeChecker(shapeTypes){function validate(props,propName,componentName,location,propFullName){var propValue=props[propName];var propType=getPropType(propValue);if(propType!=="object"){return new PropTypeError("Invalid "+location+" `"+propFullName+"` of type `"+propType+"` "+("supplied to `"+componentName+"`, expected `object`."))}for(var key in shapeTypes){var checker=shapeTypes[key];if(!checker){continue}var error=checker(propValue,key,componentName,location,propFullName+"."+key,ReactPropTypesSecret);if(error){return error}}return null}return createChainableTypeChecker(validate)}function isNode(propValue){switch(typeof propValue){case"number":case"string":case"undefined":return true;case"boolean":return!propValue;case"object":if(Array.isArray(propValue)){return propValue.every(isNode)}if(propValue===null||isValidElement(propValue)){return true}var iteratorFn=getIteratorFn(propValue);if(iteratorFn){var iterator=iteratorFn.call(propValue);var step;if(iteratorFn!==propValue.entries){while(!(step=iterator.next()).done){if(!isNode(step.value)){return false}}}else{while(!(step=iterator.next()).done){var entry=step.value;if(entry){if(!isNode(entry[1])){return false}}}}}else{return false}return true;default:return false}}function isSymbol(propType,propValue){if(propType==="symbol"){return true}if(propValue["@@toStringTag"]==="Symbol"){return true}if(typeof Symbol==="function"&&propValue instanceof Symbol){return true}return false}function getPropType(propValue){var propType=typeof propValue;if(Array.isArray(propValue)){return"array"}if(propValue instanceof RegExp){return"object"}if(isSymbol(propType,propValue)){return"symbol"}return propType}function getPreciseType(propValue){if(typeof propValue==="undefined"||propValue===null){return""+propValue}var propType=getPropType(propValue);if(propType==="object"){if(propValue instanceof Date){return"date"}else if(propValue instanceof RegExp){return"regexp"}}return propType}function getPostfixForTypeWarning(value){var type=getPreciseType(value);switch(type){case"array":case"object":return"an "+type;case"boolean":case"date":case"regexp":return"a "+type;default:return type}}function getClassName(propValue){if(!propValue.constructor||!propValue.constructor.name){return ANONYMOUS}return propValue.constructor.name}ReactPropTypes.checkPropTypes=checkPropTypes;ReactPropTypes.PropTypes=ReactPropTypes;return ReactPropTypes}}).call(this,require("_process"))},{"./checkPropTypes":27,"./lib/ReactPropTypesSecret":30,_process:184,"fbjs/lib/emptyFunction":10,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],30:[function(require,module,exports){"use strict";var ReactPropTypesSecret="SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED";module.exports=ReactPropTypesSecret},{}],31:[function(require,module,exports){"use strict";module.exports=require("./lib/ReactDOM")},{"./lib/ReactDOM":61}],32:[function(require,module,exports){"use strict";var ARIADOMPropertyConfig={Properties:{"aria-current":0,"aria-details":0,"aria-disabled":0,"aria-hidden":0,"aria-invalid":0,"aria-keyshortcuts":0,"aria-label":0,"aria-roledescription":0,"aria-autocomplete":0,"aria-checked":0,"aria-expanded":0,"aria-haspopup":0,"aria-level":0,"aria-modal":0,"aria-multiline":0,"aria-multiselectable":0,"aria-orientation":0,"aria-placeholder":0,"aria-pressed":0,"aria-readonly":0,"aria-required":0,"aria-selected":0,"aria-sort":0,"aria-valuemax":0,"aria-valuemin":0,"aria-valuenow":0,"aria-valuetext":0,"aria-atomic":0,"aria-busy":0,"aria-live":0,"aria-relevant":0,"aria-dropeffect":0,"aria-grabbed":0,"aria-activedescendant":0,"aria-colcount":0,"aria-colindex":0,"aria-colspan":0,"aria-controls":0,"aria-describedby":0,"aria-errormessage":0,"aria-flowto":0,"aria-labelledby":0,"aria-owns":0,"aria-posinset":0,"aria-rowcount":0,"aria-rowindex":0,"aria-rowspan":0,"aria-setsize":0},DOMAttributeNames:{},DOMPropertyNames:{}};module.exports=ARIADOMPropertyConfig},{}],33:[function(require,module,exports){"use strict";var ReactDOMComponentTree=require("./ReactDOMComponentTree");var focusNode=require("fbjs/lib/focusNode");var AutoFocusUtils={focusDOMComponent:function(){focusNode(ReactDOMComponentTree.getNodeFromInstance(this))}};module.exports=AutoFocusUtils},{"./ReactDOMComponentTree":64,"fbjs/lib/focusNode":12}],34:[function(require,module,exports){"use strict";var EventPropagators=require("./EventPropagators");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var FallbackCompositionState=require("./FallbackCompositionState");var SyntheticCompositionEvent=require("./SyntheticCompositionEvent");var SyntheticInputEvent=require("./SyntheticInputEvent");var END_KEYCODES=[9,13,27,32];var START_KEYCODE=229;var canUseCompositionEvent=ExecutionEnvironment.canUseDOM&&"CompositionEvent"in window;var documentMode=null;if(ExecutionEnvironment.canUseDOM&&"documentMode"in document){documentMode=document.documentMode}var canUseTextInputEvent=ExecutionEnvironment.canUseDOM&&"TextEvent"in window&&!documentMode&&!isPresto();var useFallbackCompositionData=ExecutionEnvironment.canUseDOM&&(!canUseCompositionEvent||documentMode&&documentMode>8&&documentMode<=11);function isPresto(){var opera=window.opera;return typeof opera==="object"&&typeof opera.version==="function"&&parseInt(opera.version(),10)<=12}var SPACEBAR_CODE=32;var SPACEBAR_CHAR=String.fromCharCode(SPACEBAR_CODE);var eventTypes={beforeInput:{phasedRegistrationNames:{bubbled:"onBeforeInput",captured:"onBeforeInputCapture"},dependencies:["topCompositionEnd","topKeyPress","topTextInput","topPaste"]},compositionEnd:{phasedRegistrationNames:{bubbled:"onCompositionEnd",captured:"onCompositionEndCapture"},dependencies:["topBlur","topCompositionEnd","topKeyDown","topKeyPress","topKeyUp","topMouseDown"]},compositionStart:{phasedRegistrationNames:{bubbled:"onCompositionStart",captured:"onCompositionStartCapture"},dependencies:["topBlur","topCompositionStart","topKeyDown","topKeyPress","topKeyUp","topMouseDown"]},compositionUpdate:{phasedRegistrationNames:{bubbled:"onCompositionUpdate",captured:"onCompositionUpdateCapture"},dependencies:["topBlur","topCompositionUpdate","topKeyDown","topKeyPress","topKeyUp","topMouseDown"]}};var hasSpaceKeypress=false;function isKeypressCommand(nativeEvent){return(nativeEvent.ctrlKey||nativeEvent.altKey||nativeEvent.metaKey)&&!(nativeEvent.ctrlKey&&nativeEvent.altKey)}function getCompositionEventType(topLevelType){switch(topLevelType){case"topCompositionStart":return eventTypes.compositionStart;case"topCompositionEnd":return eventTypes.compositionEnd;case"topCompositionUpdate":return eventTypes.compositionUpdate}}function isFallbackCompositionStart(topLevelType,nativeEvent){return topLevelType==="topKeyDown"&&nativeEvent.keyCode===START_KEYCODE}function isFallbackCompositionEnd(topLevelType,nativeEvent){switch(topLevelType){case"topKeyUp":return END_KEYCODES.indexOf(nativeEvent.keyCode)!==-1;case"topKeyDown":return nativeEvent.keyCode!==START_KEYCODE;case"topKeyPress":case"topMouseDown":case"topBlur":return true;default:return false}}function getDataFromCustomEvent(nativeEvent){var detail=nativeEvent.detail;if(typeof detail==="object"&&"data"in detail){return detail.data}return null}var currentComposition=null;function extractCompositionEvent(topLevelType,targetInst,nativeEvent,nativeEventTarget){var eventType;var fallbackData;if(canUseCompositionEvent){eventType=getCompositionEventType(topLevelType)}else if(!currentComposition){if(isFallbackCompositionStart(topLevelType,nativeEvent)){eventType=eventTypes.compositionStart}}else if(isFallbackCompositionEnd(topLevelType,nativeEvent)){eventType=eventTypes.compositionEnd}if(!eventType){return null}if(useFallbackCompositionData){if(!currentComposition&&eventType===eventTypes.compositionStart){currentComposition=FallbackCompositionState.getPooled(nativeEventTarget)}else if(eventType===eventTypes.compositionEnd){if(currentComposition){fallbackData=currentComposition.getData()}}}var event=SyntheticCompositionEvent.getPooled(eventType,targetInst,nativeEvent,nativeEventTarget);if(fallbackData){event.data=fallbackData}else{var customData=getDataFromCustomEvent(nativeEvent);if(customData!==null){event.data=customData}}EventPropagators.accumulateTwoPhaseDispatches(event);return event}function getNativeBeforeInputChars(topLevelType,nativeEvent){switch(topLevelType){case"topCompositionEnd":return getDataFromCustomEvent(nativeEvent);case"topKeyPress":var which=nativeEvent.which;if(which!==SPACEBAR_CODE){return null}hasSpaceKeypress=true;return SPACEBAR_CHAR;case"topTextInput":var chars=nativeEvent.data;if(chars===SPACEBAR_CHAR&&hasSpaceKeypress){return null}return chars;default:return null}}function getFallbackBeforeInputChars(topLevelType,nativeEvent){if(currentComposition){if(topLevelType==="topCompositionEnd"||!canUseCompositionEvent&&isFallbackCompositionEnd(topLevelType,nativeEvent)){var chars=currentComposition.getData();FallbackCompositionState.release(currentComposition);currentComposition=null;return chars}return null}switch(topLevelType){case"topPaste":return null;case"topKeyPress":if(nativeEvent.which&&!isKeypressCommand(nativeEvent)){return String.fromCharCode(nativeEvent.which)}return null;case"topCompositionEnd":return useFallbackCompositionData?null:nativeEvent.data;default:return null}}function extractBeforeInputEvent(topLevelType,targetInst,nativeEvent,nativeEventTarget){var chars;if(canUseTextInputEvent){chars=getNativeBeforeInputChars(topLevelType,nativeEvent)}else{chars=getFallbackBeforeInputChars(topLevelType,nativeEvent)}if(!chars){return null}var event=SyntheticInputEvent.getPooled(eventTypes.beforeInput,targetInst,nativeEvent,nativeEventTarget);event.data=chars;EventPropagators.accumulateTwoPhaseDispatches(event);return event}var BeforeInputEventPlugin={eventTypes:eventTypes,extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){return[extractCompositionEvent(topLevelType,targetInst,nativeEvent,nativeEventTarget),extractBeforeInputEvent(topLevelType,targetInst,nativeEvent,nativeEventTarget)]}};module.exports=BeforeInputEventPlugin},{"./EventPropagators":50,"./FallbackCompositionState":51,"./SyntheticCompositionEvent":115,"./SyntheticInputEvent":119,"fbjs/lib/ExecutionEnvironment":4}],35:[function(require,module,exports){"use strict";var isUnitlessNumber={animationIterationCount:true,borderImageOutset:true,borderImageSlice:true,borderImageWidth:true,boxFlex:true,boxFlexGroup:true,boxOrdinalGroup:true,columnCount:true,flex:true,flexGrow:true,flexPositive:true,flexShrink:true,flexNegative:true,flexOrder:true,gridRow:true,gridRowEnd:true,gridRowSpan:true,gridRowStart:true,gridColumn:true,gridColumnEnd:true,gridColumnSpan:true,gridColumnStart:true,fontWeight:true,lineClamp:true,lineHeight:true,opacity:true,order:true,orphans:true,tabSize:true,widows:true,zIndex:true,zoom:true,fillOpacity:true,floodOpacity:true,stopOpacity:true,strokeDasharray:true,strokeDashoffset:true,strokeMiterlimit:true,strokeOpacity:true,strokeWidth:true};function prefixKey(prefix,key){return prefix+key.charAt(0).toUpperCase()+key.substring(1)}var prefixes=["Webkit","ms","Moz","O"];Object.keys(isUnitlessNumber).forEach(function(prop){prefixes.forEach(function(prefix){isUnitlessNumber[prefixKey(prefix,prop)]=isUnitlessNumber[prop]})});var shorthandPropertyExpansions={background:{backgroundAttachment:true,backgroundColor:true,backgroundImage:true,backgroundPositionX:true,backgroundPositionY:true,backgroundRepeat:true},backgroundPosition:{backgroundPositionX:true,backgroundPositionY:true},border:{borderWidth:true,borderStyle:true,borderColor:true},borderBottom:{borderBottomWidth:true,borderBottomStyle:true,borderBottomColor:true},borderLeft:{borderLeftWidth:true,borderLeftStyle:true,borderLeftColor:true},borderRight:{borderRightWidth:true,borderRightStyle:true,borderRightColor:true},borderTop:{borderTopWidth:true,borderTopStyle:true,borderTopColor:true},font:{fontStyle:true,fontVariant:true,fontWeight:true,fontSize:true,lineHeight:true,fontFamily:true},outline:{outlineWidth:true,outlineStyle:true,outlineColor:true}};var CSSProperty={isUnitlessNumber:isUnitlessNumber,shorthandPropertyExpansions:shorthandPropertyExpansions};module.exports=CSSProperty},{}],36:[function(require,module,exports){(function(process){"use strict";var CSSProperty=require("./CSSProperty");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var ReactInstrumentation=require("./ReactInstrumentation");var camelizeStyleName=require("fbjs/lib/camelizeStyleName");var dangerousStyleValue=require("./dangerousStyleValue");var hyphenateStyleName=require("fbjs/lib/hyphenateStyleName");var memoizeStringOnly=require("fbjs/lib/memoizeStringOnly");var warning=require("fbjs/lib/warning");var processStyleName=memoizeStringOnly(function(styleName){return hyphenateStyleName(styleName)});var hasShorthandPropertyBug=false;var styleFloatAccessor="cssFloat";if(ExecutionEnvironment.canUseDOM){var tempStyle=document.createElement("div").style;try{tempStyle.font=""}catch(e){hasShorthandPropertyBug=true}if(document.documentElement.style.cssFloat===undefined){styleFloatAccessor="styleFloat"}}if(process.env.NODE_ENV!=="production"){var badVendoredStyleNamePattern=/^(?:webkit|moz|o)[A-Z]/;var badStyleValueWithSemicolonPattern=/;\s*$/;var warnedStyleNames={};var warnedStyleValues={};var warnedForNaNValue=false;var warnHyphenatedStyleName=function(name,owner){if(warnedStyleNames.hasOwnProperty(name)&&warnedStyleNames[name]){return}warnedStyleNames[name]=true;process.env.NODE_ENV!=="production"?warning(false,"Unsupported style property %s. Did you mean %s?%s",name,camelizeStyleName(name),checkRenderMessage(owner)):void 0};var warnBadVendoredStyleName=function(name,owner){if(warnedStyleNames.hasOwnProperty(name)&&warnedStyleNames[name]){return}warnedStyleNames[name]=true;process.env.NODE_ENV!=="production"?warning(false,"Unsupported vendor-prefixed style property %s. Did you mean %s?%s",name,name.charAt(0).toUpperCase()+name.slice(1),checkRenderMessage(owner)):void 0};var warnStyleValueWithSemicolon=function(name,value,owner){if(warnedStyleValues.hasOwnProperty(value)&&warnedStyleValues[value]){return}warnedStyleValues[value]=true;process.env.NODE_ENV!=="production"?warning(false,"Style property values shouldn't contain a semicolon.%s "+'Try "%s: %s" instead.',checkRenderMessage(owner),name,value.replace(badStyleValueWithSemicolonPattern,"")):void 0};var warnStyleValueIsNaN=function(name,value,owner){if(warnedForNaNValue){return}warnedForNaNValue=true;process.env.NODE_ENV!=="production"?warning(false,"`NaN` is an invalid value for the `%s` css style property.%s",name,checkRenderMessage(owner)):void 0};var checkRenderMessage=function(owner){if(owner){var name=owner.getName();if(name){return" Check the render method of `"+name+"`."}}return""};var warnValidStyle=function(name,value,component){var owner;if(component){owner=component._currentElement._owner}if(name.indexOf("-")>-1){warnHyphenatedStyleName(name,owner)}else if(badVendoredStyleNamePattern.test(name)){warnBadVendoredStyleName(name,owner)}else if(badStyleValueWithSemicolonPattern.test(value)){warnStyleValueWithSemicolon(name,value,owner)}if(typeof value==="number"&&isNaN(value)){warnStyleValueIsNaN(name,value,owner)}}}var CSSPropertyOperations={createMarkupForStyles:function(styles,component){var serialized="";for(var styleName in styles){if(!styles.hasOwnProperty(styleName)){continue}var isCustomProperty=styleName.indexOf("--")===0;var styleValue=styles[styleName];if(process.env.NODE_ENV!=="production"){if(!isCustomProperty){warnValidStyle(styleName,styleValue,component)}}if(styleValue!=null){serialized+=processStyleName(styleName)+":";serialized+=dangerousStyleValue(styleName,styleValue,component,isCustomProperty)+";"}}return serialized||null},setValueForStyles:function(node,styles,component){if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:component._debugID,type:"update styles",payload:styles})}var style=node.style;for(var styleName in styles){if(!styles.hasOwnProperty(styleName)){continue}var isCustomProperty=styleName.indexOf("--")===0;if(process.env.NODE_ENV!=="production"){if(!isCustomProperty){warnValidStyle(styleName,styles[styleName],component)}}var styleValue=dangerousStyleValue(styleName,styles[styleName],component,isCustomProperty);if(styleName==="float"||styleName==="cssFloat"){styleName=styleFloatAccessor}if(isCustomProperty){style.setProperty(styleName,styleValue)}else if(styleValue){style[styleName]=styleValue}else{var expansion=hasShorthandPropertyBug&&CSSProperty.shorthandPropertyExpansions[styleName];if(expansion){for(var individualStyleName in expansion){style[individualStyleName]=""}}else{style[styleName]=""}}}}};module.exports=CSSPropertyOperations}).call(this,require("_process"))},{"./CSSProperty":35,"./ReactInstrumentation":93,"./dangerousStyleValue":132,_process:184,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/camelizeStyleName":6,"fbjs/lib/hyphenateStyleName":17,"fbjs/lib/memoizeStringOnly":21,"fbjs/lib/warning":25}],37:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");function _classCallCheck(instance,Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function")}}var PooledClass=require("./PooledClass");var invariant=require("fbjs/lib/invariant");var CallbackQueue=function(){function CallbackQueue(arg){_classCallCheck(this,CallbackQueue);this._callbacks=null;this._contexts=null;this._arg=arg}CallbackQueue.prototype.enqueue=function enqueue(callback,context){this._callbacks=this._callbacks||[];this._callbacks.push(callback);this._contexts=this._contexts||[];this._contexts.push(context)};CallbackQueue.prototype.notifyAll=function notifyAll(){var callbacks=this._callbacks;var contexts=this._contexts;var arg=this._arg;if(callbacks&&contexts){!(callbacks.length===contexts.length)?process.env.NODE_ENV!=="production"?invariant(false,"Mismatched list of contexts in callback queue"):_prodInvariant("24"):void 0;this._callbacks=null;this._contexts=null;for(var i=0;i<callbacks.length;i++){callbacks[i].call(contexts[i],arg)}callbacks.length=0;contexts.length=0}};CallbackQueue.prototype.checkpoint=function checkpoint(){return this._callbacks?this._callbacks.length:0};CallbackQueue.prototype.rollback=function rollback(len){if(this._callbacks&&this._contexts){this._callbacks.length=len;this._contexts.length=len}};CallbackQueue.prototype.reset=function reset(){this._callbacks=null;this._contexts=null};CallbackQueue.prototype.destructor=function destructor(){this.reset()};return CallbackQueue}();module.exports=PooledClass.addPoolingTo(CallbackQueue)}).call(this,require("_process"))},{"./PooledClass":55,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],38:[function(require,module,exports){"use strict";var EventPluginHub=require("./EventPluginHub");var EventPropagators=require("./EventPropagators");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactUpdates=require("./ReactUpdates");var SyntheticEvent=require("./SyntheticEvent");var inputValueTracking=require("./inputValueTracking");var getEventTarget=require("./getEventTarget");var isEventSupported=require("./isEventSupported");var isTextInputElement=require("./isTextInputElement");var eventTypes={change:{phasedRegistrationNames:{bubbled:"onChange",captured:"onChangeCapture"},dependencies:["topBlur","topChange","topClick","topFocus","topInput","topKeyDown","topKeyUp","topSelectionChange"]}};function createAndAccumulateChangeEvent(inst,nativeEvent,target){var event=SyntheticEvent.getPooled(eventTypes.change,inst,nativeEvent,target);event.type="change";EventPropagators.accumulateTwoPhaseDispatches(event);return event}var activeElement=null;var activeElementInst=null;function shouldUseChangeEvent(elem){var nodeName=elem.nodeName&&elem.nodeName.toLowerCase();return nodeName==="select"||nodeName==="input"&&elem.type==="file"}var doesChangeEventBubble=false;if(ExecutionEnvironment.canUseDOM){doesChangeEventBubble=isEventSupported("change")&&(!document.documentMode||document.documentMode>8)}function manualDispatchChangeEvent(nativeEvent){var event=createAndAccumulateChangeEvent(activeElementInst,nativeEvent,getEventTarget(nativeEvent));ReactUpdates.batchedUpdates(runEventInBatch,event)}function runEventInBatch(event){EventPluginHub.enqueueEvents(event);EventPluginHub.processEventQueue(false)}function startWatchingForChangeEventIE8(target,targetInst){activeElement=target;activeElementInst=targetInst;activeElement.attachEvent("onchange",manualDispatchChangeEvent)}function stopWatchingForChangeEventIE8(){if(!activeElement){return}activeElement.detachEvent("onchange",manualDispatchChangeEvent);activeElement=null;activeElementInst=null}function getInstIfValueChanged(targetInst,nativeEvent){var updated=inputValueTracking.updateValueIfChanged(targetInst);var simulated=nativeEvent.simulated===true&&ChangeEventPlugin._allowSimulatedPassThrough;if(updated||simulated){return targetInst}}function getTargetInstForChangeEvent(topLevelType,targetInst){if(topLevelType==="topChange"){return targetInst}}function handleEventsForChangeEventIE8(topLevelType,target,targetInst){if(topLevelType==="topFocus"){stopWatchingForChangeEventIE8();startWatchingForChangeEventIE8(target,targetInst)}else if(topLevelType==="topBlur"){stopWatchingForChangeEventIE8()}}var isInputEventSupported=false;if(ExecutionEnvironment.canUseDOM){isInputEventSupported=isEventSupported("input")&&(!("documentMode"in document)||document.documentMode>9)}function startWatchingForValueChange(target,targetInst){activeElement=target;activeElementInst=targetInst;activeElement.attachEvent("onpropertychange",handlePropertyChange)}function stopWatchingForValueChange(){if(!activeElement){return}activeElement.detachEvent("onpropertychange",handlePropertyChange);activeElement=null;activeElementInst=null}function handlePropertyChange(nativeEvent){if(nativeEvent.propertyName!=="value"){return}if(getInstIfValueChanged(activeElementInst,nativeEvent)){manualDispatchChangeEvent(nativeEvent)}}function handleEventsForInputEventPolyfill(topLevelType,target,targetInst){if(topLevelType==="topFocus"){stopWatchingForValueChange();startWatchingForValueChange(target,targetInst)}else if(topLevelType==="topBlur"){stopWatchingForValueChange()}}function getTargetInstForInputEventPolyfill(topLevelType,targetInst,nativeEvent){if(topLevelType==="topSelectionChange"||topLevelType==="topKeyUp"||topLevelType==="topKeyDown"){return getInstIfValueChanged(activeElementInst,nativeEvent)}}function shouldUseClickEvent(elem){var nodeName=elem.nodeName;return nodeName&&nodeName.toLowerCase()==="input"&&(elem.type==="checkbox"||elem.type==="radio")}function getTargetInstForClickEvent(topLevelType,targetInst,nativeEvent){if(topLevelType==="topClick"){return getInstIfValueChanged(targetInst,nativeEvent)}}function getTargetInstForInputOrChangeEvent(topLevelType,targetInst,nativeEvent){if(topLevelType==="topInput"||topLevelType==="topChange"){return getInstIfValueChanged(targetInst,nativeEvent)}}function handleControlledInputBlur(inst,node){if(inst==null){return}var state=inst._wrapperState||node._wrapperState;if(!state||!state.controlled||node.type!=="number"){return}var value=""+node.value;if(node.getAttribute("value")!==value){node.setAttribute("value",value)}}var ChangeEventPlugin={eventTypes:eventTypes,_allowSimulatedPassThrough:true,_isInputEventSupported:isInputEventSupported,extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){var targetNode=targetInst?ReactDOMComponentTree.getNodeFromInstance(targetInst):window;var getTargetInstFunc,handleEventFunc;if(shouldUseChangeEvent(targetNode)){if(doesChangeEventBubble){getTargetInstFunc=getTargetInstForChangeEvent}else{handleEventFunc=handleEventsForChangeEventIE8}}else if(isTextInputElement(targetNode)){if(isInputEventSupported){getTargetInstFunc=getTargetInstForInputOrChangeEvent}else{getTargetInstFunc=getTargetInstForInputEventPolyfill;handleEventFunc=handleEventsForInputEventPolyfill}}else if(shouldUseClickEvent(targetNode)){getTargetInstFunc=getTargetInstForClickEvent}if(getTargetInstFunc){var inst=getTargetInstFunc(topLevelType,targetInst,nativeEvent);if(inst){var event=createAndAccumulateChangeEvent(inst,nativeEvent,nativeEventTarget);return event}}if(handleEventFunc){handleEventFunc(topLevelType,targetNode,targetInst)}if(topLevelType==="topBlur"){handleControlledInputBlur(targetInst,targetNode)}}};module.exports=ChangeEventPlugin},{"./EventPluginHub":47,"./EventPropagators":50,"./ReactDOMComponentTree":64,"./ReactUpdates":108,"./SyntheticEvent":117,"./getEventTarget":140,"./inputValueTracking":146,"./isEventSupported":148,"./isTextInputElement":149,"fbjs/lib/ExecutionEnvironment":4}],39:[function(require,module,exports){(function(process){"use strict";var DOMLazyTree=require("./DOMLazyTree");var Danger=require("./Danger");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactInstrumentation=require("./ReactInstrumentation");var createMicrosoftUnsafeLocalFunction=require("./createMicrosoftUnsafeLocalFunction");var setInnerHTML=require("./setInnerHTML");var setTextContent=require("./setTextContent");function getNodeAfter(parentNode,node){if(Array.isArray(node)){node=node[1]}return node?node.nextSibling:parentNode.firstChild}var insertChildAt=createMicrosoftUnsafeLocalFunction(function(parentNode,childNode,referenceNode){parentNode.insertBefore(childNode,referenceNode)});function insertLazyTreeChildAt(parentNode,childTree,referenceNode){DOMLazyTree.insertTreeBefore(parentNode,childTree,referenceNode)}function moveChild(parentNode,childNode,referenceNode){if(Array.isArray(childNode)){moveDelimitedText(parentNode,childNode[0],childNode[1],referenceNode)}else{insertChildAt(parentNode,childNode,referenceNode)}}function removeChild(parentNode,childNode){if(Array.isArray(childNode)){var closingComment=childNode[1];childNode=childNode[0];removeDelimitedText(parentNode,childNode,closingComment);parentNode.removeChild(closingComment)}parentNode.removeChild(childNode)}function moveDelimitedText(parentNode,openingComment,closingComment,referenceNode){var node=openingComment;while(true){var nextNode=node.nextSibling;insertChildAt(parentNode,node,referenceNode);if(node===closingComment){break}node=nextNode}}function removeDelimitedText(parentNode,startNode,closingComment){while(true){var node=startNode.nextSibling;if(node===closingComment){break}else{parentNode.removeChild(node)}}}function replaceDelimitedText(openingComment,closingComment,stringText){var parentNode=openingComment.parentNode;var nodeAfterComment=openingComment.nextSibling;if(nodeAfterComment===closingComment){if(stringText){insertChildAt(parentNode,document.createTextNode(stringText),nodeAfterComment)}}else{if(stringText){setTextContent(nodeAfterComment,stringText);removeDelimitedText(parentNode,nodeAfterComment,closingComment)}else{removeDelimitedText(parentNode,openingComment,closingComment)}}if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:ReactDOMComponentTree.getInstanceFromNode(openingComment)._debugID,type:"replace text",payload:stringText})}}var dangerouslyReplaceNodeWithMarkup=Danger.dangerouslyReplaceNodeWithMarkup;if(process.env.NODE_ENV!=="production"){dangerouslyReplaceNodeWithMarkup=function(oldChild,markup,prevInstance){Danger.dangerouslyReplaceNodeWithMarkup(oldChild,markup);if(prevInstance._debugID!==0){ReactInstrumentation.debugTool.onHostOperation({instanceID:prevInstance._debugID,type:"replace with",payload:markup.toString()})}else{var nextInstance=ReactDOMComponentTree.getInstanceFromNode(markup.node);if(nextInstance._debugID!==0){ReactInstrumentation.debugTool.onHostOperation({instanceID:nextInstance._debugID,type:"mount",payload:markup.toString()})}}}}var DOMChildrenOperations={dangerouslyReplaceNodeWithMarkup:dangerouslyReplaceNodeWithMarkup,replaceDelimitedText:replaceDelimitedText,processUpdates:function(parentNode,updates){if(process.env.NODE_ENV!=="production"){var parentNodeDebugID=ReactDOMComponentTree.getInstanceFromNode(parentNode)._debugID}for(var k=0;k<updates.length;k++){var update=updates[k];switch(update.type){case"INSERT_MARKUP":insertLazyTreeChildAt(parentNode,update.content,getNodeAfter(parentNode,update.afterNode));if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:parentNodeDebugID,type:"insert child",payload:{toIndex:update.toIndex,content:update.content.toString()}})}break;case"MOVE_EXISTING":moveChild(parentNode,update.fromNode,getNodeAfter(parentNode,update.afterNode));if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:parentNodeDebugID,type:"move child",payload:{fromIndex:update.fromIndex,toIndex:update.toIndex}})}break;case"SET_MARKUP":setInnerHTML(parentNode,update.content);if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:parentNodeDebugID,type:"replace children",payload:update.content.toString()})}break;case"TEXT_CONTENT":setTextContent(parentNode,update.content);if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:parentNodeDebugID,type:"replace text",payload:update.content.toString()})}break;case"REMOVE_NODE":removeChild(parentNode,update.fromNode);if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:parentNodeDebugID,type:"remove child",payload:{fromIndex:update.fromIndex}})}break}}}};module.exports=DOMChildrenOperations}).call(this,require("_process"))},{"./DOMLazyTree":40,"./Danger":44,"./ReactDOMComponentTree":64,"./ReactInstrumentation":93,"./createMicrosoftUnsafeLocalFunction":131,"./setInnerHTML":153,"./setTextContent":154,_process:184}],40:[function(require,module,exports){"use strict";var DOMNamespaces=require("./DOMNamespaces");var setInnerHTML=require("./setInnerHTML");var createMicrosoftUnsafeLocalFunction=require("./createMicrosoftUnsafeLocalFunction");var setTextContent=require("./setTextContent");var ELEMENT_NODE_TYPE=1;var DOCUMENT_FRAGMENT_NODE_TYPE=11;var enableLazy=typeof document!=="undefined"&&typeof document.documentMode==="number"||typeof navigator!=="undefined"&&typeof navigator.userAgent==="string"&&/\bEdge\/\d/.test(navigator.userAgent);function insertTreeChildren(tree){if(!enableLazy){return}var node=tree.node;var children=tree.children;if(children.length){for(var i=0;i<children.length;i++){insertTreeBefore(node,children[i],null)}}else if(tree.html!=null){setInnerHTML(node,tree.html)}else if(tree.text!=null){setTextContent(node,tree.text)}}var insertTreeBefore=createMicrosoftUnsafeLocalFunction(function(parentNode,tree,referenceNode){if(tree.node.nodeType===DOCUMENT_FRAGMENT_NODE_TYPE||tree.node.nodeType===ELEMENT_NODE_TYPE&&tree.node.nodeName.toLowerCase()==="object"&&(tree.node.namespaceURI==null||tree.node.namespaceURI===DOMNamespaces.html)){insertTreeChildren(tree);parentNode.insertBefore(tree.node,referenceNode)}else{parentNode.insertBefore(tree.node,referenceNode);insertTreeChildren(tree)}});function replaceChildWithTree(oldNode,newTree){oldNode.parentNode.replaceChild(newTree.node,oldNode);insertTreeChildren(newTree)}function queueChild(parentTree,childTree){if(enableLazy){parentTree.children.push(childTree)}else{parentTree.node.appendChild(childTree.node)}}function queueHTML(tree,html){if(enableLazy){tree.html=html}else{setInnerHTML(tree.node,html)}}function queueText(tree,text){if(enableLazy){tree.text=text}else{setTextContent(tree.node,text)}}function toString(){return this.node.nodeName}function DOMLazyTree(node){return{node:node,children:[],html:null,text:null,toString:toString}}DOMLazyTree.insertTreeBefore=insertTreeBefore;DOMLazyTree.replaceChildWithTree=replaceChildWithTree;DOMLazyTree.queueChild=queueChild;DOMLazyTree.queueHTML=queueHTML;DOMLazyTree.queueText=queueText;module.exports=DOMLazyTree},{"./DOMNamespaces":41,"./createMicrosoftUnsafeLocalFunction":131,"./setInnerHTML":153,"./setTextContent":154}],41:[function(require,module,exports){"use strict";var DOMNamespaces={html:"http://www.w3.org/1999/xhtml",mathml:"http://www.w3.org/1998/Math/MathML",svg:"http://www.w3.org/2000/svg"};module.exports=DOMNamespaces},{}],42:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");function checkMask(value,bitmask){return(value&bitmask)===bitmask}var DOMPropertyInjection={MUST_USE_PROPERTY:1,HAS_BOOLEAN_VALUE:4,HAS_NUMERIC_VALUE:8,HAS_POSITIVE_NUMERIC_VALUE:16|8,HAS_OVERLOADED_BOOLEAN_VALUE:32,injectDOMPropertyConfig:function(domPropertyConfig){var Injection=DOMPropertyInjection;var Properties=domPropertyConfig.Properties||{};var DOMAttributeNamespaces=domPropertyConfig.DOMAttributeNamespaces||{};var DOMAttributeNames=domPropertyConfig.DOMAttributeNames||{};var DOMPropertyNames=domPropertyConfig.DOMPropertyNames||{};var DOMMutationMethods=domPropertyConfig.DOMMutationMethods||{};if(domPropertyConfig.isCustomAttribute){DOMProperty._isCustomAttributeFunctions.push(domPropertyConfig.isCustomAttribute)}for(var propName in Properties){!!DOMProperty.properties.hasOwnProperty(propName)?process.env.NODE_ENV!=="production"?invariant(false,"injectDOMPropertyConfig(...): You're trying to inject DOM property '%s' which has already been injected. You may be accidentally injecting the same DOM property config twice, or you may be injecting two configs that have conflicting property names.",propName):_prodInvariant("48",propName):void 0;var lowerCased=propName.toLowerCase();var propConfig=Properties[propName];var propertyInfo={attributeName:lowerCased,attributeNamespace:null,propertyName:propName,mutationMethod:null,mustUseProperty:checkMask(propConfig,Injection.MUST_USE_PROPERTY),hasBooleanValue:checkMask(propConfig,Injection.HAS_BOOLEAN_VALUE),hasNumericValue:checkMask(propConfig,Injection.HAS_NUMERIC_VALUE),hasPositiveNumericValue:checkMask(propConfig,Injection.HAS_POSITIVE_NUMERIC_VALUE),hasOverloadedBooleanValue:checkMask(propConfig,Injection.HAS_OVERLOADED_BOOLEAN_VALUE)};!(propertyInfo.hasBooleanValue+propertyInfo.hasNumericValue+propertyInfo.hasOverloadedBooleanValue<=1)?process.env.NODE_ENV!=="production"?invariant(false,"DOMProperty: Value can be one of boolean, overloaded boolean, or numeric value, but not a combination: %s",propName):_prodInvariant("50",propName):void 0;if(process.env.NODE_ENV!=="production"){DOMProperty.getPossibleStandardName[lowerCased]=propName}if(DOMAttributeNames.hasOwnProperty(propName)){var attributeName=DOMAttributeNames[propName];propertyInfo.attributeName=attributeName;if(process.env.NODE_ENV!=="production"){DOMProperty.getPossibleStandardName[attributeName]=propName}}if(DOMAttributeNamespaces.hasOwnProperty(propName)){propertyInfo.attributeNamespace=DOMAttributeNamespaces[propName]}if(DOMPropertyNames.hasOwnProperty(propName)){propertyInfo.propertyName=DOMPropertyNames[propName]}if(DOMMutationMethods.hasOwnProperty(propName)){propertyInfo.mutationMethod=DOMMutationMethods[propName]}DOMProperty.properties[propName]=propertyInfo}}};var ATTRIBUTE_NAME_START_CHAR=":A-Z_a-z\\u00C0-\\u00D6\\u00D8-\\u00F6\\u00F8-\\u02FF\\u0370-\\u037D\\u037F-\\u1FFF\\u200C-\\u200D\\u2070-\\u218F\\u2C00-\\u2FEF\\u3001-\\uD7FF\\uF900-\\uFDCF\\uFDF0-\\uFFFD";var DOMProperty={ID_ATTRIBUTE_NAME:"data-reactid",ROOT_ATTRIBUTE_NAME:"data-reactroot",ATTRIBUTE_NAME_START_CHAR:ATTRIBUTE_NAME_START_CHAR,ATTRIBUTE_NAME_CHAR:ATTRIBUTE_NAME_START_CHAR+"\\-.0-9\\u00B7\\u0300-\\u036F\\u203F-\\u2040",properties:{},getPossibleStandardName:process.env.NODE_ENV!=="production"?{autofocus:"autoFocus"}:null,_isCustomAttributeFunctions:[],isCustomAttribute:function(attributeName){for(var i=0;i<DOMProperty._isCustomAttributeFunctions.length;i++){var isCustomAttributeFn=DOMProperty._isCustomAttributeFunctions[i];if(isCustomAttributeFn(attributeName)){return true}}return false},injection:DOMPropertyInjection};module.exports=DOMProperty}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],43:[function(require,module,exports){(function(process){"use strict";var DOMProperty=require("./DOMProperty");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactInstrumentation=require("./ReactInstrumentation");var quoteAttributeValueForBrowser=require("./quoteAttributeValueForBrowser");var warning=require("fbjs/lib/warning");var VALID_ATTRIBUTE_NAME_REGEX=new RegExp("^["+DOMProperty.ATTRIBUTE_NAME_START_CHAR+"]["+DOMProperty.ATTRIBUTE_NAME_CHAR+"]*$");var illegalAttributeNameCache={};var validatedAttributeNameCache={};function isAttributeNameSafe(attributeName){if(validatedAttributeNameCache.hasOwnProperty(attributeName)){return true}if(illegalAttributeNameCache.hasOwnProperty(attributeName)){return false}if(VALID_ATTRIBUTE_NAME_REGEX.test(attributeName)){validatedAttributeNameCache[attributeName]=true;return true}illegalAttributeNameCache[attributeName]=true;process.env.NODE_ENV!=="production"?warning(false,"Invalid attribute name: `%s`",attributeName):void 0;return false}function shouldIgnoreValue(propertyInfo,value){return value==null||propertyInfo.hasBooleanValue&&!value||propertyInfo.hasNumericValue&&isNaN(value)||propertyInfo.hasPositiveNumericValue&&value<1||propertyInfo.hasOverloadedBooleanValue&&value===false}var DOMPropertyOperations={createMarkupForID:function(id){return DOMProperty.ID_ATTRIBUTE_NAME+"="+quoteAttributeValueForBrowser(id)},setAttributeForID:function(node,id){node.setAttribute(DOMProperty.ID_ATTRIBUTE_NAME,id)},createMarkupForRoot:function(){return DOMProperty.ROOT_ATTRIBUTE_NAME+'=""'},setAttributeForRoot:function(node){node.setAttribute(DOMProperty.ROOT_ATTRIBUTE_NAME,"")},createMarkupForProperty:function(name,value){var propertyInfo=DOMProperty.properties.hasOwnProperty(name)?DOMProperty.properties[name]:null;if(propertyInfo){if(shouldIgnoreValue(propertyInfo,value)){return""}var attributeName=propertyInfo.attributeName;if(propertyInfo.hasBooleanValue||propertyInfo.hasOverloadedBooleanValue&&value===true){return attributeName+'=""'}return attributeName+"="+quoteAttributeValueForBrowser(value)}else if(DOMProperty.isCustomAttribute(name)){if(value==null){return""}return name+"="+quoteAttributeValueForBrowser(value)}return null},createMarkupForCustomAttribute:function(name,value){if(!isAttributeNameSafe(name)||value==null){return""}return name+"="+quoteAttributeValueForBrowser(value)},setValueForProperty:function(node,name,value){var propertyInfo=DOMProperty.properties.hasOwnProperty(name)?DOMProperty.properties[name]:null;if(propertyInfo){var mutationMethod=propertyInfo.mutationMethod;if(mutationMethod){mutationMethod(node,value)}else if(shouldIgnoreValue(propertyInfo,value)){this.deleteValueForProperty(node,name);return}else if(propertyInfo.mustUseProperty){node[propertyInfo.propertyName]=value}else{var attributeName=propertyInfo.attributeName;var namespace=propertyInfo.attributeNamespace;if(namespace){node.setAttributeNS(namespace,attributeName,""+value)}else if(propertyInfo.hasBooleanValue||propertyInfo.hasOverloadedBooleanValue&&value===true){node.setAttribute(attributeName,"")}else{node.setAttribute(attributeName,""+value)}}}else if(DOMProperty.isCustomAttribute(name)){DOMPropertyOperations.setValueForAttribute(node,name,value);return}if(process.env.NODE_ENV!=="production"){var payload={};payload[name]=value;ReactInstrumentation.debugTool.onHostOperation({instanceID:ReactDOMComponentTree.getInstanceFromNode(node)._debugID,type:"update attribute",payload:payload})}},setValueForAttribute:function(node,name,value){if(!isAttributeNameSafe(name)){return}if(value==null){node.removeAttribute(name)}else{node.setAttribute(name,""+value)}if(process.env.NODE_ENV!=="production"){var payload={};payload[name]=value;ReactInstrumentation.debugTool.onHostOperation({instanceID:ReactDOMComponentTree.getInstanceFromNode(node)._debugID,type:"update attribute",payload:payload})}},deleteValueForAttribute:function(node,name){node.removeAttribute(name);if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:ReactDOMComponentTree.getInstanceFromNode(node)._debugID,type:"remove attribute",payload:name})}},deleteValueForProperty:function(node,name){var propertyInfo=DOMProperty.properties.hasOwnProperty(name)?DOMProperty.properties[name]:null;if(propertyInfo){var mutationMethod=propertyInfo.mutationMethod;if(mutationMethod){mutationMethod(node,undefined)}else if(propertyInfo.mustUseProperty){var propName=propertyInfo.propertyName;if(propertyInfo.hasBooleanValue){node[propName]=false}else{node[propName]=""}}else{node.removeAttribute(propertyInfo.attributeName)}}else if(DOMProperty.isCustomAttribute(name)){node.removeAttribute(name)}if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onHostOperation({instanceID:ReactDOMComponentTree.getInstanceFromNode(node)._debugID,type:"remove attribute",payload:name})}}};module.exports=DOMPropertyOperations}).call(this,require("_process"))},{"./DOMProperty":42,"./ReactDOMComponentTree":64,"./ReactInstrumentation":93,"./quoteAttributeValueForBrowser":150,_process:184,"fbjs/lib/warning":25}],44:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var DOMLazyTree=require("./DOMLazyTree");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var createNodesFromMarkup=require("fbjs/lib/createNodesFromMarkup");var emptyFunction=require("fbjs/lib/emptyFunction");var invariant=require("fbjs/lib/invariant");var Danger={dangerouslyReplaceNodeWithMarkup:function(oldChild,markup){!ExecutionEnvironment.canUseDOM?process.env.NODE_ENV!=="production"?invariant(false,"dangerouslyReplaceNodeWithMarkup(...): Cannot render markup in a worker thread. Make sure `window` and `document` are available globally before requiring React when unit testing or use ReactDOMServer.renderToString() for server rendering."):_prodInvariant("56"):void 0;!markup?process.env.NODE_ENV!=="production"?invariant(false,"dangerouslyReplaceNodeWithMarkup(...): Missing markup."):_prodInvariant("57"):void 0;!(oldChild.nodeName!=="HTML")?process.env.NODE_ENV!=="production"?invariant(false,"dangerouslyReplaceNodeWithMarkup(...): Cannot replace markup of the <html> node. This is because browser quirks make this unreliable and/or slow. If you want to render to the root you must use server rendering. See ReactDOMServer.renderToString()."):_prodInvariant("58"):void 0;if(typeof markup==="string"){var newChild=createNodesFromMarkup(markup,emptyFunction)[0];oldChild.parentNode.replaceChild(newChild,oldChild)}else{DOMLazyTree.replaceChildWithTree(oldChild,markup)}}};module.exports=Danger}).call(this,require("_process"))},{"./DOMLazyTree":40,"./reactProdInvariant":151,_process:184,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/createNodesFromMarkup":9,"fbjs/lib/emptyFunction":10,"fbjs/lib/invariant":18}],45:[function(require,module,exports){"use strict";var DefaultEventPluginOrder=["ResponderEventPlugin","SimpleEventPlugin","TapEventPlugin","EnterLeaveEventPlugin","ChangeEventPlugin","SelectEventPlugin","BeforeInputEventPlugin"];module.exports=DefaultEventPluginOrder},{}],46:[function(require,module,exports){"use strict";var EventPropagators=require("./EventPropagators");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var SyntheticMouseEvent=require("./SyntheticMouseEvent");var eventTypes={mouseEnter:{registrationName:"onMouseEnter",dependencies:["topMouseOut","topMouseOver"]},mouseLeave:{registrationName:"onMouseLeave",dependencies:["topMouseOut","topMouseOver"]}};var EnterLeaveEventPlugin={eventTypes:eventTypes,extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){if(topLevelType==="topMouseOver"&&(nativeEvent.relatedTarget||nativeEvent.fromElement)){return null}if(topLevelType!=="topMouseOut"&&topLevelType!=="topMouseOver"){return null}var win;if(nativeEventTarget.window===nativeEventTarget){win=nativeEventTarget}else{var doc=nativeEventTarget.ownerDocument;if(doc){win=doc.defaultView||doc.parentWindow}else{win=window}}var from;var to;if(topLevelType==="topMouseOut"){from=targetInst;var related=nativeEvent.relatedTarget||nativeEvent.toElement;to=related?ReactDOMComponentTree.getClosestInstanceFromNode(related):null}else{from=null;to=targetInst}if(from===to){return null}var fromNode=from==null?win:ReactDOMComponentTree.getNodeFromInstance(from);var toNode=to==null?win:ReactDOMComponentTree.getNodeFromInstance(to);var leave=SyntheticMouseEvent.getPooled(eventTypes.mouseLeave,from,nativeEvent,nativeEventTarget);leave.type="mouseleave";leave.target=fromNode;leave.relatedTarget=toNode;var enter=SyntheticMouseEvent.getPooled(eventTypes.mouseEnter,to,nativeEvent,nativeEventTarget);enter.type="mouseenter";enter.target=toNode;enter.relatedTarget=fromNode;EventPropagators.accumulateEnterLeaveDispatches(leave,enter,from,to);return[leave,enter]}};module.exports=EnterLeaveEventPlugin},{"./EventPropagators":50,"./ReactDOMComponentTree":64,"./SyntheticMouseEvent":121}],47:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var EventPluginRegistry=require("./EventPluginRegistry");var EventPluginUtils=require("./EventPluginUtils");var ReactErrorUtils=require("./ReactErrorUtils");var accumulateInto=require("./accumulateInto");var forEachAccumulated=require("./forEachAccumulated");var invariant=require("fbjs/lib/invariant");var listenerBank={};var eventQueue=null;var executeDispatchesAndRelease=function(event,simulated){if(event){EventPluginUtils.executeDispatchesInOrder(event,simulated);if(!event.isPersistent()){event.constructor.release(event)}}};var executeDispatchesAndReleaseSimulated=function(e){return executeDispatchesAndRelease(e,true)};var executeDispatchesAndReleaseTopLevel=function(e){return executeDispatchesAndRelease(e,false)};var getDictionaryKey=function(inst){return"."+inst._rootNodeID};function isInteractive(tag){return tag==="button"||tag==="input"||tag==="select"||tag==="textarea"}function shouldPreventMouseEvent(name,type,props){switch(name){case"onClick":case"onClickCapture":case"onDoubleClick":case"onDoubleClickCapture":case"onMouseDown":case"onMouseDownCapture":case"onMouseMove":case"onMouseMoveCapture":case"onMouseUp":case"onMouseUpCapture":return!!(props.disabled&&isInteractive(type));default:return false}}var EventPluginHub={injection:{injectEventPluginOrder:EventPluginRegistry.injectEventPluginOrder,injectEventPluginsByName:EventPluginRegistry.injectEventPluginsByName},putListener:function(inst,registrationName,listener){!(typeof listener==="function")?process.env.NODE_ENV!=="production"?invariant(false,"Expected %s listener to be a function, instead got type %s",registrationName,typeof listener):_prodInvariant("94",registrationName,typeof listener):void 0;var key=getDictionaryKey(inst);var bankForRegistrationName=listenerBank[registrationName]||(listenerBank[registrationName]={});bankForRegistrationName[key]=listener;var PluginModule=EventPluginRegistry.registrationNameModules[registrationName];if(PluginModule&&PluginModule.didPutListener){PluginModule.didPutListener(inst,registrationName,listener)}},getListener:function(inst,registrationName){var bankForRegistrationName=listenerBank[registrationName];if(shouldPreventMouseEvent(registrationName,inst._currentElement.type,inst._currentElement.props)){return null}var key=getDictionaryKey(inst);return bankForRegistrationName&&bankForRegistrationName[key]},deleteListener:function(inst,registrationName){var PluginModule=EventPluginRegistry.registrationNameModules[registrationName];if(PluginModule&&PluginModule.willDeleteListener){PluginModule.willDeleteListener(inst,registrationName)}var bankForRegistrationName=listenerBank[registrationName];if(bankForRegistrationName){var key=getDictionaryKey(inst);delete bankForRegistrationName[key]}},deleteAllListeners:function(inst){var key=getDictionaryKey(inst);for(var registrationName in listenerBank){if(!listenerBank.hasOwnProperty(registrationName)){continue}if(!listenerBank[registrationName][key]){continue}var PluginModule=EventPluginRegistry.registrationNameModules[registrationName];if(PluginModule&&PluginModule.willDeleteListener){PluginModule.willDeleteListener(inst,registrationName)}delete listenerBank[registrationName][key]}},extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){var events;var plugins=EventPluginRegistry.plugins;for(var i=0;i<plugins.length;i++){var possiblePlugin=plugins[i];if(possiblePlugin){var extractedEvents=possiblePlugin.extractEvents(topLevelType,targetInst,nativeEvent,nativeEventTarget);if(extractedEvents){events=accumulateInto(events,extractedEvents)}}}return events},enqueueEvents:function(events){if(events){eventQueue=accumulateInto(eventQueue,events)}},processEventQueue:function(simulated){var processingEventQueue=eventQueue;eventQueue=null;if(simulated){forEachAccumulated(processingEventQueue,executeDispatchesAndReleaseSimulated)}else{forEachAccumulated(processingEventQueue,executeDispatchesAndReleaseTopLevel)}!!eventQueue?process.env.NODE_ENV!=="production"?invariant(false,"processEventQueue(): Additional events were enqueued while processing an event queue. Support for this has not yet been implemented."):_prodInvariant("95"):void 0;ReactErrorUtils.rethrowCaughtError()},__purge:function(){listenerBank={}},__getListenerBank:function(){return listenerBank}};module.exports=EventPluginHub}).call(this,require("_process"))},{"./EventPluginRegistry":48,"./EventPluginUtils":49,"./ReactErrorUtils":84,"./accumulateInto":128,"./forEachAccumulated":136,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],48:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");var eventPluginOrder=null;var namesToPlugins={};function recomputePluginOrdering(){if(!eventPluginOrder){return}for(var pluginName in namesToPlugins){var pluginModule=namesToPlugins[pluginName];var pluginIndex=eventPluginOrder.indexOf(pluginName);!(pluginIndex>-1)?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginRegistry: Cannot inject event plugins that do not exist in the plugin ordering, `%s`.",pluginName):_prodInvariant("96",pluginName):void 0;if(EventPluginRegistry.plugins[pluginIndex]){continue}!pluginModule.extractEvents?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginRegistry: Event plugins must implement an `extractEvents` method, but `%s` does not.",pluginName):_prodInvariant("97",pluginName):void 0;EventPluginRegistry.plugins[pluginIndex]=pluginModule;var publishedEvents=pluginModule.eventTypes;for(var eventName in publishedEvents){!publishEventForPlugin(publishedEvents[eventName],pluginModule,eventName)?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginRegistry: Failed to publish event `%s` for plugin `%s`.",eventName,pluginName):_prodInvariant("98",eventName,pluginName):void 0}}}function publishEventForPlugin(dispatchConfig,pluginModule,eventName){!!EventPluginRegistry.eventNameDispatchConfigs.hasOwnProperty(eventName)?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginHub: More than one plugin attempted to publish the same event name, `%s`.",eventName):_prodInvariant("99",eventName):void 0;EventPluginRegistry.eventNameDispatchConfigs[eventName]=dispatchConfig;var phasedRegistrationNames=dispatchConfig.phasedRegistrationNames;if(phasedRegistrationNames){for(var phaseName in phasedRegistrationNames){if(phasedRegistrationNames.hasOwnProperty(phaseName)){var phasedRegistrationName=phasedRegistrationNames[phaseName];publishRegistrationName(phasedRegistrationName,pluginModule,eventName)}}return true}else if(dispatchConfig.registrationName){publishRegistrationName(dispatchConfig.registrationName,pluginModule,eventName);return true}return false}function publishRegistrationName(registrationName,pluginModule,eventName){!!EventPluginRegistry.registrationNameModules[registrationName]?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginHub: More than one plugin attempted to publish the same registration name, `%s`.",registrationName):_prodInvariant("100",registrationName):void 0;EventPluginRegistry.registrationNameModules[registrationName]=pluginModule;EventPluginRegistry.registrationNameDependencies[registrationName]=pluginModule.eventTypes[eventName].dependencies;if(process.env.NODE_ENV!=="production"){var lowerCasedName=registrationName.toLowerCase();EventPluginRegistry.possibleRegistrationNames[lowerCasedName]=registrationName;if(registrationName==="onDoubleClick"){EventPluginRegistry.possibleRegistrationNames.ondblclick=registrationName}}}var EventPluginRegistry={plugins:[],eventNameDispatchConfigs:{},registrationNameModules:{},registrationNameDependencies:{},possibleRegistrationNames:process.env.NODE_ENV!=="production"?{}:null,injectEventPluginOrder:function(injectedEventPluginOrder){!!eventPluginOrder?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginRegistry: Cannot inject event plugin ordering more than once. You are likely trying to load more than one copy of React."):_prodInvariant("101"):void 0;eventPluginOrder=Array.prototype.slice.call(injectedEventPluginOrder);recomputePluginOrdering()},injectEventPluginsByName:function(injectedNamesToPlugins){var isOrderingDirty=false;for(var pluginName in injectedNamesToPlugins){if(!injectedNamesToPlugins.hasOwnProperty(pluginName)){continue}var pluginModule=injectedNamesToPlugins[pluginName];if(!namesToPlugins.hasOwnProperty(pluginName)||namesToPlugins[pluginName]!==pluginModule){!!namesToPlugins[pluginName]?process.env.NODE_ENV!=="production"?invariant(false,"EventPluginRegistry: Cannot inject two different event plugins using the same name, `%s`.",pluginName):_prodInvariant("102",pluginName):void 0;namesToPlugins[pluginName]=pluginModule;isOrderingDirty=true}}if(isOrderingDirty){recomputePluginOrdering()}},getPluginModuleForEvent:function(event){var dispatchConfig=event.dispatchConfig;if(dispatchConfig.registrationName){return EventPluginRegistry.registrationNameModules[dispatchConfig.registrationName]||null}if(dispatchConfig.phasedRegistrationNames!==undefined){var phasedRegistrationNames=dispatchConfig.phasedRegistrationNames;for(var phase in phasedRegistrationNames){if(!phasedRegistrationNames.hasOwnProperty(phase)){continue}var pluginModule=EventPluginRegistry.registrationNameModules[phasedRegistrationNames[phase]];if(pluginModule){return pluginModule}}}return null},_resetEventPlugins:function(){eventPluginOrder=null;for(var pluginName in namesToPlugins){if(namesToPlugins.hasOwnProperty(pluginName)){delete namesToPlugins[pluginName]}}EventPluginRegistry.plugins.length=0;var eventNameDispatchConfigs=EventPluginRegistry.eventNameDispatchConfigs;for(var eventName in eventNameDispatchConfigs){if(eventNameDispatchConfigs.hasOwnProperty(eventName)){delete eventNameDispatchConfigs[eventName]}}var registrationNameModules=EventPluginRegistry.registrationNameModules;for(var registrationName in registrationNameModules){if(registrationNameModules.hasOwnProperty(registrationName)){delete registrationNameModules[registrationName]}}if(process.env.NODE_ENV!=="production"){var possibleRegistrationNames=EventPluginRegistry.possibleRegistrationNames;for(var lowerCasedName in possibleRegistrationNames){if(possibleRegistrationNames.hasOwnProperty(lowerCasedName)){delete possibleRegistrationNames[lowerCasedName]}}}}};module.exports=EventPluginRegistry}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],49:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactErrorUtils=require("./ReactErrorUtils");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ComponentTree;var TreeTraversal;var injection={injectComponentTree:function(Injected){ComponentTree=Injected;if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(Injected&&Injected.getNodeFromInstance&&Injected.getInstanceFromNode,"EventPluginUtils.injection.injectComponentTree(...): Injected "+"module is missing getNodeFromInstance or getInstanceFromNode."):void 0}},injectTreeTraversal:function(Injected){TreeTraversal=Injected;if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(Injected&&Injected.isAncestor&&Injected.getLowestCommonAncestor,"EventPluginUtils.injection.injectTreeTraversal(...): Injected "+"module is missing isAncestor or getLowestCommonAncestor."):void 0}}};function isEndish(topLevelType){return topLevelType==="topMouseUp"||topLevelType==="topTouchEnd"||topLevelType==="topTouchCancel"}function isMoveish(topLevelType){return topLevelType==="topMouseMove"||topLevelType==="topTouchMove"}function isStartish(topLevelType){return topLevelType==="topMouseDown"||topLevelType==="topTouchStart"}var validateEventDispatches;if(process.env.NODE_ENV!=="production"){validateEventDispatches=function(event){var dispatchListeners=event._dispatchListeners;var dispatchInstances=event._dispatchInstances;var listenersIsArr=Array.isArray(dispatchListeners);var listenersLen=listenersIsArr?dispatchListeners.length:dispatchListeners?1:0;var instancesIsArr=Array.isArray(dispatchInstances);var instancesLen=instancesIsArr?dispatchInstances.length:dispatchInstances?1:0;process.env.NODE_ENV!=="production"?warning(instancesIsArr===listenersIsArr&&instancesLen===listenersLen,"EventPluginUtils: Invalid `event`."):void 0}}function executeDispatch(event,simulated,listener,inst){var type=event.type||"unknown-event";event.currentTarget=EventPluginUtils.getNodeFromInstance(inst);if(simulated){ReactErrorUtils.invokeGuardedCallbackWithCatch(type,listener,event)}else{ReactErrorUtils.invokeGuardedCallback(type,listener,event)}event.currentTarget=null}function executeDispatchesInOrder(event,simulated){var dispatchListeners=event._dispatchListeners;var dispatchInstances=event._dispatchInstances;if(process.env.NODE_ENV!=="production"){validateEventDispatches(event)}if(Array.isArray(dispatchListeners)){for(var i=0;i<dispatchListeners.length;i++){if(event.isPropagationStopped()){break}executeDispatch(event,simulated,dispatchListeners[i],dispatchInstances[i])}}else if(dispatchListeners){executeDispatch(event,simulated,dispatchListeners,dispatchInstances)}event._dispatchListeners=null;event._dispatchInstances=null}function executeDispatchesInOrderStopAtTrueImpl(event){var dispatchListeners=event._dispatchListeners;var dispatchInstances=event._dispatchInstances;if(process.env.NODE_ENV!=="production"){validateEventDispatches(event)}if(Array.isArray(dispatchListeners)){for(var i=0;i<dispatchListeners.length;i++){if(event.isPropagationStopped()){break}if(dispatchListeners[i](event,dispatchInstances[i])){return dispatchInstances[i]}}}else if(dispatchListeners){if(dispatchListeners(event,dispatchInstances)){return dispatchInstances}}return null}function executeDispatchesInOrderStopAtTrue(event){var ret=executeDispatchesInOrderStopAtTrueImpl(event);event._dispatchInstances=null;event._dispatchListeners=null;return ret}function executeDirectDispatch(event){if(process.env.NODE_ENV!=="production"){validateEventDispatches(event)}var dispatchListener=event._dispatchListeners;var dispatchInstance=event._dispatchInstances;!!Array.isArray(dispatchListener)?process.env.NODE_ENV!=="production"?invariant(false,"executeDirectDispatch(...): Invalid `event`."):_prodInvariant("103"):void 0;event.currentTarget=dispatchListener?EventPluginUtils.getNodeFromInstance(dispatchInstance):null;var res=dispatchListener?dispatchListener(event):null;event.currentTarget=null;event._dispatchListeners=null;event._dispatchInstances=null;return res}function hasDispatches(event){return!!event._dispatchListeners}var EventPluginUtils={isEndish:isEndish,isMoveish:isMoveish,isStartish:isStartish,executeDirectDispatch:executeDirectDispatch,executeDispatchesInOrder:executeDispatchesInOrder,executeDispatchesInOrderStopAtTrue:executeDispatchesInOrderStopAtTrue,hasDispatches:hasDispatches,getInstanceFromNode:function(node){return ComponentTree.getInstanceFromNode(node)},getNodeFromInstance:function(node){return ComponentTree.getNodeFromInstance(node)},isAncestor:function(a,b){return TreeTraversal.isAncestor(a,b)},getLowestCommonAncestor:function(a,b){return TreeTraversal.getLowestCommonAncestor(a,b)},getParentInstance:function(inst){return TreeTraversal.getParentInstance(inst)},traverseTwoPhase:function(target,fn,arg){return TreeTraversal.traverseTwoPhase(target,fn,arg)},traverseEnterLeave:function(from,to,fn,argFrom,argTo){return TreeTraversal.traverseEnterLeave(from,to,fn,argFrom,argTo)},injection:injection};module.exports=EventPluginUtils}).call(this,require("_process"))},{"./ReactErrorUtils":84,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],50:[function(require,module,exports){(function(process){"use strict";var EventPluginHub=require("./EventPluginHub");var EventPluginUtils=require("./EventPluginUtils");var accumulateInto=require("./accumulateInto");var forEachAccumulated=require("./forEachAccumulated");var warning=require("fbjs/lib/warning");var getListener=EventPluginHub.getListener;function listenerAtPhase(inst,event,propagationPhase){var registrationName=event.dispatchConfig.phasedRegistrationNames[propagationPhase];return getListener(inst,registrationName)}function accumulateDirectionalDispatches(inst,phase,event){if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(inst,"Dispatching inst must not be null"):void 0}var listener=listenerAtPhase(inst,event,phase);if(listener){event._dispatchListeners=accumulateInto(event._dispatchListeners,listener);event._dispatchInstances=accumulateInto(event._dispatchInstances,inst)}}function accumulateTwoPhaseDispatchesSingle(event){if(event&&event.dispatchConfig.phasedRegistrationNames){EventPluginUtils.traverseTwoPhase(event._targetInst,accumulateDirectionalDispatches,event)}}function accumulateTwoPhaseDispatchesSingleSkipTarget(event){if(event&&event.dispatchConfig.phasedRegistrationNames){var targetInst=event._targetInst;var parentInst=targetInst?EventPluginUtils.getParentInstance(targetInst):null;EventPluginUtils.traverseTwoPhase(parentInst,accumulateDirectionalDispatches,event)}}function accumulateDispatches(inst,ignoredDirection,event){if(event&&event.dispatchConfig.registrationName){var registrationName=event.dispatchConfig.registrationName;var listener=getListener(inst,registrationName);if(listener){event._dispatchListeners=accumulateInto(event._dispatchListeners,listener);event._dispatchInstances=accumulateInto(event._dispatchInstances,inst)}}}function accumulateDirectDispatchesSingle(event){if(event&&event.dispatchConfig.registrationName){accumulateDispatches(event._targetInst,null,event)}}function accumulateTwoPhaseDispatches(events){forEachAccumulated(events,accumulateTwoPhaseDispatchesSingle)}function accumulateTwoPhaseDispatchesSkipTarget(events){forEachAccumulated(events,accumulateTwoPhaseDispatchesSingleSkipTarget)}function accumulateEnterLeaveDispatches(leave,enter,from,to){EventPluginUtils.traverseEnterLeave(from,to,accumulateDispatches,leave,enter)}function accumulateDirectDispatches(events){forEachAccumulated(events,accumulateDirectDispatchesSingle)}var EventPropagators={accumulateTwoPhaseDispatches:accumulateTwoPhaseDispatches,accumulateTwoPhaseDispatchesSkipTarget:accumulateTwoPhaseDispatchesSkipTarget,accumulateDirectDispatches:accumulateDirectDispatches,accumulateEnterLeaveDispatches:accumulateEnterLeaveDispatches};module.exports=EventPropagators}).call(this,require("_process"))},{"./EventPluginHub":47,"./EventPluginUtils":49,"./accumulateInto":128,"./forEachAccumulated":136,_process:184,"fbjs/lib/warning":25}],51:[function(require,module,exports){"use strict";var _assign=require("object-assign");var PooledClass=require("./PooledClass");var getTextContentAccessor=require("./getTextContentAccessor");function FallbackCompositionState(root){this._root=root;this._startText=this.getText();this._fallbackText=null}_assign(FallbackCompositionState.prototype,{destructor:function(){this._root=null;this._startText=null;this._fallbackText=null},getText:function(){if("value"in this._root){return this._root.value}return this._root[getTextContentAccessor()]},getData:function(){if(this._fallbackText){return this._fallbackText}var start;var startValue=this._startText;var startLength=startValue.length;var end;var endValue=this.getText();var endLength=endValue.length;for(start=0;start<startLength;start++){if(startValue[start]!==endValue[start]){break}}var minEnd=startLength-start;for(end=1;end<=minEnd;end++){if(startValue[startLength-end]!==endValue[endLength-end]){break}}var sliceTail=end>1?1-end:undefined;this._fallbackText=endValue.slice(start,sliceTail);return this._fallbackText}});PooledClass.addPoolingTo(FallbackCompositionState);module.exports=FallbackCompositionState},{"./PooledClass":55,"./getTextContentAccessor":144,"object-assign":26}],52:[function(require,module,exports){"use strict";var DOMProperty=require("./DOMProperty");var MUST_USE_PROPERTY=DOMProperty.injection.MUST_USE_PROPERTY;var HAS_BOOLEAN_VALUE=DOMProperty.injection.HAS_BOOLEAN_VALUE;var HAS_NUMERIC_VALUE=DOMProperty.injection.HAS_NUMERIC_VALUE;var HAS_POSITIVE_NUMERIC_VALUE=DOMProperty.injection.HAS_POSITIVE_NUMERIC_VALUE;var HAS_OVERLOADED_BOOLEAN_VALUE=DOMProperty.injection.HAS_OVERLOADED_BOOLEAN_VALUE;var HTMLDOMPropertyConfig={isCustomAttribute:RegExp.prototype.test.bind(new RegExp("^(data|aria)-["+DOMProperty.ATTRIBUTE_NAME_CHAR+"]*$")),Properties:{accept:0,acceptCharset:0,accessKey:0,action:0,allowFullScreen:HAS_BOOLEAN_VALUE,allowTransparency:0,alt:0,as:0,async:HAS_BOOLEAN_VALUE,autoComplete:0,autoPlay:HAS_BOOLEAN_VALUE,capture:HAS_BOOLEAN_VALUE,cellPadding:0,cellSpacing:0,charSet:0,challenge:0,checked:MUST_USE_PROPERTY|HAS_BOOLEAN_VALUE,cite:0,classID:0,className:0,cols:HAS_POSITIVE_NUMERIC_VALUE,colSpan:0,content:0,contentEditable:0,contextMenu:0,controls:HAS_BOOLEAN_VALUE,coords:0,crossOrigin:0,data:0,dateTime:0,default:HAS_BOOLEAN_VALUE,defer:HAS_BOOLEAN_VALUE,dir:0,disabled:HAS_BOOLEAN_VALUE,download:HAS_OVERLOADED_BOOLEAN_VALUE,draggable:0,encType:0,form:0,formAction:0,formEncType:0,formMethod:0,formNoValidate:HAS_BOOLEAN_VALUE,formTarget:0,frameBorder:0,headers:0,height:0,hidden:HAS_BOOLEAN_VALUE,high:0,href:0,hrefLang:0,htmlFor:0,httpEquiv:0,icon:0,id:0,inputMode:0,integrity:0,is:0,keyParams:0,keyType:0,kind:0,label:0,lang:0,list:0,loop:HAS_BOOLEAN_VALUE,low:0,manifest:0,marginHeight:0,marginWidth:0,max:0,maxLength:0,media:0,mediaGroup:0,method:0,min:0,minLength:0,multiple:MUST_USE_PROPERTY|HAS_BOOLEAN_VALUE,muted:MUST_USE_PROPERTY|HAS_BOOLEAN_VALUE,name:0,nonce:0,noValidate:HAS_BOOLEAN_VALUE,open:HAS_BOOLEAN_VALUE,optimum:0,pattern:0,placeholder:0,playsInline:HAS_BOOLEAN_VALUE,poster:0,preload:0,profile:0,radioGroup:0,readOnly:HAS_BOOLEAN_VALUE,referrerPolicy:0,rel:0,required:HAS_BOOLEAN_VALUE,reversed:HAS_BOOLEAN_VALUE,role:0,rows:HAS_POSITIVE_NUMERIC_VALUE,rowSpan:HAS_NUMERIC_VALUE,sandbox:0,scope:0,scoped:HAS_BOOLEAN_VALUE,scrolling:0,seamless:HAS_BOOLEAN_VALUE,selected:MUST_USE_PROPERTY|HAS_BOOLEAN_VALUE,shape:0,size:HAS_POSITIVE_NUMERIC_VALUE,sizes:0,span:HAS_POSITIVE_NUMERIC_VALUE,spellCheck:0,src:0,srcDoc:0,srcLang:0,srcSet:0,start:HAS_NUMERIC_VALUE,step:0,style:0,summary:0,tabIndex:0,target:0,title:0,type:0,useMap:0,value:0,width:0,wmode:0,wrap:0,about:0,datatype:0,inlist:0,prefix:0,property:0,resource:0,typeof:0,vocab:0,autoCapitalize:0,autoCorrect:0,autoSave:0,color:0,itemProp:0,itemScope:HAS_BOOLEAN_VALUE,itemType:0,itemID:0,itemRef:0,results:0,security:0,unselectable:0},DOMAttributeNames:{acceptCharset:"accept-charset",className:"class",htmlFor:"for",httpEquiv:"http-equiv"},DOMPropertyNames:{},DOMMutationMethods:{value:function(node,value){if(value==null){return node.removeAttribute("value")}if(node.type!=="number"||node.hasAttribute("value")===false){node.setAttribute("value",""+value)}else if(node.validity&&!node.validity.badInput&&node.ownerDocument.activeElement!==node){node.setAttribute("value",""+value)}}}};module.exports=HTMLDOMPropertyConfig},{"./DOMProperty":42}],53:[function(require,module,exports){"use strict";function escape(key){var escapeRegex=/[=:]/g;var escaperLookup={"=":"=0",":":"=2"};var escapedString=(""+key).replace(escapeRegex,function(match){return escaperLookup[match]});return"$"+escapedString}function unescape(key){var unescapeRegex=/(=0|=2)/g;var unescaperLookup={"=0":"=","=2":":"};var keySubstring=key[0]==="."&&key[1]==="$"?key.substring(2):key.substring(1);return(""+keySubstring).replace(unescapeRegex,function(match){return unescaperLookup[match]})}var KeyEscapeUtils={escape:escape,unescape:unescape};module.exports=KeyEscapeUtils},{}],54:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactPropTypesSecret=require("./ReactPropTypesSecret");var propTypesFactory=require("prop-types/factory");var React=require("react/lib/React");var PropTypes=propTypesFactory(React.isValidElement);var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var hasReadOnlyValue={button:true,checkbox:true,image:true,hidden:true,radio:true,reset:true,submit:true};function _assertSingleLink(inputProps){!(inputProps.checkedLink==null||inputProps.valueLink==null)?process.env.NODE_ENV!=="production"?invariant(false,"Cannot provide a checkedLink and a valueLink. If you want to use checkedLink, you probably don't want to use valueLink and vice versa."):_prodInvariant("87"):void 0}function _assertValueLink(inputProps){_assertSingleLink(inputProps);!(inputProps.value==null&&inputProps.onChange==null)?process.env.NODE_ENV!=="production"?invariant(false,"Cannot provide a valueLink and a value or onChange event. If you want to use value or onChange, you probably don't want to use valueLink."):_prodInvariant("88"):void 0}function _assertCheckedLink(inputProps){_assertSingleLink(inputProps);!(inputProps.checked==null&&inputProps.onChange==null)?process.env.NODE_ENV!=="production"?invariant(false,"Cannot provide a checkedLink and a checked property or onChange event. If you want to use checked or onChange, you probably don't want to use checkedLink"):_prodInvariant("89"):void 0}var propTypes={value:function(props,propName,componentName){if(!props[propName]||hasReadOnlyValue[props.type]||props.onChange||props.readOnly||props.disabled){return null}return new Error("You provided a `value` prop to a form field without an "+"`onChange` handler. This will render a read-only field. If "+"the field should be mutable use `defaultValue`. Otherwise, "+"set either `onChange` or `readOnly`.")},checked:function(props,propName,componentName){if(!props[propName]||props.onChange||props.readOnly||props.disabled){return null}return new Error("You provided a `checked` prop to a form field without an "+"`onChange` handler. This will render a read-only field. If "+"the field should be mutable use `defaultChecked`. Otherwise, "+"set either `onChange` or `readOnly`.")},onChange:PropTypes.func};var loggedTypeFailures={};function getDeclarationErrorAddendum(owner){if(owner){var name=owner.getName();if(name){return" Check the render method of `"+name+"`."}}return""}var LinkedValueUtils={checkPropTypes:function(tagName,props,owner){for(var propName in propTypes){if(propTypes.hasOwnProperty(propName)){var error=propTypes[propName](props,propName,tagName,"prop",null,ReactPropTypesSecret)}if(error instanceof Error&&!(error.message in loggedTypeFailures)){loggedTypeFailures[error.message]=true;var addendum=getDeclarationErrorAddendum(owner);process.env.NODE_ENV!=="production"?warning(false,"Failed form propType: %s%s",error.message,addendum):void 0}}},getValue:function(inputProps){if(inputProps.valueLink){_assertValueLink(inputProps);return inputProps.valueLink.value}return inputProps.value},getChecked:function(inputProps){if(inputProps.checkedLink){_assertCheckedLink(inputProps);return inputProps.checkedLink.value}return inputProps.checked},executeOnChange:function(inputProps,event){if(inputProps.valueLink){_assertValueLink(inputProps);return inputProps.valueLink.requestChange(event.target.value)}else if(inputProps.checkedLink){_assertCheckedLink(inputProps);return inputProps.checkedLink.requestChange(event.target.checked)}else if(inputProps.onChange){return inputProps.onChange.call(undefined,event)}}};module.exports=LinkedValueUtils}).call(this,require("_process"))},{"./ReactPropTypesSecret":101,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"prop-types/factory":28,"react/lib/React":160}],55:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");var oneArgumentPooler=function(copyFieldsFrom){var Klass=this;if(Klass.instancePool.length){var instance=Klass.instancePool.pop();Klass.call(instance,copyFieldsFrom);return instance}else{return new Klass(copyFieldsFrom)}};var twoArgumentPooler=function(a1,a2){var Klass=this;if(Klass.instancePool.length){var instance=Klass.instancePool.pop();Klass.call(instance,a1,a2);return instance}else{return new Klass(a1,a2)}};var threeArgumentPooler=function(a1,a2,a3){var Klass=this;if(Klass.instancePool.length){var instance=Klass.instancePool.pop();Klass.call(instance,a1,a2,a3);return instance}else{return new Klass(a1,a2,a3)}};var fourArgumentPooler=function(a1,a2,a3,a4){var Klass=this;if(Klass.instancePool.length){var instance=Klass.instancePool.pop();Klass.call(instance,a1,a2,a3,a4);return instance}else{return new Klass(a1,a2,a3,a4)}};var standardReleaser=function(instance){var Klass=this;!(instance instanceof Klass)?process.env.NODE_ENV!=="production"?invariant(false,"Trying to release an instance into a pool of a different type."):_prodInvariant("25"):void 0;instance.destructor();if(Klass.instancePool.length<Klass.poolSize){Klass.instancePool.push(instance)}};var DEFAULT_POOL_SIZE=10;var DEFAULT_POOLER=oneArgumentPooler;var addPoolingTo=function(CopyConstructor,pooler){var NewKlass=CopyConstructor;NewKlass.instancePool=[];NewKlass.getPooled=pooler||DEFAULT_POOLER;if(!NewKlass.poolSize){NewKlass.poolSize=DEFAULT_POOL_SIZE}NewKlass.release=standardReleaser;return NewKlass};var PooledClass={addPoolingTo:addPoolingTo,oneArgumentPooler:oneArgumentPooler,twoArgumentPooler:twoArgumentPooler,threeArgumentPooler:threeArgumentPooler,fourArgumentPooler:fourArgumentPooler};module.exports=PooledClass}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],56:[function(require,module,exports){"use strict";var _assign=require("object-assign");var EventPluginRegistry=require("./EventPluginRegistry");var ReactEventEmitterMixin=require("./ReactEventEmitterMixin");var ViewportMetrics=require("./ViewportMetrics");var getVendorPrefixedEventName=require("./getVendorPrefixedEventName");var isEventSupported=require("./isEventSupported");var hasEventPageXY;var alreadyListeningTo={};var isMonitoringScrollValue=false;var reactTopListenersCounter=0;var topEventMapping={topAbort:"abort",topAnimationEnd:getVendorPrefixedEventName("animationend")||"animationend",topAnimationIteration:getVendorPrefixedEventName("animationiteration")||"animationiteration",topAnimationStart:getVendorPrefixedEventName("animationstart")||"animationstart",topBlur:"blur",topCanPlay:"canplay",topCanPlayThrough:"canplaythrough",topChange:"change",topClick:"click",topCompositionEnd:"compositionend",topCompositionStart:"compositionstart",topCompositionUpdate:"compositionupdate",topContextMenu:"contextmenu",topCopy:"copy",topCut:"cut",topDoubleClick:"dblclick",topDrag:"drag",topDragEnd:"dragend",topDragEnter:"dragenter",topDragExit:"dragexit",topDragLeave:"dragleave",topDragOver:"dragover",topDragStart:"dragstart",topDrop:"drop",topDurationChange:"durationchange",topEmptied:"emptied",topEncrypted:"encrypted",topEnded:"ended",topError:"error",topFocus:"focus",topInput:"input",topKeyDown:"keydown",topKeyPress:"keypress",topKeyUp:"keyup",topLoadedData:"loadeddata",topLoadedMetadata:"loadedmetadata",topLoadStart:"loadstart",topMouseDown:"mousedown",topMouseMove:"mousemove",topMouseOut:"mouseout",topMouseOver:"mouseover",topMouseUp:"mouseup",topPaste:"paste",topPause:"pause",topPlay:"play",topPlaying:"playing",topProgress:"progress",topRateChange:"ratechange",topScroll:"scroll",topSeeked:"seeked",topSeeking:"seeking",topSelectionChange:"selectionchange",topStalled:"stalled",topSuspend:"suspend",topTextInput:"textInput",topTimeUpdate:"timeupdate",topTouchCancel:"touchcancel",topTouchEnd:"touchend",topTouchMove:"touchmove",topTouchStart:"touchstart",topTransitionEnd:getVendorPrefixedEventName("transitionend")||"transitionend",topVolumeChange:"volumechange",topWaiting:"waiting",topWheel:"wheel"};var topListenersIDKey="_reactListenersID"+String(Math.random()).slice(2);function getListeningForDocument(mountAt){if(!Object.prototype.hasOwnProperty.call(mountAt,topListenersIDKey)){mountAt[topListenersIDKey]=reactTopListenersCounter++;alreadyListeningTo[mountAt[topListenersIDKey]]={}}return alreadyListeningTo[mountAt[topListenersIDKey]]}var ReactBrowserEventEmitter=_assign({},ReactEventEmitterMixin,{ReactEventListener:null,injection:{injectReactEventListener:function(ReactEventListener){ReactEventListener.setHandleTopLevel(ReactBrowserEventEmitter.handleTopLevel);ReactBrowserEventEmitter.ReactEventListener=ReactEventListener}},setEnabled:function(enabled){if(ReactBrowserEventEmitter.ReactEventListener){ReactBrowserEventEmitter.ReactEventListener.setEnabled(enabled)}},isEnabled:function(){return!!(ReactBrowserEventEmitter.ReactEventListener&&ReactBrowserEventEmitter.ReactEventListener.isEnabled())},listenTo:function(registrationName,contentDocumentHandle){var mountAt=contentDocumentHandle;var isListening=getListeningForDocument(mountAt);var dependencies=EventPluginRegistry.registrationNameDependencies[registrationName];for(var i=0;i<dependencies.length;i++){var dependency=dependencies[i];if(!(isListening.hasOwnProperty(dependency)&&isListening[dependency])){if(dependency==="topWheel"){if(isEventSupported("wheel")){ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topWheel","wheel",mountAt)}else if(isEventSupported("mousewheel")){ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topWheel","mousewheel",mountAt)}else{ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topWheel","DOMMouseScroll",mountAt)}}else if(dependency==="topScroll"){if(isEventSupported("scroll",true)){ReactBrowserEventEmitter.ReactEventListener.trapCapturedEvent("topScroll","scroll",mountAt)}else{ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topScroll","scroll",ReactBrowserEventEmitter.ReactEventListener.WINDOW_HANDLE)}}else if(dependency==="topFocus"||dependency==="topBlur"){if(isEventSupported("focus",true)){ReactBrowserEventEmitter.ReactEventListener.trapCapturedEvent("topFocus","focus",mountAt);ReactBrowserEventEmitter.ReactEventListener.trapCapturedEvent("topBlur","blur",mountAt)}else if(isEventSupported("focusin")){ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topFocus","focusin",mountAt);ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent("topBlur","focusout",mountAt)}isListening.topBlur=true;isListening.topFocus=true}else if(topEventMapping.hasOwnProperty(dependency)){ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent(dependency,topEventMapping[dependency],mountAt)}isListening[dependency]=true}}},trapBubbledEvent:function(topLevelType,handlerBaseName,handle){return ReactBrowserEventEmitter.ReactEventListener.trapBubbledEvent(topLevelType,handlerBaseName,handle)},trapCapturedEvent:function(topLevelType,handlerBaseName,handle){return ReactBrowserEventEmitter.ReactEventListener.trapCapturedEvent(topLevelType,handlerBaseName,handle)},supportsEventPageXY:function(){if(!document.createEvent){return false}var ev=document.createEvent("MouseEvent");return ev!=null&&"pageX"in ev},ensureScrollValueMonitoring:function(){if(hasEventPageXY===undefined){hasEventPageXY=ReactBrowserEventEmitter.supportsEventPageXY()}if(!hasEventPageXY&&!isMonitoringScrollValue){var refresh=ViewportMetrics.refreshScrollValues;ReactBrowserEventEmitter.ReactEventListener.monitorScrollValue(refresh);isMonitoringScrollValue=true}}});module.exports=ReactBrowserEventEmitter},{"./EventPluginRegistry":48,"./ReactEventEmitterMixin":85,"./ViewportMetrics":127,"./getVendorPrefixedEventName":145,"./isEventSupported":148,"object-assign":26}],57:[function(require,module,exports){(function(process){"use strict";var ReactReconciler=require("./ReactReconciler");var instantiateReactComponent=require("./instantiateReactComponent");var KeyEscapeUtils=require("./KeyEscapeUtils");var shouldUpdateReactComponent=require("./shouldUpdateReactComponent");var traverseAllChildren=require("./traverseAllChildren");var warning=require("fbjs/lib/warning");var ReactComponentTreeHook;if(typeof process!=="undefined"&&process.env&&process.env.NODE_ENV==="test"){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}function instantiateChild(childInstances,child,name,selfDebugID){var keyUnique=childInstances[name]===undefined;if(process.env.NODE_ENV!=="production"){if(!ReactComponentTreeHook){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}if(!keyUnique){process.env.NODE_ENV!=="production"?warning(false,"flattenChildren(...): Encountered two children with the same key, "+"`%s`. Child keys must be unique; when two children share a key, only "+"the first child will be used.%s",KeyEscapeUtils.unescape(name),ReactComponentTreeHook.getStackAddendumByID(selfDebugID)):void 0}}if(child!=null&&keyUnique){childInstances[name]=instantiateReactComponent(child,true)}}var ReactChildReconciler={instantiateChildren:function(nestedChildNodes,transaction,context,selfDebugID){if(nestedChildNodes==null){return null}var childInstances={};if(process.env.NODE_ENV!=="production"){traverseAllChildren(nestedChildNodes,function(childInsts,child,name){return instantiateChild(childInsts,child,name,selfDebugID)},childInstances)}else{traverseAllChildren(nestedChildNodes,instantiateChild,childInstances)}return childInstances},updateChildren:function(prevChildren,nextChildren,mountImages,removedNodes,transaction,hostParent,hostContainerInfo,context,selfDebugID){if(!nextChildren&&!prevChildren){return}var name;var prevChild;for(name in nextChildren){if(!nextChildren.hasOwnProperty(name)){continue}prevChild=prevChildren&&prevChildren[name];var prevElement=prevChild&&prevChild._currentElement;var nextElement=nextChildren[name];if(prevChild!=null&&shouldUpdateReactComponent(prevElement,nextElement)){ReactReconciler.receiveComponent(prevChild,nextElement,transaction,context);nextChildren[name]=prevChild}else{if(prevChild){removedNodes[name]=ReactReconciler.getHostNode(prevChild);ReactReconciler.unmountComponent(prevChild,false)}var nextChildInstance=instantiateReactComponent(nextElement,true);nextChildren[name]=nextChildInstance;var nextChildMountImage=ReactReconciler.mountComponent(nextChildInstance,transaction,hostParent,hostContainerInfo,context,selfDebugID);mountImages.push(nextChildMountImage)}}for(name in prevChildren){if(prevChildren.hasOwnProperty(name)&&!(nextChildren&&nextChildren.hasOwnProperty(name))){prevChild=prevChildren[name];removedNodes[name]=ReactReconciler.getHostNode(prevChild);ReactReconciler.unmountComponent(prevChild,false)}}},unmountChildren:function(renderedChildren,safely){for(var name in renderedChildren){if(renderedChildren.hasOwnProperty(name)){var renderedChild=renderedChildren[name];ReactReconciler.unmountComponent(renderedChild,safely)}}}};module.exports=ReactChildReconciler}).call(this,require("_process"))},{"./KeyEscapeUtils":53,"./ReactReconciler":103,"./instantiateReactComponent":147,"./shouldUpdateReactComponent":155,"./traverseAllChildren":156,_process:184,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],58:[function(require,module,exports){"use strict";var DOMChildrenOperations=require("./DOMChildrenOperations");var ReactDOMIDOperations=require("./ReactDOMIDOperations");var ReactComponentBrowserEnvironment={processChildrenUpdates:ReactDOMIDOperations.dangerouslyProcessChildrenUpdates,replaceNodeWithMarkup:DOMChildrenOperations.dangerouslyReplaceNodeWithMarkup};module.exports=ReactComponentBrowserEnvironment},{"./DOMChildrenOperations":39,"./ReactDOMIDOperations":68}],59:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");var injected=false;var ReactComponentEnvironment={replaceNodeWithMarkup:null,processChildrenUpdates:null,injection:{injectEnvironment:function(environment){!!injected?process.env.NODE_ENV!=="production"?invariant(false,"ReactCompositeComponent: injectEnvironment() can only be called once."):_prodInvariant("104"):void 0;ReactComponentEnvironment.replaceNodeWithMarkup=environment.replaceNodeWithMarkup;ReactComponentEnvironment.processChildrenUpdates=environment.processChildrenUpdates;injected=true}}};module.exports=ReactComponentEnvironment}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],60:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var React=require("react/lib/React");var ReactComponentEnvironment=require("./ReactComponentEnvironment");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var ReactErrorUtils=require("./ReactErrorUtils");var ReactInstanceMap=require("./ReactInstanceMap");var ReactInstrumentation=require("./ReactInstrumentation");var ReactNodeTypes=require("./ReactNodeTypes");var ReactReconciler=require("./ReactReconciler");if(process.env.NODE_ENV!=="production"){var checkReactTypeSpec=require("./checkReactTypeSpec")}var emptyObject=require("fbjs/lib/emptyObject");var invariant=require("fbjs/lib/invariant");var shallowEqual=require("fbjs/lib/shallowEqual");var shouldUpdateReactComponent=require("./shouldUpdateReactComponent");var warning=require("fbjs/lib/warning");var CompositeTypes={ImpureClass:0,PureClass:1,StatelessFunctional:2};function StatelessComponent(Component){}StatelessComponent.prototype.render=function(){var Component=ReactInstanceMap.get(this)._currentElement.type;var element=Component(this.props,this.context,this.updater);warnIfInvalidElement(Component,element);return element};function warnIfInvalidElement(Component,element){if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(element===null||element===false||React.isValidElement(element),"%s(...): A valid React element (or null) must be returned. You may have "+"returned undefined, an array or some other invalid object.",Component.displayName||Component.name||"Component"):void 0;process.env.NODE_ENV!=="production"?warning(!Component.childContextTypes,"%s(...): childContextTypes cannot be defined on a functional component.",Component.displayName||Component.name||"Component"):void 0}}function shouldConstruct(Component){return!!(Component.prototype&&Component.prototype.isReactComponent)}function isPureComponent(Component){return!!(Component.prototype&&Component.prototype.isPureReactComponent)}function measureLifeCyclePerf(fn,debugID,timerType){if(debugID===0){return fn()}ReactInstrumentation.debugTool.onBeginLifeCycleTimer(debugID,timerType);try{return fn()}finally{ReactInstrumentation.debugTool.onEndLifeCycleTimer(debugID,timerType)}}var nextMountID=1;var ReactCompositeComponent={construct:function(element){this._currentElement=element;this._rootNodeID=0;this._compositeType=null;this._instance=null;this._hostParent=null;this._hostContainerInfo=null;this._updateBatchNumber=null;this._pendingElement=null;this._pendingStateQueue=null;this._pendingReplaceState=false;this._pendingForceUpdate=false;this._renderedNodeType=null;this._renderedComponent=null;this._context=null;this._mountOrder=0;this._topLevelWrapper=null;this._pendingCallbacks=null;this._calledComponentWillUnmount=false;if(process.env.NODE_ENV!=="production"){this._warnedAboutRefsInRender=false}},mountComponent:function(transaction,hostParent,hostContainerInfo,context){var _this=this;this._context=context;this._mountOrder=nextMountID++;this._hostParent=hostParent;this._hostContainerInfo=hostContainerInfo;var publicProps=this._currentElement.props;var publicContext=this._processContext(context);var Component=this._currentElement.type;var updateQueue=transaction.getUpdateQueue();var doConstruct=shouldConstruct(Component);var inst=this._constructComponent(doConstruct,publicProps,publicContext,updateQueue);var renderedElement;if(!doConstruct&&(inst==null||inst.render==null)){renderedElement=inst;warnIfInvalidElement(Component,renderedElement);!(inst===null||inst===false||React.isValidElement(inst))?process.env.NODE_ENV!=="production"?invariant(false,"%s(...): A valid React element (or null) must be returned. You may have returned undefined, an array or some other invalid object.",Component.displayName||Component.name||"Component"):_prodInvariant("105",Component.displayName||Component.name||"Component"):void 0;inst=new StatelessComponent(Component);this._compositeType=CompositeTypes.StatelessFunctional}else{if(isPureComponent(Component)){this._compositeType=CompositeTypes.PureClass}else{this._compositeType=CompositeTypes.ImpureClass}}if(process.env.NODE_ENV!=="production"){if(inst.render==null){process.env.NODE_ENV!=="production"?warning(false,"%s(...): No `render` method found on the returned component "+"instance: you may have forgotten to define `render`.",Component.displayName||Component.name||"Component"):void 0}var propsMutated=inst.props!==publicProps;var componentName=Component.displayName||Component.name||"Component";process.env.NODE_ENV!=="production"?warning(inst.props===undefined||!propsMutated,"%s(...): When calling super() in `%s`, make sure to pass "+"up the same props that your component's constructor was passed.",componentName,componentName):void 0}inst.props=publicProps;inst.context=publicContext;inst.refs=emptyObject;inst.updater=updateQueue;this._instance=inst;ReactInstanceMap.set(inst,this);if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(!inst.getInitialState||inst.getInitialState.isReactClassApproved||inst.state,"getInitialState was defined on %s, a plain JavaScript class. "+"This is only supported for classes created using React.createClass. "+"Did you mean to define a state property instead?",this.getName()||"a component"):void 0;process.env.NODE_ENV!=="production"?warning(!inst.getDefaultProps||inst.getDefaultProps.isReactClassApproved,"getDefaultProps was defined on %s, a plain JavaScript class. "+"This is only supported for classes created using React.createClass. "+"Use a static property to define defaultProps instead.",this.getName()||"a component"):void 0;process.env.NODE_ENV!=="production"?warning(!inst.propTypes,"propTypes was defined as an instance property on %s. Use a static "+"property to define propTypes instead.",this.getName()||"a component"):void 0;process.env.NODE_ENV!=="production"?warning(!inst.contextTypes,"contextTypes was defined as an instance property on %s. Use a "+"static property to define contextTypes instead.",this.getName()||"a component"):void 0;process.env.NODE_ENV!=="production"?warning(typeof inst.componentShouldUpdate!=="function","%s has a method called "+"componentShouldUpdate(). Did you mean shouldComponentUpdate()? "+"The name is phrased as a question because the function is "+"expected to return a value.",this.getName()||"A component"):void 0;process.env.NODE_ENV!=="production"?warning(typeof inst.componentDidUnmount!=="function","%s has a method called "+"componentDidUnmount(). But there is no such lifecycle method. "+"Did you mean componentWillUnmount()?",this.getName()||"A component"):void 0;process.env.NODE_ENV!=="production"?warning(typeof inst.componentWillRecieveProps!=="function","%s has a method called "+"componentWillRecieveProps(). Did you mean componentWillReceiveProps()?",this.getName()||"A component"):void 0}var initialState=inst.state;if(initialState===undefined){inst.state=initialState=null}!(typeof initialState==="object"&&!Array.isArray(initialState))?process.env.NODE_ENV!=="production"?invariant(false,"%s.state: must be set to an object or null",this.getName()||"ReactCompositeComponent"):_prodInvariant("106",this.getName()||"ReactCompositeComponent"):void 0;this._pendingStateQueue=null;this._pendingReplaceState=false;this._pendingForceUpdate=false;var markup;if(inst.unstable_handleError){markup=this.performInitialMountWithErrorHandling(renderedElement,hostParent,hostContainerInfo,transaction,context)}else{markup=this.performInitialMount(renderedElement,hostParent,hostContainerInfo,transaction,context)}if(inst.componentDidMount){if(process.env.NODE_ENV!=="production"){transaction.getReactMountReady().enqueue(function(){measureLifeCyclePerf(function(){return inst.componentDidMount()},_this._debugID,"componentDidMount")})}else{transaction.getReactMountReady().enqueue(inst.componentDidMount,inst)}}return markup},_constructComponent:function(doConstruct,publicProps,publicContext,updateQueue){if(process.env.NODE_ENV!=="production"){ReactCurrentOwner.current=this;try{return this._constructComponentWithoutOwner(doConstruct,publicProps,publicContext,updateQueue)}finally{ReactCurrentOwner.current=null}}else{return this._constructComponentWithoutOwner(doConstruct,publicProps,publicContext,updateQueue)}},_constructComponentWithoutOwner:function(doConstruct,publicProps,publicContext,updateQueue){var Component=this._currentElement.type;if(doConstruct){if(process.env.NODE_ENV!=="production"){return measureLifeCyclePerf(function(){return new Component(publicProps,publicContext,updateQueue)},this._debugID,"ctor")}else{return new Component(publicProps,publicContext,updateQueue)}}if(process.env.NODE_ENV!=="production"){return measureLifeCyclePerf(function(){return Component(publicProps,publicContext,updateQueue)},this._debugID,"render")}else{return Component(publicProps,publicContext,updateQueue)}},performInitialMountWithErrorHandling:function(renderedElement,hostParent,hostContainerInfo,transaction,context){var markup;var checkpoint=transaction.checkpoint();try{markup=this.performInitialMount(renderedElement,hostParent,hostContainerInfo,transaction,context)}catch(e){transaction.rollback(checkpoint);this._instance.unstable_handleError(e);if(this._pendingStateQueue){this._instance.state=this._processPendingState(this._instance.props,this._instance.context)}checkpoint=transaction.checkpoint();this._renderedComponent.unmountComponent(true);transaction.rollback(checkpoint);markup=this.performInitialMount(renderedElement,hostParent,hostContainerInfo,transaction,context)}return markup},performInitialMount:function(renderedElement,hostParent,hostContainerInfo,transaction,context){var inst=this._instance;var debugID=0;if(process.env.NODE_ENV!=="production"){debugID=this._debugID}if(inst.componentWillMount){if(process.env.NODE_ENV!=="production"){measureLifeCyclePerf(function(){return inst.componentWillMount()},debugID,"componentWillMount")}else{inst.componentWillMount()}if(this._pendingStateQueue){inst.state=this._processPendingState(inst.props,inst.context)}}if(renderedElement===undefined){renderedElement=this._renderValidatedComponent()}var nodeType=ReactNodeTypes.getType(renderedElement);this._renderedNodeType=nodeType;var child=this._instantiateReactComponent(renderedElement,nodeType!==ReactNodeTypes.EMPTY);this._renderedComponent=child;var markup=ReactReconciler.mountComponent(child,transaction,hostParent,hostContainerInfo,this._processChildContext(context),debugID);if(process.env.NODE_ENV!=="production"){if(debugID!==0){var childDebugIDs=child._debugID!==0?[child._debugID]:[];ReactInstrumentation.debugTool.onSetChildren(debugID,childDebugIDs)}}return markup},getHostNode:function(){return ReactReconciler.getHostNode(this._renderedComponent)},unmountComponent:function(safely){if(!this._renderedComponent){return}var inst=this._instance;if(inst.componentWillUnmount&&!inst._calledComponentWillUnmount){inst._calledComponentWillUnmount=true;if(safely){var name=this.getName()+".componentWillUnmount()";ReactErrorUtils.invokeGuardedCallback(name,inst.componentWillUnmount.bind(inst))}else{if(process.env.NODE_ENV!=="production"){measureLifeCyclePerf(function(){return inst.componentWillUnmount()},this._debugID,"componentWillUnmount")}else{inst.componentWillUnmount()}}}if(this._renderedComponent){ReactReconciler.unmountComponent(this._renderedComponent,safely);this._renderedNodeType=null;this._renderedComponent=null;this._instance=null}this._pendingStateQueue=null;this._pendingReplaceState=false;this._pendingForceUpdate=false;this._pendingCallbacks=null;this._pendingElement=null;this._context=null;this._rootNodeID=0;this._topLevelWrapper=null;ReactInstanceMap.remove(inst)},_maskContext:function(context){var Component=this._currentElement.type;var contextTypes=Component.contextTypes;if(!contextTypes){return emptyObject}var maskedContext={};for(var contextName in contextTypes){maskedContext[contextName]=context[contextName]}return maskedContext},_processContext:function(context){var maskedContext=this._maskContext(context);if(process.env.NODE_ENV!=="production"){var Component=this._currentElement.type;if(Component.contextTypes){this._checkContextTypes(Component.contextTypes,maskedContext,"context")}}return maskedContext},_processChildContext:function(currentContext){var Component=this._currentElement.type;var inst=this._instance;var childContext;if(inst.getChildContext){if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onBeginProcessingChildContext();try{childContext=inst.getChildContext()}finally{ReactInstrumentation.debugTool.onEndProcessingChildContext()}}else{childContext=inst.getChildContext()}}if(childContext){!(typeof Component.childContextTypes==="object")?process.env.NODE_ENV!=="production"?invariant(false,"%s.getChildContext(): childContextTypes must be defined in order to use getChildContext().",this.getName()||"ReactCompositeComponent"):_prodInvariant("107",this.getName()||"ReactCompositeComponent"):void 0;if(process.env.NODE_ENV!=="production"){this._checkContextTypes(Component.childContextTypes,childContext,"child context")}for(var name in childContext){!(name in Component.childContextTypes)?process.env.NODE_ENV!=="production"?invariant(false,'%s.getChildContext(): key "%s" is not defined in childContextTypes.',this.getName()||"ReactCompositeComponent",name):_prodInvariant("108",this.getName()||"ReactCompositeComponent",name):void 0}return _assign({},currentContext,childContext)}return currentContext},_checkContextTypes:function(typeSpecs,values,location){if(process.env.NODE_ENV!=="production"){checkReactTypeSpec(typeSpecs,values,location,this.getName(),null,this._debugID)}},receiveComponent:function(nextElement,transaction,nextContext){var prevElement=this._currentElement;var prevContext=this._context;this._pendingElement=null;this.updateComponent(transaction,prevElement,nextElement,prevContext,nextContext)},performUpdateIfNecessary:function(transaction){if(this._pendingElement!=null){ReactReconciler.receiveComponent(this,this._pendingElement,transaction,this._context)}else if(this._pendingStateQueue!==null||this._pendingForceUpdate){this.updateComponent(transaction,this._currentElement,this._currentElement,this._context,this._context)}else{this._updateBatchNumber=null}},updateComponent:function(transaction,prevParentElement,nextParentElement,prevUnmaskedContext,nextUnmaskedContext){var inst=this._instance;!(inst!=null)?process.env.NODE_ENV!=="production"?invariant(false,"Attempted to update component `%s` that has already been unmounted (or failed to mount).",this.getName()||"ReactCompositeComponent"):_prodInvariant("136",this.getName()||"ReactCompositeComponent"):void 0;var willReceive=false;var nextContext;if(this._context===nextUnmaskedContext){nextContext=inst.context}else{nextContext=this._processContext(nextUnmaskedContext);willReceive=true}var prevProps=prevParentElement.props;var nextProps=nextParentElement.props;if(prevParentElement!==nextParentElement){willReceive=true}if(willReceive&&inst.componentWillReceiveProps){if(process.env.NODE_ENV!=="production"){measureLifeCyclePerf(function(){return inst.componentWillReceiveProps(nextProps,nextContext)},this._debugID,"componentWillReceiveProps")}else{inst.componentWillReceiveProps(nextProps,nextContext)}}var nextState=this._processPendingState(nextProps,nextContext);var shouldUpdate=true;if(!this._pendingForceUpdate){if(inst.shouldComponentUpdate){if(process.env.NODE_ENV!=="production"){shouldUpdate=measureLifeCyclePerf(function(){return inst.shouldComponentUpdate(nextProps,nextState,nextContext)},this._debugID,"shouldComponentUpdate")}else{shouldUpdate=inst.shouldComponentUpdate(nextProps,nextState,nextContext)}}else{if(this._compositeType===CompositeTypes.PureClass){shouldUpdate=!shallowEqual(prevProps,nextProps)||!shallowEqual(inst.state,nextState)}}}if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(shouldUpdate!==undefined,"%s.shouldComponentUpdate(): Returned undefined instead of a "+"boolean value. Make sure to return true or false.",this.getName()||"ReactCompositeComponent"):void 0}this._updateBatchNumber=null;if(shouldUpdate){this._pendingForceUpdate=false;this._performComponentUpdate(nextParentElement,nextProps,nextState,nextContext,transaction,nextUnmaskedContext)}else{this._currentElement=nextParentElement;this._context=nextUnmaskedContext;inst.props=nextProps;inst.state=nextState;inst.context=nextContext}},_processPendingState:function(props,context){var inst=this._instance;var queue=this._pendingStateQueue;var replace=this._pendingReplaceState;this._pendingReplaceState=false;this._pendingStateQueue=null;if(!queue){return inst.state}if(replace&&queue.length===1){return queue[0]}var nextState=_assign({},replace?queue[0]:inst.state);for(var i=replace?1:0;i<queue.length;i++){var partial=queue[i];_assign(nextState,typeof partial==="function"?partial.call(inst,nextState,props,context):partial)}return nextState},_performComponentUpdate:function(nextElement,nextProps,nextState,nextContext,transaction,unmaskedContext){var _this2=this;var inst=this._instance;var hasComponentDidUpdate=Boolean(inst.componentDidUpdate);var prevProps;var prevState;var prevContext;if(hasComponentDidUpdate){prevProps=inst.props;prevState=inst.state;prevContext=inst.context}if(inst.componentWillUpdate){if(process.env.NODE_ENV!=="production"){measureLifeCyclePerf(function(){return inst.componentWillUpdate(nextProps,nextState,nextContext)},this._debugID,"componentWillUpdate")}else{inst.componentWillUpdate(nextProps,nextState,nextContext)}}this._currentElement=nextElement;this._context=unmaskedContext;inst.props=nextProps;inst.state=nextState;inst.context=nextContext;this._updateRenderedComponent(transaction,unmaskedContext);if(hasComponentDidUpdate){if(process.env.NODE_ENV!=="production"){transaction.getReactMountReady().enqueue(function(){measureLifeCyclePerf(inst.componentDidUpdate.bind(inst,prevProps,prevState,prevContext),_this2._debugID,"componentDidUpdate")})}else{transaction.getReactMountReady().enqueue(inst.componentDidUpdate.bind(inst,prevProps,prevState,prevContext),inst)}}},_updateRenderedComponent:function(transaction,context){var prevComponentInstance=this._renderedComponent;var prevRenderedElement=prevComponentInstance._currentElement;var nextRenderedElement=this._renderValidatedComponent();var debugID=0;if(process.env.NODE_ENV!=="production"){debugID=this._debugID}if(shouldUpdateReactComponent(prevRenderedElement,nextRenderedElement)){ReactReconciler.receiveComponent(prevComponentInstance,nextRenderedElement,transaction,this._processChildContext(context))}else{var oldHostNode=ReactReconciler.getHostNode(prevComponentInstance);ReactReconciler.unmountComponent(prevComponentInstance,false);var nodeType=ReactNodeTypes.getType(nextRenderedElement);this._renderedNodeType=nodeType;var child=this._instantiateReactComponent(nextRenderedElement,nodeType!==ReactNodeTypes.EMPTY);this._renderedComponent=child;var nextMarkup=ReactReconciler.mountComponent(child,transaction,this._hostParent,this._hostContainerInfo,this._processChildContext(context),debugID);if(process.env.NODE_ENV!=="production"){if(debugID!==0){var childDebugIDs=child._debugID!==0?[child._debugID]:[];ReactInstrumentation.debugTool.onSetChildren(debugID,childDebugIDs)}}this._replaceNodeWithMarkup(oldHostNode,nextMarkup,prevComponentInstance)}},_replaceNodeWithMarkup:function(oldHostNode,nextMarkup,prevInstance){ReactComponentEnvironment.replaceNodeWithMarkup(oldHostNode,nextMarkup,prevInstance)},_renderValidatedComponentWithoutOwnerOrContext:function(){var inst=this._instance;var renderedElement;if(process.env.NODE_ENV!=="production"){renderedElement=measureLifeCyclePerf(function(){return inst.render()},this._debugID,"render")}else{renderedElement=inst.render()}if(process.env.NODE_ENV!=="production"){if(renderedElement===undefined&&inst.render._isMockFunction){renderedElement=null}}return renderedElement},_renderValidatedComponent:function(){var renderedElement;if(process.env.NODE_ENV!=="production"||this._compositeType!==CompositeTypes.StatelessFunctional){ReactCurrentOwner.current=this;try{renderedElement=this._renderValidatedComponentWithoutOwnerOrContext()}finally{ReactCurrentOwner.current=null}}else{renderedElement=this._renderValidatedComponentWithoutOwnerOrContext()}!(renderedElement===null||renderedElement===false||React.isValidElement(renderedElement))?process.env.NODE_ENV!=="production"?invariant(false,"%s.render(): A valid React element (or null) must be returned. You may have returned undefined, an array or some other invalid object.",this.getName()||"ReactCompositeComponent"):_prodInvariant("109",this.getName()||"ReactCompositeComponent"):void 0;return renderedElement},attachRef:function(ref,component){var inst=this.getPublicInstance();!(inst!=null)?process.env.NODE_ENV!=="production"?invariant(false,"Stateless function components cannot have refs."):_prodInvariant("110"):void 0;var publicComponentInstance=component.getPublicInstance();if(process.env.NODE_ENV!=="production"){var componentName=component&&component.getName?component.getName():"a component";process.env.NODE_ENV!=="production"?warning(publicComponentInstance!=null||component._compositeType!==CompositeTypes.StatelessFunctional,"Stateless function components cannot be given refs "+'(See ref "%s" in %s created by %s). '+"Attempts to access this ref will fail.",ref,componentName,this.getName()):void 0}var refs=inst.refs===emptyObject?inst.refs={}:inst.refs;refs[ref]=publicComponentInstance},detachRef:function(ref){var refs=this.getPublicInstance().refs;delete refs[ref]},getName:function(){var type=this._currentElement.type;var constructor=this._instance&&this._instance.constructor;return type.displayName||constructor&&constructor.displayName||type.name||constructor&&constructor.name||null},getPublicInstance:function(){var inst=this._instance;if(this._compositeType===CompositeTypes.StatelessFunctional){return null}return inst},_instantiateReactComponent:null};module.exports=ReactCompositeComponent}).call(this,require("_process"))},{"./ReactComponentEnvironment":59,"./ReactErrorUtils":84,"./ReactInstanceMap":92,"./ReactInstrumentation":93,"./ReactNodeTypes":98,"./ReactReconciler":103,"./checkReactTypeSpec":130,"./reactProdInvariant":151,"./shouldUpdateReactComponent":155,_process:184,"fbjs/lib/emptyObject":11,"fbjs/lib/invariant":18,"fbjs/lib/shallowEqual":24,"fbjs/lib/warning":25,"object-assign":26,"react/lib/React":160,"react/lib/ReactCurrentOwner":164}],61:[function(require,module,exports){(function(process){"use strict";var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDefaultInjection=require("./ReactDefaultInjection");var ReactMount=require("./ReactMount");var ReactReconciler=require("./ReactReconciler");var ReactUpdates=require("./ReactUpdates");var ReactVersion=require("./ReactVersion");var findDOMNode=require("./findDOMNode");var getHostComponentFromComposite=require("./getHostComponentFromComposite");var renderSubtreeIntoContainer=require("./renderSubtreeIntoContainer");var warning=require("fbjs/lib/warning");ReactDefaultInjection.inject();var ReactDOM={findDOMNode:findDOMNode,render:ReactMount.render,unmountComponentAtNode:ReactMount.unmountComponentAtNode,version:ReactVersion,unstable_batchedUpdates:ReactUpdates.batchedUpdates,unstable_renderSubtreeIntoContainer:renderSubtreeIntoContainer};if(typeof __REACT_DEVTOOLS_GLOBAL_HOOK__!=="undefined"&&typeof __REACT_DEVTOOLS_GLOBAL_HOOK__.inject==="function"){__REACT_DEVTOOLS_GLOBAL_HOOK__.inject({ComponentTree:{getClosestInstanceFromNode:ReactDOMComponentTree.getClosestInstanceFromNode,getNodeFromInstance:function(inst){if(inst._renderedComponent){inst=getHostComponentFromComposite(inst)}if(inst){return ReactDOMComponentTree.getNodeFromInstance(inst)}else{return null}}},Mount:ReactMount,Reconciler:ReactReconciler})}if(process.env.NODE_ENV!=="production"){var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");if(ExecutionEnvironment.canUseDOM&&window.top===window.self){if(typeof __REACT_DEVTOOLS_GLOBAL_HOOK__==="undefined"){if(navigator.userAgent.indexOf("Chrome")>-1&&navigator.userAgent.indexOf("Edge")===-1||navigator.userAgent.indexOf("Firefox")>-1){var showFileUrlMessage=window.location.protocol.indexOf("http")===-1&&navigator.userAgent.indexOf("Firefox")===-1;console.debug("Download the React DevTools "+(showFileUrlMessage?"and use an HTTP server (instead of a file: URL) ":"")+"for a better development experience: "+"https://fb.me/react-devtools")}}var testFunc=function testFn(){};process.env.NODE_ENV!=="production"?warning((testFunc.name||testFunc.toString()).indexOf("testFn")!==-1,"It looks like you're using a minified copy of the development build "+"of React. When deploying React apps to production, make sure to use "+"the production build which skips development warnings and is faster. "+"See https://fb.me/react-minification for more details."):void 0;var ieCompatibilityMode=document.documentMode&&document.documentMode<8;process.env.NODE_ENV!=="production"?warning(!ieCompatibilityMode,"Internet Explorer is running in compatibility mode; please add the "+"following tag to your HTML to prevent this from happening: "+'<meta http-equiv="X-UA-Compatible" content="IE=edge" />'):void 0;var expectedFeatures=[Array.isArray,Array.prototype.every,Array.prototype.forEach,Array.prototype.indexOf,Array.prototype.map,Date.now,Function.prototype.bind,Object.keys,String.prototype.trim];for(var i=0;i<expectedFeatures.length;i++){if(!expectedFeatures[i]){process.env.NODE_ENV!=="production"?warning(false,"One or more ES5 shims expected by React are not available: "+"https://fb.me/react-warning-polyfills"):void 0;break}}}}if(process.env.NODE_ENV!=="production"){var ReactInstrumentation=require("./ReactInstrumentation");var ReactDOMUnknownPropertyHook=require("./ReactDOMUnknownPropertyHook");var ReactDOMNullInputValuePropHook=require("./ReactDOMNullInputValuePropHook");var ReactDOMInvalidARIAHook=require("./ReactDOMInvalidARIAHook");ReactInstrumentation.debugTool.addHook(ReactDOMUnknownPropertyHook);ReactInstrumentation.debugTool.addHook(ReactDOMNullInputValuePropHook);ReactInstrumentation.debugTool.addHook(ReactDOMInvalidARIAHook)}module.exports=ReactDOM}).call(this,require("_process"))},{"./ReactDOMComponentTree":64,"./ReactDOMInvalidARIAHook":70,"./ReactDOMNullInputValuePropHook":71,"./ReactDOMUnknownPropertyHook":78,"./ReactDefaultInjection":81,"./ReactInstrumentation":93,"./ReactMount":96,"./ReactReconciler":103,"./ReactUpdates":108,"./ReactVersion":109,"./findDOMNode":134,"./getHostComponentFromComposite":141,"./renderSubtreeIntoContainer":152,_process:184,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/warning":25}],62:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var AutoFocusUtils=require("./AutoFocusUtils");var CSSPropertyOperations=require("./CSSPropertyOperations");var DOMLazyTree=require("./DOMLazyTree");var DOMNamespaces=require("./DOMNamespaces");var DOMProperty=require("./DOMProperty");var DOMPropertyOperations=require("./DOMPropertyOperations");var EventPluginHub=require("./EventPluginHub");var EventPluginRegistry=require("./EventPluginRegistry");var ReactBrowserEventEmitter=require("./ReactBrowserEventEmitter");var ReactDOMComponentFlags=require("./ReactDOMComponentFlags");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMInput=require("./ReactDOMInput");var ReactDOMOption=require("./ReactDOMOption");var ReactDOMSelect=require("./ReactDOMSelect");var ReactDOMTextarea=require("./ReactDOMTextarea");var ReactInstrumentation=require("./ReactInstrumentation");var ReactMultiChild=require("./ReactMultiChild");var ReactServerRenderingTransaction=require("./ReactServerRenderingTransaction");var emptyFunction=require("fbjs/lib/emptyFunction");var escapeTextContentForBrowser=require("./escapeTextContentForBrowser");var invariant=require("fbjs/lib/invariant");var isEventSupported=require("./isEventSupported");var shallowEqual=require("fbjs/lib/shallowEqual");var inputValueTracking=require("./inputValueTracking");var validateDOMNesting=require("./validateDOMNesting");var warning=require("fbjs/lib/warning");var Flags=ReactDOMComponentFlags;var deleteListener=EventPluginHub.deleteListener;var getNode=ReactDOMComponentTree.getNodeFromInstance;var listenTo=ReactBrowserEventEmitter.listenTo;var registrationNameModules=EventPluginRegistry.registrationNameModules;var CONTENT_TYPES={string:true,number:true};var STYLE="style";var HTML="__html";var RESERVED_PROPS={children:null,dangerouslySetInnerHTML:null,suppressContentEditableWarning:null};var DOC_FRAGMENT_TYPE=11;function getDeclarationErrorAddendum(internalInstance){if(internalInstance){var owner=internalInstance._currentElement._owner||null;if(owner){var name=owner.getName();if(name){return" This DOM node was rendered by `"+name+"`."}}}return""}function friendlyStringify(obj){if(typeof obj==="object"){if(Array.isArray(obj)){return"["+obj.map(friendlyStringify).join(", ")+"]"}else{var pairs=[];for(var key in obj){if(Object.prototype.hasOwnProperty.call(obj,key)){var keyEscaped=/^[a-z$_][\w$_]*$/i.test(key)?key:JSON.stringify(key);pairs.push(keyEscaped+": "+friendlyStringify(obj[key]))}}return"{"+pairs.join(", ")+"}"}}else if(typeof obj==="string"){return JSON.stringify(obj)}else if(typeof obj==="function"){return"[function object]"}return String(obj)}var styleMutationWarning={};function checkAndWarnForMutatedStyle(style1,style2,component){if(style1==null||style2==null){return}if(shallowEqual(style1,style2)){return}var componentName=component._tag;var owner=component._currentElement._owner;var ownerName;if(owner){ownerName=owner.getName()}var hash=ownerName+"|"+componentName;if(styleMutationWarning.hasOwnProperty(hash)){return}styleMutationWarning[hash]=true;process.env.NODE_ENV!=="production"?warning(false,"`%s` was passed a style object that has previously been mutated. "+"Mutating `style` is deprecated. Consider cloning it beforehand. Check "+"the `render` %s. Previous style: %s. Mutated style: %s.",componentName,owner?"of `"+ownerName+"`":"using <"+componentName+">",friendlyStringify(style1),friendlyStringify(style2)):void 0}function assertValidProps(component,props){if(!props){return}if(voidElementTags[component._tag]){!(props.children==null&&props.dangerouslySetInnerHTML==null)?process.env.NODE_ENV!=="production"?invariant(false,"%s is a void element tag and must neither have `children` nor use `dangerouslySetInnerHTML`.%s",component._tag,component._currentElement._owner?" Check the render method of "+component._currentElement._owner.getName()+".":""):_prodInvariant("137",component._tag,component._currentElement._owner?" Check the render method of "+component._currentElement._owner.getName()+".":""):void 0}if(props.dangerouslySetInnerHTML!=null){!(props.children==null)?process.env.NODE_ENV!=="production"?invariant(false,"Can only set one of `children` or `props.dangerouslySetInnerHTML`."):_prodInvariant("60"):void 0;!(typeof props.dangerouslySetInnerHTML==="object"&&HTML in props.dangerouslySetInnerHTML)?process.env.NODE_ENV!=="production"?invariant(false,"`props.dangerouslySetInnerHTML` must be in the form `{__html: ...}`. Please visit https://fb.me/react-invariant-dangerously-set-inner-html for more information."):_prodInvariant("61"):void 0}if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(props.innerHTML==null,"Directly setting property `innerHTML` is not permitted. "+"For more information, lookup documentation on `dangerouslySetInnerHTML`."):void 0;process.env.NODE_ENV!=="production"?warning(props.suppressContentEditableWarning||!props.contentEditable||props.children==null,"A component is `contentEditable` and contains `children` managed by "+"React. It is now your responsibility to guarantee that none of "+"those nodes are unexpectedly modified or duplicated. This is "+"probably not intentional."):void 0;process.env.NODE_ENV!=="production"?warning(props.onFocusIn==null&&props.onFocusOut==null,"React uses onFocus and onBlur instead of onFocusIn and onFocusOut. "+"All React events are normalized to bubble, so onFocusIn and onFocusOut "+"are not needed/supported by React."):void 0}!(props.style==null||typeof props.style==="object")?process.env.NODE_ENV!=="production"?invariant(false,"The `style` prop expects a mapping from style properties to values, not a string. For example, style={{marginRight: spacing + 'em'}} when using JSX.%s",getDeclarationErrorAddendum(component)):_prodInvariant("62",getDeclarationErrorAddendum(component)):void 0}function enqueuePutListener(inst,registrationName,listener,transaction){if(transaction instanceof ReactServerRenderingTransaction){return}if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(registrationName!=="onScroll"||isEventSupported("scroll",true),"This browser doesn't support the `onScroll` event"):void 0}var containerInfo=inst._hostContainerInfo;var isDocumentFragment=containerInfo._node&&containerInfo._node.nodeType===DOC_FRAGMENT_TYPE;var doc=isDocumentFragment?containerInfo._node:containerInfo._ownerDocument;listenTo(registrationName,doc);transaction.getReactMountReady().enqueue(putListener,{inst:inst,registrationName:registrationName,listener:listener})}function putListener(){var listenerToPut=this;EventPluginHub.putListener(listenerToPut.inst,listenerToPut.registrationName,listenerToPut.listener)}function inputPostMount(){var inst=this;ReactDOMInput.postMountWrapper(inst)}function textareaPostMount(){var inst=this;ReactDOMTextarea.postMountWrapper(inst)}function optionPostMount(){var inst=this;ReactDOMOption.postMountWrapper(inst)}var setAndValidateContentChildDev=emptyFunction;if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev=function(content){var hasExistingContent=this._contentDebugID!=null;var debugID=this._debugID;var contentDebugID=-debugID;if(content==null){if(hasExistingContent){ReactInstrumentation.debugTool.onUnmountComponent(this._contentDebugID)}this._contentDebugID=null;return}validateDOMNesting(null,String(content),this,this._ancestorInfo);this._contentDebugID=contentDebugID;if(hasExistingContent){ReactInstrumentation.debugTool.onBeforeUpdateComponent(contentDebugID,content);ReactInstrumentation.debugTool.onUpdateComponent(contentDebugID)}else{ReactInstrumentation.debugTool.onBeforeMountComponent(contentDebugID,content,debugID);ReactInstrumentation.debugTool.onMountComponent(contentDebugID);ReactInstrumentation.debugTool.onSetChildren(debugID,[contentDebugID])}}}var mediaEvents={topAbort:"abort",topCanPlay:"canplay",topCanPlayThrough:"canplaythrough",topDurationChange:"durationchange",topEmptied:"emptied",topEncrypted:"encrypted",topEnded:"ended",topError:"error",topLoadedData:"loadeddata",topLoadedMetadata:"loadedmetadata",topLoadStart:"loadstart",topPause:"pause",topPlay:"play",topPlaying:"playing",topProgress:"progress",topRateChange:"ratechange",topSeeked:"seeked",topSeeking:"seeking",topStalled:"stalled",topSuspend:"suspend",topTimeUpdate:"timeupdate",topVolumeChange:"volumechange",topWaiting:"waiting"};function trackInputValue(){inputValueTracking.track(this)}function trapBubbledEventsLocal(){var inst=this;!inst._rootNodeID?process.env.NODE_ENV!=="production"?invariant(false,"Must be mounted to trap events"):_prodInvariant("63"):void 0;var node=getNode(inst);!node?process.env.NODE_ENV!=="production"?invariant(false,"trapBubbledEvent(...): Requires node to be rendered."):_prodInvariant("64"):void 0;switch(inst._tag){case"iframe":case"object":inst._wrapperState.listeners=[ReactBrowserEventEmitter.trapBubbledEvent("topLoad","load",node)];break;case"video":case"audio":inst._wrapperState.listeners=[];for(var event in mediaEvents){if(mediaEvents.hasOwnProperty(event)){inst._wrapperState.listeners.push(ReactBrowserEventEmitter.trapBubbledEvent(event,mediaEvents[event],node))}}break;case"source":inst._wrapperState.listeners=[ReactBrowserEventEmitter.trapBubbledEvent("topError","error",node)];break;case"img":inst._wrapperState.listeners=[ReactBrowserEventEmitter.trapBubbledEvent("topError","error",node),ReactBrowserEventEmitter.trapBubbledEvent("topLoad","load",node)];break;case"form":inst._wrapperState.listeners=[ReactBrowserEventEmitter.trapBubbledEvent("topReset","reset",node),ReactBrowserEventEmitter.trapBubbledEvent("topSubmit","submit",node)];break;case"input":case"select":case"textarea":inst._wrapperState.listeners=[ReactBrowserEventEmitter.trapBubbledEvent("topInvalid","invalid",node)];break}}function postUpdateSelectWrapper(){ReactDOMSelect.postUpdateWrapper(this)}var omittedCloseTags={area:true,base:true,br:true,col:true,embed:true,hr:true,img:true,input:true,keygen:true,link:true,meta:true,param:true,source:true,track:true,wbr:true};var newlineEatingTags={listing:true,pre:true,textarea:true};var voidElementTags=_assign({menuitem:true},omittedCloseTags);var VALID_TAG_REGEX=/^[a-zA-Z][a-zA-Z:_\.\-\d]*$/;var validatedTagCache={};var hasOwnProperty={}.hasOwnProperty;function validateDangerousTag(tag){if(!hasOwnProperty.call(validatedTagCache,tag)){!VALID_TAG_REGEX.test(tag)?process.env.NODE_ENV!=="production"?invariant(false,"Invalid tag: %s",tag):_prodInvariant("65",tag):void 0;validatedTagCache[tag]=true}}function isCustomComponent(tagName,props){return tagName.indexOf("-")>=0||props.is!=null}var globalIdCounter=1;function ReactDOMComponent(element){var tag=element.type;validateDangerousTag(tag);this._currentElement=element;this._tag=tag.toLowerCase();this._namespaceURI=null;this._renderedChildren=null;this._previousStyle=null;this._previousStyleCopy=null;this._hostNode=null;this._hostParent=null;this._rootNodeID=0;this._domID=0;this._hostContainerInfo=null;this._wrapperState=null;this._topLevelWrapper=null;this._flags=0;if(process.env.NODE_ENV!=="production"){this._ancestorInfo=null;setAndValidateContentChildDev.call(this,null)}}ReactDOMComponent.displayName="ReactDOMComponent";ReactDOMComponent.Mixin={mountComponent:function(transaction,hostParent,hostContainerInfo,context){this._rootNodeID=globalIdCounter++;this._domID=hostContainerInfo._idCounter++;this._hostParent=hostParent;this._hostContainerInfo=hostContainerInfo;var props=this._currentElement.props;switch(this._tag){case"audio":case"form":case"iframe":case"img":case"link":case"object":case"source":case"video":this._wrapperState={listeners:null};transaction.getReactMountReady().enqueue(trapBubbledEventsLocal,this);break;case"input":ReactDOMInput.mountWrapper(this,props,hostParent);props=ReactDOMInput.getHostProps(this,props);transaction.getReactMountReady().enqueue(trackInputValue,this);transaction.getReactMountReady().enqueue(trapBubbledEventsLocal,this);break;case"option":ReactDOMOption.mountWrapper(this,props,hostParent);props=ReactDOMOption.getHostProps(this,props);break;case"select":ReactDOMSelect.mountWrapper(this,props,hostParent);props=ReactDOMSelect.getHostProps(this,props);transaction.getReactMountReady().enqueue(trapBubbledEventsLocal,this);break;case"textarea":ReactDOMTextarea.mountWrapper(this,props,hostParent);props=ReactDOMTextarea.getHostProps(this,props);transaction.getReactMountReady().enqueue(trackInputValue,this);transaction.getReactMountReady().enqueue(trapBubbledEventsLocal,this);break}assertValidProps(this,props);var namespaceURI;var parentTag;if(hostParent!=null){namespaceURI=hostParent._namespaceURI;parentTag=hostParent._tag}else if(hostContainerInfo._tag){namespaceURI=hostContainerInfo._namespaceURI;parentTag=hostContainerInfo._tag}if(namespaceURI==null||namespaceURI===DOMNamespaces.svg&&parentTag==="foreignobject"){namespaceURI=DOMNamespaces.html}if(namespaceURI===DOMNamespaces.html){if(this._tag==="svg"){namespaceURI=DOMNamespaces.svg}else if(this._tag==="math"){namespaceURI=DOMNamespaces.mathml}}this._namespaceURI=namespaceURI;if(process.env.NODE_ENV!=="production"){var parentInfo;if(hostParent!=null){parentInfo=hostParent._ancestorInfo}else if(hostContainerInfo._tag){parentInfo=hostContainerInfo._ancestorInfo}if(parentInfo){validateDOMNesting(this._tag,null,this,parentInfo)}this._ancestorInfo=validateDOMNesting.updatedAncestorInfo(parentInfo,this._tag,this)}var mountImage;if(transaction.useCreateElement){var ownerDocument=hostContainerInfo._ownerDocument;var el;if(namespaceURI===DOMNamespaces.html){if(this._tag==="script"){var div=ownerDocument.createElement("div");var type=this._currentElement.type;div.innerHTML="<"+type+"></"+type+">";el=div.removeChild(div.firstChild)}else if(props.is){el=ownerDocument.createElement(this._currentElement.type,props.is)}else{el=ownerDocument.createElement(this._currentElement.type)}}else{el=ownerDocument.createElementNS(namespaceURI,this._currentElement.type)}ReactDOMComponentTree.precacheNode(this,el);this._flags|=Flags.hasCachedChildNodes;if(!this._hostParent){DOMPropertyOperations.setAttributeForRoot(el)}this._updateDOMProperties(null,props,transaction);var lazyTree=DOMLazyTree(el);this._createInitialChildren(transaction,props,context,lazyTree);mountImage=lazyTree}else{var tagOpen=this._createOpenTagMarkupAndPutListeners(transaction,props);var tagContent=this._createContentMarkup(transaction,props,context);if(!tagContent&&omittedCloseTags[this._tag]){mountImage=tagOpen+"/>"}else{mountImage=tagOpen+">"+tagContent+"</"+this._currentElement.type+">"}}switch(this._tag){case"input":transaction.getReactMountReady().enqueue(inputPostMount,this);if(props.autoFocus){transaction.getReactMountReady().enqueue(AutoFocusUtils.focusDOMComponent,this)}break;case"textarea":transaction.getReactMountReady().enqueue(textareaPostMount,this);if(props.autoFocus){transaction.getReactMountReady().enqueue(AutoFocusUtils.focusDOMComponent,this)}break;case"select":if(props.autoFocus){transaction.getReactMountReady().enqueue(AutoFocusUtils.focusDOMComponent,this)}break;case"button":if(props.autoFocus){transaction.getReactMountReady().enqueue(AutoFocusUtils.focusDOMComponent,this)}break;case"option":transaction.getReactMountReady().enqueue(optionPostMount,this);break}return mountImage},_createOpenTagMarkupAndPutListeners:function(transaction,props){var ret="<"+this._currentElement.type;for(var propKey in props){if(!props.hasOwnProperty(propKey)){continue}var propValue=props[propKey];if(propValue==null){continue}if(registrationNameModules.hasOwnProperty(propKey)){if(propValue){enqueuePutListener(this,propKey,propValue,transaction)}}else{if(propKey===STYLE){if(propValue){if(process.env.NODE_ENV!=="production"){this._previousStyle=propValue}propValue=this._previousStyleCopy=_assign({},props.style)}propValue=CSSPropertyOperations.createMarkupForStyles(propValue,this)}var markup=null;if(this._tag!=null&&isCustomComponent(this._tag,props)){if(!RESERVED_PROPS.hasOwnProperty(propKey)){markup=DOMPropertyOperations.createMarkupForCustomAttribute(propKey,propValue)}}else{markup=DOMPropertyOperations.createMarkupForProperty(propKey,propValue)}if(markup){ret+=" "+markup}}}if(transaction.renderToStaticMarkup){return ret}if(!this._hostParent){ret+=" "+DOMPropertyOperations.createMarkupForRoot()}ret+=" "+DOMPropertyOperations.createMarkupForID(this._domID);return ret},_createContentMarkup:function(transaction,props,context){var ret="";var innerHTML=props.dangerouslySetInnerHTML;if(innerHTML!=null){if(innerHTML.__html!=null){ret=innerHTML.__html}}else{var contentToUse=CONTENT_TYPES[typeof props.children]?props.children:null;var childrenToUse=contentToUse!=null?null:props.children;if(contentToUse!=null){ret=escapeTextContentForBrowser(contentToUse);if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev.call(this,contentToUse)}}else if(childrenToUse!=null){var mountImages=this.mountChildren(childrenToUse,transaction,context);ret=mountImages.join("")}}if(newlineEatingTags[this._tag]&&ret.charAt(0)==="\n"){return"\n"+ret}else{return ret}},_createInitialChildren:function(transaction,props,context,lazyTree){var innerHTML=props.dangerouslySetInnerHTML;if(innerHTML!=null){if(innerHTML.__html!=null){DOMLazyTree.queueHTML(lazyTree,innerHTML.__html)}}else{var contentToUse=CONTENT_TYPES[typeof props.children]?props.children:null;var childrenToUse=contentToUse!=null?null:props.children;if(contentToUse!=null){if(contentToUse!==""){if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev.call(this,contentToUse)}DOMLazyTree.queueText(lazyTree,contentToUse)}}else if(childrenToUse!=null){var mountImages=this.mountChildren(childrenToUse,transaction,context);for(var i=0;i<mountImages.length;i++){DOMLazyTree.queueChild(lazyTree,mountImages[i])}}}},receiveComponent:function(nextElement,transaction,context){var prevElement=this._currentElement;this._currentElement=nextElement;this.updateComponent(transaction,prevElement,nextElement,context)},updateComponent:function(transaction,prevElement,nextElement,context){var lastProps=prevElement.props;var nextProps=this._currentElement.props;switch(this._tag){case"input":lastProps=ReactDOMInput.getHostProps(this,lastProps);nextProps=ReactDOMInput.getHostProps(this,nextProps);break;case"option":lastProps=ReactDOMOption.getHostProps(this,lastProps);nextProps=ReactDOMOption.getHostProps(this,nextProps);break;case"select":lastProps=ReactDOMSelect.getHostProps(this,lastProps);nextProps=ReactDOMSelect.getHostProps(this,nextProps);break;case"textarea":lastProps=ReactDOMTextarea.getHostProps(this,lastProps);nextProps=ReactDOMTextarea.getHostProps(this,nextProps);break}assertValidProps(this,nextProps);this._updateDOMProperties(lastProps,nextProps,transaction);this._updateDOMChildren(lastProps,nextProps,transaction,context);switch(this._tag){case"input":ReactDOMInput.updateWrapper(this);break;case"textarea":ReactDOMTextarea.updateWrapper(this);break;case"select":transaction.getReactMountReady().enqueue(postUpdateSelectWrapper,this);break}},_updateDOMProperties:function(lastProps,nextProps,transaction){var propKey;var styleName;var styleUpdates;for(propKey in lastProps){if(nextProps.hasOwnProperty(propKey)||!lastProps.hasOwnProperty(propKey)||lastProps[propKey]==null){continue}if(propKey===STYLE){var lastStyle=this._previousStyleCopy;for(styleName in lastStyle){if(lastStyle.hasOwnProperty(styleName)){styleUpdates=styleUpdates||{};styleUpdates[styleName]=""}}this._previousStyleCopy=null}else if(registrationNameModules.hasOwnProperty(propKey)){if(lastProps[propKey]){deleteListener(this,propKey)}}else if(isCustomComponent(this._tag,lastProps)){if(!RESERVED_PROPS.hasOwnProperty(propKey)){DOMPropertyOperations.deleteValueForAttribute(getNode(this),propKey)}}else if(DOMProperty.properties[propKey]||DOMProperty.isCustomAttribute(propKey)){DOMPropertyOperations.deleteValueForProperty(getNode(this),propKey)}}for(propKey in nextProps){var nextProp=nextProps[propKey];var lastProp=propKey===STYLE?this._previousStyleCopy:lastProps!=null?lastProps[propKey]:undefined;if(!nextProps.hasOwnProperty(propKey)||nextProp===lastProp||nextProp==null&&lastProp==null){continue}if(propKey===STYLE){if(nextProp){if(process.env.NODE_ENV!=="production"){checkAndWarnForMutatedStyle(this._previousStyleCopy,this._previousStyle,this);this._previousStyle=nextProp}nextProp=this._previousStyleCopy=_assign({},nextProp)}else{this._previousStyleCopy=null}if(lastProp){for(styleName in lastProp){if(lastProp.hasOwnProperty(styleName)&&(!nextProp||!nextProp.hasOwnProperty(styleName))){styleUpdates=styleUpdates||{};styleUpdates[styleName]=""}}for(styleName in nextProp){if(nextProp.hasOwnProperty(styleName)&&lastProp[styleName]!==nextProp[styleName]){styleUpdates=styleUpdates||{};styleUpdates[styleName]=nextProp[styleName]}}}else{styleUpdates=nextProp}}else if(registrationNameModules.hasOwnProperty(propKey)){if(nextProp){enqueuePutListener(this,propKey,nextProp,transaction)}else if(lastProp){deleteListener(this,propKey)}}else if(isCustomComponent(this._tag,nextProps)){if(!RESERVED_PROPS.hasOwnProperty(propKey)){DOMPropertyOperations.setValueForAttribute(getNode(this),propKey,nextProp)}}else if(DOMProperty.properties[propKey]||DOMProperty.isCustomAttribute(propKey)){var node=getNode(this);if(nextProp!=null){DOMPropertyOperations.setValueForProperty(node,propKey,nextProp)}else{DOMPropertyOperations.deleteValueForProperty(node,propKey)}}}if(styleUpdates){CSSPropertyOperations.setValueForStyles(getNode(this),styleUpdates,this)}},_updateDOMChildren:function(lastProps,nextProps,transaction,context){var lastContent=CONTENT_TYPES[typeof lastProps.children]?lastProps.children:null;var nextContent=CONTENT_TYPES[typeof nextProps.children]?nextProps.children:null;var lastHtml=lastProps.dangerouslySetInnerHTML&&lastProps.dangerouslySetInnerHTML.__html;var nextHtml=nextProps.dangerouslySetInnerHTML&&nextProps.dangerouslySetInnerHTML.__html;var lastChildren=lastContent!=null?null:lastProps.children;var nextChildren=nextContent!=null?null:nextProps.children;var lastHasContentOrHtml=lastContent!=null||lastHtml!=null;var nextHasContentOrHtml=nextContent!=null||nextHtml!=null;if(lastChildren!=null&&nextChildren==null){this.updateChildren(null,transaction,context)}else if(lastHasContentOrHtml&&!nextHasContentOrHtml){this.updateTextContent("");if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onSetChildren(this._debugID,[])}}if(nextContent!=null){if(lastContent!==nextContent){this.updateTextContent(""+nextContent);if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev.call(this,nextContent)}}}else if(nextHtml!=null){if(lastHtml!==nextHtml){this.updateMarkup(""+nextHtml)}if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onSetChildren(this._debugID,[])}}else if(nextChildren!=null){if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev.call(this,null)}this.updateChildren(nextChildren,transaction,context)}},getHostNode:function(){return getNode(this)},unmountComponent:function(safely){switch(this._tag){case"audio":case"form":case"iframe":case"img":case"link":case"object":case"source":case"video":var listeners=this._wrapperState.listeners;if(listeners){for(var i=0;i<listeners.length;i++){listeners[i].remove()}}break;case"input":case"textarea":inputValueTracking.stopTracking(this);break;case"html":case"head":case"body":!false?process.env.NODE_ENV!=="production"?invariant(false,"<%s> tried to unmount. Because of cross-browser quirks it is impossible to unmount some top-level components (eg <html>, <head>, and <body>) reliably and efficiently. To fix this, have a single top-level component that never unmounts render these elements.",this._tag):_prodInvariant("66",this._tag):void 0;break}this.unmountChildren(safely);ReactDOMComponentTree.uncacheNode(this);EventPluginHub.deleteAllListeners(this);this._rootNodeID=0;this._domID=0;this._wrapperState=null;if(process.env.NODE_ENV!=="production"){setAndValidateContentChildDev.call(this,null)}},getPublicInstance:function(){return getNode(this)}};_assign(ReactDOMComponent.prototype,ReactDOMComponent.Mixin,ReactMultiChild.Mixin);module.exports=ReactDOMComponent}).call(this,require("_process"))},{"./AutoFocusUtils":33,"./CSSPropertyOperations":36,"./DOMLazyTree":40,"./DOMNamespaces":41,"./DOMProperty":42,"./DOMPropertyOperations":43,"./EventPluginHub":47,"./EventPluginRegistry":48,"./ReactBrowserEventEmitter":56,"./ReactDOMComponentFlags":63,"./ReactDOMComponentTree":64,"./ReactDOMInput":69,"./ReactDOMOption":72,"./ReactDOMSelect":73,"./ReactDOMTextarea":76,"./ReactInstrumentation":93,"./ReactMultiChild":97,"./ReactServerRenderingTransaction":105,"./escapeTextContentForBrowser":133,"./inputValueTracking":146,"./isEventSupported":148,"./reactProdInvariant":151,"./validateDOMNesting":157,_process:184,"fbjs/lib/emptyFunction":10,"fbjs/lib/invariant":18,"fbjs/lib/shallowEqual":24,"fbjs/lib/warning":25,"object-assign":26}],63:[function(require,module,exports){"use strict";var ReactDOMComponentFlags={hasCachedChildNodes:1<<0};module.exports=ReactDOMComponentFlags},{}],64:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var DOMProperty=require("./DOMProperty");var ReactDOMComponentFlags=require("./ReactDOMComponentFlags");var invariant=require("fbjs/lib/invariant");var ATTR_NAME=DOMProperty.ID_ATTRIBUTE_NAME;var Flags=ReactDOMComponentFlags;var internalInstanceKey="__reactInternalInstance$"+Math.random().toString(36).slice(2);function shouldPrecacheNode(node,nodeID){return node.nodeType===1&&node.getAttribute(ATTR_NAME)===String(nodeID)||node.nodeType===8&&node.nodeValue===" react-text: "+nodeID+" "||node.nodeType===8&&node.nodeValue===" react-empty: "+nodeID+" "}function getRenderedHostOrTextFromComponent(component){var rendered;while(rendered=component._renderedComponent){component=rendered}return component}function precacheNode(inst,node){var hostInst=getRenderedHostOrTextFromComponent(inst);hostInst._hostNode=node;node[internalInstanceKey]=hostInst}function uncacheNode(inst){var node=inst._hostNode;if(node){delete node[internalInstanceKey];inst._hostNode=null}}function precacheChildNodes(inst,node){if(inst._flags&Flags.hasCachedChildNodes){return}var children=inst._renderedChildren;var childNode=node.firstChild;outer:for(var name in children){if(!children.hasOwnProperty(name)){continue}var childInst=children[name];var childID=getRenderedHostOrTextFromComponent(childInst)._domID;if(childID===0){continue}for(;childNode!==null;childNode=childNode.nextSibling){if(shouldPrecacheNode(childNode,childID)){precacheNode(childInst,childNode);continue outer}}!false?process.env.NODE_ENV!=="production"?invariant(false,"Unable to find element with ID %s.",childID):_prodInvariant("32",childID):void 0}inst._flags|=Flags.hasCachedChildNodes}function getClosestInstanceFromNode(node){if(node[internalInstanceKey]){return node[internalInstanceKey]}var parents=[];while(!node[internalInstanceKey]){parents.push(node);if(node.parentNode){node=node.parentNode}else{return null}}var closest;var inst;for(;node&&(inst=node[internalInstanceKey]);node=parents.pop()){closest=inst;if(parents.length){precacheChildNodes(inst,node)}}return closest}function getInstanceFromNode(node){var inst=getClosestInstanceFromNode(node);if(inst!=null&&inst._hostNode===node){return inst}else{return null}}function getNodeFromInstance(inst){!(inst._hostNode!==undefined)?process.env.NODE_ENV!=="production"?invariant(false,"getNodeFromInstance: Invalid argument."):_prodInvariant("33"):void 0;if(inst._hostNode){return inst._hostNode}var parents=[];while(!inst._hostNode){parents.push(inst);!inst._hostParent?process.env.NODE_ENV!=="production"?invariant(false,"React DOM tree root should always have a node reference."):_prodInvariant("34"):void 0;inst=inst._hostParent}for(;parents.length;inst=parents.pop()){precacheChildNodes(inst,inst._hostNode)}return inst._hostNode}var ReactDOMComponentTree={getClosestInstanceFromNode:getClosestInstanceFromNode,getInstanceFromNode:getInstanceFromNode,getNodeFromInstance:getNodeFromInstance,precacheChildNodes:precacheChildNodes,precacheNode:precacheNode,uncacheNode:uncacheNode};module.exports=ReactDOMComponentTree}).call(this,require("_process"))},{"./DOMProperty":42,"./ReactDOMComponentFlags":63,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],65:[function(require,module,exports){(function(process){"use strict";var validateDOMNesting=require("./validateDOMNesting");var DOC_NODE_TYPE=9;function ReactDOMContainerInfo(topLevelWrapper,node){var info={_topLevelWrapper:topLevelWrapper,_idCounter:1,_ownerDocument:node?node.nodeType===DOC_NODE_TYPE?node:node.ownerDocument:null,_node:node,_tag:node?node.nodeName.toLowerCase():null,_namespaceURI:node?node.namespaceURI:null};if(process.env.NODE_ENV!=="production"){info._ancestorInfo=node?validateDOMNesting.updatedAncestorInfo(null,info._tag,null):null}return info}module.exports=ReactDOMContainerInfo}).call(this,require("_process"))},{"./validateDOMNesting":157,_process:184}],66:[function(require,module,exports){"use strict";var _assign=require("object-assign");var DOMLazyTree=require("./DOMLazyTree");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMEmptyComponent=function(instantiate){this._currentElement=null;this._hostNode=null;this._hostParent=null;this._hostContainerInfo=null;this._domID=0};_assign(ReactDOMEmptyComponent.prototype,{mountComponent:function(transaction,hostParent,hostContainerInfo,context){var domID=hostContainerInfo._idCounter++;this._domID=domID;this._hostParent=hostParent;this._hostContainerInfo=hostContainerInfo;var nodeValue=" react-empty: "+this._domID+" ";if(transaction.useCreateElement){var ownerDocument=hostContainerInfo._ownerDocument;var node=ownerDocument.createComment(nodeValue);ReactDOMComponentTree.precacheNode(this,node);return DOMLazyTree(node)}else{if(transaction.renderToStaticMarkup){return""}return"\x3c!--"+nodeValue+"--\x3e"}},receiveComponent:function(){},getHostNode:function(){return ReactDOMComponentTree.getNodeFromInstance(this)},unmountComponent:function(){ReactDOMComponentTree.uncacheNode(this)}});module.exports=ReactDOMEmptyComponent},{"./DOMLazyTree":40,"./ReactDOMComponentTree":64,"object-assign":26}],67:[function(require,module,exports){"use strict";var ReactDOMFeatureFlags={useCreateElement:true,useFiber:false};module.exports=ReactDOMFeatureFlags},{}],68:[function(require,module,exports){"use strict";var DOMChildrenOperations=require("./DOMChildrenOperations");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMIDOperations={dangerouslyProcessChildrenUpdates:function(parentInst,updates){var node=ReactDOMComponentTree.getNodeFromInstance(parentInst);DOMChildrenOperations.processUpdates(node,updates)}};module.exports=ReactDOMIDOperations},{"./DOMChildrenOperations":39,"./ReactDOMComponentTree":64}],69:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var DOMPropertyOperations=require("./DOMPropertyOperations");var LinkedValueUtils=require("./LinkedValueUtils");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactUpdates=require("./ReactUpdates");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var didWarnValueLink=false;var didWarnCheckedLink=false;var didWarnValueDefaultValue=false;var didWarnCheckedDefaultChecked=false;var didWarnControlledToUncontrolled=false;var didWarnUncontrolledToControlled=false;function forceUpdateIfMounted(){if(this._rootNodeID){ReactDOMInput.updateWrapper(this)}}function isControlled(props){var usesChecked=props.type==="checkbox"||props.type==="radio";return usesChecked?props.checked!=null:props.value!=null}var ReactDOMInput={getHostProps:function(inst,props){var value=LinkedValueUtils.getValue(props);var checked=LinkedValueUtils.getChecked(props);var hostProps=_assign({type:undefined,step:undefined,min:undefined,max:undefined},props,{defaultChecked:undefined,defaultValue:undefined,value:value!=null?value:inst._wrapperState.initialValue,checked:checked!=null?checked:inst._wrapperState.initialChecked,onChange:inst._wrapperState.onChange});return hostProps},mountWrapper:function(inst,props){if(process.env.NODE_ENV!=="production"){LinkedValueUtils.checkPropTypes("input",props,inst._currentElement._owner);var owner=inst._currentElement._owner;if(props.valueLink!==undefined&&!didWarnValueLink){process.env.NODE_ENV!=="production"?warning(false,"`valueLink` prop on `input` is deprecated; set `value` and `onChange` instead."):void 0;didWarnValueLink=true}if(props.checkedLink!==undefined&&!didWarnCheckedLink){process.env.NODE_ENV!=="production"?warning(false,"`checkedLink` prop on `input` is deprecated; set `value` and `onChange` instead."):void 0;didWarnCheckedLink=true}if(props.checked!==undefined&&props.defaultChecked!==undefined&&!didWarnCheckedDefaultChecked){process.env.NODE_ENV!=="production"?warning(false,"%s contains an input of type %s with both checked and defaultChecked props. "+"Input elements must be either controlled or uncontrolled "+"(specify either the checked prop, or the defaultChecked prop, but not "+"both). Decide between using a controlled or uncontrolled input "+"element and remove one of these props. More info: "+"https://fb.me/react-controlled-components",owner&&owner.getName()||"A component",props.type):void 0;didWarnCheckedDefaultChecked=true}if(props.value!==undefined&&props.defaultValue!==undefined&&!didWarnValueDefaultValue){process.env.NODE_ENV!=="production"?warning(false,"%s contains an input of type %s with both value and defaultValue props. "+"Input elements must be either controlled or uncontrolled "+"(specify either the value prop, or the defaultValue prop, but not "+"both). Decide between using a controlled or uncontrolled input "+"element and remove one of these props. More info: "+"https://fb.me/react-controlled-components",owner&&owner.getName()||"A component",props.type):void 0;didWarnValueDefaultValue=true}}var defaultValue=props.defaultValue;inst._wrapperState={initialChecked:props.checked!=null?props.checked:props.defaultChecked,initialValue:props.value!=null?props.value:defaultValue,listeners:null,onChange:_handleChange.bind(inst),controlled:isControlled(props)}},updateWrapper:function(inst){var props=inst._currentElement.props;if(process.env.NODE_ENV!=="production"){var controlled=isControlled(props);var owner=inst._currentElement._owner;if(!inst._wrapperState.controlled&&controlled&&!didWarnUncontrolledToControlled){process.env.NODE_ENV!=="production"?warning(false,"%s is changing an uncontrolled input of type %s to be controlled. "+"Input elements should not switch from uncontrolled to controlled (or vice versa). "+"Decide between using a controlled or uncontrolled input "+"element for the lifetime of the component. More info: https://fb.me/react-controlled-components",owner&&owner.getName()||"A component",props.type):void 0;didWarnUncontrolledToControlled=true}if(inst._wrapperState.controlled&&!controlled&&!didWarnControlledToUncontrolled){process.env.NODE_ENV!=="production"?warning(false,"%s is changing a controlled input of type %s to be uncontrolled. "+"Input elements should not switch from controlled to uncontrolled (or vice versa). "+"Decide between using a controlled or uncontrolled input "+"element for the lifetime of the component. More info: https://fb.me/react-controlled-components",owner&&owner.getName()||"A component",props.type):void 0;didWarnControlledToUncontrolled=true}}var checked=props.checked;if(checked!=null){DOMPropertyOperations.setValueForProperty(ReactDOMComponentTree.getNodeFromInstance(inst),"checked",checked||false)}var node=ReactDOMComponentTree.getNodeFromInstance(inst);var value=LinkedValueUtils.getValue(props);if(value!=null){if(value===0&&node.value===""){node.value="0"}else if(props.type==="number"){var valueAsNumber=parseFloat(node.value,10)||0;if(value!=valueAsNumber||value==valueAsNumber&&node.value!=value){node.value=""+value}}else if(node.value!==""+value){node.value=""+value}}else{if(props.value==null&&props.defaultValue!=null){if(node.defaultValue!==""+props.defaultValue){node.defaultValue=""+props.defaultValue}}if(props.checked==null&&props.defaultChecked!=null){node.defaultChecked=!!props.defaultChecked}}},postMountWrapper:function(inst){var props=inst._currentElement.props;var node=ReactDOMComponentTree.getNodeFromInstance(inst);switch(props.type){case"submit":case"reset":break;case"color":case"date":case"datetime":case"datetime-local":case"month":case"time":case"week":node.value="";node.value=node.defaultValue;break;default:node.value=node.value;break}var name=node.name;if(name!==""){node.name=""}node.defaultChecked=!node.defaultChecked;node.defaultChecked=!node.defaultChecked;if(name!==""){node.name=name}}};function _handleChange(event){var props=this._currentElement.props;var returnValue=LinkedValueUtils.executeOnChange(props,event);ReactUpdates.asap(forceUpdateIfMounted,this);var name=props.name;if(props.type==="radio"&&name!=null){var rootNode=ReactDOMComponentTree.getNodeFromInstance(this);var queryRoot=rootNode;while(queryRoot.parentNode){queryRoot=queryRoot.parentNode}var group=queryRoot.querySelectorAll("input[name="+JSON.stringify(""+name)+'][type="radio"]');for(var i=0;i<group.length;i++){var otherNode=group[i];if(otherNode===rootNode||otherNode.form!==rootNode.form){continue}var otherInstance=ReactDOMComponentTree.getInstanceFromNode(otherNode);!otherInstance?process.env.NODE_ENV!=="production"?invariant(false,"ReactDOMInput: Mixing React and non-React radio inputs with the same `name` is not supported."):_prodInvariant("90"):void 0;ReactUpdates.asap(forceUpdateIfMounted,otherInstance)}}return returnValue}module.exports=ReactDOMInput}).call(this,require("_process"))},{"./DOMPropertyOperations":43,"./LinkedValueUtils":54,"./ReactDOMComponentTree":64,"./ReactUpdates":108,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"object-assign":26}],70:[function(require,module,exports){(function(process){"use strict";var DOMProperty=require("./DOMProperty");var ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook");var warning=require("fbjs/lib/warning");var warnedProperties={};var rARIA=new RegExp("^(aria)-["+DOMProperty.ATTRIBUTE_NAME_CHAR+"]*$");function validateProperty(tagName,name,debugID){if(warnedProperties.hasOwnProperty(name)&&warnedProperties[name]){return true}if(rARIA.test(name)){var lowerCasedName=name.toLowerCase();var standardName=DOMProperty.getPossibleStandardName.hasOwnProperty(lowerCasedName)?DOMProperty.getPossibleStandardName[lowerCasedName]:null;if(standardName==null){warnedProperties[name]=true;return false}if(name!==standardName){process.env.NODE_ENV!=="production"?warning(false,"Unknown ARIA attribute %s. Did you mean %s?%s",name,standardName,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0;warnedProperties[name]=true;return true}}return true}function warnInvalidARIAProps(debugID,element){var invalidProps=[];for(var key in element.props){var isValid=validateProperty(element.type,key,debugID);if(!isValid){invalidProps.push(key)}}var unknownPropString=invalidProps.map(function(prop){return"`"+prop+"`"}).join(", ");if(invalidProps.length===1){process.env.NODE_ENV!=="production"?warning(false,"Invalid aria prop %s on <%s> tag. "+"For details, see https://fb.me/invalid-aria-prop%s",unknownPropString,element.type,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0}else if(invalidProps.length>1){process.env.NODE_ENV!=="production"?warning(false,"Invalid aria props %s on <%s> tag. "+"For details, see https://fb.me/invalid-aria-prop%s",unknownPropString,element.type,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0}}function handleElement(debugID,element){if(element==null||typeof element.type!=="string"){return}if(element.type.indexOf("-")>=0||element.props.is){return}warnInvalidARIAProps(debugID,element)}var ReactDOMInvalidARIAHook={onBeforeMountComponent:function(debugID,element){if(process.env.NODE_ENV!=="production"){handleElement(debugID,element)}},onBeforeUpdateComponent:function(debugID,element){if(process.env.NODE_ENV!=="production"){handleElement(debugID,element)}}};module.exports=ReactDOMInvalidARIAHook}).call(this,require("_process"))},{"./DOMProperty":42,_process:184,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],71:[function(require,module,exports){(function(process){"use strict";var ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook");var warning=require("fbjs/lib/warning");var didWarnValueNull=false;function handleElement(debugID,element){if(element==null){return}if(element.type!=="input"&&element.type!=="textarea"&&element.type!=="select"){return}if(element.props!=null&&element.props.value===null&&!didWarnValueNull){process.env.NODE_ENV!=="production"?warning(false,"`value` prop on `%s` should not be null. "+"Consider using the empty string to clear the component or `undefined` "+"for uncontrolled components.%s",element.type,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0;didWarnValueNull=true}}var ReactDOMNullInputValuePropHook={onBeforeMountComponent:function(debugID,element){handleElement(debugID,element)},onBeforeUpdateComponent:function(debugID,element){handleElement(debugID,element)}};module.exports=ReactDOMNullInputValuePropHook}).call(this,require("_process"))},{_process:184,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],72:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var React=require("react/lib/React");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMSelect=require("./ReactDOMSelect");var warning=require("fbjs/lib/warning");var didWarnInvalidOptionChildren=false;function flattenChildren(children){var content="";React.Children.forEach(children,function(child){if(child==null){return}if(typeof child==="string"||typeof child==="number"){content+=child}else if(!didWarnInvalidOptionChildren){didWarnInvalidOptionChildren=true;process.env.NODE_ENV!=="production"?warning(false,"Only strings and numbers are supported as <option> children."):void 0}});return content}var ReactDOMOption={mountWrapper:function(inst,props,hostParent){if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(props.selected==null,"Use the `defaultValue` or `value` props on <select> instead of "+"setting `selected` on <option>."):void 0}var selectValue=null;if(hostParent!=null){var selectParent=hostParent;if(selectParent._tag==="optgroup"){selectParent=selectParent._hostParent}if(selectParent!=null&&selectParent._tag==="select"){selectValue=ReactDOMSelect.getSelectValueContext(selectParent)}}var selected=null;if(selectValue!=null){var value;if(props.value!=null){value=props.value+""}else{value=flattenChildren(props.children)}selected=false;if(Array.isArray(selectValue)){for(var i=0;i<selectValue.length;i++){if(""+selectValue[i]===value){selected=true;break}}}else{selected=""+selectValue===value}}inst._wrapperState={selected:selected}},postMountWrapper:function(inst){var props=inst._currentElement.props;if(props.value!=null){var node=ReactDOMComponentTree.getNodeFromInstance(inst);node.setAttribute("value",props.value)}},getHostProps:function(inst,props){var hostProps=_assign({selected:undefined,children:undefined},props);if(inst._wrapperState.selected!=null){hostProps.selected=inst._wrapperState.selected}var content=flattenChildren(props.children);if(content){hostProps.children=content}return hostProps}};module.exports=ReactDOMOption}).call(this,require("_process"))},{"./ReactDOMComponentTree":64,"./ReactDOMSelect":73,_process:184,"fbjs/lib/warning":25,"object-assign":26,"react/lib/React":160}],73:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var LinkedValueUtils=require("./LinkedValueUtils");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactUpdates=require("./ReactUpdates");var warning=require("fbjs/lib/warning");var didWarnValueLink=false;var didWarnValueDefaultValue=false;function updateOptionsIfPendingUpdateAndMounted(){if(this._rootNodeID&&this._wrapperState.pendingUpdate){this._wrapperState.pendingUpdate=false;var props=this._currentElement.props;var value=LinkedValueUtils.getValue(props);if(value!=null){updateOptions(this,Boolean(props.multiple),value)}}}function getDeclarationErrorAddendum(owner){if(owner){var name=owner.getName();if(name){return" Check the render method of `"+name+"`."}}return""}var valuePropNames=["value","defaultValue"];function checkSelectPropTypes(inst,props){var owner=inst._currentElement._owner;LinkedValueUtils.checkPropTypes("select",props,owner);if(props.valueLink!==undefined&&!didWarnValueLink){process.env.NODE_ENV!=="production"?warning(false,"`valueLink` prop on `select` is deprecated; set `value` and `onChange` instead."):void 0;didWarnValueLink=true}for(var i=0;i<valuePropNames.length;i++){var propName=valuePropNames[i];if(props[propName]==null){continue}var isArray=Array.isArray(props[propName]);if(props.multiple&&!isArray){process.env.NODE_ENV!=="production"?warning(false,"The `%s` prop supplied to <select> must be an array if "+"`multiple` is true.%s",propName,getDeclarationErrorAddendum(owner)):void 0}else if(!props.multiple&&isArray){process.env.NODE_ENV!=="production"?warning(false,"The `%s` prop supplied to <select> must be a scalar "+"value if `multiple` is false.%s",propName,getDeclarationErrorAddendum(owner)):void 0}}}function updateOptions(inst,multiple,propValue){var selectedValue,i;var options=ReactDOMComponentTree.getNodeFromInstance(inst).options;if(multiple){selectedValue={};for(i=0;i<propValue.length;i++){selectedValue[""+propValue[i]]=true}for(i=0;i<options.length;i++){var selected=selectedValue.hasOwnProperty(options[i].value);if(options[i].selected!==selected){options[i].selected=selected}}}else{selectedValue=""+propValue;for(i=0;i<options.length;i++){if(options[i].value===selectedValue){options[i].selected=true;return}}if(options.length){options[0].selected=true}}}var ReactDOMSelect={getHostProps:function(inst,props){return _assign({},props,{onChange:inst._wrapperState.onChange,value:undefined})},mountWrapper:function(inst,props){if(process.env.NODE_ENV!=="production"){checkSelectPropTypes(inst,props)}var value=LinkedValueUtils.getValue(props);inst._wrapperState={pendingUpdate:false,initialValue:value!=null?value:props.defaultValue,listeners:null,onChange:_handleChange.bind(inst),wasMultiple:Boolean(props.multiple)};if(props.value!==undefined&&props.defaultValue!==undefined&&!didWarnValueDefaultValue){process.env.NODE_ENV!=="production"?warning(false,"Select elements must be either controlled or uncontrolled "+"(specify either the value prop, or the defaultValue prop, but not "+"both). Decide between using a controlled or uncontrolled select "+"element and remove one of these props. More info: "+"https://fb.me/react-controlled-components"):void 0;didWarnValueDefaultValue=true}},getSelectValueContext:function(inst){return inst._wrapperState.initialValue},postUpdateWrapper:function(inst){var props=inst._currentElement.props;inst._wrapperState.initialValue=undefined;var wasMultiple=inst._wrapperState.wasMultiple;inst._wrapperState.wasMultiple=Boolean(props.multiple);var value=LinkedValueUtils.getValue(props);if(value!=null){inst._wrapperState.pendingUpdate=false;updateOptions(inst,Boolean(props.multiple),value)}else if(wasMultiple!==Boolean(props.multiple)){if(props.defaultValue!=null){updateOptions(inst,Boolean(props.multiple),props.defaultValue)}else{updateOptions(inst,Boolean(props.multiple),props.multiple?[]:"")}}}};function _handleChange(event){var props=this._currentElement.props;var returnValue=LinkedValueUtils.executeOnChange(props,event);if(this._rootNodeID){this._wrapperState.pendingUpdate=true}ReactUpdates.asap(updateOptionsIfPendingUpdateAndMounted,this);return returnValue}module.exports=ReactDOMSelect}).call(this,require("_process"))},{"./LinkedValueUtils":54,"./ReactDOMComponentTree":64,"./ReactUpdates":108,_process:184,"fbjs/lib/warning":25,"object-assign":26}],74:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var getNodeForCharacterOffset=require("./getNodeForCharacterOffset");var getTextContentAccessor=require("./getTextContentAccessor");function isCollapsed(anchorNode,anchorOffset,focusNode,focusOffset){return anchorNode===focusNode&&anchorOffset===focusOffset}function getIEOffsets(node){var selection=document.selection;var selectedRange=selection.createRange();var selectedLength=selectedRange.text.length;var fromStart=selectedRange.duplicate();fromStart.moveToElementText(node);fromStart.setEndPoint("EndToStart",selectedRange);var startOffset=fromStart.text.length;var endOffset=startOffset+selectedLength;return{start:startOffset,end:endOffset}}function getModernOffsets(node){var selection=window.getSelection&&window.getSelection();if(!selection||selection.rangeCount===0){return null}var anchorNode=selection.anchorNode;var anchorOffset=selection.anchorOffset;var focusNode=selection.focusNode;var focusOffset=selection.focusOffset;var currentRange=selection.getRangeAt(0);try{currentRange.startContainer.nodeType;currentRange.endContainer.nodeType}catch(e){return null}var isSelectionCollapsed=isCollapsed(selection.anchorNode,selection.anchorOffset,selection.focusNode,selection.focusOffset);var rangeLength=isSelectionCollapsed?0:currentRange.toString().length;var tempRange=currentRange.cloneRange();tempRange.selectNodeContents(node);tempRange.setEnd(currentRange.startContainer,currentRange.startOffset);var isTempRangeCollapsed=isCollapsed(tempRange.startContainer,tempRange.startOffset,tempRange.endContainer,tempRange.endOffset);var start=isTempRangeCollapsed?0:tempRange.toString().length;var end=start+rangeLength;var detectionRange=document.createRange();detectionRange.setStart(anchorNode,anchorOffset);detectionRange.setEnd(focusNode,focusOffset);var isBackward=detectionRange.collapsed;return{start:isBackward?end:start,end:isBackward?start:end}}function setIEOffsets(node,offsets){var range=document.selection.createRange().duplicate();var start,end;if(offsets.end===undefined){start=offsets.start;end=start}else if(offsets.start>offsets.end){start=offsets.end;end=offsets.start}else{start=offsets.start;end=offsets.end}range.moveToElementText(node);range.moveStart("character",start);range.setEndPoint("EndToStart",range);range.moveEnd("character",end-start);range.select()}function setModernOffsets(node,offsets){if(!window.getSelection){return}var selection=window.getSelection();var length=node[getTextContentAccessor()].length;var start=Math.min(offsets.start,length);var end=offsets.end===undefined?start:Math.min(offsets.end,length);if(!selection.extend&&start>end){var temp=end;end=start;start=temp}var startMarker=getNodeForCharacterOffset(node,start);var endMarker=getNodeForCharacterOffset(node,end);if(startMarker&&endMarker){var range=document.createRange();range.setStart(startMarker.node,startMarker.offset);selection.removeAllRanges();if(start>end){selection.addRange(range);selection.extend(endMarker.node,endMarker.offset)}else{range.setEnd(endMarker.node,endMarker.offset);selection.addRange(range)}}}var useIEOffsets=ExecutionEnvironment.canUseDOM&&"selection"in document&&!("getSelection"in window);var ReactDOMSelection={getOffsets:useIEOffsets?getIEOffsets:getModernOffsets,setOffsets:useIEOffsets?setIEOffsets:setModernOffsets};module.exports=ReactDOMSelection},{"./getNodeForCharacterOffset":143,"./getTextContentAccessor":144,"fbjs/lib/ExecutionEnvironment":4}],75:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var DOMChildrenOperations=require("./DOMChildrenOperations");var DOMLazyTree=require("./DOMLazyTree");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var escapeTextContentForBrowser=require("./escapeTextContentForBrowser");var invariant=require("fbjs/lib/invariant");var validateDOMNesting=require("./validateDOMNesting");var ReactDOMTextComponent=function(text){this._currentElement=text;this._stringText=""+text;this._hostNode=null;this._hostParent=null;this._domID=0;this._mountIndex=0;this._closingComment=null;this._commentNodes=null};_assign(ReactDOMTextComponent.prototype,{mountComponent:function(transaction,hostParent,hostContainerInfo,context){if(process.env.NODE_ENV!=="production"){var parentInfo;if(hostParent!=null){parentInfo=hostParent._ancestorInfo}else if(hostContainerInfo!=null){parentInfo=hostContainerInfo._ancestorInfo}if(parentInfo){validateDOMNesting(null,this._stringText,this,parentInfo)}}var domID=hostContainerInfo._idCounter++;var openingValue=" react-text: "+domID+" ";var closingValue=" /react-text ";this._domID=domID;this._hostParent=hostParent;if(transaction.useCreateElement){var ownerDocument=hostContainerInfo._ownerDocument;var openingComment=ownerDocument.createComment(openingValue);var closingComment=ownerDocument.createComment(closingValue);var lazyTree=DOMLazyTree(ownerDocument.createDocumentFragment());DOMLazyTree.queueChild(lazyTree,DOMLazyTree(openingComment));if(this._stringText){DOMLazyTree.queueChild(lazyTree,DOMLazyTree(ownerDocument.createTextNode(this._stringText)))}DOMLazyTree.queueChild(lazyTree,DOMLazyTree(closingComment));ReactDOMComponentTree.precacheNode(this,openingComment);this._closingComment=closingComment;return lazyTree}else{var escapedText=escapeTextContentForBrowser(this._stringText);if(transaction.renderToStaticMarkup){return escapedText}return"\x3c!--"+openingValue+"--\x3e"+escapedText+"\x3c!--"+closingValue+"--\x3e"}},receiveComponent:function(nextText,transaction){if(nextText!==this._currentElement){this._currentElement=nextText;var nextStringText=""+nextText;if(nextStringText!==this._stringText){this._stringText=nextStringText;var commentNodes=this.getHostNode();DOMChildrenOperations.replaceDelimitedText(commentNodes[0],commentNodes[1],nextStringText)}}},getHostNode:function(){var hostNode=this._commentNodes;if(hostNode){return hostNode}if(!this._closingComment){var openingComment=ReactDOMComponentTree.getNodeFromInstance(this);var node=openingComment.nextSibling;while(true){!(node!=null)?process.env.NODE_ENV!=="production"?invariant(false,"Missing closing comment for text component %s",this._domID):_prodInvariant("67",this._domID):void 0;if(node.nodeType===8&&node.nodeValue===" /react-text "){this._closingComment=node;break}node=node.nextSibling}}hostNode=[this._hostNode,this._closingComment];this._commentNodes=hostNode;return hostNode},unmountComponent:function(){this._closingComment=null;this._commentNodes=null;ReactDOMComponentTree.uncacheNode(this)}});module.exports=ReactDOMTextComponent}).call(this,require("_process"))},{"./DOMChildrenOperations":39,"./DOMLazyTree":40,"./ReactDOMComponentTree":64,"./escapeTextContentForBrowser":133,"./reactProdInvariant":151,"./validateDOMNesting":157,_process:184,"fbjs/lib/invariant":18,"object-assign":26}],76:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var LinkedValueUtils=require("./LinkedValueUtils");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactUpdates=require("./ReactUpdates");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var didWarnValueLink=false;var didWarnValDefaultVal=false;function forceUpdateIfMounted(){if(this._rootNodeID){ReactDOMTextarea.updateWrapper(this)}}var ReactDOMTextarea={getHostProps:function(inst,props){!(props.dangerouslySetInnerHTML==null)?process.env.NODE_ENV!=="production"?invariant(false,"`dangerouslySetInnerHTML` does not make sense on <textarea>."):_prodInvariant("91"):void 0;var hostProps=_assign({},props,{value:undefined,defaultValue:undefined,children:""+inst._wrapperState.initialValue,onChange:inst._wrapperState.onChange});return hostProps},mountWrapper:function(inst,props){if(process.env.NODE_ENV!=="production"){LinkedValueUtils.checkPropTypes("textarea",props,inst._currentElement._owner);if(props.valueLink!==undefined&&!didWarnValueLink){process.env.NODE_ENV!=="production"?warning(false,"`valueLink` prop on `textarea` is deprecated; set `value` and `onChange` instead."):void 0;didWarnValueLink=true}if(props.value!==undefined&&props.defaultValue!==undefined&&!didWarnValDefaultVal){process.env.NODE_ENV!=="production"?warning(false,"Textarea elements must be either controlled or uncontrolled "+"(specify either the value prop, or the defaultValue prop, but not "+"both). Decide between using a controlled or uncontrolled textarea "+"and remove one of these props. More info: "+"https://fb.me/react-controlled-components"):void 0;didWarnValDefaultVal=true}}var value=LinkedValueUtils.getValue(props);var initialValue=value;if(value==null){var defaultValue=props.defaultValue;var children=props.children;if(children!=null){if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(false,"Use the `defaultValue` or `value` props instead of setting "+"children on <textarea>."):void 0}!(defaultValue==null)?process.env.NODE_ENV!=="production"?invariant(false,"If you supply `defaultValue` on a <textarea>, do not pass children."):_prodInvariant("92"):void 0;if(Array.isArray(children)){!(children.length<=1)?process.env.NODE_ENV!=="production"?invariant(false,"<textarea> can only have at most one child."):_prodInvariant("93"):void 0;children=children[0]}defaultValue=""+children}if(defaultValue==null){defaultValue=""}initialValue=defaultValue}inst._wrapperState={initialValue:""+initialValue,listeners:null,onChange:_handleChange.bind(inst)}},updateWrapper:function(inst){var props=inst._currentElement.props;var node=ReactDOMComponentTree.getNodeFromInstance(inst);var value=LinkedValueUtils.getValue(props);if(value!=null){var newValue=""+value;if(newValue!==node.value){node.value=newValue}if(props.defaultValue==null){node.defaultValue=newValue}}if(props.defaultValue!=null){node.defaultValue=props.defaultValue}},postMountWrapper:function(inst){var node=ReactDOMComponentTree.getNodeFromInstance(inst);var textContent=node.textContent;if(textContent===inst._wrapperState.initialValue){node.value=textContent}}};function _handleChange(event){var props=this._currentElement.props;var returnValue=LinkedValueUtils.executeOnChange(props,event);ReactUpdates.asap(forceUpdateIfMounted,this);return returnValue}module.exports=ReactDOMTextarea}).call(this,require("_process"))},{"./LinkedValueUtils":54,"./ReactDOMComponentTree":64,"./ReactUpdates":108,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"object-assign":26}],77:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");function getLowestCommonAncestor(instA,instB){!("_hostNode"in instA)?process.env.NODE_ENV!=="production"?invariant(false,"getNodeFromInstance: Invalid argument."):_prodInvariant("33"):void 0;!("_hostNode"in instB)?process.env.NODE_ENV!=="production"?invariant(false,"getNodeFromInstance: Invalid argument."):_prodInvariant("33"):void 0;var depthA=0;for(var tempA=instA;tempA;tempA=tempA._hostParent){depthA++}var depthB=0;for(var tempB=instB;tempB;tempB=tempB._hostParent){depthB++}while(depthA-depthB>0){instA=instA._hostParent;depthA--}while(depthB-depthA>0){instB=instB._hostParent;depthB--}var depth=depthA;while(depth--){if(instA===instB){return instA}instA=instA._hostParent;instB=instB._hostParent}return null}function isAncestor(instA,instB){!("_hostNode"in instA)?process.env.NODE_ENV!=="production"?invariant(false,"isAncestor: Invalid argument."):_prodInvariant("35"):void 0;!("_hostNode"in instB)?process.env.NODE_ENV!=="production"?invariant(false,"isAncestor: Invalid argument."):_prodInvariant("35"):void 0;while(instB){if(instB===instA){return true}instB=instB._hostParent}return false}function getParentInstance(inst){!("_hostNode"in inst)?process.env.NODE_ENV!=="production"?invariant(false,"getParentInstance: Invalid argument."):_prodInvariant("36"):void 0;return inst._hostParent}function traverseTwoPhase(inst,fn,arg){var path=[];while(inst){path.push(inst);inst=inst._hostParent}var i;for(i=path.length;i-- >0;){fn(path[i],"captured",arg)}for(i=0;i<path.length;i++){fn(path[i],"bubbled",arg)}}function traverseEnterLeave(from,to,fn,argFrom,argTo){var common=from&&to?getLowestCommonAncestor(from,to):null;var pathFrom=[];while(from&&from!==common){pathFrom.push(from);from=from._hostParent}var pathTo=[];while(to&&to!==common){pathTo.push(to);to=to._hostParent}var i;for(i=0;i<pathFrom.length;i++){fn(pathFrom[i],"bubbled",argFrom)}for(i=pathTo.length;i-- >0;){fn(pathTo[i],"captured",argTo)}}module.exports={isAncestor:isAncestor,getLowestCommonAncestor:getLowestCommonAncestor,getParentInstance:getParentInstance,traverseTwoPhase:traverseTwoPhase,traverseEnterLeave:traverseEnterLeave}}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],78:[function(require,module,exports){(function(process){"use strict";var DOMProperty=require("./DOMProperty");var EventPluginRegistry=require("./EventPluginRegistry");var ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook");var warning=require("fbjs/lib/warning");if(process.env.NODE_ENV!=="production"){var reactProps={children:true,dangerouslySetInnerHTML:true,key:true,ref:true,autoFocus:true,defaultValue:true,valueLink:true,defaultChecked:true,checkedLink:true,innerHTML:true,suppressContentEditableWarning:true,onFocusIn:true,onFocusOut:true};var warnedProperties={};var validateProperty=function(tagName,name,debugID){if(DOMProperty.properties.hasOwnProperty(name)||DOMProperty.isCustomAttribute(name)){return true}if(reactProps.hasOwnProperty(name)&&reactProps[name]||warnedProperties.hasOwnProperty(name)&&warnedProperties[name]){return true}if(EventPluginRegistry.registrationNameModules.hasOwnProperty(name)){return true}warnedProperties[name]=true;var lowerCasedName=name.toLowerCase();var standardName=DOMProperty.isCustomAttribute(lowerCasedName)?lowerCasedName:DOMProperty.getPossibleStandardName.hasOwnProperty(lowerCasedName)?DOMProperty.getPossibleStandardName[lowerCasedName]:null;var registrationName=EventPluginRegistry.possibleRegistrationNames.hasOwnProperty(lowerCasedName)?EventPluginRegistry.possibleRegistrationNames[lowerCasedName]:null;if(standardName!=null){process.env.NODE_ENV!=="production"?warning(false,"Unknown DOM property %s. Did you mean %s?%s",name,standardName,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0;return true}else if(registrationName!=null){process.env.NODE_ENV!=="production"?warning(false,"Unknown event handler property %s. Did you mean `%s`?%s",name,registrationName,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0;return true}else{return false}}}var warnUnknownProperties=function(debugID,element){var unknownProps=[];for(var key in element.props){var isValid=validateProperty(element.type,key,debugID);if(!isValid){unknownProps.push(key)}}var unknownPropString=unknownProps.map(function(prop){return"`"+prop+"`"}).join(", ");if(unknownProps.length===1){process.env.NODE_ENV!=="production"?warning(false,"Unknown prop %s on <%s> tag. Remove this prop from the element. "+"For details, see https://fb.me/react-unknown-prop%s",unknownPropString,element.type,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0}else if(unknownProps.length>1){process.env.NODE_ENV!=="production"?warning(false,"Unknown props %s on <%s> tag. Remove these props from the element. "+"For details, see https://fb.me/react-unknown-prop%s",unknownPropString,element.type,ReactComponentTreeHook.getStackAddendumByID(debugID)):void 0}};function handleElement(debugID,element){if(element==null||typeof element.type!=="string"){return}if(element.type.indexOf("-")>=0||element.props.is){return}warnUnknownProperties(debugID,element)}var ReactDOMUnknownPropertyHook={onBeforeMountComponent:function(debugID,element){handleElement(debugID,element)},onBeforeUpdateComponent:function(debugID,element){handleElement(debugID,element)}};module.exports=ReactDOMUnknownPropertyHook}).call(this,require("_process"))},{"./DOMProperty":42,"./EventPluginRegistry":48,_process:184,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],79:[function(require,module,exports){(function(process){"use strict";var ReactInvalidSetStateWarningHook=require("./ReactInvalidSetStateWarningHook");var ReactHostOperationHistoryHook=require("./ReactHostOperationHistoryHook");var ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var performanceNow=require("fbjs/lib/performanceNow");var warning=require("fbjs/lib/warning");var hooks=[];var didHookThrowForEvent={};function callHook(event,fn,context,arg1,arg2,arg3,arg4,arg5){try{fn.call(context,arg1,arg2,arg3,arg4,arg5)}catch(e){process.env.NODE_ENV!=="production"?warning(didHookThrowForEvent[event],"Exception thrown by hook while handling %s: %s",event,e+"\n"+e.stack):void 0;didHookThrowForEvent[event]=true}}function emitEvent(event,arg1,arg2,arg3,arg4,arg5){for(var i=0;i<hooks.length;i++){var hook=hooks[i];var fn=hook[event];if(fn){callHook(event,fn,hook,arg1,arg2,arg3,arg4,arg5)}}}var isProfiling=false;var flushHistory=[];var lifeCycleTimerStack=[];var currentFlushNesting=0;var currentFlushMeasurements=[];var currentFlushStartTime=0;var currentTimerDebugID=null;var currentTimerStartTime=0;var currentTimerNestedFlushDuration=0;var currentTimerType=null;var lifeCycleTimerHasWarned=false;function clearHistory(){ReactComponentTreeHook.purgeUnmountedComponents();ReactHostOperationHistoryHook.clearHistory()}function getTreeSnapshot(registeredIDs){return registeredIDs.reduce(function(tree,id){var ownerID=ReactComponentTreeHook.getOwnerID(id);var parentID=ReactComponentTreeHook.getParentID(id);tree[id]={displayName:ReactComponentTreeHook.getDisplayName(id),text:ReactComponentTreeHook.getText(id),updateCount:ReactComponentTreeHook.getUpdateCount(id),childIDs:ReactComponentTreeHook.getChildIDs(id),ownerID:ownerID||parentID&&ReactComponentTreeHook.getOwnerID(parentID)||0,parentID:parentID};return tree},{})}function resetMeasurements(){var previousStartTime=currentFlushStartTime;var previousMeasurements=currentFlushMeasurements;var previousOperations=ReactHostOperationHistoryHook.getHistory();if(currentFlushNesting===0){currentFlushStartTime=0;currentFlushMeasurements=[];clearHistory();return}if(previousMeasurements.length||previousOperations.length){var registeredIDs=ReactComponentTreeHook.getRegisteredIDs();flushHistory.push({duration:performanceNow()-previousStartTime,measurements:previousMeasurements||[],operations:previousOperations||[],treeSnapshot:getTreeSnapshot(registeredIDs)})}clearHistory();currentFlushStartTime=performanceNow();currentFlushMeasurements=[]}function checkDebugID(debugID){var allowRoot=arguments.length>1&&arguments[1]!==undefined?arguments[1]:false;if(allowRoot&&debugID===0){return}if(!debugID){process.env.NODE_ENV!=="production"?warning(false,"ReactDebugTool: debugID may not be empty."):void 0}}function beginLifeCycleTimer(debugID,timerType){if(currentFlushNesting===0){return}if(currentTimerType&&!lifeCycleTimerHasWarned){process.env.NODE_ENV!=="production"?warning(false,"There is an internal error in the React performance measurement code. "+"Did not expect %s timer to start while %s timer is still in "+"progress for %s instance.",timerType,currentTimerType||"no",debugID===currentTimerDebugID?"the same":"another"):void 0;lifeCycleTimerHasWarned=true}currentTimerStartTime=performanceNow();currentTimerNestedFlushDuration=0;currentTimerDebugID=debugID;currentTimerType=timerType}function endLifeCycleTimer(debugID,timerType){if(currentFlushNesting===0){return}if(currentTimerType!==timerType&&!lifeCycleTimerHasWarned){process.env.NODE_ENV!=="production"?warning(false,"There is an internal error in the React performance measurement code. "+"We did not expect %s timer to stop while %s timer is still in "+"progress for %s instance. Please report this as a bug in React.",timerType,currentTimerType||"no",debugID===currentTimerDebugID?"the same":"another"):void 0;lifeCycleTimerHasWarned=true}if(isProfiling){currentFlushMeasurements.push({timerType:timerType,instanceID:debugID,duration:performanceNow()-currentTimerStartTime-currentTimerNestedFlushDuration})}currentTimerStartTime=0;currentTimerNestedFlushDuration=0;currentTimerDebugID=null;currentTimerType=null}function pauseCurrentLifeCycleTimer(){var currentTimer={startTime:currentTimerStartTime,nestedFlushStartTime:performanceNow(),debugID:currentTimerDebugID,timerType:currentTimerType};lifeCycleTimerStack.push(currentTimer);currentTimerStartTime=0;currentTimerNestedFlushDuration=0;currentTimerDebugID=null;currentTimerType=null}function resumeCurrentLifeCycleTimer(){var _lifeCycleTimerStack$=lifeCycleTimerStack.pop(),startTime=_lifeCycleTimerStack$.startTime,nestedFlushStartTime=_lifeCycleTimerStack$.nestedFlushStartTime,debugID=_lifeCycleTimerStack$.debugID,timerType=_lifeCycleTimerStack$.timerType;var nestedFlushDuration=performanceNow()-nestedFlushStartTime;currentTimerStartTime=startTime;currentTimerNestedFlushDuration+=nestedFlushDuration;currentTimerDebugID=debugID;currentTimerType=timerType}var lastMarkTimeStamp=0;var canUsePerformanceMeasure=typeof performance!=="undefined"&&typeof performance.mark==="function"&&typeof performance.clearMarks==="function"&&typeof performance.measure==="function"&&typeof performance.clearMeasures==="function";function shouldMark(debugID){if(!isProfiling||!canUsePerformanceMeasure){return false}var element=ReactComponentTreeHook.getElement(debugID);if(element==null||typeof element!=="object"){return false}var isHostElement=typeof element.type==="string";if(isHostElement){return false}return true}function markBegin(debugID,markType){if(!shouldMark(debugID)){return}var markName=debugID+"::"+markType;lastMarkTimeStamp=performanceNow();performance.mark(markName)}function markEnd(debugID,markType){if(!shouldMark(debugID)){return}var markName=debugID+"::"+markType;var displayName=ReactComponentTreeHook.getDisplayName(debugID)||"Unknown";var timeStamp=performanceNow();if(timeStamp-lastMarkTimeStamp>.1){var measurementName=displayName+" ["+markType+"]";performance.measure(measurementName,markName)}performance.clearMarks(markName);if(measurementName){performance.clearMeasures(measurementName)}}var ReactDebugTool={addHook:function(hook){hooks.push(hook)},removeHook:function(hook){for(var i=0;i<hooks.length;i++){if(hooks[i]===hook){hooks.splice(i,1);i--}}},isProfiling:function(){return isProfiling},beginProfiling:function(){if(isProfiling){return}isProfiling=true;flushHistory.length=0;resetMeasurements();ReactDebugTool.addHook(ReactHostOperationHistoryHook)},endProfiling:function(){if(!isProfiling){return}isProfiling=false;resetMeasurements();ReactDebugTool.removeHook(ReactHostOperationHistoryHook)},getFlushHistory:function(){return flushHistory},onBeginFlush:function(){currentFlushNesting++;resetMeasurements();pauseCurrentLifeCycleTimer();emitEvent("onBeginFlush")},onEndFlush:function(){resetMeasurements();currentFlushNesting--;resumeCurrentLifeCycleTimer();emitEvent("onEndFlush")},onBeginLifeCycleTimer:function(debugID,timerType){checkDebugID(debugID);emitEvent("onBeginLifeCycleTimer",debugID,timerType);markBegin(debugID,timerType);beginLifeCycleTimer(debugID,timerType)},onEndLifeCycleTimer:function(debugID,timerType){checkDebugID(debugID);endLifeCycleTimer(debugID,timerType);markEnd(debugID,timerType);emitEvent("onEndLifeCycleTimer",debugID,timerType)},onBeginProcessingChildContext:function(){emitEvent("onBeginProcessingChildContext")},onEndProcessingChildContext:function(){emitEvent("onEndProcessingChildContext")},onHostOperation:function(operation){checkDebugID(operation.instanceID);emitEvent("onHostOperation",operation)},onSetState:function(){emitEvent("onSetState")},onSetChildren:function(debugID,childDebugIDs){checkDebugID(debugID);childDebugIDs.forEach(checkDebugID);emitEvent("onSetChildren",debugID,childDebugIDs)},onBeforeMountComponent:function(debugID,element,parentDebugID){checkDebugID(debugID);checkDebugID(parentDebugID,true);emitEvent("onBeforeMountComponent",debugID,element,parentDebugID);markBegin(debugID,"mount")},onMountComponent:function(debugID){checkDebugID(debugID);markEnd(debugID,"mount");emitEvent("onMountComponent",debugID)},onBeforeUpdateComponent:function(debugID,element){checkDebugID(debugID);emitEvent("onBeforeUpdateComponent",debugID,element);markBegin(debugID,"update")},onUpdateComponent:function(debugID){checkDebugID(debugID);markEnd(debugID,"update");emitEvent("onUpdateComponent",debugID)},onBeforeUnmountComponent:function(debugID){checkDebugID(debugID);emitEvent("onBeforeUnmountComponent",debugID);markBegin(debugID,"unmount")},onUnmountComponent:function(debugID){checkDebugID(debugID);markEnd(debugID,"unmount");emitEvent("onUnmountComponent",debugID)},onTestEvent:function(){emitEvent("onTestEvent")}};ReactDebugTool.addDevtool=ReactDebugTool.addHook;ReactDebugTool.removeDevtool=ReactDebugTool.removeHook;ReactDebugTool.addHook(ReactInvalidSetStateWarningHook);ReactDebugTool.addHook(ReactComponentTreeHook);var url=ExecutionEnvironment.canUseDOM&&window.location.href||"";if(/[?&]react_perf\b/.test(url)){ReactDebugTool.beginProfiling()}module.exports=ReactDebugTool}).call(this,require("_process"))},{"./ReactHostOperationHistoryHook":89,"./ReactInvalidSetStateWarningHook":94,_process:184,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/performanceNow":23,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],80:[function(require,module,exports){"use strict";var _assign=require("object-assign");var ReactUpdates=require("./ReactUpdates");var Transaction=require("./Transaction");var emptyFunction=require("fbjs/lib/emptyFunction");var RESET_BATCHED_UPDATES={initialize:emptyFunction,close:function(){ReactDefaultBatchingStrategy.isBatchingUpdates=false}};var FLUSH_BATCHED_UPDATES={initialize:emptyFunction,close:ReactUpdates.flushBatchedUpdates.bind(ReactUpdates)};var TRANSACTION_WRAPPERS=[FLUSH_BATCHED_UPDATES,RESET_BATCHED_UPDATES];function ReactDefaultBatchingStrategyTransaction(){this.reinitializeTransaction()}_assign(ReactDefaultBatchingStrategyTransaction.prototype,Transaction,{getTransactionWrappers:function(){return TRANSACTION_WRAPPERS}});var transaction=new ReactDefaultBatchingStrategyTransaction;var ReactDefaultBatchingStrategy={isBatchingUpdates:false,batchedUpdates:function(callback,a,b,c,d,e){var alreadyBatchingUpdates=ReactDefaultBatchingStrategy.isBatchingUpdates;ReactDefaultBatchingStrategy.isBatchingUpdates=true;if(alreadyBatchingUpdates){return callback(a,b,c,d,e)}else{return transaction.perform(callback,null,a,b,c,d,e)}}};module.exports=ReactDefaultBatchingStrategy},{"./ReactUpdates":108,"./Transaction":126,"fbjs/lib/emptyFunction":10,"object-assign":26}],81:[function(require,module,exports){"use strict";var ARIADOMPropertyConfig=require("./ARIADOMPropertyConfig");var BeforeInputEventPlugin=require("./BeforeInputEventPlugin");var ChangeEventPlugin=require("./ChangeEventPlugin");var DefaultEventPluginOrder=require("./DefaultEventPluginOrder");var EnterLeaveEventPlugin=require("./EnterLeaveEventPlugin");var HTMLDOMPropertyConfig=require("./HTMLDOMPropertyConfig");var ReactComponentBrowserEnvironment=require("./ReactComponentBrowserEnvironment");var ReactDOMComponent=require("./ReactDOMComponent");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMEmptyComponent=require("./ReactDOMEmptyComponent");var ReactDOMTreeTraversal=require("./ReactDOMTreeTraversal");var ReactDOMTextComponent=require("./ReactDOMTextComponent");var ReactDefaultBatchingStrategy=require("./ReactDefaultBatchingStrategy");var ReactEventListener=require("./ReactEventListener");var ReactInjection=require("./ReactInjection");var ReactReconcileTransaction=require("./ReactReconcileTransaction");var SVGDOMPropertyConfig=require("./SVGDOMPropertyConfig");var SelectEventPlugin=require("./SelectEventPlugin");var SimpleEventPlugin=require("./SimpleEventPlugin");var alreadyInjected=false;function inject(){if(alreadyInjected){return}alreadyInjected=true;ReactInjection.EventEmitter.injectReactEventListener(ReactEventListener);ReactInjection.EventPluginHub.injectEventPluginOrder(DefaultEventPluginOrder);ReactInjection.EventPluginUtils.injectComponentTree(ReactDOMComponentTree);ReactInjection.EventPluginUtils.injectTreeTraversal(ReactDOMTreeTraversal);ReactInjection.EventPluginHub.injectEventPluginsByName({SimpleEventPlugin:SimpleEventPlugin,EnterLeaveEventPlugin:EnterLeaveEventPlugin,ChangeEventPlugin:ChangeEventPlugin,SelectEventPlugin:SelectEventPlugin,BeforeInputEventPlugin:BeforeInputEventPlugin});ReactInjection.HostComponent.injectGenericComponentClass(ReactDOMComponent);ReactInjection.HostComponent.injectTextComponentClass(ReactDOMTextComponent);ReactInjection.DOMProperty.injectDOMPropertyConfig(ARIADOMPropertyConfig);ReactInjection.DOMProperty.injectDOMPropertyConfig(HTMLDOMPropertyConfig);ReactInjection.DOMProperty.injectDOMPropertyConfig(SVGDOMPropertyConfig);ReactInjection.EmptyComponent.injectEmptyComponentFactory(function(instantiate){return new ReactDOMEmptyComponent(instantiate)});ReactInjection.Updates.injectReconcileTransaction(ReactReconcileTransaction);ReactInjection.Updates.injectBatchingStrategy(ReactDefaultBatchingStrategy);ReactInjection.Component.injectEnvironment(ReactComponentBrowserEnvironment)}module.exports={inject:inject}},{"./ARIADOMPropertyConfig":32,"./BeforeInputEventPlugin":34,"./ChangeEventPlugin":38,"./DefaultEventPluginOrder":45,"./EnterLeaveEventPlugin":46,"./HTMLDOMPropertyConfig":52,"./ReactComponentBrowserEnvironment":58,"./ReactDOMComponent":62,"./ReactDOMComponentTree":64,"./ReactDOMEmptyComponent":66,"./ReactDOMTextComponent":75,"./ReactDOMTreeTraversal":77,"./ReactDefaultBatchingStrategy":80,"./ReactEventListener":86,"./ReactInjection":90,"./ReactReconcileTransaction":102,"./SVGDOMPropertyConfig":110,"./SelectEventPlugin":111,"./SimpleEventPlugin":112}],82:[function(require,module,exports){"use strict";var REACT_ELEMENT_TYPE=typeof Symbol==="function"&&Symbol["for"]&&Symbol["for"]("react.element")||60103;module.exports=REACT_ELEMENT_TYPE},{}],83:[function(require,module,exports){"use strict";var emptyComponentFactory;var ReactEmptyComponentInjection={injectEmptyComponentFactory:function(factory){emptyComponentFactory=factory}};var ReactEmptyComponent={create:function(instantiate){return emptyComponentFactory(instantiate)}};ReactEmptyComponent.injection=ReactEmptyComponentInjection;module.exports=ReactEmptyComponent},{}],84:[function(require,module,exports){(function(process){"use strict";var caughtError=null;function invokeGuardedCallback(name,func,a){try{func(a)}catch(x){if(caughtError===null){caughtError=x}}}var ReactErrorUtils={invokeGuardedCallback:invokeGuardedCallback,invokeGuardedCallbackWithCatch:invokeGuardedCallback,rethrowCaughtError:function(){if(caughtError){var error=caughtError;caughtError=null;throw error}}};if(process.env.NODE_ENV!=="production"){if(typeof window!=="undefined"&&typeof window.dispatchEvent==="function"&&typeof document!=="undefined"&&typeof document.createEvent==="function"){var fakeNode=document.createElement("react");ReactErrorUtils.invokeGuardedCallback=function(name,func,a){var boundFunc=func.bind(null,a);var evtType="react-"+name;fakeNode.addEventListener(evtType,boundFunc,false);var evt=document.createEvent("Event");evt.initEvent(evtType,false,false);fakeNode.dispatchEvent(evt);fakeNode.removeEventListener(evtType,boundFunc,false)}}}module.exports=ReactErrorUtils}).call(this,require("_process"))},{_process:184}],85:[function(require,module,exports){"use strict";var EventPluginHub=require("./EventPluginHub");function runEventQueueInBatch(events){EventPluginHub.enqueueEvents(events);EventPluginHub.processEventQueue(false)}var ReactEventEmitterMixin={handleTopLevel:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){var events=EventPluginHub.extractEvents(topLevelType,targetInst,nativeEvent,nativeEventTarget);runEventQueueInBatch(events)}};module.exports=ReactEventEmitterMixin},{"./EventPluginHub":47}],86:[function(require,module,exports){"use strict";var _assign=require("object-assign");var EventListener=require("fbjs/lib/EventListener");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var PooledClass=require("./PooledClass");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactUpdates=require("./ReactUpdates");var getEventTarget=require("./getEventTarget");var getUnboundedScrollPosition=require("fbjs/lib/getUnboundedScrollPosition");function findParent(inst){while(inst._hostParent){inst=inst._hostParent}var rootNode=ReactDOMComponentTree.getNodeFromInstance(inst);var container=rootNode.parentNode;return ReactDOMComponentTree.getClosestInstanceFromNode(container)}function TopLevelCallbackBookKeeping(topLevelType,nativeEvent){this.topLevelType=topLevelType;this.nativeEvent=nativeEvent;this.ancestors=[]}_assign(TopLevelCallbackBookKeeping.prototype,{destructor:function(){this.topLevelType=null;this.nativeEvent=null;this.ancestors.length=0}});PooledClass.addPoolingTo(TopLevelCallbackBookKeeping,PooledClass.twoArgumentPooler);function handleTopLevelImpl(bookKeeping){var nativeEventTarget=getEventTarget(bookKeeping.nativeEvent);var targetInst=ReactDOMComponentTree.getClosestInstanceFromNode(nativeEventTarget);var ancestor=targetInst;do{bookKeeping.ancestors.push(ancestor);ancestor=ancestor&&findParent(ancestor)}while(ancestor);for(var i=0;i<bookKeeping.ancestors.length;i++){targetInst=bookKeeping.ancestors[i];ReactEventListener._handleTopLevel(bookKeeping.topLevelType,targetInst,bookKeeping.nativeEvent,getEventTarget(bookKeeping.nativeEvent))}}function scrollValueMonitor(cb){var scrollPosition=getUnboundedScrollPosition(window);cb(scrollPosition)}var ReactEventListener={_enabled:true,_handleTopLevel:null,WINDOW_HANDLE:ExecutionEnvironment.canUseDOM?window:null,setHandleTopLevel:function(handleTopLevel){ReactEventListener._handleTopLevel=handleTopLevel},setEnabled:function(enabled){ReactEventListener._enabled=!!enabled},isEnabled:function(){return ReactEventListener._enabled},trapBubbledEvent:function(topLevelType,handlerBaseName,element){if(!element){return null}return EventListener.listen(element,handlerBaseName,ReactEventListener.dispatchEvent.bind(null,topLevelType))},trapCapturedEvent:function(topLevelType,handlerBaseName,element){if(!element){return null}return EventListener.capture(element,handlerBaseName,ReactEventListener.dispatchEvent.bind(null,topLevelType))},monitorScrollValue:function(refresh){var callback=scrollValueMonitor.bind(null,refresh);EventListener.listen(window,"scroll",callback)},dispatchEvent:function(topLevelType,nativeEvent){if(!ReactEventListener._enabled){return}var bookKeeping=TopLevelCallbackBookKeeping.getPooled(topLevelType,nativeEvent);try{ReactUpdates.batchedUpdates(handleTopLevelImpl,bookKeeping)}finally{TopLevelCallbackBookKeeping.release(bookKeeping)}}};module.exports=ReactEventListener},{"./PooledClass":55,"./ReactDOMComponentTree":64,"./ReactUpdates":108,"./getEventTarget":140,"fbjs/lib/EventListener":3,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/getUnboundedScrollPosition":15,"object-assign":26}],87:[function(require,module,exports){"use strict";var ReactFeatureFlags={logTopLevelRenders:false};module.exports=ReactFeatureFlags},{}],88:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");var genericComponentClass=null;var textComponentClass=null;var ReactHostComponentInjection={injectGenericComponentClass:function(componentClass){genericComponentClass=componentClass},injectTextComponentClass:function(componentClass){textComponentClass=componentClass}};function createInternalComponent(element){!genericComponentClass?process.env.NODE_ENV!=="production"?invariant(false,"There is no registered component for the tag %s",element.type):_prodInvariant("111",element.type):void 0;return new genericComponentClass(element)}function createInstanceForText(text){return new textComponentClass(text)}function isTextComponent(component){return component instanceof textComponentClass}var ReactHostComponent={createInternalComponent:createInternalComponent,createInstanceForText:createInstanceForText,isTextComponent:isTextComponent,injection:ReactHostComponentInjection};module.exports=ReactHostComponent}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],89:[function(require,module,exports){"use strict";var history=[];var ReactHostOperationHistoryHook={onHostOperation:function(operation){history.push(operation)},clearHistory:function(){if(ReactHostOperationHistoryHook._preventClearing){return}history=[]},getHistory:function(){return history}};module.exports=ReactHostOperationHistoryHook},{}],90:[function(require,module,exports){"use strict";var DOMProperty=require("./DOMProperty");var EventPluginHub=require("./EventPluginHub");var EventPluginUtils=require("./EventPluginUtils");var ReactComponentEnvironment=require("./ReactComponentEnvironment");var ReactEmptyComponent=require("./ReactEmptyComponent");var ReactBrowserEventEmitter=require("./ReactBrowserEventEmitter");var ReactHostComponent=require("./ReactHostComponent");var ReactUpdates=require("./ReactUpdates");var ReactInjection={Component:ReactComponentEnvironment.injection,DOMProperty:DOMProperty.injection,EmptyComponent:ReactEmptyComponent.injection,EventPluginHub:EventPluginHub.injection,EventPluginUtils:EventPluginUtils.injection,EventEmitter:ReactBrowserEventEmitter.injection,HostComponent:ReactHostComponent.injection,Updates:ReactUpdates.injection};module.exports=ReactInjection},{"./DOMProperty":42,"./EventPluginHub":47,"./EventPluginUtils":49,"./ReactBrowserEventEmitter":56,"./ReactComponentEnvironment":59,"./ReactEmptyComponent":83,"./ReactHostComponent":88,"./ReactUpdates":108}],91:[function(require,module,exports){"use strict";var ReactDOMSelection=require("./ReactDOMSelection");var containsNode=require("fbjs/lib/containsNode");var focusNode=require("fbjs/lib/focusNode");var getActiveElement=require("fbjs/lib/getActiveElement");function isInDocument(node){return containsNode(document.documentElement,node)}var ReactInputSelection={hasSelectionCapabilities:function(elem){var nodeName=elem&&elem.nodeName&&elem.nodeName.toLowerCase();return nodeName&&(nodeName==="input"&&elem.type==="text"||nodeName==="textarea"||elem.contentEditable==="true")},getSelectionInformation:function(){var focusedElem=getActiveElement();return{focusedElem:focusedElem,selectionRange:ReactInputSelection.hasSelectionCapabilities(focusedElem)?ReactInputSelection.getSelection(focusedElem):null}},restoreSelection:function(priorSelectionInformation){var curFocusedElem=getActiveElement();var priorFocusedElem=priorSelectionInformation.focusedElem;var priorSelectionRange=priorSelectionInformation.selectionRange;if(curFocusedElem!==priorFocusedElem&&isInDocument(priorFocusedElem)){if(ReactInputSelection.hasSelectionCapabilities(priorFocusedElem)){ReactInputSelection.setSelection(priorFocusedElem,priorSelectionRange)}focusNode(priorFocusedElem)}},getSelection:function(input){var selection;if("selectionStart"in input){selection={start:input.selectionStart,end:input.selectionEnd}}else if(document.selection&&input.nodeName&&input.nodeName.toLowerCase()==="input"){var range=document.selection.createRange();if(range.parentElement()===input){selection={start:-range.moveStart("character",-input.value.length),end:-range.moveEnd("character",-input.value.length)}}}else{selection=ReactDOMSelection.getOffsets(input)}return selection||{start:0,end:0}},setSelection:function(input,offsets){var start=offsets.start;var end=offsets.end;if(end===undefined){end=start}if("selectionStart"in input){input.selectionStart=start;input.selectionEnd=Math.min(end,input.value.length)}else if(document.selection&&input.nodeName&&input.nodeName.toLowerCase()==="input"){var range=input.createTextRange();range.collapse(true);range.moveStart("character",start);range.moveEnd("character",end-start);range.select()}else{ReactDOMSelection.setOffsets(input,offsets)}}};module.exports=ReactInputSelection},{"./ReactDOMSelection":74,"fbjs/lib/containsNode":7,"fbjs/lib/focusNode":12,"fbjs/lib/getActiveElement":13}],92:[function(require,module,exports){"use strict";var ReactInstanceMap={remove:function(key){key._reactInternalInstance=undefined},get:function(key){return key._reactInternalInstance},has:function(key){return key._reactInternalInstance!==undefined},set:function(key,value){key._reactInternalInstance=value}};module.exports=ReactInstanceMap},{}],93:[function(require,module,exports){(function(process){"use strict";var debugTool=null;if(process.env.NODE_ENV!=="production"){var ReactDebugTool=require("./ReactDebugTool");debugTool=ReactDebugTool}module.exports={debugTool:debugTool}}).call(this,require("_process"))},{"./ReactDebugTool":79,_process:184}],94:[function(require,module,exports){(function(process){"use strict";var warning=require("fbjs/lib/warning");if(process.env.NODE_ENV!=="production"){var processingChildContext=false;var warnInvalidSetState=function(){process.env.NODE_ENV!=="production"?warning(!processingChildContext,"setState(...): Cannot call setState() inside getChildContext()"):void 0}}var ReactInvalidSetStateWarningHook={onBeginProcessingChildContext:function(){processingChildContext=true},onEndProcessingChildContext:function(){processingChildContext=false},onSetState:function(){warnInvalidSetState()}};module.exports=ReactInvalidSetStateWarningHook}).call(this,require("_process"))},{_process:184,"fbjs/lib/warning":25}],95:[function(require,module,exports){"use strict";var adler32=require("./adler32");var TAG_END=/\/?>/;var COMMENT_START=/^<\!\-\-/;var ReactMarkupChecksum={CHECKSUM_ATTR_NAME:"data-react-checksum",addChecksumToMarkup:function(markup){var checksum=adler32(markup);if(COMMENT_START.test(markup)){return markup}else{return markup.replace(TAG_END," "+ReactMarkupChecksum.CHECKSUM_ATTR_NAME+'="'+checksum+'"$&')}},canReuseMarkup:function(markup,element){var existingChecksum=element.getAttribute(ReactMarkupChecksum.CHECKSUM_ATTR_NAME);existingChecksum=existingChecksum&&parseInt(existingChecksum,10);var markupChecksum=adler32(markup);return markupChecksum===existingChecksum}};module.exports=ReactMarkupChecksum},{"./adler32":129}],96:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var DOMLazyTree=require("./DOMLazyTree");var DOMProperty=require("./DOMProperty");var React=require("react/lib/React");var ReactBrowserEventEmitter=require("./ReactBrowserEventEmitter");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactDOMContainerInfo=require("./ReactDOMContainerInfo");var ReactDOMFeatureFlags=require("./ReactDOMFeatureFlags");var ReactFeatureFlags=require("./ReactFeatureFlags");var ReactInstanceMap=require("./ReactInstanceMap");var ReactInstrumentation=require("./ReactInstrumentation");var ReactMarkupChecksum=require("./ReactMarkupChecksum");var ReactReconciler=require("./ReactReconciler");var ReactUpdateQueue=require("./ReactUpdateQueue");var ReactUpdates=require("./ReactUpdates");var emptyObject=require("fbjs/lib/emptyObject");var instantiateReactComponent=require("./instantiateReactComponent");var invariant=require("fbjs/lib/invariant");var setInnerHTML=require("./setInnerHTML");var shouldUpdateReactComponent=require("./shouldUpdateReactComponent");var warning=require("fbjs/lib/warning");var ATTR_NAME=DOMProperty.ID_ATTRIBUTE_NAME;var ROOT_ATTR_NAME=DOMProperty.ROOT_ATTRIBUTE_NAME;var ELEMENT_NODE_TYPE=1;var DOC_NODE_TYPE=9;var DOCUMENT_FRAGMENT_NODE_TYPE=11;var instancesByReactRootID={};function firstDifferenceIndex(string1,string2){var minLen=Math.min(string1.length,string2.length);for(var i=0;i<minLen;i++){if(string1.charAt(i)!==string2.charAt(i)){return i}}return string1.length===string2.length?-1:minLen}function getReactRootElementInContainer(container){if(!container){return null}if(container.nodeType===DOC_NODE_TYPE){return container.documentElement}else{return container.firstChild}}function internalGetID(node){return node.getAttribute&&node.getAttribute(ATTR_NAME)||""}function mountComponentIntoNode(wrapperInstance,container,transaction,shouldReuseMarkup,context){var markerName;if(ReactFeatureFlags.logTopLevelRenders){var wrappedElement=wrapperInstance._currentElement.props.child;var type=wrappedElement.type;markerName="React mount: "+(typeof type==="string"?type:type.displayName||type.name);console.time(markerName)}var markup=ReactReconciler.mountComponent(wrapperInstance,transaction,null,ReactDOMContainerInfo(wrapperInstance,container),context,0);if(markerName){console.timeEnd(markerName)}wrapperInstance._renderedComponent._topLevelWrapper=wrapperInstance;ReactMount._mountImageIntoNode(markup,container,wrapperInstance,shouldReuseMarkup,transaction)}function batchedMountComponentIntoNode(componentInstance,container,shouldReuseMarkup,context){var transaction=ReactUpdates.ReactReconcileTransaction.getPooled(!shouldReuseMarkup&&ReactDOMFeatureFlags.useCreateElement);transaction.perform(mountComponentIntoNode,null,componentInstance,container,transaction,shouldReuseMarkup,context);ReactUpdates.ReactReconcileTransaction.release(transaction)}function unmountComponentFromNode(instance,container,safely){if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onBeginFlush()}ReactReconciler.unmountComponent(instance,safely);if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onEndFlush()}if(container.nodeType===DOC_NODE_TYPE){container=container.documentElement}while(container.lastChild){container.removeChild(container.lastChild)}}function hasNonRootReactChild(container){var rootEl=getReactRootElementInContainer(container);if(rootEl){var inst=ReactDOMComponentTree.getInstanceFromNode(rootEl);return!!(inst&&inst._hostParent)}}function nodeIsRenderedByOtherInstance(container){var rootEl=getReactRootElementInContainer(container);return!!(rootEl&&isReactNode(rootEl)&&!ReactDOMComponentTree.getInstanceFromNode(rootEl))}function isValidContainer(node){return!!(node&&(node.nodeType===ELEMENT_NODE_TYPE||node.nodeType===DOC_NODE_TYPE||node.nodeType===DOCUMENT_FRAGMENT_NODE_TYPE))}function isReactNode(node){return isValidContainer(node)&&(node.hasAttribute(ROOT_ATTR_NAME)||node.hasAttribute(ATTR_NAME))}function getHostRootInstanceInContainer(container){var rootEl=getReactRootElementInContainer(container);var prevHostInstance=rootEl&&ReactDOMComponentTree.getInstanceFromNode(rootEl);return prevHostInstance&&!prevHostInstance._hostParent?prevHostInstance:null}function getTopLevelWrapperInContainer(container){var root=getHostRootInstanceInContainer(container);return root?root._hostContainerInfo._topLevelWrapper:null}var topLevelRootCounter=1;var TopLevelWrapper=function(){this.rootID=topLevelRootCounter++};TopLevelWrapper.prototype.isReactComponent={};if(process.env.NODE_ENV!=="production"){TopLevelWrapper.displayName="TopLevelWrapper"}TopLevelWrapper.prototype.render=function(){return this.props.child};TopLevelWrapper.isReactTopLevelWrapper=true;var ReactMount={TopLevelWrapper:TopLevelWrapper,_instancesByReactRootID:instancesByReactRootID,scrollMonitor:function(container,renderCallback){renderCallback()},_updateRootComponent:function(prevComponent,nextElement,nextContext,container,callback){ReactMount.scrollMonitor(container,function(){ReactUpdateQueue.enqueueElementInternal(prevComponent,nextElement,nextContext);if(callback){ReactUpdateQueue.enqueueCallbackInternal(prevComponent,callback)}});return prevComponent},_renderNewRootComponent:function(nextElement,container,shouldReuseMarkup,context){process.env.NODE_ENV!=="production"?warning(ReactCurrentOwner.current==null,"_renderNewRootComponent(): Render methods should be a pure function "+"of props and state; triggering nested component updates from "+"render is not allowed. If necessary, trigger nested updates in "+"componentDidUpdate. Check the render method of %s.",ReactCurrentOwner.current&&ReactCurrentOwner.current.getName()||"ReactCompositeComponent"):void 0;!isValidContainer(container)?process.env.NODE_ENV!=="production"?invariant(false,"_registerComponent(...): Target container is not a DOM element."):_prodInvariant("37"):void 0;ReactBrowserEventEmitter.ensureScrollValueMonitoring();var componentInstance=instantiateReactComponent(nextElement,false);ReactUpdates.batchedUpdates(batchedMountComponentIntoNode,componentInstance,container,shouldReuseMarkup,context);var wrapperID=componentInstance._instance.rootID;instancesByReactRootID[wrapperID]=componentInstance;return componentInstance},renderSubtreeIntoContainer:function(parentComponent,nextElement,container,callback){!(parentComponent!=null&&ReactInstanceMap.has(parentComponent))?process.env.NODE_ENV!=="production"?invariant(false,"parentComponent must be a valid React Component"):_prodInvariant("38"):void 0;return ReactMount._renderSubtreeIntoContainer(parentComponent,nextElement,container,callback)},_renderSubtreeIntoContainer:function(parentComponent,nextElement,container,callback){ReactUpdateQueue.validateCallback(callback,"ReactDOM.render");!React.isValidElement(nextElement)?process.env.NODE_ENV!=="production"?invariant(false,"ReactDOM.render(): Invalid component element.%s",typeof nextElement==="string"?" Instead of passing a string like 'div', pass "+"React.createElement('div') or <div />.":typeof nextElement==="function"?" Instead of passing a class like Foo, pass "+"React.createElement(Foo) or <Foo />.":nextElement!=null&&nextElement.props!==undefined?" This may be caused by unintentionally loading two independent "+"copies of React.":""):_prodInvariant("39",typeof nextElement==="string"?" Instead of passing a string like 'div', pass "+"React.createElement('div') or <div />.":typeof nextElement==="function"?" Instead of passing a class like Foo, pass "+"React.createElement(Foo) or <Foo />.":nextElement!=null&&nextElement.props!==undefined?" This may be caused by unintentionally loading two independent "+"copies of React.":""):void 0;process.env.NODE_ENV!=="production"?warning(!container||!container.tagName||container.tagName.toUpperCase()!=="BODY","render(): Rendering components directly into document.body is "+"discouraged, since its children are often manipulated by third-party "+"scripts and browser extensions. This may lead to subtle "+"reconciliation issues. Try rendering into a container element created "+"for your app."):void 0;var nextWrappedElement=React.createElement(TopLevelWrapper,{child:nextElement});var nextContext;if(parentComponent){var parentInst=ReactInstanceMap.get(parentComponent);nextContext=parentInst._processChildContext(parentInst._context)}else{nextContext=emptyObject}var prevComponent=getTopLevelWrapperInContainer(container);if(prevComponent){var prevWrappedElement=prevComponent._currentElement;var prevElement=prevWrappedElement.props.child;if(shouldUpdateReactComponent(prevElement,nextElement)){var publicInst=prevComponent._renderedComponent.getPublicInstance();var updatedCallback=callback&&function(){callback.call(publicInst)};ReactMount._updateRootComponent(prevComponent,nextWrappedElement,nextContext,container,updatedCallback);return publicInst}else{ReactMount.unmountComponentAtNode(container)}}var reactRootElement=getReactRootElementInContainer(container);var containerHasReactMarkup=reactRootElement&&!!internalGetID(reactRootElement);var containerHasNonRootReactChild=hasNonRootReactChild(container);if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(!containerHasNonRootReactChild,"render(...): Replacing React-rendered children with a new root "+"component. If you intended to update the children of this node, "+"you should instead have the existing children update their state "+"and render the new components instead of calling ReactDOM.render."):void 0;if(!containerHasReactMarkup||reactRootElement.nextSibling){var rootElementSibling=reactRootElement;while(rootElementSibling){if(internalGetID(rootElementSibling)){process.env.NODE_ENV!=="production"?warning(false,"render(): Target node has markup rendered by React, but there "+"are unrelated nodes as well. This is most commonly caused by "+"white-space inserted around server-rendered markup."):void 0;break}rootElementSibling=rootElementSibling.nextSibling}}}var shouldReuseMarkup=containerHasReactMarkup&&!prevComponent&&!containerHasNonRootReactChild;var component=ReactMount._renderNewRootComponent(nextWrappedElement,container,shouldReuseMarkup,nextContext)._renderedComponent.getPublicInstance();if(callback){callback.call(component)}return component},render:function(nextElement,container,callback){return ReactMount._renderSubtreeIntoContainer(null,nextElement,container,callback)},unmountComponentAtNode:function(container){process.env.NODE_ENV!=="production"?warning(ReactCurrentOwner.current==null,"unmountComponentAtNode(): Render methods should be a pure function "+"of props and state; triggering nested component updates from render "+"is not allowed. If necessary, trigger nested updates in "+"componentDidUpdate. Check the render method of %s.",ReactCurrentOwner.current&&ReactCurrentOwner.current.getName()||"ReactCompositeComponent"):void 0;!isValidContainer(container)?process.env.NODE_ENV!=="production"?invariant(false,"unmountComponentAtNode(...): Target container is not a DOM element."):_prodInvariant("40"):void 0;if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(!nodeIsRenderedByOtherInstance(container),"unmountComponentAtNode(): The node you're attempting to unmount "+"was rendered by another copy of React."):void 0}var prevComponent=getTopLevelWrapperInContainer(container);if(!prevComponent){var containerHasNonRootReactChild=hasNonRootReactChild(container);var isContainerReactRoot=container.nodeType===1&&container.hasAttribute(ROOT_ATTR_NAME);if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(!containerHasNonRootReactChild,"unmountComponentAtNode(): The node you're attempting to unmount "+"was rendered by React and is not a top-level container. %s",isContainerReactRoot?"You may have accidentally passed in a React root node instead "+"of its container.":"Instead, have the parent component update its state and "+"rerender in order to remove this component."):void 0}return false}delete instancesByReactRootID[prevComponent._instance.rootID];ReactUpdates.batchedUpdates(unmountComponentFromNode,prevComponent,container,false);return true},_mountImageIntoNode:function(markup,container,instance,shouldReuseMarkup,transaction){!isValidContainer(container)?process.env.NODE_ENV!=="production"?invariant(false,"mountComponentIntoNode(...): Target container is not valid."):_prodInvariant("41"):void 0;if(shouldReuseMarkup){var rootElement=getReactRootElementInContainer(container);if(ReactMarkupChecksum.canReuseMarkup(markup,rootElement)){ReactDOMComponentTree.precacheNode(instance,rootElement);return}else{var checksum=rootElement.getAttribute(ReactMarkupChecksum.CHECKSUM_ATTR_NAME);rootElement.removeAttribute(ReactMarkupChecksum.CHECKSUM_ATTR_NAME);var rootMarkup=rootElement.outerHTML;rootElement.setAttribute(ReactMarkupChecksum.CHECKSUM_ATTR_NAME,checksum);var normalizedMarkup=markup;if(process.env.NODE_ENV!=="production"){var normalizer;if(container.nodeType===ELEMENT_NODE_TYPE){normalizer=document.createElement("div");normalizer.innerHTML=markup;normalizedMarkup=normalizer.innerHTML}else{normalizer=document.createElement("iframe");document.body.appendChild(normalizer);normalizer.contentDocument.write(markup);normalizedMarkup=normalizer.contentDocument.documentElement.outerHTML;document.body.removeChild(normalizer)}}var diffIndex=firstDifferenceIndex(normalizedMarkup,rootMarkup);var difference=" (client) "+normalizedMarkup.substring(diffIndex-20,diffIndex+20)+"\n (server) "+rootMarkup.substring(diffIndex-20,diffIndex+20);!(container.nodeType!==DOC_NODE_TYPE)?process.env.NODE_ENV!=="production"?invariant(false,"You're trying to render a component to the document using server rendering but the checksum was invalid. This usually means you rendered a different component type or props on the client from the one on the server, or your render() methods are impure. React cannot handle this case due to cross-browser quirks by rendering at the document root. You should look for environment dependent code in your components and ensure the props are the same client and server side:\n%s",difference):_prodInvariant("42",difference):void 0;if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(false,"React attempted to reuse markup in a container but the "+"checksum was invalid. This generally means that you are "+"using server rendering and the markup generated on the "+"server was not what the client was expecting. React injected "+"new markup to compensate which works but you have lost many "+"of the benefits of server rendering. Instead, figure out "+"why the markup being generated is different on the client "+"or server:\n%s",difference):void 0}}}!(container.nodeType!==DOC_NODE_TYPE)?process.env.NODE_ENV!=="production"?invariant(false,"You're trying to render a component to the document but you didn't use server rendering. We can't do this without using server rendering due to cross-browser quirks. See ReactDOMServer.renderToString() for server rendering."):_prodInvariant("43"):void 0;if(transaction.useCreateElement){while(container.lastChild){container.removeChild(container.lastChild)}DOMLazyTree.insertTreeBefore(container,markup,null)}else{setInnerHTML(container,markup);ReactDOMComponentTree.precacheNode(instance,container.firstChild)}if(process.env.NODE_ENV!=="production"){var hostNode=ReactDOMComponentTree.getInstanceFromNode(container.firstChild);if(hostNode._debugID!==0){ReactInstrumentation.debugTool.onHostOperation({instanceID:hostNode._debugID,type:"mount",payload:markup.toString()})}}}};module.exports=ReactMount}).call(this,require("_process"))},{"./DOMLazyTree":40,"./DOMProperty":42,"./ReactBrowserEventEmitter":56,"./ReactDOMComponentTree":64,"./ReactDOMContainerInfo":65,"./ReactDOMFeatureFlags":67,"./ReactFeatureFlags":87,"./ReactInstanceMap":92,"./ReactInstrumentation":93,"./ReactMarkupChecksum":95,"./ReactReconciler":103,"./ReactUpdateQueue":107,"./ReactUpdates":108,"./instantiateReactComponent":147,"./reactProdInvariant":151,"./setInnerHTML":153,"./shouldUpdateReactComponent":155,_process:184,"fbjs/lib/emptyObject":11,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"react/lib/React":160,"react/lib/ReactCurrentOwner":164}],97:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactComponentEnvironment=require("./ReactComponentEnvironment");var ReactInstanceMap=require("./ReactInstanceMap");var ReactInstrumentation=require("./ReactInstrumentation");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var ReactReconciler=require("./ReactReconciler");var ReactChildReconciler=require("./ReactChildReconciler");var emptyFunction=require("fbjs/lib/emptyFunction");var flattenChildren=require("./flattenChildren");var invariant=require("fbjs/lib/invariant");function makeInsertMarkup(markup,afterNode,toIndex){return{type:"INSERT_MARKUP",content:markup,fromIndex:null,fromNode:null,toIndex:toIndex,afterNode:afterNode}}function makeMove(child,afterNode,toIndex){return{type:"MOVE_EXISTING",content:null,fromIndex:child._mountIndex,fromNode:ReactReconciler.getHostNode(child),toIndex:toIndex,afterNode:afterNode}}function makeRemove(child,node){return{type:"REMOVE_NODE",content:null,fromIndex:child._mountIndex,fromNode:node,toIndex:null,afterNode:null}}function makeSetMarkup(markup){return{type:"SET_MARKUP",content:markup,fromIndex:null,fromNode:null,toIndex:null,afterNode:null}}function makeTextContent(textContent){return{type:"TEXT_CONTENT",content:textContent,fromIndex:null,fromNode:null,toIndex:null,afterNode:null}}function enqueue(queue,update){if(update){queue=queue||[];queue.push(update)}return queue}function processQueue(inst,updateQueue){ReactComponentEnvironment.processChildrenUpdates(inst,updateQueue)}var setChildrenForInstrumentation=emptyFunction;if(process.env.NODE_ENV!=="production"){var getDebugID=function(inst){if(!inst._debugID){var internal;if(internal=ReactInstanceMap.get(inst)){inst=internal}}return inst._debugID};setChildrenForInstrumentation=function(children){var debugID=getDebugID(this);if(debugID!==0){ReactInstrumentation.debugTool.onSetChildren(debugID,children?Object.keys(children).map(function(key){return children[key]._debugID}):[])}}}var ReactMultiChild={Mixin:{_reconcilerInstantiateChildren:function(nestedChildren,transaction,context){if(process.env.NODE_ENV!=="production"){var selfDebugID=getDebugID(this);if(this._currentElement){try{ReactCurrentOwner.current=this._currentElement._owner;return ReactChildReconciler.instantiateChildren(nestedChildren,transaction,context,selfDebugID)}finally{ReactCurrentOwner.current=null}}}return ReactChildReconciler.instantiateChildren(nestedChildren,transaction,context)},_reconcilerUpdateChildren:function(prevChildren,nextNestedChildrenElements,mountImages,removedNodes,transaction,context){var nextChildren;var selfDebugID=0;if(process.env.NODE_ENV!=="production"){selfDebugID=getDebugID(this);if(this._currentElement){try{ReactCurrentOwner.current=this._currentElement._owner;nextChildren=flattenChildren(nextNestedChildrenElements,selfDebugID)}finally{ReactCurrentOwner.current=null}ReactChildReconciler.updateChildren(prevChildren,nextChildren,mountImages,removedNodes,transaction,this,this._hostContainerInfo,context,selfDebugID);return nextChildren}}nextChildren=flattenChildren(nextNestedChildrenElements,selfDebugID);ReactChildReconciler.updateChildren(prevChildren,nextChildren,mountImages,removedNodes,transaction,this,this._hostContainerInfo,context,selfDebugID);return nextChildren},mountChildren:function(nestedChildren,transaction,context){var children=this._reconcilerInstantiateChildren(nestedChildren,transaction,context);this._renderedChildren=children;var mountImages=[];var index=0;for(var name in children){if(children.hasOwnProperty(name)){var child=children[name];var selfDebugID=0;if(process.env.NODE_ENV!=="production"){selfDebugID=getDebugID(this)}var mountImage=ReactReconciler.mountComponent(child,transaction,this,this._hostContainerInfo,context,selfDebugID);child._mountIndex=index++;mountImages.push(mountImage)}}if(process.env.NODE_ENV!=="production"){setChildrenForInstrumentation.call(this,children)}return mountImages},updateTextContent:function(nextContent){var prevChildren=this._renderedChildren;ReactChildReconciler.unmountChildren(prevChildren,false);for(var name in prevChildren){if(prevChildren.hasOwnProperty(name)){!false?process.env.NODE_ENV!=="production"?invariant(false,"updateTextContent called on non-empty component."):_prodInvariant("118"):void 0}}var updates=[makeTextContent(nextContent)];processQueue(this,updates)},updateMarkup:function(nextMarkup){var prevChildren=this._renderedChildren;ReactChildReconciler.unmountChildren(prevChildren,false);for(var name in prevChildren){if(prevChildren.hasOwnProperty(name)){!false?process.env.NODE_ENV!=="production"?invariant(false,"updateTextContent called on non-empty component."):_prodInvariant("118"):void 0}}var updates=[makeSetMarkup(nextMarkup)];processQueue(this,updates)},updateChildren:function(nextNestedChildrenElements,transaction,context){this._updateChildren(nextNestedChildrenElements,transaction,context)},_updateChildren:function(nextNestedChildrenElements,transaction,context){var prevChildren=this._renderedChildren;var removedNodes={};var mountImages=[];var nextChildren=this._reconcilerUpdateChildren(prevChildren,nextNestedChildrenElements,mountImages,removedNodes,transaction,context);if(!nextChildren&&!prevChildren){return}var updates=null;var name;var nextIndex=0;var lastIndex=0;var nextMountIndex=0;var lastPlacedNode=null;for(name in nextChildren){if(!nextChildren.hasOwnProperty(name)){continue}var prevChild=prevChildren&&prevChildren[name];var nextChild=nextChildren[name];if(prevChild===nextChild){updates=enqueue(updates,this.moveChild(prevChild,lastPlacedNode,nextIndex,lastIndex));lastIndex=Math.max(prevChild._mountIndex,lastIndex);prevChild._mountIndex=nextIndex}else{if(prevChild){lastIndex=Math.max(prevChild._mountIndex,lastIndex)}updates=enqueue(updates,this._mountChildAtIndex(nextChild,mountImages[nextMountIndex],lastPlacedNode,nextIndex,transaction,context));nextMountIndex++}nextIndex++;lastPlacedNode=ReactReconciler.getHostNode(nextChild)}for(name in removedNodes){if(removedNodes.hasOwnProperty(name)){updates=enqueue(updates,this._unmountChild(prevChildren[name],removedNodes[name]))}}if(updates){processQueue(this,updates)}this._renderedChildren=nextChildren;if(process.env.NODE_ENV!=="production"){setChildrenForInstrumentation.call(this,nextChildren)}},unmountChildren:function(safely){var renderedChildren=this._renderedChildren;ReactChildReconciler.unmountChildren(renderedChildren,safely);this._renderedChildren=null},moveChild:function(child,afterNode,toIndex,lastIndex){if(child._mountIndex<lastIndex){return makeMove(child,afterNode,toIndex)}},createChild:function(child,afterNode,mountImage){return makeInsertMarkup(mountImage,afterNode,child._mountIndex)},removeChild:function(child,node){return makeRemove(child,node)},_mountChildAtIndex:function(child,mountImage,afterNode,index,transaction,context){child._mountIndex=index;return this.createChild(child,afterNode,mountImage)},_unmountChild:function(child,node){var update=this.removeChild(child,node);child._mountIndex=null;return update}}};module.exports=ReactMultiChild}).call(this,require("_process"))},{"./ReactChildReconciler":57,"./ReactComponentEnvironment":59,"./ReactInstanceMap":92,"./ReactInstrumentation":93,"./ReactReconciler":103,"./flattenChildren":135,"./reactProdInvariant":151,_process:184,"fbjs/lib/emptyFunction":10,"fbjs/lib/invariant":18,"react/lib/ReactCurrentOwner":164}],98:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var React=require("react/lib/React");var invariant=require("fbjs/lib/invariant");var ReactNodeTypes={HOST:0,COMPOSITE:1,EMPTY:2,getType:function(node){if(node===null||node===false){return ReactNodeTypes.EMPTY}else if(React.isValidElement(node)){if(typeof node.type==="function"){return ReactNodeTypes.COMPOSITE}else{return ReactNodeTypes.HOST}}!false?process.env.NODE_ENV!=="production"?invariant(false,"Unexpected node: %s",node):_prodInvariant("26",node):void 0}};module.exports=ReactNodeTypes}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"react/lib/React":160}],99:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");function isValidOwner(object){return!!(object&&typeof object.attachRef==="function"&&typeof object.detachRef==="function")}var ReactOwner={addComponentAsRefTo:function(component,ref,owner){!isValidOwner(owner)?process.env.NODE_ENV!=="production"?invariant(false,"addComponentAsRefTo(...): Only a ReactOwner can have refs. You might be adding a ref to a component that was not created inside a component's `render` method, or you have multiple copies of React loaded (details: https://fb.me/react-refs-must-have-owner)."):_prodInvariant("119"):void 0;owner.attachRef(ref,component)},removeComponentAsRefFrom:function(component,ref,owner){!isValidOwner(owner)?process.env.NODE_ENV!=="production"?invariant(false,"removeComponentAsRefFrom(...): Only a ReactOwner can have refs. You might be removing a ref to a component that was not created inside a component's `render` method, or you have multiple copies of React loaded (details: https://fb.me/react-refs-must-have-owner)."):_prodInvariant("120"):void 0;var ownerPublicInstance=owner.getPublicInstance();if(ownerPublicInstance&&ownerPublicInstance.refs[ref]===component.getPublicInstance()){owner.detachRef(ref)}}};module.exports=ReactOwner}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],100:[function(require,module,exports){(function(process){"use strict";var ReactPropTypeLocationNames={};if(process.env.NODE_ENV!=="production"){ReactPropTypeLocationNames={prop:"prop",context:"context",childContext:"child context"}}module.exports=ReactPropTypeLocationNames}).call(this,require("_process"))},{_process:184}],101:[function(require,module,exports){"use strict";var ReactPropTypesSecret="SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED";module.exports=ReactPropTypesSecret},{}],102:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var CallbackQueue=require("./CallbackQueue");var PooledClass=require("./PooledClass");var ReactBrowserEventEmitter=require("./ReactBrowserEventEmitter");var ReactInputSelection=require("./ReactInputSelection");var ReactInstrumentation=require("./ReactInstrumentation");var Transaction=require("./Transaction");var ReactUpdateQueue=require("./ReactUpdateQueue");var SELECTION_RESTORATION={initialize:ReactInputSelection.getSelectionInformation,close:ReactInputSelection.restoreSelection};var EVENT_SUPPRESSION={initialize:function(){var currentlyEnabled=ReactBrowserEventEmitter.isEnabled();ReactBrowserEventEmitter.setEnabled(false);return currentlyEnabled},close:function(previouslyEnabled){ReactBrowserEventEmitter.setEnabled(previouslyEnabled)}};var ON_DOM_READY_QUEUEING={initialize:function(){this.reactMountReady.reset()},close:function(){this.reactMountReady.notifyAll()}};var TRANSACTION_WRAPPERS=[SELECTION_RESTORATION,EVENT_SUPPRESSION,ON_DOM_READY_QUEUEING];if(process.env.NODE_ENV!=="production"){TRANSACTION_WRAPPERS.push({initialize:ReactInstrumentation.debugTool.onBeginFlush,close:ReactInstrumentation.debugTool.onEndFlush})}function ReactReconcileTransaction(useCreateElement){this.reinitializeTransaction();this.renderToStaticMarkup=false;this.reactMountReady=CallbackQueue.getPooled(null);this.useCreateElement=useCreateElement}var Mixin={getTransactionWrappers:function(){return TRANSACTION_WRAPPERS},getReactMountReady:function(){return this.reactMountReady},getUpdateQueue:function(){return ReactUpdateQueue},checkpoint:function(){return this.reactMountReady.checkpoint()},rollback:function(checkpoint){this.reactMountReady.rollback(checkpoint)},destructor:function(){CallbackQueue.release(this.reactMountReady);this.reactMountReady=null}};_assign(ReactReconcileTransaction.prototype,Transaction,Mixin);PooledClass.addPoolingTo(ReactReconcileTransaction);module.exports=ReactReconcileTransaction}).call(this,require("_process"))},{"./CallbackQueue":37,"./PooledClass":55,"./ReactBrowserEventEmitter":56,"./ReactInputSelection":91,"./ReactInstrumentation":93,"./ReactUpdateQueue":107,"./Transaction":126,_process:184,"object-assign":26}],103:[function(require,module,exports){(function(process){"use strict";var ReactRef=require("./ReactRef");var ReactInstrumentation=require("./ReactInstrumentation");var warning=require("fbjs/lib/warning");function attachRefs(){ReactRef.attachRefs(this,this._currentElement)}var ReactReconciler={mountComponent:function(internalInstance,transaction,hostParent,hostContainerInfo,context,parentDebugID){if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onBeforeMountComponent(internalInstance._debugID,internalInstance._currentElement,parentDebugID)}}var markup=internalInstance.mountComponent(transaction,hostParent,hostContainerInfo,context,parentDebugID);if(internalInstance._currentElement&&internalInstance._currentElement.ref!=null){transaction.getReactMountReady().enqueue(attachRefs,internalInstance)}if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onMountComponent(internalInstance._debugID)}}return markup},getHostNode:function(internalInstance){return internalInstance.getHostNode()},unmountComponent:function(internalInstance,safely){if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onBeforeUnmountComponent(internalInstance._debugID)}}ReactRef.detachRefs(internalInstance,internalInstance._currentElement);internalInstance.unmountComponent(safely);if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onUnmountComponent(internalInstance._debugID)}}},receiveComponent:function(internalInstance,nextElement,transaction,context){var prevElement=internalInstance._currentElement;if(nextElement===prevElement&&context===internalInstance._context){return}if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onBeforeUpdateComponent(internalInstance._debugID,nextElement)}}var refsChanged=ReactRef.shouldUpdateRefs(prevElement,nextElement);if(refsChanged){ReactRef.detachRefs(internalInstance,prevElement)}internalInstance.receiveComponent(nextElement,transaction,context);if(refsChanged&&internalInstance._currentElement&&internalInstance._currentElement.ref!=null){transaction.getReactMountReady().enqueue(attachRefs,internalInstance)}if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onUpdateComponent(internalInstance._debugID)}}},performUpdateIfNecessary:function(internalInstance,transaction,updateBatchNumber){if(internalInstance._updateBatchNumber!==updateBatchNumber){process.env.NODE_ENV!=="production"?warning(internalInstance._updateBatchNumber==null||internalInstance._updateBatchNumber===updateBatchNumber+1,"performUpdateIfNecessary: Unexpected batch number (current %s, "+"pending %s)",updateBatchNumber,internalInstance._updateBatchNumber):void 0;return}if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onBeforeUpdateComponent(internalInstance._debugID,internalInstance._currentElement)}}internalInstance.performUpdateIfNecessary(transaction);if(process.env.NODE_ENV!=="production"){if(internalInstance._debugID!==0){ReactInstrumentation.debugTool.onUpdateComponent(internalInstance._debugID)}}}};module.exports=ReactReconciler}).call(this,require("_process"))},{"./ReactInstrumentation":93,"./ReactRef":104,_process:184,"fbjs/lib/warning":25}],104:[function(require,module,exports){"use strict";var ReactOwner=require("./ReactOwner");var ReactRef={};function attachRef(ref,component,owner){if(typeof ref==="function"){ref(component.getPublicInstance())}else{ReactOwner.addComponentAsRefTo(component,ref,owner)}}function detachRef(ref,component,owner){if(typeof ref==="function"){ref(null)}else{ReactOwner.removeComponentAsRefFrom(component,ref,owner)}}ReactRef.attachRefs=function(instance,element){if(element===null||typeof element!=="object"){return}var ref=element.ref;if(ref!=null){attachRef(ref,instance,element._owner)}};ReactRef.shouldUpdateRefs=function(prevElement,nextElement){var prevRef=null;var prevOwner=null;if(prevElement!==null&&typeof prevElement==="object"){prevRef=prevElement.ref;prevOwner=prevElement._owner}var nextRef=null;var nextOwner=null;if(nextElement!==null&&typeof nextElement==="object"){nextRef=nextElement.ref;nextOwner=nextElement._owner}return prevRef!==nextRef||typeof nextRef==="string"&&nextOwner!==prevOwner};ReactRef.detachRefs=function(instance,element){if(element===null||typeof element!=="object"){return}var ref=element.ref;if(ref!=null){detachRef(ref,instance,element._owner)}};module.exports=ReactRef},{"./ReactOwner":99}],105:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var PooledClass=require("./PooledClass");var Transaction=require("./Transaction");var ReactInstrumentation=require("./ReactInstrumentation");var ReactServerUpdateQueue=require("./ReactServerUpdateQueue");var TRANSACTION_WRAPPERS=[];if(process.env.NODE_ENV!=="production"){TRANSACTION_WRAPPERS.push({initialize:ReactInstrumentation.debugTool.onBeginFlush,close:ReactInstrumentation.debugTool.onEndFlush})}var noopCallbackQueue={enqueue:function(){}};function ReactServerRenderingTransaction(renderToStaticMarkup){this.reinitializeTransaction();this.renderToStaticMarkup=renderToStaticMarkup;this.useCreateElement=false;this.updateQueue=new ReactServerUpdateQueue(this)}var Mixin={getTransactionWrappers:function(){return TRANSACTION_WRAPPERS},getReactMountReady:function(){return noopCallbackQueue},getUpdateQueue:function(){return this.updateQueue},destructor:function(){},checkpoint:function(){},rollback:function(){}};_assign(ReactServerRenderingTransaction.prototype,Transaction,Mixin);PooledClass.addPoolingTo(ReactServerRenderingTransaction);module.exports=ReactServerRenderingTransaction}).call(this,require("_process"))},{"./PooledClass":55,"./ReactInstrumentation":93,"./ReactServerUpdateQueue":106,"./Transaction":126,_process:184,"object-assign":26}],106:[function(require,module,exports){(function(process){"use strict";function _classCallCheck(instance,Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function")}}var ReactUpdateQueue=require("./ReactUpdateQueue");var warning=require("fbjs/lib/warning");function warnNoop(publicInstance,callerName){if(process.env.NODE_ENV!=="production"){var constructor=publicInstance.constructor;process.env.NODE_ENV!=="production"?warning(false,"%s(...): Can only update a mounting component. "+"This usually means you called %s() outside componentWillMount() on the server. "+"This is a no-op. Please check the code for the %s component.",callerName,callerName,constructor&&(constructor.displayName||constructor.name)||"ReactClass"):void 0}}var ReactServerUpdateQueue=function(){function ReactServerUpdateQueue(transaction){_classCallCheck(this,ReactServerUpdateQueue);this.transaction=transaction}ReactServerUpdateQueue.prototype.isMounted=function isMounted(publicInstance){return false};ReactServerUpdateQueue.prototype.enqueueCallback=function enqueueCallback(publicInstance,callback,callerName){if(this.transaction.isInTransaction()){ReactUpdateQueue.enqueueCallback(publicInstance,callback,callerName)}};ReactServerUpdateQueue.prototype.enqueueForceUpdate=function enqueueForceUpdate(publicInstance){if(this.transaction.isInTransaction()){ReactUpdateQueue.enqueueForceUpdate(publicInstance)}else{warnNoop(publicInstance,"forceUpdate")}};ReactServerUpdateQueue.prototype.enqueueReplaceState=function enqueueReplaceState(publicInstance,completeState){if(this.transaction.isInTransaction()){ReactUpdateQueue.enqueueReplaceState(publicInstance,completeState)}else{warnNoop(publicInstance,"replaceState")}};ReactServerUpdateQueue.prototype.enqueueSetState=function enqueueSetState(publicInstance,partialState){if(this.transaction.isInTransaction()){ReactUpdateQueue.enqueueSetState(publicInstance,partialState)}else{warnNoop(publicInstance,"setState")}};return ReactServerUpdateQueue}();module.exports=ReactServerUpdateQueue}).call(this,require("_process"))},{"./ReactUpdateQueue":107,_process:184,"fbjs/lib/warning":25}],107:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var ReactInstanceMap=require("./ReactInstanceMap");var ReactInstrumentation=require("./ReactInstrumentation");var ReactUpdates=require("./ReactUpdates");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");function enqueueUpdate(internalInstance){ReactUpdates.enqueueUpdate(internalInstance)}function formatUnexpectedArgument(arg){var type=typeof arg;if(type!=="object"){return type}var displayName=arg.constructor&&arg.constructor.name||type;var keys=Object.keys(arg);if(keys.length>0&&keys.length<20){return displayName+" (keys: "+keys.join(", ")+")"}return displayName}function getInternalInstanceReadyForUpdate(publicInstance,callerName){var internalInstance=ReactInstanceMap.get(publicInstance);if(!internalInstance){if(process.env.NODE_ENV!=="production"){var ctor=publicInstance.constructor;process.env.NODE_ENV!=="production"?warning(!callerName,"%s(...): Can only update a mounted or mounting component. "+"This usually means you called %s() on an unmounted component. "+"This is a no-op. Please check the code for the %s component.",callerName,callerName,ctor&&(ctor.displayName||ctor.name)||"ReactClass"):void 0}return null}if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(ReactCurrentOwner.current==null,"%s(...): Cannot update during an existing state transition (such as "+"within `render` or another component's constructor). Render methods "+"should be a pure function of props and state; constructor "+"side-effects are an anti-pattern, but can be moved to "+"`componentWillMount`.",callerName):void 0}return internalInstance}var ReactUpdateQueue={isMounted:function(publicInstance){if(process.env.NODE_ENV!=="production"){var owner=ReactCurrentOwner.current;if(owner!==null){process.env.NODE_ENV!=="production"?warning(owner._warnedAboutRefsInRender,"%s is accessing isMounted inside its render() function. "+"render() should be a pure function of props and state. It should "+"never access something that requires stale data from the previous "+"render, such as refs. Move this logic to componentDidMount and "+"componentDidUpdate instead.",owner.getName()||"A component"):void 0;owner._warnedAboutRefsInRender=true}}var internalInstance=ReactInstanceMap.get(publicInstance);if(internalInstance){return!!internalInstance._renderedComponent}else{return false}},enqueueCallback:function(publicInstance,callback,callerName){ReactUpdateQueue.validateCallback(callback,callerName);var internalInstance=getInternalInstanceReadyForUpdate(publicInstance);if(!internalInstance){return null}if(internalInstance._pendingCallbacks){internalInstance._pendingCallbacks.push(callback)}else{internalInstance._pendingCallbacks=[callback]}enqueueUpdate(internalInstance)},enqueueCallbackInternal:function(internalInstance,callback){if(internalInstance._pendingCallbacks){internalInstance._pendingCallbacks.push(callback)}else{internalInstance._pendingCallbacks=[callback]}enqueueUpdate(internalInstance)},enqueueForceUpdate:function(publicInstance){var internalInstance=getInternalInstanceReadyForUpdate(publicInstance,"forceUpdate");if(!internalInstance){return}internalInstance._pendingForceUpdate=true;enqueueUpdate(internalInstance)},enqueueReplaceState:function(publicInstance,completeState,callback){var internalInstance=getInternalInstanceReadyForUpdate(publicInstance,"replaceState");if(!internalInstance){return}internalInstance._pendingStateQueue=[completeState];internalInstance._pendingReplaceState=true;if(callback!==undefined&&callback!==null){ReactUpdateQueue.validateCallback(callback,"replaceState");if(internalInstance._pendingCallbacks){internalInstance._pendingCallbacks.push(callback)}else{internalInstance._pendingCallbacks=[callback]}}enqueueUpdate(internalInstance)},enqueueSetState:function(publicInstance,partialState){if(process.env.NODE_ENV!=="production"){ReactInstrumentation.debugTool.onSetState();process.env.NODE_ENV!=="production"?warning(partialState!=null,"setState(...): You passed an undefined or null state object; "+"instead, use forceUpdate()."):void 0}var internalInstance=getInternalInstanceReadyForUpdate(publicInstance,"setState");if(!internalInstance){return}var queue=internalInstance._pendingStateQueue||(internalInstance._pendingStateQueue=[]);queue.push(partialState);enqueueUpdate(internalInstance)},enqueueElementInternal:function(internalInstance,nextElement,nextContext){internalInstance._pendingElement=nextElement;internalInstance._context=nextContext;enqueueUpdate(internalInstance)},validateCallback:function(callback,callerName){!(!callback||typeof callback==="function")?process.env.NODE_ENV!=="production"?invariant(false,"%s(...): Expected the last optional `callback` argument to be a function. Instead received: %s.",callerName,formatUnexpectedArgument(callback)):_prodInvariant("122",callerName,formatUnexpectedArgument(callback)):void 0}};module.exports=ReactUpdateQueue}).call(this,require("_process"))},{"./ReactInstanceMap":92,"./ReactInstrumentation":93,"./ReactUpdates":108,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"react/lib/ReactCurrentOwner":164}],108:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var CallbackQueue=require("./CallbackQueue");var PooledClass=require("./PooledClass");var ReactFeatureFlags=require("./ReactFeatureFlags");var ReactReconciler=require("./ReactReconciler");var Transaction=require("./Transaction");var invariant=require("fbjs/lib/invariant");var dirtyComponents=[];var updateBatchNumber=0;var asapCallbackQueue=CallbackQueue.getPooled();var asapEnqueued=false;var batchingStrategy=null;function ensureInjected(){!(ReactUpdates.ReactReconcileTransaction&&batchingStrategy)?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates: must inject a reconcile transaction class and batching strategy"):_prodInvariant("123"):void 0}var NESTED_UPDATES={initialize:function(){this.dirtyComponentsLength=dirtyComponents.length},close:function(){if(this.dirtyComponentsLength!==dirtyComponents.length){dirtyComponents.splice(0,this.dirtyComponentsLength);flushBatchedUpdates()}else{dirtyComponents.length=0}}};var UPDATE_QUEUEING={initialize:function(){this.callbackQueue.reset()},close:function(){this.callbackQueue.notifyAll()}};var TRANSACTION_WRAPPERS=[NESTED_UPDATES,UPDATE_QUEUEING];function ReactUpdatesFlushTransaction(){this.reinitializeTransaction();this.dirtyComponentsLength=null;this.callbackQueue=CallbackQueue.getPooled();this.reconcileTransaction=ReactUpdates.ReactReconcileTransaction.getPooled(true)}_assign(ReactUpdatesFlushTransaction.prototype,Transaction,{getTransactionWrappers:function(){return TRANSACTION_WRAPPERS},destructor:function(){this.dirtyComponentsLength=null;CallbackQueue.release(this.callbackQueue);this.callbackQueue=null;ReactUpdates.ReactReconcileTransaction.release(this.reconcileTransaction);this.reconcileTransaction=null},perform:function(method,scope,a){return Transaction.perform.call(this,this.reconcileTransaction.perform,this.reconcileTransaction,method,scope,a)}});PooledClass.addPoolingTo(ReactUpdatesFlushTransaction);function batchedUpdates(callback,a,b,c,d,e){ensureInjected();return batchingStrategy.batchedUpdates(callback,a,b,c,d,e)}function mountOrderComparator(c1,c2){return c1._mountOrder-c2._mountOrder}function runBatchedUpdates(transaction){var len=transaction.dirtyComponentsLength;!(len===dirtyComponents.length)?process.env.NODE_ENV!=="production"?invariant(false,"Expected flush transaction's stored dirty-components length (%s) to match dirty-components array length (%s).",len,dirtyComponents.length):_prodInvariant("124",len,dirtyComponents.length):void 0;dirtyComponents.sort(mountOrderComparator);updateBatchNumber++;for(var i=0;i<len;i++){var component=dirtyComponents[i];var callbacks=component._pendingCallbacks;component._pendingCallbacks=null;var markerName;if(ReactFeatureFlags.logTopLevelRenders){var namedComponent=component;if(component._currentElement.type.isReactTopLevelWrapper){namedComponent=component._renderedComponent}markerName="React update: "+namedComponent.getName();console.time(markerName)}ReactReconciler.performUpdateIfNecessary(component,transaction.reconcileTransaction,updateBatchNumber);if(markerName){console.timeEnd(markerName)}if(callbacks){for(var j=0;j<callbacks.length;j++){transaction.callbackQueue.enqueue(callbacks[j],component.getPublicInstance())}}}}var flushBatchedUpdates=function(){while(dirtyComponents.length||asapEnqueued){if(dirtyComponents.length){var transaction=ReactUpdatesFlushTransaction.getPooled();transaction.perform(runBatchedUpdates,null,transaction);ReactUpdatesFlushTransaction.release(transaction)}if(asapEnqueued){asapEnqueued=false;var queue=asapCallbackQueue;asapCallbackQueue=CallbackQueue.getPooled();queue.notifyAll();CallbackQueue.release(queue)}}};function enqueueUpdate(component){ensureInjected();if(!batchingStrategy.isBatchingUpdates){batchingStrategy.batchedUpdates(enqueueUpdate,component);return}dirtyComponents.push(component);if(component._updateBatchNumber==null){component._updateBatchNumber=updateBatchNumber+1}}function asap(callback,context){!batchingStrategy.isBatchingUpdates?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates.asap: Can't enqueue an asap callback in a context whereupdates are not being batched."):_prodInvariant("125"):void 0;asapCallbackQueue.enqueue(callback,context);asapEnqueued=true}var ReactUpdatesInjection={injectReconcileTransaction:function(ReconcileTransaction){!ReconcileTransaction?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates: must provide a reconcile transaction class"):_prodInvariant("126"):void 0;ReactUpdates.ReactReconcileTransaction=ReconcileTransaction},injectBatchingStrategy:function(_batchingStrategy){!_batchingStrategy?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates: must provide a batching strategy"):_prodInvariant("127"):void 0;!(typeof _batchingStrategy.batchedUpdates==="function")?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates: must provide a batchedUpdates() function"):_prodInvariant("128"):void 0;!(typeof _batchingStrategy.isBatchingUpdates==="boolean")?process.env.NODE_ENV!=="production"?invariant(false,"ReactUpdates: must provide an isBatchingUpdates boolean attribute"):_prodInvariant("129"):void 0;batchingStrategy=_batchingStrategy}};var ReactUpdates={ReactReconcileTransaction:null,batchedUpdates:batchedUpdates,enqueueUpdate:enqueueUpdate,flushBatchedUpdates:flushBatchedUpdates,injection:ReactUpdatesInjection,asap:asap};module.exports=ReactUpdates}).call(this,require("_process"))},{"./CallbackQueue":37,"./PooledClass":55,"./ReactFeatureFlags":87,"./ReactReconciler":103,"./Transaction":126,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"object-assign":26}],109:[function(require,module,exports){"use strict";module.exports="15.6.1"},{}],110:[function(require,module,exports){"use strict";var NS={xlink:"http://www.w3.org/1999/xlink",xml:"http://www.w3.org/XML/1998/namespace"};var ATTRS={accentHeight:"accent-height",accumulate:0,additive:0,alignmentBaseline:"alignment-baseline",allowReorder:"allowReorder",alphabetic:0,amplitude:0,arabicForm:"arabic-form",ascent:0,attributeName:"attributeName",attributeType:"attributeType",autoReverse:"autoReverse",azimuth:0,baseFrequency:"baseFrequency",baseProfile:"baseProfile",baselineShift:"baseline-shift",bbox:0,begin:0,bias:0,by:0,calcMode:"calcMode",capHeight:"cap-height",clip:0,clipPath:"clip-path",clipRule:"clip-rule",clipPathUnits:"clipPathUnits",colorInterpolation:"color-interpolation",colorInterpolationFilters:"color-interpolation-filters",colorProfile:"color-profile",colorRendering:"color-rendering",contentScriptType:"contentScriptType",contentStyleType:"contentStyleType",cursor:0,cx:0,cy:0,d:0,decelerate:0,descent:0,diffuseConstant:"diffuseConstant",direction:0,display:0,divisor:0,dominantBaseline:"dominant-baseline",dur:0,dx:0,dy:0,edgeMode:"edgeMode",elevation:0,enableBackground:"enable-background",end:0,exponent:0,externalResourcesRequired:"externalResourcesRequired",fill:0,fillOpacity:"fill-opacity",fillRule:"fill-rule",filter:0,filterRes:"filterRes",filterUnits:"filterUnits",floodColor:"flood-color",floodOpacity:"flood-opacity",focusable:0,fontFamily:"font-family",fontSize:"font-size",fontSizeAdjust:"font-size-adjust",fontStretch:"font-stretch",fontStyle:"font-style",fontVariant:"font-variant",fontWeight:"font-weight",format:0,from:0,fx:0,fy:0,g1:0,g2:0,glyphName:"glyph-name",glyphOrientationHorizontal:"glyph-orientation-horizontal",glyphOrientationVertical:"glyph-orientation-vertical",glyphRef:"glyphRef",gradientTransform:"gradientTransform",gradientUnits:"gradientUnits",hanging:0,horizAdvX:"horiz-adv-x",horizOriginX:"horiz-origin-x",ideographic:0,imageRendering:"image-rendering",in:0,in2:0,intercept:0,k:0,k1:0,k2:0,k3:0,k4:0,kernelMatrix:"kernelMatrix",kernelUnitLength:"kernelUnitLength",kerning:0,keyPoints:"keyPoints",keySplines:"keySplines",keyTimes:"keyTimes",lengthAdjust:"lengthAdjust",letterSpacing:"letter-spacing",lightingColor:"lighting-color",limitingConeAngle:"limitingConeAngle",local:0,markerEnd:"marker-end",markerMid:"marker-mid",markerStart:"marker-start",markerHeight:"markerHeight",markerUnits:"markerUnits",markerWidth:"markerWidth",mask:0,maskContentUnits:"maskContentUnits",maskUnits:"maskUnits",mathematical:0,mode:0,numOctaves:"numOctaves",offset:0,opacity:0,operator:0,order:0,orient:0,orientation:0,origin:0,overflow:0,overlinePosition:"overline-position",overlineThickness:"overline-thickness",paintOrder:"paint-order",panose1:"panose-1",pathLength:"pathLength",patternContentUnits:"patternContentUnits",patternTransform:"patternTransform",patternUnits:"patternUnits",pointerEvents:"pointer-events",points:0,pointsAtX:"pointsAtX",pointsAtY:"pointsAtY",pointsAtZ:"pointsAtZ",preserveAlpha:"preserveAlpha",preserveAspectRatio:"preserveAspectRatio",primitiveUnits:"primitiveUnits",r:0,radius:0,refX:"refX",refY:"refY",renderingIntent:"rendering-intent",repeatCount:"repeatCount",repeatDur:"repeatDur",requiredExtensions:"requiredExtensions",requiredFeatures:"requiredFeatures",restart:0,result:0,rotate:0,rx:0,ry:0,scale:0,seed:0,shapeRendering:"shape-rendering",slope:0,spacing:0,specularConstant:"specularConstant",specularExponent:"specularExponent",speed:0,spreadMethod:"spreadMethod",startOffset:"startOffset",stdDeviation:"stdDeviation",stemh:0,stemv:0,stitchTiles:"stitchTiles",stopColor:"stop-color",stopOpacity:"stop-opacity",strikethroughPosition:"strikethrough-position",strikethroughThickness:"strikethrough-thickness",string:0,stroke:0,strokeDasharray:"stroke-dasharray",strokeDashoffset:"stroke-dashoffset",strokeLinecap:"stroke-linecap",strokeLinejoin:"stroke-linejoin",strokeMiterlimit:"stroke-miterlimit",strokeOpacity:"stroke-opacity",strokeWidth:"stroke-width",surfaceScale:"surfaceScale",systemLanguage:"systemLanguage",tableValues:"tableValues",targetX:"targetX",targetY:"targetY",textAnchor:"text-anchor",textDecoration:"text-decoration",textRendering:"text-rendering",textLength:"textLength",to:0,transform:0,u1:0,u2:0,underlinePosition:"underline-position",underlineThickness:"underline-thickness",unicode:0,unicodeBidi:"unicode-bidi",unicodeRange:"unicode-range",unitsPerEm:"units-per-em",vAlphabetic:"v-alphabetic",vHanging:"v-hanging",vIdeographic:"v-ideographic",vMathematical:"v-mathematical",values:0,vectorEffect:"vector-effect",version:0,vertAdvY:"vert-adv-y",vertOriginX:"vert-origin-x",vertOriginY:"vert-origin-y",viewBox:"viewBox",viewTarget:"viewTarget",visibility:0,widths:0,wordSpacing:"word-spacing",writingMode:"writing-mode",x:0,xHeight:"x-height",x1:0,x2:0,xChannelSelector:"xChannelSelector",xlinkActuate:"xlink:actuate",xlinkArcrole:"xlink:arcrole",xlinkHref:"xlink:href",xlinkRole:"xlink:role",xlinkShow:"xlink:show",xlinkTitle:"xlink:title",xlinkType:"xlink:type",xmlBase:"xml:base",xmlns:0,xmlnsXlink:"xmlns:xlink",xmlLang:"xml:lang",xmlSpace:"xml:space",y:0,y1:0,y2:0,yChannelSelector:"yChannelSelector",z:0,zoomAndPan:"zoomAndPan"};var SVGDOMPropertyConfig={Properties:{},DOMAttributeNamespaces:{xlinkActuate:NS.xlink,xlinkArcrole:NS.xlink,xlinkHref:NS.xlink,xlinkRole:NS.xlink,xlinkShow:NS.xlink,xlinkTitle:NS.xlink,xlinkType:NS.xlink,xmlBase:NS.xml,xmlLang:NS.xml,xmlSpace:NS.xml},DOMAttributeNames:{}};Object.keys(ATTRS).forEach(function(key){SVGDOMPropertyConfig.Properties[key]=0;if(ATTRS[key]){SVGDOMPropertyConfig.DOMAttributeNames[key]=ATTRS[key]}});module.exports=SVGDOMPropertyConfig},{}],111:[function(require,module,exports){"use strict";var EventPropagators=require("./EventPropagators");var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactInputSelection=require("./ReactInputSelection");var SyntheticEvent=require("./SyntheticEvent");var getActiveElement=require("fbjs/lib/getActiveElement");var isTextInputElement=require("./isTextInputElement");var shallowEqual=require("fbjs/lib/shallowEqual");var skipSelectionChangeEvent=ExecutionEnvironment.canUseDOM&&"documentMode"in document&&document.documentMode<=11;var eventTypes={select:{phasedRegistrationNames:{bubbled:"onSelect",captured:"onSelectCapture"},dependencies:["topBlur","topContextMenu","topFocus","topKeyDown","topKeyUp","topMouseDown","topMouseUp","topSelectionChange"]}};var activeElement=null;var activeElementInst=null;var lastSelection=null;var mouseDown=false;var hasListener=false;function getSelection(node){if("selectionStart"in node&&ReactInputSelection.hasSelectionCapabilities(node)){return{start:node.selectionStart,end:node.selectionEnd}}else if(window.getSelection){var selection=window.getSelection();return{anchorNode:selection.anchorNode,anchorOffset:selection.anchorOffset,focusNode:selection.focusNode,focusOffset:selection.focusOffset}}else if(document.selection){var range=document.selection.createRange();return{parentElement:range.parentElement(),text:range.text,top:range.boundingTop,left:range.boundingLeft}}}function constructSelectEvent(nativeEvent,nativeEventTarget){if(mouseDown||activeElement==null||activeElement!==getActiveElement()){return null}var currentSelection=getSelection(activeElement);if(!lastSelection||!shallowEqual(lastSelection,currentSelection)){lastSelection=currentSelection;var syntheticEvent=SyntheticEvent.getPooled(eventTypes.select,activeElementInst,nativeEvent,nativeEventTarget);syntheticEvent.type="select";syntheticEvent.target=activeElement;EventPropagators.accumulateTwoPhaseDispatches(syntheticEvent);return syntheticEvent}return null}var SelectEventPlugin={eventTypes:eventTypes,extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){if(!hasListener){return null}var targetNode=targetInst?ReactDOMComponentTree.getNodeFromInstance(targetInst):window;switch(topLevelType){case"topFocus":if(isTextInputElement(targetNode)||targetNode.contentEditable==="true"){activeElement=targetNode;activeElementInst=targetInst;lastSelection=null}break;case"topBlur":activeElement=null;activeElementInst=null;lastSelection=null;break;case"topMouseDown":mouseDown=true;break;case"topContextMenu":case"topMouseUp":mouseDown=false;return constructSelectEvent(nativeEvent,nativeEventTarget);case"topSelectionChange":if(skipSelectionChangeEvent){break}case"topKeyDown":case"topKeyUp":return constructSelectEvent(nativeEvent,nativeEventTarget)}return null},didPutListener:function(inst,registrationName,listener){if(registrationName==="onSelect"){hasListener=true}}};module.exports=SelectEventPlugin},{"./EventPropagators":50,"./ReactDOMComponentTree":64,"./ReactInputSelection":91,"./SyntheticEvent":117,"./isTextInputElement":149,"fbjs/lib/ExecutionEnvironment":4,"fbjs/lib/getActiveElement":13,"fbjs/lib/shallowEqual":24}],112:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var EventListener=require("fbjs/lib/EventListener");var EventPropagators=require("./EventPropagators");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var SyntheticAnimationEvent=require("./SyntheticAnimationEvent");var SyntheticClipboardEvent=require("./SyntheticClipboardEvent");var SyntheticEvent=require("./SyntheticEvent");var SyntheticFocusEvent=require("./SyntheticFocusEvent");var SyntheticKeyboardEvent=require("./SyntheticKeyboardEvent");var SyntheticMouseEvent=require("./SyntheticMouseEvent");var SyntheticDragEvent=require("./SyntheticDragEvent");var SyntheticTouchEvent=require("./SyntheticTouchEvent");var SyntheticTransitionEvent=require("./SyntheticTransitionEvent");var SyntheticUIEvent=require("./SyntheticUIEvent");var SyntheticWheelEvent=require("./SyntheticWheelEvent");var emptyFunction=require("fbjs/lib/emptyFunction");var getEventCharCode=require("./getEventCharCode");var invariant=require("fbjs/lib/invariant");var eventTypes={};var topLevelEventsToDispatchConfig={};["abort","animationEnd","animationIteration","animationStart","blur","canPlay","canPlayThrough","click","contextMenu","copy","cut","doubleClick","drag","dragEnd","dragEnter","dragExit","dragLeave","dragOver","dragStart","drop","durationChange","emptied","encrypted","ended","error","focus","input","invalid","keyDown","keyPress","keyUp","load","loadedData","loadedMetadata","loadStart","mouseDown","mouseMove","mouseOut","mouseOver","mouseUp","paste","pause","play","playing","progress","rateChange","reset","scroll","seeked","seeking","stalled","submit","suspend","timeUpdate","touchCancel","touchEnd","touchMove","touchStart","transitionEnd","volumeChange","waiting","wheel"].forEach(function(event){var capitalizedEvent=event[0].toUpperCase()+event.slice(1);var onEvent="on"+capitalizedEvent;var topEvent="top"+capitalizedEvent;var type={phasedRegistrationNames:{bubbled:onEvent,captured:onEvent+"Capture"},dependencies:[topEvent]};eventTypes[event]=type;topLevelEventsToDispatchConfig[topEvent]=type});var onClickListeners={};function getDictionaryKey(inst){return"."+inst._rootNodeID}function isInteractive(tag){return tag==="button"||tag==="input"||tag==="select"||tag==="textarea"}var SimpleEventPlugin={eventTypes:eventTypes,extractEvents:function(topLevelType,targetInst,nativeEvent,nativeEventTarget){var dispatchConfig=topLevelEventsToDispatchConfig[topLevelType];if(!dispatchConfig){return null}var EventConstructor;switch(topLevelType){case"topAbort":case"topCanPlay":case"topCanPlayThrough":case"topDurationChange":case"topEmptied":case"topEncrypted":case"topEnded":case"topError":case"topInput":case"topInvalid":case"topLoad":case"topLoadedData":case"topLoadedMetadata":case"topLoadStart":case"topPause":case"topPlay":case"topPlaying":case"topProgress":case"topRateChange":case"topReset":case"topSeeked":case"topSeeking":case"topStalled":case"topSubmit":case"topSuspend":case"topTimeUpdate":case"topVolumeChange":case"topWaiting":EventConstructor=SyntheticEvent;break;case"topKeyPress":if(getEventCharCode(nativeEvent)===0){return null}case"topKeyDown":case"topKeyUp":EventConstructor=SyntheticKeyboardEvent;break;case"topBlur":case"topFocus":EventConstructor=SyntheticFocusEvent;break;case"topClick":if(nativeEvent.button===2){return null}case"topDoubleClick":case"topMouseDown":case"topMouseMove":case"topMouseUp":case"topMouseOut":case"topMouseOver":case"topContextMenu":EventConstructor=SyntheticMouseEvent;break;case"topDrag":case"topDragEnd":case"topDragEnter":case"topDragExit":case"topDragLeave":case"topDragOver":case"topDragStart":case"topDrop":EventConstructor=SyntheticDragEvent;break;case"topTouchCancel":case"topTouchEnd":case"topTouchMove":case"topTouchStart":EventConstructor=SyntheticTouchEvent;break;case"topAnimationEnd":case"topAnimationIteration":case"topAnimationStart":EventConstructor=SyntheticAnimationEvent;break;case"topTransitionEnd":EventConstructor=SyntheticTransitionEvent;break;case"topScroll":EventConstructor=SyntheticUIEvent;break;case"topWheel":EventConstructor=SyntheticWheelEvent;break;case"topCopy":case"topCut":case"topPaste":EventConstructor=SyntheticClipboardEvent;break}!EventConstructor?process.env.NODE_ENV!=="production"?invariant(false,"SimpleEventPlugin: Unhandled event type, `%s`.",topLevelType):_prodInvariant("86",topLevelType):void 0;var event=EventConstructor.getPooled(dispatchConfig,targetInst,nativeEvent,nativeEventTarget);EventPropagators.accumulateTwoPhaseDispatches(event);return event},didPutListener:function(inst,registrationName,listener){if(registrationName==="onClick"&&!isInteractive(inst._tag)){var key=getDictionaryKey(inst);var node=ReactDOMComponentTree.getNodeFromInstance(inst);if(!onClickListeners[key]){onClickListeners[key]=EventListener.listen(node,"click",emptyFunction)}}},willDeleteListener:function(inst,registrationName){if(registrationName==="onClick"&&!isInteractive(inst._tag)){var key=getDictionaryKey(inst);onClickListeners[key].remove();delete onClickListeners[key]}}};module.exports=SimpleEventPlugin}).call(this,require("_process"))},{"./EventPropagators":50,"./ReactDOMComponentTree":64,"./SyntheticAnimationEvent":113,"./SyntheticClipboardEvent":114,"./SyntheticDragEvent":116,"./SyntheticEvent":117,"./SyntheticFocusEvent":118,"./SyntheticKeyboardEvent":120,"./SyntheticMouseEvent":121,"./SyntheticTouchEvent":122,"./SyntheticTransitionEvent":123,"./SyntheticUIEvent":124,"./SyntheticWheelEvent":125,"./getEventCharCode":137,"./reactProdInvariant":151,_process:184,"fbjs/lib/EventListener":3,"fbjs/lib/emptyFunction":10,"fbjs/lib/invariant":18}],113:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var AnimationEventInterface={animationName:null,elapsedTime:null,pseudoElement:null};function SyntheticAnimationEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticAnimationEvent,AnimationEventInterface);module.exports=SyntheticAnimationEvent},{"./SyntheticEvent":117}],114:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var ClipboardEventInterface={clipboardData:function(event){return"clipboardData"in event?event.clipboardData:window.clipboardData}};function SyntheticClipboardEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticClipboardEvent,ClipboardEventInterface);module.exports=SyntheticClipboardEvent},{"./SyntheticEvent":117}],115:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var CompositionEventInterface={data:null};function SyntheticCompositionEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticCompositionEvent,CompositionEventInterface);module.exports=SyntheticCompositionEvent},{"./SyntheticEvent":117}],116:[function(require,module,exports){"use strict";var SyntheticMouseEvent=require("./SyntheticMouseEvent");var DragEventInterface={dataTransfer:null};function SyntheticDragEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticMouseEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticMouseEvent.augmentClass(SyntheticDragEvent,DragEventInterface);module.exports=SyntheticDragEvent},{"./SyntheticMouseEvent":121}],117:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var PooledClass=require("./PooledClass");var emptyFunction=require("fbjs/lib/emptyFunction");var warning=require("fbjs/lib/warning");var didWarnForAddedNewProperty=false;var isProxySupported=typeof Proxy==="function";var shouldBeReleasedProperties=["dispatchConfig","_targetInst","nativeEvent","isDefaultPrevented","isPropagationStopped","_dispatchListeners","_dispatchInstances"];var EventInterface={type:null,target:null,currentTarget:emptyFunction.thatReturnsNull,eventPhase:null,bubbles:null,cancelable:null,timeStamp:function(event){return event.timeStamp||Date.now()},defaultPrevented:null,isTrusted:null};function SyntheticEvent(dispatchConfig,targetInst,nativeEvent,nativeEventTarget){if(process.env.NODE_ENV!=="production"){delete this.nativeEvent;delete this.preventDefault;delete this.stopPropagation}this.dispatchConfig=dispatchConfig;this._targetInst=targetInst;this.nativeEvent=nativeEvent;var Interface=this.constructor.Interface;for(var propName in Interface){if(!Interface.hasOwnProperty(propName)){continue}if(process.env.NODE_ENV!=="production"){delete this[propName]}var normalize=Interface[propName];if(normalize){this[propName]=normalize(nativeEvent)}else{if(propName==="target"){this.target=nativeEventTarget}else{this[propName]=nativeEvent[propName]}}}var defaultPrevented=nativeEvent.defaultPrevented!=null?nativeEvent.defaultPrevented:nativeEvent.returnValue===false;if(defaultPrevented){this.isDefaultPrevented=emptyFunction.thatReturnsTrue}else{this.isDefaultPrevented=emptyFunction.thatReturnsFalse}this.isPropagationStopped=emptyFunction.thatReturnsFalse;return this}_assign(SyntheticEvent.prototype,{preventDefault:function(){this.defaultPrevented=true;var event=this.nativeEvent;if(!event){return}if(event.preventDefault){event.preventDefault()}else if(typeof event.returnValue!=="unknown"){event.returnValue=false}this.isDefaultPrevented=emptyFunction.thatReturnsTrue},stopPropagation:function(){var event=this.nativeEvent;if(!event){return}if(event.stopPropagation){event.stopPropagation()}else if(typeof event.cancelBubble!=="unknown"){event.cancelBubble=true}this.isPropagationStopped=emptyFunction.thatReturnsTrue},persist:function(){this.isPersistent=emptyFunction.thatReturnsTrue},isPersistent:emptyFunction.thatReturnsFalse,destructor:function(){var Interface=this.constructor.Interface;for(var propName in Interface){if(process.env.NODE_ENV!=="production"){Object.defineProperty(this,propName,getPooledWarningPropertyDefinition(propName,Interface[propName]))}else{this[propName]=null}}for(var i=0;i<shouldBeReleasedProperties.length;i++){this[shouldBeReleasedProperties[i]]=null}if(process.env.NODE_ENV!=="production"){Object.defineProperty(this,"nativeEvent",getPooledWarningPropertyDefinition("nativeEvent",null));Object.defineProperty(this,"preventDefault",getPooledWarningPropertyDefinition("preventDefault",emptyFunction));Object.defineProperty(this,"stopPropagation",getPooledWarningPropertyDefinition("stopPropagation",emptyFunction))}}});SyntheticEvent.Interface=EventInterface;if(process.env.NODE_ENV!=="production"){if(isProxySupported){SyntheticEvent=new Proxy(SyntheticEvent,{construct:function(target,args){return this.apply(target,Object.create(target.prototype),args)},apply:function(constructor,that,args){return new Proxy(constructor.apply(that,args),{set:function(target,prop,value){if(prop!=="isPersistent"&&!target.constructor.Interface.hasOwnProperty(prop)&&shouldBeReleasedProperties.indexOf(prop)===-1){process.env.NODE_ENV!=="production"?warning(didWarnForAddedNewProperty||target.isPersistent(),"This synthetic event is reused for performance reasons. If you're "+"seeing this, you're adding a new property in the synthetic event object. "+"The property is never released. See "+"https://fb.me/react-event-pooling for more information."):void 0;didWarnForAddedNewProperty=true}target[prop]=value;return true}})}})}}SyntheticEvent.augmentClass=function(Class,Interface){var Super=this;var E=function(){};E.prototype=Super.prototype;var prototype=new E;_assign(prototype,Class.prototype);Class.prototype=prototype;Class.prototype.constructor=Class;Class.Interface=_assign({},Super.Interface,Interface);Class.augmentClass=Super.augmentClass;PooledClass.addPoolingTo(Class,PooledClass.fourArgumentPooler)};PooledClass.addPoolingTo(SyntheticEvent,PooledClass.fourArgumentPooler);module.exports=SyntheticEvent;function getPooledWarningPropertyDefinition(propName,getVal){var isFunction=typeof getVal==="function";return{configurable:true,set:set,get:get};function set(val){var action=isFunction?"setting the method":"setting the property";warn(action,"This is effectively a no-op");return val}function get(){var action=isFunction?"accessing the method":"accessing the property";var result=isFunction?"This is a no-op function":"This is set to null";warn(action,result);return getVal}function warn(action,result){var warningCondition=false;process.env.NODE_ENV!=="production"?warning(warningCondition,"This synthetic event is reused for performance reasons. If you're seeing this, "+"you're %s `%s` on a released/nullified synthetic event. %s. "+"If you must keep the original synthetic event around, use event.persist(). "+"See https://fb.me/react-event-pooling for more information.",action,propName,result):void 0}}}).call(this,require("_process"))},{"./PooledClass":55,_process:184,"fbjs/lib/emptyFunction":10,"fbjs/lib/warning":25,"object-assign":26}],118:[function(require,module,exports){"use strict";var SyntheticUIEvent=require("./SyntheticUIEvent");var FocusEventInterface={relatedTarget:null};function SyntheticFocusEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticUIEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticUIEvent.augmentClass(SyntheticFocusEvent,FocusEventInterface);module.exports=SyntheticFocusEvent},{"./SyntheticUIEvent":124}],119:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var InputEventInterface={data:null};function SyntheticInputEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticInputEvent,InputEventInterface);module.exports=SyntheticInputEvent},{"./SyntheticEvent":117}],120:[function(require,module,exports){"use strict";var SyntheticUIEvent=require("./SyntheticUIEvent");var getEventCharCode=require("./getEventCharCode");var getEventKey=require("./getEventKey");var getEventModifierState=require("./getEventModifierState");var KeyboardEventInterface={key:getEventKey,location:null,ctrlKey:null,shiftKey:null,altKey:null,metaKey:null,repeat:null,locale:null,getModifierState:getEventModifierState,charCode:function(event){if(event.type==="keypress"){return getEventCharCode(event)}return 0},keyCode:function(event){if(event.type==="keydown"||event.type==="keyup"){return event.keyCode}return 0},which:function(event){if(event.type==="keypress"){return getEventCharCode(event)}if(event.type==="keydown"||event.type==="keyup"){return event.keyCode}return 0}};function SyntheticKeyboardEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticUIEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticUIEvent.augmentClass(SyntheticKeyboardEvent,KeyboardEventInterface);module.exports=SyntheticKeyboardEvent},{"./SyntheticUIEvent":124,"./getEventCharCode":137,"./getEventKey":138,"./getEventModifierState":139}],121:[function(require,module,exports){"use strict";var SyntheticUIEvent=require("./SyntheticUIEvent");var ViewportMetrics=require("./ViewportMetrics");var getEventModifierState=require("./getEventModifierState");var MouseEventInterface={screenX:null,screenY:null,clientX:null,clientY:null,ctrlKey:null,shiftKey:null,altKey:null,metaKey:null,getModifierState:getEventModifierState,button:function(event){var button=event.button;if("which"in event){return button}return button===2?2:button===4?1:0},buttons:null,relatedTarget:function(event){return event.relatedTarget||(event.fromElement===event.srcElement?event.toElement:event.fromElement)},pageX:function(event){return"pageX"in event?event.pageX:event.clientX+ViewportMetrics.currentScrollLeft},pageY:function(event){return"pageY"in event?event.pageY:event.clientY+ViewportMetrics.currentScrollTop}};function SyntheticMouseEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticUIEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticUIEvent.augmentClass(SyntheticMouseEvent,MouseEventInterface);module.exports=SyntheticMouseEvent},{"./SyntheticUIEvent":124,"./ViewportMetrics":127,"./getEventModifierState":139}],122:[function(require,module,exports){"use strict";var SyntheticUIEvent=require("./SyntheticUIEvent");var getEventModifierState=require("./getEventModifierState");var TouchEventInterface={touches:null,targetTouches:null,changedTouches:null,altKey:null,metaKey:null,ctrlKey:null,shiftKey:null,getModifierState:getEventModifierState};function SyntheticTouchEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticUIEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticUIEvent.augmentClass(SyntheticTouchEvent,TouchEventInterface);module.exports=SyntheticTouchEvent},{"./SyntheticUIEvent":124,"./getEventModifierState":139}],123:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var TransitionEventInterface={propertyName:null,elapsedTime:null,pseudoElement:null};function SyntheticTransitionEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticTransitionEvent,TransitionEventInterface);module.exports=SyntheticTransitionEvent},{"./SyntheticEvent":117}],124:[function(require,module,exports){"use strict";var SyntheticEvent=require("./SyntheticEvent");var getEventTarget=require("./getEventTarget");var UIEventInterface={view:function(event){if(event.view){return event.view}var target=getEventTarget(event);if(target.window===target){return target}var doc=target.ownerDocument;if(doc){return doc.defaultView||doc.parentWindow}else{return window}},detail:function(event){return event.detail||0}};function SyntheticUIEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticEvent.augmentClass(SyntheticUIEvent,UIEventInterface);module.exports=SyntheticUIEvent},{"./SyntheticEvent":117,"./getEventTarget":140}],125:[function(require,module,exports){"use strict";var SyntheticMouseEvent=require("./SyntheticMouseEvent");var WheelEventInterface={deltaX:function(event){return"deltaX"in event?event.deltaX:"wheelDeltaX"in event?-event.wheelDeltaX:0},deltaY:function(event){return"deltaY"in event?event.deltaY:"wheelDeltaY"in event?-event.wheelDeltaY:"wheelDelta"in event?-event.wheelDelta:0},deltaZ:null,deltaMode:null};function SyntheticWheelEvent(dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget){return SyntheticMouseEvent.call(this,dispatchConfig,dispatchMarker,nativeEvent,nativeEventTarget)}SyntheticMouseEvent.augmentClass(SyntheticWheelEvent,WheelEventInterface);module.exports=SyntheticWheelEvent},{"./SyntheticMouseEvent":121}],126:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");var OBSERVED_ERROR={};var TransactionImpl={reinitializeTransaction:function(){this.transactionWrappers=this.getTransactionWrappers();if(this.wrapperInitData){this.wrapperInitData.length=0}else{this.wrapperInitData=[]}this._isInTransaction=false},_isInTransaction:false,getTransactionWrappers:null,isInTransaction:function(){return!!this._isInTransaction},perform:function(method,scope,a,b,c,d,e,f){!!this.isInTransaction()?process.env.NODE_ENV!=="production"?invariant(false,"Transaction.perform(...): Cannot initialize a transaction when there is already an outstanding transaction."):_prodInvariant("27"):void 0;var errorThrown;var ret;try{this._isInTransaction=true;errorThrown=true;this.initializeAll(0);ret=method.call(scope,a,b,c,d,e,f);errorThrown=false}finally{try{if(errorThrown){try{this.closeAll(0)}catch(err){}}else{this.closeAll(0)}}finally{this._isInTransaction=false}}return ret},initializeAll:function(startIndex){var transactionWrappers=this.transactionWrappers;for(var i=startIndex;i<transactionWrappers.length;i++){var wrapper=transactionWrappers[i];try{this.wrapperInitData[i]=OBSERVED_ERROR;this.wrapperInitData[i]=wrapper.initialize?wrapper.initialize.call(this):null}finally{if(this.wrapperInitData[i]===OBSERVED_ERROR){try{this.initializeAll(i+1)}catch(err){}}}}},closeAll:function(startIndex){!this.isInTransaction()?process.env.NODE_ENV!=="production"?invariant(false,"Transaction.closeAll(): Cannot close transaction when none are open."):_prodInvariant("28"):void 0;var transactionWrappers=this.transactionWrappers;for(var i=startIndex;i<transactionWrappers.length;i++){var wrapper=transactionWrappers[i];var initData=this.wrapperInitData[i];var errorThrown;try{errorThrown=true;if(initData!==OBSERVED_ERROR&&wrapper.close){wrapper.close.call(this,initData)}errorThrown=false}finally{if(errorThrown){try{this.closeAll(i+1)}catch(e){}}}}this.wrapperInitData.length=0}};module.exports=TransactionImpl}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],127:[function(require,module,exports){"use strict";var ViewportMetrics={currentScrollLeft:0,currentScrollTop:0,refreshScrollValues:function(scrollPosition){ViewportMetrics.currentScrollLeft=scrollPosition.x;ViewportMetrics.currentScrollTop=scrollPosition.y}};module.exports=ViewportMetrics},{}],128:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var invariant=require("fbjs/lib/invariant");function accumulateInto(current,next){!(next!=null)?process.env.NODE_ENV!=="production"?invariant(false,"accumulateInto(...): Accumulated items must not be null or undefined."):_prodInvariant("30"):void 0;if(current==null){return next}if(Array.isArray(current)){if(Array.isArray(next)){current.push.apply(current,next);return current}current.push(next);return current}if(Array.isArray(next)){return[current].concat(next)}return[current,next]}module.exports=accumulateInto}).call(this,require("_process"))},{"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18}],129:[function(require,module,exports){"use strict";var MOD=65521;function adler32(data){var a=1;var b=0;var i=0;var l=data.length;var m=l&~3;while(i<m){var n=Math.min(i+4096,m);for(;i<n;i+=4){b+=(a+=data.charCodeAt(i))+(a+=data.charCodeAt(i+1))+(a+=data.charCodeAt(i+2))+(a+=data.charCodeAt(i+3))}a%=MOD;b%=MOD}for(;i<l;i++){b+=a+=data.charCodeAt(i)}a%=MOD;b%=MOD;return a|b<<16}module.exports=adler32},{}],130:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactPropTypeLocationNames=require("./ReactPropTypeLocationNames");var ReactPropTypesSecret=require("./ReactPropTypesSecret");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ReactComponentTreeHook;if(typeof process!=="undefined"&&process.env&&process.env.NODE_ENV==="test"){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}var loggedTypeFailures={};function checkReactTypeSpec(typeSpecs,values,location,componentName,element,debugID){for(var typeSpecName in typeSpecs){if(typeSpecs.hasOwnProperty(typeSpecName)){var error;try{!(typeof typeSpecs[typeSpecName]==="function")?process.env.NODE_ENV!=="production"?invariant(false,"%s: %s type `%s` is invalid; it must be a function, usually from React.PropTypes.",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName):_prodInvariant("84",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName):void 0;error=typeSpecs[typeSpecName](values,typeSpecName,componentName,location,null,ReactPropTypesSecret)}catch(ex){error=ex}process.env.NODE_ENV!=="production"?warning(!error||error instanceof Error,"%s: type specification of %s `%s` is invalid; the type checker "+"function must return `null` or an `Error` but returned a %s. "+"You may have forgotten to pass an argument to the type checker "+"creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and "+"shape all require an argument).",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName,typeof error):void 0;if(error instanceof Error&&!(error.message in loggedTypeFailures)){loggedTypeFailures[error.message]=true;var componentStackInfo="";if(process.env.NODE_ENV!=="production"){if(!ReactComponentTreeHook){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}if(debugID!==null){componentStackInfo=ReactComponentTreeHook.getStackAddendumByID(debugID)}else if(element!==null){componentStackInfo=ReactComponentTreeHook.getCurrentStackAddendum(element)}}process.env.NODE_ENV!=="production"?warning(false,"Failed %s type: %s%s",location,error.message,componentStackInfo):void 0}}}}module.exports=checkReactTypeSpec}).call(this,require("_process"))},{"./ReactPropTypeLocationNames":100,"./ReactPropTypesSecret":101,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],131:[function(require,module,exports){"use strict";var createMicrosoftUnsafeLocalFunction=function(func){if(typeof MSApp!=="undefined"&&MSApp.execUnsafeLocalFunction){return function(arg0,arg1,arg2,arg3){MSApp.execUnsafeLocalFunction(function(){return func(arg0,arg1,arg2,arg3)})}}else{return func}};module.exports=createMicrosoftUnsafeLocalFunction},{}],132:[function(require,module,exports){(function(process){"use strict";var CSSProperty=require("./CSSProperty");var warning=require("fbjs/lib/warning");var isUnitlessNumber=CSSProperty.isUnitlessNumber;var styleWarnings={};function dangerousStyleValue(name,value,component,isCustomProperty){var isEmpty=value==null||typeof value==="boolean"||value==="";if(isEmpty){return""}var isNonNumeric=isNaN(value);if(isCustomProperty||isNonNumeric||value===0||isUnitlessNumber.hasOwnProperty(name)&&isUnitlessNumber[name]){return""+value}if(typeof value==="string"){if(process.env.NODE_ENV!=="production"){if(component&&value!=="0"){var owner=component._currentElement._owner;var ownerName=owner?owner.getName():null;if(ownerName&&!styleWarnings[ownerName]){styleWarnings[ownerName]={}}var warned=false;if(ownerName){var warnings=styleWarnings[ownerName];warned=warnings[name];if(!warned){warnings[name]=true}}if(!warned){process.env.NODE_ENV!=="production"?warning(false,"a `%s` tag (owner: `%s`) was passed a numeric string value "+"for CSS property `%s` (value: `%s`) which will be treated "+"as a unitless number in a future version of React.",component._currentElement.type,ownerName||"unknown",name,value):void 0}}}value=value.trim()}return value+"px"}module.exports=dangerousStyleValue}).call(this,require("_process"))},{"./CSSProperty":35,_process:184,"fbjs/lib/warning":25}],133:[function(require,module,exports){"use strict";var matchHtmlRegExp=/["'&<>]/;function escapeHtml(string){var str=""+string;var match=matchHtmlRegExp.exec(str);if(!match){return str}var escape;var html="";var index=0;var lastIndex=0;for(index=match.index;index<str.length;index++){switch(str.charCodeAt(index)){case 34:escape="&quot;";break;case 38:escape="&amp;";break;case 39:escape="&#x27;";break;case 60:escape="&lt;";break;case 62:escape="&gt;";break;default:continue}if(lastIndex!==index){html+=str.substring(lastIndex,index)}lastIndex=index+1;html+=escape}return lastIndex!==index?html+str.substring(lastIndex,index):html}function escapeTextContentForBrowser(text){if(typeof text==="boolean"||typeof text==="number"){return""+text}return escapeHtml(text)}module.exports=escapeTextContentForBrowser},{}],134:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var ReactDOMComponentTree=require("./ReactDOMComponentTree");var ReactInstanceMap=require("./ReactInstanceMap");var getHostComponentFromComposite=require("./getHostComponentFromComposite");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");function findDOMNode(componentOrElement){if(process.env.NODE_ENV!=="production"){var owner=ReactCurrentOwner.current;if(owner!==null){process.env.NODE_ENV!=="production"?warning(owner._warnedAboutRefsInRender,"%s is accessing findDOMNode inside its render(). "+"render() should be a pure function of props and state. It should "+"never access something that requires stale data from the previous "+"render, such as refs. Move this logic to componentDidMount and "+"componentDidUpdate instead.",owner.getName()||"A component"):void 0;owner._warnedAboutRefsInRender=true}}if(componentOrElement==null){return null}if(componentOrElement.nodeType===1){return componentOrElement}var inst=ReactInstanceMap.get(componentOrElement);if(inst){inst=getHostComponentFromComposite(inst);return inst?ReactDOMComponentTree.getNodeFromInstance(inst):null}if(typeof componentOrElement.render==="function"){!false?process.env.NODE_ENV!=="production"?invariant(false,"findDOMNode was called on an unmounted component."):_prodInvariant("44"):void 0}else{!false?process.env.NODE_ENV!=="production"?invariant(false,"Element appears to be neither ReactComponent nor DOMNode (keys: %s)",Object.keys(componentOrElement)):_prodInvariant("45",Object.keys(componentOrElement)):void 0}}module.exports=findDOMNode}).call(this,require("_process"))},{"./ReactDOMComponentTree":64,"./ReactInstanceMap":92,"./getHostComponentFromComposite":141,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"react/lib/ReactCurrentOwner":164}],135:[function(require,module,exports){(function(process){"use strict";var KeyEscapeUtils=require("./KeyEscapeUtils");var traverseAllChildren=require("./traverseAllChildren");var warning=require("fbjs/lib/warning");var ReactComponentTreeHook;if(typeof process!=="undefined"&&process.env&&process.env.NODE_ENV==="test"){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}function flattenSingleChildIntoContext(traverseContext,child,name,selfDebugID){if(traverseContext&&typeof traverseContext==="object"){var result=traverseContext;var keyUnique=result[name]===undefined;if(process.env.NODE_ENV!=="production"){if(!ReactComponentTreeHook){ReactComponentTreeHook=require("react/lib/ReactComponentTreeHook")}if(!keyUnique){process.env.NODE_ENV!=="production"?warning(false,"flattenChildren(...): Encountered two children with the same key, "+"`%s`. Child keys must be unique; when two children share a key, only "+"the first child will be used.%s",KeyEscapeUtils.unescape(name),ReactComponentTreeHook.getStackAddendumByID(selfDebugID)):void 0}}if(keyUnique&&child!=null){result[name]=child}}}function flattenChildren(children,selfDebugID){if(children==null){return children}var result={};if(process.env.NODE_ENV!=="production"){traverseAllChildren(children,function(traverseContext,child,name){return flattenSingleChildIntoContext(traverseContext,child,name,selfDebugID)},result)}else{traverseAllChildren(children,flattenSingleChildIntoContext,result)}return result}module.exports=flattenChildren}).call(this,require("_process"))},{"./KeyEscapeUtils":53,"./traverseAllChildren":156,_process:184,"fbjs/lib/warning":25,"react/lib/ReactComponentTreeHook":163}],136:[function(require,module,exports){"use strict";function forEachAccumulated(arr,cb,scope){if(Array.isArray(arr)){arr.forEach(cb,scope)}else if(arr){cb.call(scope,arr)}}module.exports=forEachAccumulated},{}],137:[function(require,module,exports){"use strict";function getEventCharCode(nativeEvent){var charCode;var keyCode=nativeEvent.keyCode;if("charCode"in nativeEvent){charCode=nativeEvent.charCode;if(charCode===0&&keyCode===13){charCode=13}}else{charCode=keyCode}if(charCode>=32||charCode===13){return charCode}return 0}module.exports=getEventCharCode},{}],138:[function(require,module,exports){"use strict";var getEventCharCode=require("./getEventCharCode");var normalizeKey={Esc:"Escape",Spacebar:" ",Left:"ArrowLeft",Up:"ArrowUp",Right:"ArrowRight",Down:"ArrowDown",Del:"Delete",Win:"OS",Menu:"ContextMenu",Apps:"ContextMenu",Scroll:"ScrollLock",MozPrintableKey:"Unidentified"};var translateToKey={8:"Backspace",9:"Tab",12:"Clear",13:"Enter",16:"Shift",17:"Control",18:"Alt",19:"Pause",20:"CapsLock",27:"Escape",32:" ",33:"PageUp",34:"PageDown",35:"End",36:"Home",37:"ArrowLeft",38:"ArrowUp",39:"ArrowRight",40:"ArrowDown",45:"Insert",46:"Delete",112:"F1",113:"F2",114:"F3",115:"F4",116:"F5",117:"F6",118:"F7",119:"F8",120:"F9",121:"F10",122:"F11",123:"F12",144:"NumLock",145:"ScrollLock",224:"Meta"};function getEventKey(nativeEvent){if(nativeEvent.key){var key=normalizeKey[nativeEvent.key]||nativeEvent.key;if(key!=="Unidentified"){return key}}if(nativeEvent.type==="keypress"){var charCode=getEventCharCode(nativeEvent);return charCode===13?"Enter":String.fromCharCode(charCode)}if(nativeEvent.type==="keydown"||nativeEvent.type==="keyup"){return translateToKey[nativeEvent.keyCode]||"Unidentified"}return""}module.exports=getEventKey},{"./getEventCharCode":137}],139:[function(require,module,exports){"use strict";var modifierKeyToProp={Alt:"altKey",Control:"ctrlKey",Meta:"metaKey",Shift:"shiftKey"};function modifierStateGetter(keyArg){var syntheticEvent=this;var nativeEvent=syntheticEvent.nativeEvent;if(nativeEvent.getModifierState){return nativeEvent.getModifierState(keyArg)}var keyProp=modifierKeyToProp[keyArg];return keyProp?!!nativeEvent[keyProp]:false}function getEventModifierState(nativeEvent){return modifierStateGetter}module.exports=getEventModifierState},{}],140:[function(require,module,exports){"use strict";function getEventTarget(nativeEvent){var target=nativeEvent.target||nativeEvent.srcElement||window;if(target.correspondingUseElement){target=target.correspondingUseElement}return target.nodeType===3?target.parentNode:target}module.exports=getEventTarget},{}],141:[function(require,module,exports){"use strict";var ReactNodeTypes=require("./ReactNodeTypes");function getHostComponentFromComposite(inst){var type;while((type=inst._renderedNodeType)===ReactNodeTypes.COMPOSITE){inst=inst._renderedComponent}if(type===ReactNodeTypes.HOST){return inst._renderedComponent}else if(type===ReactNodeTypes.EMPTY){return null}}module.exports=getHostComponentFromComposite},{"./ReactNodeTypes":98}],142:[function(require,module,exports){"use strict";var ITERATOR_SYMBOL=typeof Symbol==="function"&&Symbol.iterator;var FAUX_ITERATOR_SYMBOL="@@iterator";function getIteratorFn(maybeIterable){var iteratorFn=maybeIterable&&(ITERATOR_SYMBOL&&maybeIterable[ITERATOR_SYMBOL]||maybeIterable[FAUX_ITERATOR_SYMBOL]);if(typeof iteratorFn==="function"){return iteratorFn}}module.exports=getIteratorFn},{}],143:[function(require,module,exports){"use strict";function getLeafNode(node){while(node&&node.firstChild){node=node.firstChild}return node}function getSiblingNode(node){while(node){if(node.nextSibling){return node.nextSibling}node=node.parentNode}}function getNodeForCharacterOffset(root,offset){var node=getLeafNode(root);var nodeStart=0;var nodeEnd=0;while(node){if(node.nodeType===3){nodeEnd=nodeStart+node.textContent.length;if(nodeStart<=offset&&nodeEnd>=offset){return{node:node,offset:offset-nodeStart}}nodeStart=nodeEnd}node=getLeafNode(getSiblingNode(node))}}module.exports=getNodeForCharacterOffset},{}],144:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var contentKey=null;function getTextContentAccessor(){if(!contentKey&&ExecutionEnvironment.canUseDOM){contentKey="textContent"in document.documentElement?"textContent":"innerText"}return contentKey}module.exports=getTextContentAccessor},{"fbjs/lib/ExecutionEnvironment":4}],145:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");function makePrefixMap(styleProp,eventName){var prefixes={};prefixes[styleProp.toLowerCase()]=eventName.toLowerCase();prefixes["Webkit"+styleProp]="webkit"+eventName;prefixes["Moz"+styleProp]="moz"+eventName;prefixes["ms"+styleProp]="MS"+eventName;prefixes["O"+styleProp]="o"+eventName.toLowerCase();return prefixes}var vendorPrefixes={animationend:makePrefixMap("Animation","AnimationEnd"),animationiteration:makePrefixMap("Animation","AnimationIteration"),animationstart:makePrefixMap("Animation","AnimationStart"),transitionend:makePrefixMap("Transition","TransitionEnd")};var prefixedEventNames={};var style={};if(ExecutionEnvironment.canUseDOM){style=document.createElement("div").style;if(!("AnimationEvent"in window)){delete vendorPrefixes.animationend.animation;delete vendorPrefixes.animationiteration.animation;delete vendorPrefixes.animationstart.animation}if(!("TransitionEvent"in window)){delete vendorPrefixes.transitionend.transition}}function getVendorPrefixedEventName(eventName){if(prefixedEventNames[eventName]){return prefixedEventNames[eventName]}else if(!vendorPrefixes[eventName]){return eventName}var prefixMap=vendorPrefixes[eventName];for(var styleProp in prefixMap){if(prefixMap.hasOwnProperty(styleProp)&&styleProp in style){return prefixedEventNames[eventName]=prefixMap[styleProp]}}return""}module.exports=getVendorPrefixedEventName},{"fbjs/lib/ExecutionEnvironment":4}],146:[function(require,module,exports){"use strict";var ReactDOMComponentTree=require("./ReactDOMComponentTree");function isCheckable(elem){var type=elem.type;var nodeName=elem.nodeName;return nodeName&&nodeName.toLowerCase()==="input"&&(type==="checkbox"||type==="radio")}function getTracker(inst){return inst._wrapperState.valueTracker}function attachTracker(inst,tracker){inst._wrapperState.valueTracker=tracker}function detachTracker(inst){delete inst._wrapperState.valueTracker}function getValueFromNode(node){var value;if(node){value=isCheckable(node)?""+node.checked:node.value}return value}var inputValueTracking={_getTrackerFromNode:function(node){return getTracker(ReactDOMComponentTree.getInstanceFromNode(node))},track:function(inst){if(getTracker(inst)){return}var node=ReactDOMComponentTree.getNodeFromInstance(inst);var valueField=isCheckable(node)?"checked":"value";var descriptor=Object.getOwnPropertyDescriptor(node.constructor.prototype,valueField);var currentValue=""+node[valueField];if(node.hasOwnProperty(valueField)||typeof descriptor.get!=="function"||typeof descriptor.set!=="function"){return}Object.defineProperty(node,valueField,{enumerable:descriptor.enumerable,configurable:true,get:function(){return descriptor.get.call(this)},set:function(value){currentValue=""+value;descriptor.set.call(this,value)}});attachTracker(inst,{getValue:function(){return currentValue},setValue:function(value){currentValue=""+value},stopTracking:function(){detachTracker(inst);delete node[valueField]}})},updateValueIfChanged:function(inst){if(!inst){return false}var tracker=getTracker(inst);if(!tracker){inputValueTracking.track(inst);return true}var lastValue=tracker.getValue();var nextValue=getValueFromNode(ReactDOMComponentTree.getNodeFromInstance(inst));if(nextValue!==lastValue){tracker.setValue(nextValue);return true}return false},stopTracking:function(inst){var tracker=getTracker(inst);if(tracker){tracker.stopTracking()}}};module.exports=inputValueTracking},{"./ReactDOMComponentTree":64}],147:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var ReactCompositeComponent=require("./ReactCompositeComponent");var ReactEmptyComponent=require("./ReactEmptyComponent");var ReactHostComponent=require("./ReactHostComponent");var getNextDebugID=require("react/lib/getNextDebugID");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ReactCompositeComponentWrapper=function(element){this.construct(element)};function getDeclarationErrorAddendum(owner){if(owner){var name=owner.getName();if(name){return" Check the render method of `"+name+"`."}}return""}function isInternalComponentType(type){return typeof type==="function"&&typeof type.prototype!=="undefined"&&typeof type.prototype.mountComponent==="function"&&typeof type.prototype.receiveComponent==="function"}function instantiateReactComponent(node,shouldHaveDebugID){var instance;if(node===null||node===false){instance=ReactEmptyComponent.create(instantiateReactComponent)}else if(typeof node==="object"){var element=node;var type=element.type;if(typeof type!=="function"&&typeof type!=="string"){var info="";if(process.env.NODE_ENV!=="production"){if(type===undefined||typeof type==="object"&&type!==null&&Object.keys(type).length===0){info+=" You likely forgot to export your component from the file "+"it's defined in."}}info+=getDeclarationErrorAddendum(element._owner);!false?process.env.NODE_ENV!=="production"?invariant(false,"Element type is invalid: expected a string (for built-in components) or a class/function (for composite components) but got: %s.%s",type==null?type:typeof type,info):_prodInvariant("130",type==null?type:typeof type,info):void 0}if(typeof element.type==="string"){instance=ReactHostComponent.createInternalComponent(element)}else if(isInternalComponentType(element.type)){instance=new element.type(element);if(!instance.getHostNode){instance.getHostNode=instance.getNativeNode}}else{instance=new ReactCompositeComponentWrapper(element)}}else if(typeof node==="string"||typeof node==="number"){instance=ReactHostComponent.createInstanceForText(node)}else{!false?process.env.NODE_ENV!=="production"?invariant(false,"Encountered invalid React node of type %s",typeof node):_prodInvariant("131",typeof node):void 0}if(process.env.NODE_ENV!=="production"){process.env.NODE_ENV!=="production"?warning(typeof instance.mountComponent==="function"&&typeof instance.receiveComponent==="function"&&typeof instance.getHostNode==="function"&&typeof instance.unmountComponent==="function","Only React Components can be mounted."):void 0}instance._mountIndex=0;instance._mountImage=null;if(process.env.NODE_ENV!=="production"){instance._debugID=shouldHaveDebugID?getNextDebugID():0}if(process.env.NODE_ENV!=="production"){if(Object.preventExtensions){Object.preventExtensions(instance)}}return instance}_assign(ReactCompositeComponentWrapper.prototype,ReactCompositeComponent,{_instantiateReactComponent:instantiateReactComponent});module.exports=instantiateReactComponent}).call(this,require("_process"))},{"./ReactCompositeComponent":60,"./ReactEmptyComponent":83,"./ReactHostComponent":88,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"object-assign":26,"react/lib/getNextDebugID":178}],148:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var useHasFeature;if(ExecutionEnvironment.canUseDOM){useHasFeature=document.implementation&&document.implementation.hasFeature&&document.implementation.hasFeature("","")!==true}function isEventSupported(eventNameSuffix,capture){if(!ExecutionEnvironment.canUseDOM||capture&&!("addEventListener"in document)){return false}var eventName="on"+eventNameSuffix;var isSupported=eventName in document;if(!isSupported){var element=document.createElement("div");element.setAttribute(eventName,"return;");isSupported=typeof element[eventName]==="function"}if(!isSupported&&useHasFeature&&eventNameSuffix==="wheel"){isSupported=document.implementation.hasFeature("Events.wheel","3.0")}return isSupported}module.exports=isEventSupported},{"fbjs/lib/ExecutionEnvironment":4}],149:[function(require,module,exports){"use strict";var supportedInputTypes={color:true,date:true,datetime:true,"datetime-local":true,email:true,month:true,number:true,password:true,range:true,search:true,tel:true,text:true,time:true,url:true,week:true};function isTextInputElement(elem){var nodeName=elem&&elem.nodeName&&elem.nodeName.toLowerCase();if(nodeName==="input"){return!!supportedInputTypes[elem.type]}if(nodeName==="textarea"){return true}return false}module.exports=isTextInputElement},{}],150:[function(require,module,exports){"use strict";var escapeTextContentForBrowser=require("./escapeTextContentForBrowser");function quoteAttributeValueForBrowser(value){return'"'+escapeTextContentForBrowser(value)+'"'}module.exports=quoteAttributeValueForBrowser},{"./escapeTextContentForBrowser":133}],151:[function(require,module,exports){"use strict";function reactProdInvariant(code){var argCount=arguments.length-1;var message="Minified React error #"+code+"; visit "+"http://facebook.github.io/react/docs/error-decoder.html?invariant="+code;for(var argIdx=0;argIdx<argCount;argIdx++){message+="&args[]="+encodeURIComponent(arguments[argIdx+1])}message+=" for the full message or use the non-minified dev environment"+" for full errors and additional helpful warnings.";var error=new Error(message);error.name="Invariant Violation";error.framesToPop=1;throw error}module.exports=reactProdInvariant},{}],152:[function(require,module,exports){"use strict";var ReactMount=require("./ReactMount");module.exports=ReactMount.renderSubtreeIntoContainer},{"./ReactMount":96}],153:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var DOMNamespaces=require("./DOMNamespaces");var WHITESPACE_TEST=/^[ \r\n\t\f]/;var NONVISIBLE_TEST=/<(!--|link|noscript|meta|script|style)[ \r\n\t\f\/>]/;var createMicrosoftUnsafeLocalFunction=require("./createMicrosoftUnsafeLocalFunction");var reusableSVGContainer;var setInnerHTML=createMicrosoftUnsafeLocalFunction(function(node,html){if(node.namespaceURI===DOMNamespaces.svg&&!("innerHTML"in node)){reusableSVGContainer=reusableSVGContainer||document.createElement("div");reusableSVGContainer.innerHTML="<svg>"+html+"</svg>";var svgNode=reusableSVGContainer.firstChild;while(svgNode.firstChild){node.appendChild(svgNode.firstChild)}}else{node.innerHTML=html}});if(ExecutionEnvironment.canUseDOM){var testElement=document.createElement("div");testElement.innerHTML=" ";if(testElement.innerHTML===""){setInnerHTML=function(node,html){if(node.parentNode){node.parentNode.replaceChild(node,node)}if(WHITESPACE_TEST.test(html)||html[0]==="<"&&NONVISIBLE_TEST.test(html)){node.innerHTML=String.fromCharCode(65279)+html;var textNode=node.firstChild;if(textNode.data.length===1){node.removeChild(textNode)}else{textNode.deleteData(0,1)}}else{node.innerHTML=html}}}testElement=null}module.exports=setInnerHTML},{"./DOMNamespaces":41,"./createMicrosoftUnsafeLocalFunction":131,"fbjs/lib/ExecutionEnvironment":4}],154:[function(require,module,exports){"use strict";var ExecutionEnvironment=require("fbjs/lib/ExecutionEnvironment");var escapeTextContentForBrowser=require("./escapeTextContentForBrowser");var setInnerHTML=require("./setInnerHTML");var setTextContent=function(node,text){if(text){var firstChild=node.firstChild;if(firstChild&&firstChild===node.lastChild&&firstChild.nodeType===3){firstChild.nodeValue=text;return}}node.textContent=text};if(ExecutionEnvironment.canUseDOM){if(!("textContent"in document.documentElement)){setTextContent=function(node,text){if(node.nodeType===3){node.nodeValue=text;return}setInnerHTML(node,escapeTextContentForBrowser(text))}}}module.exports=setTextContent},{"./escapeTextContentForBrowser":133,"./setInnerHTML":153,"fbjs/lib/ExecutionEnvironment":4}],155:[function(require,module,exports){"use strict";function shouldUpdateReactComponent(prevElement,nextElement){var prevEmpty=prevElement===null||prevElement===false;var nextEmpty=nextElement===null||nextElement===false;if(prevEmpty||nextEmpty){return prevEmpty===nextEmpty}var prevType=typeof prevElement;var nextType=typeof nextElement;if(prevType==="string"||prevType==="number"){return nextType==="string"||nextType==="number"}else{return nextType==="object"&&prevElement.type===nextElement.type&&prevElement.key===nextElement.key}}module.exports=shouldUpdateReactComponent},{}],156:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactCurrentOwner=require("react/lib/ReactCurrentOwner");var REACT_ELEMENT_TYPE=require("./ReactElementSymbol");var getIteratorFn=require("./getIteratorFn");var invariant=require("fbjs/lib/invariant");var KeyEscapeUtils=require("./KeyEscapeUtils");var warning=require("fbjs/lib/warning");var SEPARATOR=".";var SUBSEPARATOR=":";var didWarnAboutMaps=false;function getComponentKey(component,index){if(component&&typeof component==="object"&&component.key!=null){return KeyEscapeUtils.escape(component.key)}return index.toString(36)}function traverseAllChildrenImpl(children,nameSoFar,callback,traverseContext){var type=typeof children;if(type==="undefined"||type==="boolean"){children=null}if(children===null||type==="string"||type==="number"||type==="object"&&children.$$typeof===REACT_ELEMENT_TYPE){callback(traverseContext,children,nameSoFar===""?SEPARATOR+getComponentKey(children,0):nameSoFar);return 1}var child;var nextName;var subtreeCount=0;var nextNamePrefix=nameSoFar===""?SEPARATOR:nameSoFar+SUBSEPARATOR;if(Array.isArray(children)){for(var i=0;i<children.length;i++){child=children[i];nextName=nextNamePrefix+getComponentKey(child,i);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}else{var iteratorFn=getIteratorFn(children);if(iteratorFn){var iterator=iteratorFn.call(children);var step;if(iteratorFn!==children.entries){var ii=0;while(!(step=iterator.next()).done){child=step.value;nextName=nextNamePrefix+getComponentKey(child,ii++);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}else{if(process.env.NODE_ENV!=="production"){var mapsAsChildrenAddendum="";if(ReactCurrentOwner.current){var mapsAsChildrenOwnerName=ReactCurrentOwner.current.getName();if(mapsAsChildrenOwnerName){mapsAsChildrenAddendum=" Check the render method of `"+mapsAsChildrenOwnerName+"`."}}process.env.NODE_ENV!=="production"?warning(didWarnAboutMaps,"Using Maps as children is not yet fully supported. It is an "+"experimental feature that might be removed. Convert it to a "+"sequence / iterable of keyed ReactElements instead.%s",mapsAsChildrenAddendum):void 0;didWarnAboutMaps=true}while(!(step=iterator.next()).done){var entry=step.value;if(entry){child=entry[1];nextName=nextNamePrefix+KeyEscapeUtils.escape(entry[0])+SUBSEPARATOR+getComponentKey(child,0);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}}}else if(type==="object"){var addendum="";if(process.env.NODE_ENV!=="production"){addendum=" If you meant to render a collection of children, use an array "+"instead or wrap the object using createFragment(object) from the "+"React add-ons.";if(children._isReactElement){addendum=" It looks like you're using an element created by a different "+"version of React. Make sure to use only one copy of React."}if(ReactCurrentOwner.current){var name=ReactCurrentOwner.current.getName();if(name){addendum+=" Check the render method of `"+name+"`."}}}var childrenString=String(children);!false?process.env.NODE_ENV!=="production"?invariant(false,"Objects are not valid as a React child (found: %s).%s",childrenString==="[object Object]"?"object with keys {"+Object.keys(children).join(", ")+"}":childrenString,addendum):_prodInvariant("31",childrenString==="[object Object]"?"object with keys {"+Object.keys(children).join(", ")+"}":childrenString,addendum):void 0}}return subtreeCount}function traverseAllChildren(children,callback,traverseContext){if(children==null){return 0}return traverseAllChildrenImpl(children,"",callback,traverseContext)}module.exports=traverseAllChildren}).call(this,require("_process"))},{"./KeyEscapeUtils":53,"./ReactElementSymbol":82,"./getIteratorFn":142,"./reactProdInvariant":151,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25,"react/lib/ReactCurrentOwner":164}],157:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var emptyFunction=require("fbjs/lib/emptyFunction");var warning=require("fbjs/lib/warning");var validateDOMNesting=emptyFunction;if(process.env.NODE_ENV!=="production"){var specialTags=["address","applet","area","article","aside","base","basefont","bgsound","blockquote","body","br","button","caption","center","col","colgroup","dd","details","dir","div","dl","dt","embed","fieldset","figcaption","figure","footer","form","frame","frameset","h1","h2","h3","h4","h5","h6","head","header","hgroup","hr","html","iframe","img","input","isindex","li","link","listing","main","marquee","menu","menuitem","meta","nav","noembed","noframes","noscript","object","ol","p","param","plaintext","pre","script","section","select","source","style","summary","table","tbody","td","template","textarea","tfoot","th","thead","title","tr","track","ul","wbr","xmp"];var inScopeTags=["applet","caption","html","table","td","th","marquee","object","template","foreignObject","desc","title"];var buttonScopeTags=inScopeTags.concat(["button"]);var impliedEndTags=["dd","dt","li","option","optgroup","p","rp","rt"];var emptyAncestorInfo={current:null,formTag:null,aTagInScope:null,buttonTagInScope:null,nobrTagInScope:null,pTagInButtonScope:null,listItemTagAutoclosing:null,dlItemTagAutoclosing:null};var updatedAncestorInfo=function(oldInfo,tag,instance){var ancestorInfo=_assign({},oldInfo||emptyAncestorInfo);var info={tag:tag,instance:instance};if(inScopeTags.indexOf(tag)!==-1){ancestorInfo.aTagInScope=null;ancestorInfo.buttonTagInScope=null;ancestorInfo.nobrTagInScope=null}if(buttonScopeTags.indexOf(tag)!==-1){ancestorInfo.pTagInButtonScope=null}if(specialTags.indexOf(tag)!==-1&&tag!=="address"&&tag!=="div"&&tag!=="p"){ancestorInfo.listItemTagAutoclosing=null;ancestorInfo.dlItemTagAutoclosing=null}ancestorInfo.current=info;if(tag==="form"){ancestorInfo.formTag=info}if(tag==="a"){ancestorInfo.aTagInScope=info}if(tag==="button"){ancestorInfo.buttonTagInScope=info}if(tag==="nobr"){ancestorInfo.nobrTagInScope=info}if(tag==="p"){ancestorInfo.pTagInButtonScope=info}if(tag==="li"){ancestorInfo.listItemTagAutoclosing=info}if(tag==="dd"||tag==="dt"){ancestorInfo.dlItemTagAutoclosing=info}return ancestorInfo};var isTagValidWithParent=function(tag,parentTag){switch(parentTag){case"select":return tag==="option"||tag==="optgroup"||tag==="#text";case"optgroup":return tag==="option"||tag==="#text";case"option":return tag==="#text";case"tr":return tag==="th"||tag==="td"||tag==="style"||tag==="script"||tag==="template";case"tbody":case"thead":case"tfoot":return tag==="tr"||tag==="style"||tag==="script"||tag==="template";case"colgroup":return tag==="col"||tag==="template";case"table":return tag==="caption"||tag==="colgroup"||tag==="tbody"||tag==="tfoot"||tag==="thead"||tag==="style"||tag==="script"||tag==="template";case"head":return tag==="base"||tag==="basefont"||tag==="bgsound"||tag==="link"||tag==="meta"||tag==="title"||tag==="noscript"||tag==="noframes"||tag==="style"||tag==="script"||tag==="template";case"html":return tag==="head"||tag==="body";case"#document":return tag==="html"}switch(tag){case"h1":case"h2":case"h3":case"h4":case"h5":case"h6":return parentTag!=="h1"&&parentTag!=="h2"&&parentTag!=="h3"&&parentTag!=="h4"&&parentTag!=="h5"&&parentTag!=="h6";case"rp":case"rt":return impliedEndTags.indexOf(parentTag)===-1;case"body":case"caption":case"col":case"colgroup":case"frame":case"head":case"html":case"tbody":case"td":case"tfoot":case"th":case"thead":case"tr":return parentTag==null}return true};var findInvalidAncestorForTag=function(tag,ancestorInfo){switch(tag){case"address":case"article":case"aside":case"blockquote":case"center":case"details":case"dialog":case"dir":case"div":case"dl":case"fieldset":case"figcaption":case"figure":case"footer":case"header":case"hgroup":case"main":case"menu":case"nav":case"ol":case"p":case"section":case"summary":case"ul":case"pre":case"listing":case"table":case"hr":case"xmp":case"h1":case"h2":case"h3":case"h4":case"h5":case"h6":return ancestorInfo.pTagInButtonScope;case"form":return ancestorInfo.formTag||ancestorInfo.pTagInButtonScope;case"li":return ancestorInfo.listItemTagAutoclosing;case"dd":case"dt":return ancestorInfo.dlItemTagAutoclosing;case"button":return ancestorInfo.buttonTagInScope;case"a":return ancestorInfo.aTagInScope;case"nobr":return ancestorInfo.nobrTagInScope}return null};var findOwnerStack=function(instance){if(!instance){return[]}var stack=[];do{stack.push(instance)}while(instance=instance._currentElement._owner);stack.reverse();return stack};var didWarn={};validateDOMNesting=function(childTag,childText,childInstance,ancestorInfo){ancestorInfo=ancestorInfo||emptyAncestorInfo;var parentInfo=ancestorInfo.current;var parentTag=parentInfo&&parentInfo.tag;if(childText!=null){process.env.NODE_ENV!=="production"?warning(childTag==null,"validateDOMNesting: when childText is passed, childTag should be null"):void 0;childTag="#text"}var invalidParent=isTagValidWithParent(childTag,parentTag)?null:parentInfo;var invalidAncestor=invalidParent?null:findInvalidAncestorForTag(childTag,ancestorInfo);var problematic=invalidParent||invalidAncestor;if(problematic){var ancestorTag=problematic.tag;var ancestorInstance=problematic.instance;var childOwner=childInstance&&childInstance._currentElement._owner;var ancestorOwner=ancestorInstance&&ancestorInstance._currentElement._owner;var childOwners=findOwnerStack(childOwner);var ancestorOwners=findOwnerStack(ancestorOwner);var minStackLen=Math.min(childOwners.length,ancestorOwners.length);var i;var deepestCommon=-1;for(i=0;i<minStackLen;i++){if(childOwners[i]===ancestorOwners[i]){deepestCommon=i}else{break}}var UNKNOWN="(unknown)";var childOwnerNames=childOwners.slice(deepestCommon+1).map(function(inst){return inst.getName()||UNKNOWN});var ancestorOwnerNames=ancestorOwners.slice(deepestCommon+1).map(function(inst){return inst.getName()||UNKNOWN});var ownerInfo=[].concat(deepestCommon!==-1?childOwners[deepestCommon].getName()||UNKNOWN:[],ancestorOwnerNames,ancestorTag,invalidAncestor?["..."]:[],childOwnerNames,childTag).join(" > ");var warnKey=!!invalidParent+"|"+childTag+"|"+ancestorTag+"|"+ownerInfo;if(didWarn[warnKey]){return}didWarn[warnKey]=true;var tagDisplayName=childTag;var whitespaceInfo="";if(childTag==="#text"){if(/\S/.test(childText)){tagDisplayName="Text nodes"}else{tagDisplayName="Whitespace text nodes";whitespaceInfo=" Make sure you don't have any extra whitespace between tags on "+"each line of your source code."}}else{tagDisplayName="<"+childTag+">"}if(invalidParent){var info="";if(ancestorTag==="table"&&childTag==="tr"){info+=" Add a <tbody> to your code to match the DOM tree generated by "+"the browser."}process.env.NODE_ENV!=="production"?warning(false,"validateDOMNesting(...): %s cannot appear as a child of <%s>.%s "+"See %s.%s",tagDisplayName,ancestorTag,whitespaceInfo,ownerInfo,info):void 0}else{process.env.NODE_ENV!=="production"?warning(false,"validateDOMNesting(...): %s cannot appear as a descendant of "+"<%s>. See %s.",tagDisplayName,ancestorTag,ownerInfo):void 0}}};validateDOMNesting.updatedAncestorInfo=updatedAncestorInfo;validateDOMNesting.isTagValidInContext=function(tag,ancestorInfo){ancestorInfo=ancestorInfo||emptyAncestorInfo;var parentInfo=ancestorInfo.current;var parentTag=parentInfo&&parentInfo.tag;return isTagValidWithParent(tag,parentTag)&&!findInvalidAncestorForTag(tag,ancestorInfo)}}module.exports=validateDOMNesting}).call(this,require("_process"))},{_process:184,"fbjs/lib/emptyFunction":10,"fbjs/lib/warning":25,"object-assign":26}],158:[function(require,module,exports){arguments[4][53][0].apply(exports,arguments)},{dup:53}],159:[function(require,module,exports){arguments[4][55][0].apply(exports,arguments)},{"./reactProdInvariant":181,_process:184,dup:55,"fbjs/lib/invariant":18}],160:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var ReactBaseClasses=require("./ReactBaseClasses");var ReactChildren=require("./ReactChildren");var ReactDOMFactories=require("./ReactDOMFactories");var ReactElement=require("./ReactElement");var ReactPropTypes=require("./ReactPropTypes");var ReactVersion=require("./ReactVersion");var createReactClass=require("./createClass");var onlyChild=require("./onlyChild");var createElement=ReactElement.createElement;var createFactory=ReactElement.createFactory;var cloneElement=ReactElement.cloneElement;if(process.env.NODE_ENV!=="production"){var lowPriorityWarning=require("./lowPriorityWarning");var canDefineProperty=require("./canDefineProperty");var ReactElementValidator=require("./ReactElementValidator");var didWarnPropTypesDeprecated=false;createElement=ReactElementValidator.createElement;createFactory=ReactElementValidator.createFactory;cloneElement=ReactElementValidator.cloneElement}var __spread=_assign;var createMixin=function(mixin){return mixin};if(process.env.NODE_ENV!=="production"){var warnedForSpread=false;var warnedForCreateMixin=false;__spread=function(){lowPriorityWarning(warnedForSpread,"React.__spread is deprecated and should not be used. Use "+"Object.assign directly or another helper function with similar "+"semantics. You may be seeing this warning due to your compiler. "+"See https://fb.me/react-spread-deprecation for more details.");warnedForSpread=true;return _assign.apply(null,arguments)};createMixin=function(mixin){lowPriorityWarning(warnedForCreateMixin,"React.createMixin is deprecated and should not be used. "+"In React v16.0, it will be removed. "+"You can use this mixin directly instead. "+"See https://fb.me/createmixin-was-never-implemented for more info.");warnedForCreateMixin=true;return mixin}}var React={Children:{map:ReactChildren.map,forEach:ReactChildren.forEach,count:ReactChildren.count,toArray:ReactChildren.toArray,only:onlyChild},Component:ReactBaseClasses.Component,PureComponent:ReactBaseClasses.PureComponent,createElement:createElement,cloneElement:cloneElement,isValidElement:ReactElement.isValidElement,PropTypes:ReactPropTypes,createClass:createReactClass,createFactory:createFactory,createMixin:createMixin,DOM:ReactDOMFactories,version:ReactVersion,__spread:__spread};if(process.env.NODE_ENV!=="production"){var warnedForCreateClass=false;if(canDefineProperty){Object.defineProperty(React,"PropTypes",{get:function(){lowPriorityWarning(didWarnPropTypesDeprecated,"Accessing PropTypes via the main React package is deprecated,"+" and will be removed in  React v16.0."+" Use the latest available v15.* prop-types package from npm instead."+" For info on usage, compatibility, migration and more, see "+"https://fb.me/prop-types-docs");didWarnPropTypesDeprecated=true;return ReactPropTypes}});Object.defineProperty(React,"createClass",{get:function(){lowPriorityWarning(warnedForCreateClass,"Accessing createClass via the main React package is deprecated,"+" and will be removed in React v16.0."+" Use a plain JavaScript class instead. If you're not yet "+"ready to migrate, create-react-class v15.* is available "+"on npm as a temporary, drop-in replacement. "+"For more info see https://fb.me/react-create-class");warnedForCreateClass=true;return createReactClass}})}React.DOM={};var warnedForFactories=false;Object.keys(ReactDOMFactories).forEach(function(factory){React.DOM[factory]=function(){if(!warnedForFactories){lowPriorityWarning(false,"Accessing factories like React.DOM.%s has been deprecated "+"and will be removed in v16.0+. Use the "+"react-dom-factories package instead. "+" Version 1.0 provides a drop-in replacement."+" For more info, see https://fb.me/react-dom-factories",factory);warnedForFactories=true}return ReactDOMFactories[factory].apply(ReactDOMFactories,arguments)}})}module.exports=React}).call(this,require("_process"))},{"./ReactBaseClasses":161,"./ReactChildren":162,"./ReactDOMFactories":165,"./ReactElement":166,"./ReactElementValidator":168,"./ReactPropTypes":171,"./ReactVersion":173,"./canDefineProperty":174,"./createClass":176,"./lowPriorityWarning":179,"./onlyChild":180,_process:184,"object-assign":26}],161:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant"),_assign=require("object-assign");var ReactNoopUpdateQueue=require("./ReactNoopUpdateQueue");var canDefineProperty=require("./canDefineProperty");var emptyObject=require("fbjs/lib/emptyObject");var invariant=require("fbjs/lib/invariant");var lowPriorityWarning=require("./lowPriorityWarning");function ReactComponent(props,context,updater){this.props=props;this.context=context;this.refs=emptyObject;this.updater=updater||ReactNoopUpdateQueue}ReactComponent.prototype.isReactComponent={};ReactComponent.prototype.setState=function(partialState,callback){!(typeof partialState==="object"||typeof partialState==="function"||partialState==null)?process.env.NODE_ENV!=="production"?invariant(false,"setState(...): takes an object of state variables to update or a function which returns an object of state variables."):_prodInvariant("85"):void 0;this.updater.enqueueSetState(this,partialState);if(callback){this.updater.enqueueCallback(this,callback,"setState")}};ReactComponent.prototype.forceUpdate=function(callback){this.updater.enqueueForceUpdate(this);if(callback){this.updater.enqueueCallback(this,callback,"forceUpdate")}};if(process.env.NODE_ENV!=="production"){var deprecatedAPIs={isMounted:["isMounted","Instead, make sure to clean up subscriptions and pending requests in "+"componentWillUnmount to prevent memory leaks."],replaceState:["replaceState","Refactor your code to use setState instead (see "+"https://github.com/facebook/react/issues/3236)."]};var defineDeprecationWarning=function(methodName,info){if(canDefineProperty){Object.defineProperty(ReactComponent.prototype,methodName,{get:function(){lowPriorityWarning(false,"%s(...) is deprecated in plain JavaScript React classes. %s",info[0],info[1]);return undefined}})}};for(var fnName in deprecatedAPIs){if(deprecatedAPIs.hasOwnProperty(fnName)){defineDeprecationWarning(fnName,deprecatedAPIs[fnName])}}}function ReactPureComponent(props,context,updater){this.props=props;this.context=context;this.refs=emptyObject;this.updater=updater||ReactNoopUpdateQueue}function ComponentDummy(){}ComponentDummy.prototype=ReactComponent.prototype;ReactPureComponent.prototype=new ComponentDummy;ReactPureComponent.prototype.constructor=ReactPureComponent;_assign(ReactPureComponent.prototype,ReactComponent.prototype);ReactPureComponent.prototype.isPureReactComponent=true;module.exports={Component:ReactComponent,PureComponent:ReactPureComponent}}).call(this,require("_process"))},{"./ReactNoopUpdateQueue":169,"./canDefineProperty":174,"./lowPriorityWarning":179,"./reactProdInvariant":181,_process:184,"fbjs/lib/emptyObject":11,"fbjs/lib/invariant":18,"object-assign":26}],162:[function(require,module,exports){"use strict";var PooledClass=require("./PooledClass");var ReactElement=require("./ReactElement");var emptyFunction=require("fbjs/lib/emptyFunction");var traverseAllChildren=require("./traverseAllChildren");var twoArgumentPooler=PooledClass.twoArgumentPooler;var fourArgumentPooler=PooledClass.fourArgumentPooler;var userProvidedKeyEscapeRegex=/\/+/g;function escapeUserProvidedKey(text){return(""+text).replace(userProvidedKeyEscapeRegex,"$&/")}function ForEachBookKeeping(forEachFunction,forEachContext){this.func=forEachFunction;this.context=forEachContext;this.count=0}ForEachBookKeeping.prototype.destructor=function(){this.func=null;this.context=null;this.count=0};PooledClass.addPoolingTo(ForEachBookKeeping,twoArgumentPooler);function forEachSingleChild(bookKeeping,child,name){var func=bookKeeping.func,context=bookKeeping.context;func.call(context,child,bookKeeping.count++)}function forEachChildren(children,forEachFunc,forEachContext){if(children==null){return children}var traverseContext=ForEachBookKeeping.getPooled(forEachFunc,forEachContext);traverseAllChildren(children,forEachSingleChild,traverseContext);ForEachBookKeeping.release(traverseContext)}function MapBookKeeping(mapResult,keyPrefix,mapFunction,mapContext){this.result=mapResult;this.keyPrefix=keyPrefix;this.func=mapFunction;this.context=mapContext;this.count=0}MapBookKeeping.prototype.destructor=function(){this.result=null;this.keyPrefix=null;this.func=null;this.context=null;this.count=0};PooledClass.addPoolingTo(MapBookKeeping,fourArgumentPooler);function mapSingleChildIntoContext(bookKeeping,child,childKey){var result=bookKeeping.result,keyPrefix=bookKeeping.keyPrefix,func=bookKeeping.func,context=bookKeeping.context;var mappedChild=func.call(context,child,bookKeeping.count++);if(Array.isArray(mappedChild)){mapIntoWithKeyPrefixInternal(mappedChild,result,childKey,emptyFunction.thatReturnsArgument)}else if(mappedChild!=null){if(ReactElement.isValidElement(mappedChild)){mappedChild=ReactElement.cloneAndReplaceKey(mappedChild,keyPrefix+(mappedChild.key&&(!child||child.key!==mappedChild.key)?escapeUserProvidedKey(mappedChild.key)+"/":"")+childKey)}result.push(mappedChild)}}function mapIntoWithKeyPrefixInternal(children,array,prefix,func,context){var escapedPrefix="";if(prefix!=null){escapedPrefix=escapeUserProvidedKey(prefix)+"/"}var traverseContext=MapBookKeeping.getPooled(array,escapedPrefix,func,context);traverseAllChildren(children,mapSingleChildIntoContext,traverseContext);MapBookKeeping.release(traverseContext)}function mapChildren(children,func,context){if(children==null){return children}var result=[];mapIntoWithKeyPrefixInternal(children,result,null,func,context);return result}function forEachSingleChildDummy(traverseContext,child,name){return null}function countChildren(children,context){return traverseAllChildren(children,forEachSingleChildDummy,null)}function toArray(children){var result=[];mapIntoWithKeyPrefixInternal(children,result,null,emptyFunction.thatReturnsArgument);return result}var ReactChildren={forEach:forEachChildren,map:mapChildren,mapIntoWithKeyPrefixInternal:mapIntoWithKeyPrefixInternal,count:countChildren,toArray:toArray};module.exports=ReactChildren},{"./PooledClass":159,"./ReactElement":166,"./traverseAllChildren":182,"fbjs/lib/emptyFunction":10}],163:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactCurrentOwner=require("./ReactCurrentOwner");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");function isNative(fn){var funcToString=Function.prototype.toString;var hasOwnProperty=Object.prototype.hasOwnProperty;var reIsNative=RegExp("^"+funcToString.call(hasOwnProperty).replace(/[\\^$.*+?()[\]{}|]/g,"\\$&").replace(/hasOwnProperty|(function).*?(?=\\\()| for .+?(?=\\\])/g,"$1.*?")+"$");try{var source=funcToString.call(fn);return reIsNative.test(source)}catch(err){return false}}var canUseCollections=typeof Array.from==="function"&&typeof Map==="function"&&isNative(Map)&&Map.prototype!=null&&typeof Map.prototype.keys==="function"&&isNative(Map.prototype.keys)&&typeof Set==="function"&&isNative(Set)&&Set.prototype!=null&&typeof Set.prototype.keys==="function"&&isNative(Set.prototype.keys);var setItem;var getItem;var removeItem;var getItemIDs;var addRoot;var removeRoot;var getRootIDs;if(canUseCollections){var itemMap=new Map;var rootIDSet=new Set;setItem=function(id,item){itemMap.set(id,item)};getItem=function(id){return itemMap.get(id)};removeItem=function(id){itemMap["delete"](id)};getItemIDs=function(){return Array.from(itemMap.keys())};addRoot=function(id){rootIDSet.add(id)};removeRoot=function(id){rootIDSet["delete"](id)};getRootIDs=function(){return Array.from(rootIDSet.keys())}}else{var itemByKey={};var rootByKey={};var getKeyFromID=function(id){return"."+id};var getIDFromKey=function(key){return parseInt(key.substr(1),10)};setItem=function(id,item){var key=getKeyFromID(id);itemByKey[key]=item};getItem=function(id){var key=getKeyFromID(id);return itemByKey[key]};removeItem=function(id){var key=getKeyFromID(id);delete itemByKey[key]};getItemIDs=function(){return Object.keys(itemByKey).map(getIDFromKey)};addRoot=function(id){var key=getKeyFromID(id);rootByKey[key]=true};removeRoot=function(id){var key=getKeyFromID(id);delete rootByKey[key]};getRootIDs=function(){return Object.keys(rootByKey).map(getIDFromKey)}}var unmountedIDs=[];function purgeDeep(id){var item=getItem(id);if(item){var childIDs=item.childIDs;removeItem(id);childIDs.forEach(purgeDeep)}}function describeComponentFrame(name,source,ownerName){return"\n    in "+(name||"Unknown")+(source?" (at "+source.fileName.replace(/^.*[\\\/]/,"")+":"+source.lineNumber+")":ownerName?" (created by "+ownerName+")":"")}function getDisplayName(element){if(element==null){return"#empty"}else if(typeof element==="string"||typeof element==="number"){return"#text"}else if(typeof element.type==="string"){return element.type}else{return element.type.displayName||element.type.name||"Unknown"}}function describeID(id){var name=ReactComponentTreeHook.getDisplayName(id);var element=ReactComponentTreeHook.getElement(id);var ownerID=ReactComponentTreeHook.getOwnerID(id);var ownerName;if(ownerID){ownerName=ReactComponentTreeHook.getDisplayName(ownerID)}process.env.NODE_ENV!=="production"?warning(element,"ReactComponentTreeHook: Missing React element for debugID %s when "+"building stack",id):void 0;return describeComponentFrame(name,element&&element._source,ownerName)}var ReactComponentTreeHook={onSetChildren:function(id,nextChildIDs){var item=getItem(id);!item?process.env.NODE_ENV!=="production"?invariant(false,"Item must have been set"):_prodInvariant("144"):void 0;item.childIDs=nextChildIDs;for(var i=0;i<nextChildIDs.length;i++){var nextChildID=nextChildIDs[i];var nextChild=getItem(nextChildID);!nextChild?process.env.NODE_ENV!=="production"?invariant(false,"Expected hook events to fire for the child before its parent includes it in onSetChildren()."):_prodInvariant("140"):void 0;!(nextChild.childIDs!=null||typeof nextChild.element!=="object"||nextChild.element==null)?process.env.NODE_ENV!=="production"?invariant(false,"Expected onSetChildren() to fire for a container child before its parent includes it in onSetChildren()."):_prodInvariant("141"):void 0;!nextChild.isMounted?process.env.NODE_ENV!=="production"?invariant(false,"Expected onMountComponent() to fire for the child before its parent includes it in onSetChildren()."):_prodInvariant("71"):void 0;if(nextChild.parentID==null){nextChild.parentID=id}!(nextChild.parentID===id)?process.env.NODE_ENV!=="production"?invariant(false,"Expected onBeforeMountComponent() parent and onSetChildren() to be consistent (%s has parents %s and %s).",nextChildID,nextChild.parentID,id):_prodInvariant("142",nextChildID,nextChild.parentID,id):void 0}},onBeforeMountComponent:function(id,element,parentID){var item={element:element,parentID:parentID,text:null,childIDs:[],isMounted:false,updateCount:0};setItem(id,item)},onBeforeUpdateComponent:function(id,element){var item=getItem(id);if(!item||!item.isMounted){return}item.element=element},onMountComponent:function(id){var item=getItem(id);!item?process.env.NODE_ENV!=="production"?invariant(false,"Item must have been set"):_prodInvariant("144"):void 0;item.isMounted=true;var isRoot=item.parentID===0;if(isRoot){addRoot(id)}},onUpdateComponent:function(id){var item=getItem(id);if(!item||!item.isMounted){return}item.updateCount++},onUnmountComponent:function(id){var item=getItem(id);if(item){item.isMounted=false;var isRoot=item.parentID===0;if(isRoot){removeRoot(id)}}unmountedIDs.push(id)},purgeUnmountedComponents:function(){if(ReactComponentTreeHook._preventPurging){return}for(var i=0;i<unmountedIDs.length;i++){var id=unmountedIDs[i];purgeDeep(id)}unmountedIDs.length=0},isMounted:function(id){var item=getItem(id);return item?item.isMounted:false},getCurrentStackAddendum:function(topElement){var info="";if(topElement){var name=getDisplayName(topElement);var owner=topElement._owner;info+=describeComponentFrame(name,topElement._source,owner&&owner.getName())}var currentOwner=ReactCurrentOwner.current;var id=currentOwner&&currentOwner._debugID;info+=ReactComponentTreeHook.getStackAddendumByID(id);return info},getStackAddendumByID:function(id){var info="";while(id){info+=describeID(id);id=ReactComponentTreeHook.getParentID(id)}return info},getChildIDs:function(id){var item=getItem(id);return item?item.childIDs:[]},getDisplayName:function(id){var element=ReactComponentTreeHook.getElement(id);if(!element){return null}return getDisplayName(element)},getElement:function(id){var item=getItem(id);return item?item.element:null},getOwnerID:function(id){var element=ReactComponentTreeHook.getElement(id);if(!element||!element._owner){return null}return element._owner._debugID},getParentID:function(id){var item=getItem(id);return item?item.parentID:null},getSource:function(id){var item=getItem(id);var element=item?item.element:null;var source=element!=null?element._source:null;return source},getText:function(id){var element=ReactComponentTreeHook.getElement(id);if(typeof element==="string"){return element}else if(typeof element==="number"){return""+element}else{return null}},getUpdateCount:function(id){var item=getItem(id);return item?item.updateCount:0},getRootIDs:getRootIDs,getRegisteredIDs:getItemIDs,pushNonStandardWarningStack:function(isCreatingElement,currentSource){if(typeof console.reactStack!=="function"){return}var stack=[];var currentOwner=ReactCurrentOwner.current;var id=currentOwner&&currentOwner._debugID;try{if(isCreatingElement){stack.push({name:id?ReactComponentTreeHook.getDisplayName(id):null,fileName:currentSource?currentSource.fileName:null,lineNumber:currentSource?currentSource.lineNumber:null})}while(id){var element=ReactComponentTreeHook.getElement(id);var parentID=ReactComponentTreeHook.getParentID(id);var ownerID=ReactComponentTreeHook.getOwnerID(id);var ownerName=ownerID?ReactComponentTreeHook.getDisplayName(ownerID):null;var source=element&&element._source;stack.push({name:ownerName,fileName:source?source.fileName:null,lineNumber:source?source.lineNumber:null});id=parentID}}catch(err){}console.reactStack(stack)},popNonStandardWarningStack:function(){if(typeof console.reactStackEnd!=="function"){return}console.reactStackEnd()}};module.exports=ReactComponentTreeHook}).call(this,require("_process"))},{"./ReactCurrentOwner":164,"./reactProdInvariant":181,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],164:[function(require,module,exports){"use strict";var ReactCurrentOwner={current:null};module.exports=ReactCurrentOwner},{}],165:[function(require,module,exports){(function(process){"use strict";var ReactElement=require("./ReactElement");var createDOMFactory=ReactElement.createFactory;if(process.env.NODE_ENV!=="production"){var ReactElementValidator=require("./ReactElementValidator");createDOMFactory=ReactElementValidator.createFactory}var ReactDOMFactories={a:createDOMFactory("a"),abbr:createDOMFactory("abbr"),address:createDOMFactory("address"),area:createDOMFactory("area"),article:createDOMFactory("article"),aside:createDOMFactory("aside"),audio:createDOMFactory("audio"),b:createDOMFactory("b"),base:createDOMFactory("base"),bdi:createDOMFactory("bdi"),bdo:createDOMFactory("bdo"),big:createDOMFactory("big"),blockquote:createDOMFactory("blockquote"),body:createDOMFactory("body"),br:createDOMFactory("br"),button:createDOMFactory("button"),canvas:createDOMFactory("canvas"),caption:createDOMFactory("caption"),cite:createDOMFactory("cite"),code:createDOMFactory("code"),col:createDOMFactory("col"),colgroup:createDOMFactory("colgroup"),data:createDOMFactory("data"),datalist:createDOMFactory("datalist"),dd:createDOMFactory("dd"),del:createDOMFactory("del"),details:createDOMFactory("details"),dfn:createDOMFactory("dfn"),dialog:createDOMFactory("dialog"),div:createDOMFactory("div"),dl:createDOMFactory("dl"),dt:createDOMFactory("dt"),em:createDOMFactory("em"),embed:createDOMFactory("embed"),fieldset:createDOMFactory("fieldset"),figcaption:createDOMFactory("figcaption"),figure:createDOMFactory("figure"),footer:createDOMFactory("footer"),form:createDOMFactory("form"),h1:createDOMFactory("h1"),h2:createDOMFactory("h2"),h3:createDOMFactory("h3"),h4:createDOMFactory("h4"),h5:createDOMFactory("h5"),h6:createDOMFactory("h6"),head:createDOMFactory("head"),header:createDOMFactory("header"),hgroup:createDOMFactory("hgroup"),hr:createDOMFactory("hr"),html:createDOMFactory("html"),i:createDOMFactory("i"),iframe:createDOMFactory("iframe"),img:createDOMFactory("img"),input:createDOMFactory("input"),ins:createDOMFactory("ins"),kbd:createDOMFactory("kbd"),keygen:createDOMFactory("keygen"),label:createDOMFactory("label"),legend:createDOMFactory("legend"),li:createDOMFactory("li"),link:createDOMFactory("link"),main:createDOMFactory("main"),map:createDOMFactory("map"),mark:createDOMFactory("mark"),menu:createDOMFactory("menu"),menuitem:createDOMFactory("menuitem"),meta:createDOMFactory("meta"),meter:createDOMFactory("meter"),nav:createDOMFactory("nav"),noscript:createDOMFactory("noscript"),object:createDOMFactory("object"),ol:createDOMFactory("ol"),optgroup:createDOMFactory("optgroup"),option:createDOMFactory("option"),output:createDOMFactory("output"),p:createDOMFactory("p"),param:createDOMFactory("param"),picture:createDOMFactory("picture"),pre:createDOMFactory("pre"),progress:createDOMFactory("progress"),q:createDOMFactory("q"),rp:createDOMFactory("rp"),rt:createDOMFactory("rt"),ruby:createDOMFactory("ruby"),s:createDOMFactory("s"),samp:createDOMFactory("samp"),script:createDOMFactory("script"),section:createDOMFactory("section"),select:createDOMFactory("select"),small:createDOMFactory("small"),source:createDOMFactory("source"),span:createDOMFactory("span"),strong:createDOMFactory("strong"),style:createDOMFactory("style"),sub:createDOMFactory("sub"),summary:createDOMFactory("summary"),sup:createDOMFactory("sup"),table:createDOMFactory("table"),tbody:createDOMFactory("tbody"),td:createDOMFactory("td"),textarea:createDOMFactory("textarea"),tfoot:createDOMFactory("tfoot"),th:createDOMFactory("th"),thead:createDOMFactory("thead"),time:createDOMFactory("time"),title:createDOMFactory("title"),tr:createDOMFactory("tr"),track:createDOMFactory("track"),u:createDOMFactory("u"),ul:createDOMFactory("ul"),var:createDOMFactory("var"),video:createDOMFactory("video"),wbr:createDOMFactory("wbr"),circle:createDOMFactory("circle"),clipPath:createDOMFactory("clipPath"),defs:createDOMFactory("defs"),ellipse:createDOMFactory("ellipse"),g:createDOMFactory("g"),image:createDOMFactory("image"),line:createDOMFactory("line"),linearGradient:createDOMFactory("linearGradient"),mask:createDOMFactory("mask"),path:createDOMFactory("path"),pattern:createDOMFactory("pattern"),polygon:createDOMFactory("polygon"),polyline:createDOMFactory("polyline"),radialGradient:createDOMFactory("radialGradient"),rect:createDOMFactory("rect"),stop:createDOMFactory("stop"),svg:createDOMFactory("svg"),text:createDOMFactory("text"),tspan:createDOMFactory("tspan")};module.exports=ReactDOMFactories}).call(this,require("_process"))},{"./ReactElement":166,"./ReactElementValidator":168,_process:184}],166:[function(require,module,exports){(function(process){"use strict";var _assign=require("object-assign");var ReactCurrentOwner=require("./ReactCurrentOwner");var warning=require("fbjs/lib/warning");var canDefineProperty=require("./canDefineProperty");var hasOwnProperty=Object.prototype.hasOwnProperty;var REACT_ELEMENT_TYPE=require("./ReactElementSymbol");var RESERVED_PROPS={key:true,ref:true,__self:true,__source:true};var specialPropKeyWarningShown,specialPropRefWarningShown;function hasValidRef(config){if(process.env.NODE_ENV!=="production"){if(hasOwnProperty.call(config,"ref")){var getter=Object.getOwnPropertyDescriptor(config,"ref").get;if(getter&&getter.isReactWarning){return false}}}return config.ref!==undefined}function hasValidKey(config){if(process.env.NODE_ENV!=="production"){if(hasOwnProperty.call(config,"key")){var getter=Object.getOwnPropertyDescriptor(config,"key").get;if(getter&&getter.isReactWarning){return false}}}return config.key!==undefined}function defineKeyPropWarningGetter(props,displayName){var warnAboutAccessingKey=function(){if(!specialPropKeyWarningShown){specialPropKeyWarningShown=true;process.env.NODE_ENV!=="production"?warning(false,"%s: `key` is not a prop. Trying to access it will result "+"in `undefined` being returned. If you need to access the same "+"value within the child component, you should pass it as a different "+"prop. (https://fb.me/react-special-props)",displayName):void 0}};warnAboutAccessingKey.isReactWarning=true;Object.defineProperty(props,"key",{get:warnAboutAccessingKey,configurable:true})}function defineRefPropWarningGetter(props,displayName){var warnAboutAccessingRef=function(){if(!specialPropRefWarningShown){specialPropRefWarningShown=true;process.env.NODE_ENV!=="production"?warning(false,"%s: `ref` is not a prop. Trying to access it will result "+"in `undefined` being returned. If you need to access the same "+"value within the child component, you should pass it as a different "+"prop. (https://fb.me/react-special-props)",displayName):void 0}};warnAboutAccessingRef.isReactWarning=true;Object.defineProperty(props,"ref",{get:warnAboutAccessingRef,configurable:true})}var ReactElement=function(type,key,ref,self,source,owner,props){var element={$$typeof:REACT_ELEMENT_TYPE,type:type,key:key,ref:ref,props:props,_owner:owner};if(process.env.NODE_ENV!=="production"){element._store={};if(canDefineProperty){Object.defineProperty(element._store,"validated",{configurable:false,enumerable:false,writable:true,value:false});Object.defineProperty(element,"_self",{configurable:false,enumerable:false,writable:false,value:self});Object.defineProperty(element,"_source",{configurable:false,enumerable:false,writable:false,value:source})}else{element._store.validated=false;element._self=self;element._source=source}if(Object.freeze){Object.freeze(element.props);Object.freeze(element)}}return element};ReactElement.createElement=function(type,config,children){var propName;var props={};var key=null;var ref=null;var self=null;var source=null;if(config!=null){if(hasValidRef(config)){ref=config.ref}if(hasValidKey(config)){key=""+config.key}self=config.__self===undefined?null:config.__self;source=config.__source===undefined?null:config.__source;for(propName in config){if(hasOwnProperty.call(config,propName)&&!RESERVED_PROPS.hasOwnProperty(propName)){props[propName]=config[propName]}}}var childrenLength=arguments.length-2;if(childrenLength===1){props.children=children}else if(childrenLength>1){var childArray=Array(childrenLength);for(var i=0;i<childrenLength;i++){childArray[i]=arguments[i+2]}if(process.env.NODE_ENV!=="production"){if(Object.freeze){Object.freeze(childArray)}}props.children=childArray}if(type&&type.defaultProps){var defaultProps=type.defaultProps;for(propName in defaultProps){if(props[propName]===undefined){props[propName]=defaultProps[propName]}}}if(process.env.NODE_ENV!=="production"){if(key||ref){if(typeof props.$$typeof==="undefined"||props.$$typeof!==REACT_ELEMENT_TYPE){var displayName=typeof type==="function"?type.displayName||type.name||"Unknown":type;if(key){defineKeyPropWarningGetter(props,displayName)}if(ref){defineRefPropWarningGetter(props,displayName)}}}}return ReactElement(type,key,ref,self,source,ReactCurrentOwner.current,props)};ReactElement.createFactory=function(type){var factory=ReactElement.createElement.bind(null,type);factory.type=type;return factory};ReactElement.cloneAndReplaceKey=function(oldElement,newKey){var newElement=ReactElement(oldElement.type,newKey,oldElement.ref,oldElement._self,oldElement._source,oldElement._owner,oldElement.props);return newElement};ReactElement.cloneElement=function(element,config,children){var propName;var props=_assign({},element.props);var key=element.key;var ref=element.ref;var self=element._self;var source=element._source;var owner=element._owner;if(config!=null){if(hasValidRef(config)){ref=config.ref;owner=ReactCurrentOwner.current}if(hasValidKey(config)){key=""+config.key}var defaultProps;if(element.type&&element.type.defaultProps){defaultProps=element.type.defaultProps}for(propName in config){if(hasOwnProperty.call(config,propName)&&!RESERVED_PROPS.hasOwnProperty(propName)){if(config[propName]===undefined&&defaultProps!==undefined){props[propName]=defaultProps[propName]}else{props[propName]=config[propName]}}}}var childrenLength=arguments.length-2;if(childrenLength===1){props.children=children}else if(childrenLength>1){var childArray=Array(childrenLength);for(var i=0;i<childrenLength;i++){childArray[i]=arguments[i+2]}props.children=childArray}return ReactElement(element.type,key,ref,self,source,owner,props)};ReactElement.isValidElement=function(object){return typeof object==="object"&&object!==null&&object.$$typeof===REACT_ELEMENT_TYPE};module.exports=ReactElement}).call(this,require("_process"))},{"./ReactCurrentOwner":164,"./ReactElementSymbol":167,"./canDefineProperty":174,_process:184,"fbjs/lib/warning":25,"object-assign":26}],167:[function(require,module,exports){arguments[4][82][0].apply(exports,arguments)},{dup:82}],168:[function(require,module,exports){(function(process){"use strict";var ReactCurrentOwner=require("./ReactCurrentOwner");var ReactComponentTreeHook=require("./ReactComponentTreeHook");var ReactElement=require("./ReactElement");var checkReactTypeSpec=require("./checkReactTypeSpec");var canDefineProperty=require("./canDefineProperty");var getIteratorFn=require("./getIteratorFn");var warning=require("fbjs/lib/warning");var lowPriorityWarning=require("./lowPriorityWarning");function getDeclarationErrorAddendum(){if(ReactCurrentOwner.current){var name=ReactCurrentOwner.current.getName();if(name){return" Check the render method of `"+name+"`."}}return""}function getSourceInfoErrorAddendum(elementProps){if(elementProps!==null&&elementProps!==undefined&&elementProps.__source!==undefined){var source=elementProps.__source;var fileName=source.fileName.replace(/^.*[\\\/]/,"");var lineNumber=source.lineNumber;return" Check your code at "+fileName+":"+lineNumber+"."}return""}var ownerHasKeyUseWarning={};function getCurrentComponentErrorInfo(parentType){var info=getDeclarationErrorAddendum();if(!info){var parentName=typeof parentType==="string"?parentType:parentType.displayName||parentType.name;if(parentName){info=" Check the top-level render call using <"+parentName+">."}}return info}function validateExplicitKey(element,parentType){if(!element._store||element._store.validated||element.key!=null){return}element._store.validated=true;var memoizer=ownerHasKeyUseWarning.uniqueKey||(ownerHasKeyUseWarning.uniqueKey={});var currentComponentErrorInfo=getCurrentComponentErrorInfo(parentType);if(memoizer[currentComponentErrorInfo]){return}memoizer[currentComponentErrorInfo]=true;var childOwner="";if(element&&element._owner&&element._owner!==ReactCurrentOwner.current){childOwner=" It was passed a child from "+element._owner.getName()+"."}process.env.NODE_ENV!=="production"?warning(false,'Each child in an array or iterator should have a unique "key" prop.'+"%s%s See https://fb.me/react-warning-keys for more information.%s",currentComponentErrorInfo,childOwner,ReactComponentTreeHook.getCurrentStackAddendum(element)):void 0}function validateChildKeys(node,parentType){if(typeof node!=="object"){return}if(Array.isArray(node)){for(var i=0;i<node.length;i++){var child=node[i];if(ReactElement.isValidElement(child)){validateExplicitKey(child,parentType)}}}else if(ReactElement.isValidElement(node)){if(node._store){node._store.validated=true}}else if(node){var iteratorFn=getIteratorFn(node);if(iteratorFn){if(iteratorFn!==node.entries){var iterator=iteratorFn.call(node);var step;while(!(step=iterator.next()).done){if(ReactElement.isValidElement(step.value)){validateExplicitKey(step.value,parentType)}}}}}}function validatePropTypes(element){var componentClass=element.type;if(typeof componentClass!=="function"){return}var name=componentClass.displayName||componentClass.name;if(componentClass.propTypes){checkReactTypeSpec(componentClass.propTypes,element.props,"prop",name,element,null)}if(typeof componentClass.getDefaultProps==="function"){process.env.NODE_ENV!=="production"?warning(componentClass.getDefaultProps.isReactClassApproved,"getDefaultProps is only used on classic React.createClass "+"definitions. Use a static property named `defaultProps` instead."):void 0}}var ReactElementValidator={createElement:function(type,props,children){var validType=typeof type==="string"||typeof type==="function";if(!validType){if(typeof type!=="function"&&typeof type!=="string"){var info="";if(type===undefined||typeof type==="object"&&type!==null&&Object.keys(type).length===0){info+=" You likely forgot to export your component from the file "+"it's defined in."}var sourceInfo=getSourceInfoErrorAddendum(props);if(sourceInfo){info+=sourceInfo}else{info+=getDeclarationErrorAddendum()}info+=ReactComponentTreeHook.getCurrentStackAddendum();var currentSource=props!==null&&props!==undefined&&props.__source!==undefined?props.__source:null;ReactComponentTreeHook.pushNonStandardWarningStack(true,currentSource);process.env.NODE_ENV!=="production"?warning(false,"React.createElement: type is invalid -- expected a string (for "+"built-in components) or a class/function (for composite "+"components) but got: %s.%s",type==null?type:typeof type,info):void 0;ReactComponentTreeHook.popNonStandardWarningStack()}}var element=ReactElement.createElement.apply(this,arguments);if(element==null){return element}if(validType){for(var i=2;i<arguments.length;i++){validateChildKeys(arguments[i],type)}}validatePropTypes(element);return element},createFactory:function(type){var validatedFactory=ReactElementValidator.createElement.bind(null,type);validatedFactory.type=type;if(process.env.NODE_ENV!=="production"){if(canDefineProperty){Object.defineProperty(validatedFactory,"type",{enumerable:false,get:function(){lowPriorityWarning(false,"Factory.type is deprecated. Access the class directly "+"before passing it to createFactory.");Object.defineProperty(this,"type",{value:type});return type}})}}return validatedFactory},cloneElement:function(element,props,children){var newElement=ReactElement.cloneElement.apply(this,arguments);for(var i=2;i<arguments.length;i++){validateChildKeys(arguments[i],newElement.type)}validatePropTypes(newElement);return newElement}};module.exports=ReactElementValidator}).call(this,require("_process"))},{"./ReactComponentTreeHook":163,"./ReactCurrentOwner":164,"./ReactElement":166,"./canDefineProperty":174,"./checkReactTypeSpec":175,"./getIteratorFn":177,"./lowPriorityWarning":179,_process:184,"fbjs/lib/warning":25}],169:[function(require,module,exports){(function(process){"use strict";var warning=require("fbjs/lib/warning");function warnNoop(publicInstance,callerName){if(process.env.NODE_ENV!=="production"){var constructor=publicInstance.constructor;process.env.NODE_ENV!=="production"?warning(false,"%s(...): Can only update a mounted or mounting component. "+"This usually means you called %s() on an unmounted component. "+"This is a no-op. Please check the code for the %s component.",callerName,callerName,constructor&&(constructor.displayName||constructor.name)||"ReactClass"):void 0}}var ReactNoopUpdateQueue={isMounted:function(publicInstance){return false},enqueueCallback:function(publicInstance,callback){},enqueueForceUpdate:function(publicInstance){warnNoop(publicInstance,"forceUpdate")},enqueueReplaceState:function(publicInstance,completeState){warnNoop(publicInstance,"replaceState")},enqueueSetState:function(publicInstance,partialState){warnNoop(publicInstance,"setState")}};module.exports=ReactNoopUpdateQueue}).call(this,require("_process"))},{_process:184,"fbjs/lib/warning":25}],170:[function(require,module,exports){arguments[4][100][0].apply(exports,arguments)},{_process:184,dup:100}],171:[function(require,module,exports){"use strict";var _require=require("./ReactElement"),isValidElement=_require.isValidElement;var factory=require("prop-types/factory");module.exports=factory(isValidElement)},{"./ReactElement":166,"prop-types/factory":28}],172:[function(require,module,exports){arguments[4][101][0].apply(exports,arguments)},{dup:101}],173:[function(require,module,exports){arguments[4][109][0].apply(exports,arguments)},{dup:109}],174:[function(require,module,exports){(function(process){"use strict";var canDefineProperty=false;if(process.env.NODE_ENV!=="production"){try{Object.defineProperty({},"x",{get:function(){}});canDefineProperty=true}catch(x){}}module.exports=canDefineProperty}).call(this,require("_process"))},{_process:184}],175:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactPropTypeLocationNames=require("./ReactPropTypeLocationNames");var ReactPropTypesSecret=require("./ReactPropTypesSecret");var invariant=require("fbjs/lib/invariant");var warning=require("fbjs/lib/warning");var ReactComponentTreeHook;if(typeof process!=="undefined"&&process.env&&process.env.NODE_ENV==="test"){ReactComponentTreeHook=require("./ReactComponentTreeHook")}var loggedTypeFailures={};function checkReactTypeSpec(typeSpecs,values,location,componentName,element,debugID){for(var typeSpecName in typeSpecs){if(typeSpecs.hasOwnProperty(typeSpecName)){var error;try{!(typeof typeSpecs[typeSpecName]==="function")?process.env.NODE_ENV!=="production"?invariant(false,"%s: %s type `%s` is invalid; it must be a function, usually from React.PropTypes.",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName):_prodInvariant("84",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName):void 0;error=typeSpecs[typeSpecName](values,typeSpecName,componentName,location,null,ReactPropTypesSecret)}catch(ex){error=ex}process.env.NODE_ENV!=="production"?warning(!error||error instanceof Error,"%s: type specification of %s `%s` is invalid; the type checker "+"function must return `null` or an `Error` but returned a %s. "+"You may have forgotten to pass an argument to the type checker "+"creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and "+"shape all require an argument).",componentName||"React class",ReactPropTypeLocationNames[location],typeSpecName,typeof error):void 0;if(error instanceof Error&&!(error.message in loggedTypeFailures)){loggedTypeFailures[error.message]=true;var componentStackInfo="";if(process.env.NODE_ENV!=="production"){if(!ReactComponentTreeHook){ReactComponentTreeHook=require("./ReactComponentTreeHook")}if(debugID!==null){componentStackInfo=ReactComponentTreeHook.getStackAddendumByID(debugID)}else if(element!==null){componentStackInfo=ReactComponentTreeHook.getCurrentStackAddendum(element)}}process.env.NODE_ENV!=="production"?warning(false,"Failed %s type: %s%s",location,error.message,componentStackInfo):void 0}}}}module.exports=checkReactTypeSpec}).call(this,require("_process"))},{"./ReactComponentTreeHook":163,"./ReactPropTypeLocationNames":170,"./ReactPropTypesSecret":172,"./reactProdInvariant":181,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],176:[function(require,module,exports){"use strict";var _require=require("./ReactBaseClasses"),Component=_require.Component;var _require2=require("./ReactElement"),isValidElement=_require2.isValidElement;var ReactNoopUpdateQueue=require("./ReactNoopUpdateQueue");var factory=require("create-react-class/factory");module.exports=factory(Component,isValidElement,ReactNoopUpdateQueue)},{"./ReactBaseClasses":161,"./ReactElement":166,"./ReactNoopUpdateQueue":169,"create-react-class/factory":2}],177:[function(require,module,exports){arguments[4][142][0].apply(exports,arguments)},{dup:142}],178:[function(require,module,exports){"use strict";var nextDebugID=1;function getNextDebugID(){return nextDebugID++}module.exports=getNextDebugID},{}],179:[function(require,module,exports){(function(process){"use strict";var lowPriorityWarning=function(){};if(process.env.NODE_ENV!=="production"){var printWarning=function(format){for(var _len=arguments.length,args=Array(_len>1?_len-1:0),_key=1;_key<_len;_key++){args[_key-1]=arguments[_key]}var argIndex=0;var message="Warning: "+format.replace(/%s/g,function(){return args[argIndex++]});if(typeof console!=="undefined"){console.warn(message)}try{throw new Error(message)}catch(x){}};lowPriorityWarning=function(condition,format){if(format===undefined){throw new Error("`warning(condition, format, ...args)` requires a warning "+"message argument")}if(!condition){for(var _len2=arguments.length,args=Array(_len2>2?_len2-2:0),_key2=2;_key2<_len2;_key2++){args[_key2-2]=arguments[_key2]}printWarning.apply(undefined,[format].concat(args))}}}module.exports=lowPriorityWarning}).call(this,require("_process"))},{_process:184}],180:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactElement=require("./ReactElement");var invariant=require("fbjs/lib/invariant");function onlyChild(children){!ReactElement.isValidElement(children)?process.env.NODE_ENV!=="production"?invariant(false,"React.Children.only expected to receive a single React element child."):_prodInvariant("143"):void 0;return children}module.exports=onlyChild}).call(this,require("_process"))},{"./ReactElement":166,"./reactProdInvariant":181,_process:184,"fbjs/lib/invariant":18}],181:[function(require,module,exports){arguments[4][151][0].apply(exports,arguments)},{dup:151}],182:[function(require,module,exports){(function(process){"use strict";var _prodInvariant=require("./reactProdInvariant");var ReactCurrentOwner=require("./ReactCurrentOwner");var REACT_ELEMENT_TYPE=require("./ReactElementSymbol");var getIteratorFn=require("./getIteratorFn");var invariant=require("fbjs/lib/invariant");var KeyEscapeUtils=require("./KeyEscapeUtils");var warning=require("fbjs/lib/warning");var SEPARATOR=".";var SUBSEPARATOR=":";var didWarnAboutMaps=false;function getComponentKey(component,index){if(component&&typeof component==="object"&&component.key!=null){return KeyEscapeUtils.escape(component.key)}return index.toString(36)}function traverseAllChildrenImpl(children,nameSoFar,callback,traverseContext){var type=typeof children;if(type==="undefined"||type==="boolean"){children=null}if(children===null||type==="string"||type==="number"||type==="object"&&children.$$typeof===REACT_ELEMENT_TYPE){callback(traverseContext,children,nameSoFar===""?SEPARATOR+getComponentKey(children,0):nameSoFar);return 1}var child;var nextName;var subtreeCount=0;var nextNamePrefix=nameSoFar===""?SEPARATOR:nameSoFar+SUBSEPARATOR;if(Array.isArray(children)){for(var i=0;i<children.length;i++){child=children[i];nextName=nextNamePrefix+getComponentKey(child,i);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}else{var iteratorFn=getIteratorFn(children);if(iteratorFn){var iterator=iteratorFn.call(children);var step;if(iteratorFn!==children.entries){var ii=0;while(!(step=iterator.next()).done){child=step.value;nextName=nextNamePrefix+getComponentKey(child,ii++);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}else{if(process.env.NODE_ENV!=="production"){var mapsAsChildrenAddendum="";if(ReactCurrentOwner.current){var mapsAsChildrenOwnerName=ReactCurrentOwner.current.getName();if(mapsAsChildrenOwnerName){mapsAsChildrenAddendum=" Check the render method of `"+mapsAsChildrenOwnerName+"`."}}process.env.NODE_ENV!=="production"?warning(didWarnAboutMaps,"Using Maps as children is not yet fully supported. It is an "+"experimental feature that might be removed. Convert it to a "+"sequence / iterable of keyed ReactElements instead.%s",mapsAsChildrenAddendum):void 0;didWarnAboutMaps=true}while(!(step=iterator.next()).done){var entry=step.value;if(entry){child=entry[1];nextName=nextNamePrefix+KeyEscapeUtils.escape(entry[0])+SUBSEPARATOR+getComponentKey(child,0);subtreeCount+=traverseAllChildrenImpl(child,nextName,callback,traverseContext)}}}}else if(type==="object"){var addendum="";if(process.env.NODE_ENV!=="production"){addendum=" If you meant to render a collection of children, use an array "+"instead or wrap the object using createFragment(object) from the "+"React add-ons.";if(children._isReactElement){addendum=" It looks like you're using an element created by a different "+"version of React. Make sure to use only one copy of React."}if(ReactCurrentOwner.current){var name=ReactCurrentOwner.current.getName();if(name){addendum+=" Check the render method of `"+name+"`."}}}var childrenString=String(children);!false?process.env.NODE_ENV!=="production"?invariant(false,"Objects are not valid as a React child (found: %s).%s",childrenString==="[object Object]"?"object with keys {"+Object.keys(children).join(", ")+"}":childrenString,addendum):_prodInvariant("31",childrenString==="[object Object]"?"object with keys {"+Object.keys(children).join(", ")+"}":childrenString,addendum):void 0}}return subtreeCount}function traverseAllChildren(children,callback,traverseContext){if(children==null){return 0}return traverseAllChildrenImpl(children,"",callback,traverseContext)}module.exports=traverseAllChildren}).call(this,require("_process"))},{"./KeyEscapeUtils":158,"./ReactCurrentOwner":164,"./ReactElementSymbol":167,"./getIteratorFn":177,"./reactProdInvariant":181,_process:184,"fbjs/lib/invariant":18,"fbjs/lib/warning":25}],183:[function(require,module,exports){"use strict";module.exports=require("./lib/React")},{"./lib/React":160}],184:[function(require,module,exports){var process=module.exports={};var cachedSetTimeout;var cachedClearTimeout;function defaultSetTimout(){throw new Error("setTimeout has not been defined")}function defaultClearTimeout(){throw new Error("clearTimeout has not been defined")}(function(){try{if(typeof setTimeout==="function"){cachedSetTimeout=setTimeout}else{cachedSetTimeout=defaultSetTimout}}catch(e){cachedSetTimeout=defaultSetTimout}try{if(typeof clearTimeout==="function"){cachedClearTimeout=clearTimeout}else{cachedClearTimeout=defaultClearTimeout}}catch(e){cachedClearTimeout=defaultClearTimeout}})();function runTimeout(fun){if(cachedSetTimeout===setTimeout){return setTimeout(fun,0)}if((cachedSetTimeout===defaultSetTimout||!cachedSetTimeout)&&setTimeout){cachedSetTimeout=setTimeout;return setTimeout(fun,0)}try{return cachedSetTimeout(fun,0)}catch(e){try{return cachedSetTimeout.call(null,fun,0)}catch(e){return cachedSetTimeout.call(this,fun,0)}}}function runClearTimeout(marker){if(cachedClearTimeout===clearTimeout){return clearTimeout(marker)}if((cachedClearTimeout===defaultClearTimeout||!cachedClearTimeout)&&clearTimeout){cachedClearTimeout=clearTimeout;return clearTimeout(marker)}try{return cachedClearTimeout(marker)}catch(e){try{return cachedClearTimeout.call(null,marker)}catch(e){return cachedClearTimeout.call(this,marker)}}}var queue=[];var draining=false;var currentQueue;var queueIndex=-1;function cleanUpNextTick(){if(!draining||!currentQueue){return}draining=false;if(currentQueue.length){queue=currentQueue.concat(queue)}else{queueIndex=-1}if(queue.length){drainQueue()}}function drainQueue(){if(draining){return}var timeout=runTimeout(cleanUpNextTick);draining=true;var len=queue.length;while(len){currentQueue=queue;queue=[];while(++queueIndex<len){if(currentQueue){currentQueue[queueIndex].run()}}queueIndex=-1;len=queue.length}currentQueue=null;draining=false;runClearTimeout(timeout)}process.nextTick=function(fun){var args=new Array(arguments.length-1);if(arguments.length>1){for(var i=1;i<arguments.length;i++){args[i-1]=arguments[i]}}queue.push(new Item(fun,args));if(queue.length===1&&!draining){runTimeout(drainQueue)}};function Item(fun,array){this.fun=fun;this.array=array}Item.prototype.run=function(){this.fun.apply(null,this.array)};process.title="browser";process.browser=true;process.env={};process.argv=[];process.version="";process.versions={};function noop(){}process.on=noop;process.addListener=noop;process.once=noop;process.off=noop;process.removeListener=noop;process.removeAllListeners=noop;process.emit=noop;process.prependListener=noop;process.prependOnceListener=noop;process.listeners=function(name){return[]};process.binding=function(name){throw new Error("process.binding is not supported")};process.cwd=function(){return"/"};process.chdir=function(dir){throw new Error("process.chdir is not supported")};process.umask=function(){return 0}},{}]},{},[1]);






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

function h$concurEventCallback(async, action, ev) {
    var a = (h$c2(h$ap1_e,(action),((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (ev))))));
    if(async) {
        h$run(a);
    } else {
        h$runSync(a, true);
    }
}
function h$hsprimitive_memcpy(dst_d, dst_o, doff, src_d, src_o, soff, len) {
  return h$primitive_memmove(dst_d, dst_o, doff, src_d, src_o, len);
}

function h$hsprimitive_memmove(dst_d, dst_o, doff, src_d, src_o, soff, len) {
  if(len === 0) return;
  var du8 = dst_d.u8, su8 = src_d.u8;
  for(var i=len-1;i>=0;i--) {
    du8[dst_o+i] = su8[src_o+i];
  }
}
function h$hsprimitive_memsetba_Word8 (p_d, off, n, x) { if(n > 0) { if(p_d.u8.fill) p_d.u8.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.u8[i] = x; } }
function h$hsprimitive_memsetba_Word16 (p_d, off, n, x) { if(n > 0) { if(p_d.u1.fill) p_d.u1.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.u1[i] = x; } }
function h$hsprimitive_memsetba_Word32 (p_d, off, n, x) { if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.i3[i] = x; } }
function h$hsprimitive_memsetba_Word (p_d, off, n, x) { if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.i3[i] = x; } }
function h$hsprimitive_memsetba_Float (p_d, off, n, x) { if(n > 0) { if(p_d.f3.fill) p_d.f3.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.f3[i] = x; } }
function h$hsprimitive_memsetba_Double (p_d, off, n, x) { if(n > 0) { if(p_d.f6.fill) p_d.f6.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.f6[i] = x; } }
function h$hsprimitive_memsetba_Char (p_d, off, n, x) { if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.i3[i] = x; } }

function h$hsprimitive_memset_Word8 (p_d, p_o, off, n, x) { var start = (p_o >> 0) + off; if(n > 0) { if(p_d.u8.fill) p_d.u8.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.u8[i] = x; } }
function h$hsprimitive_memset_Word16 (p_d, p_o, off, n, x) { var start = (p_o >> 1) + off; if(n > 0) { if(p_d.u1.fill) p_d.u1.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.u1[i] = x; } }
function h$hsprimitive_memset_Word32 (p_d, p_o, off, n, x) { var start = (p_o >> 2) + off; if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.i3[i] = x; } }
function h$hsprimitive_memset_Word (p_d, p_o, off, n, x) { var start = (p_o >> 2) + off; if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.i3[i] = x; } }
function h$hsprimitive_memset_Float (p_d, p_o, off, n, x) { var start = (p_o >> 2) + off; if(n > 0) { if(p_d.f3.fill) p_d.f3.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.f3[i] = x; } }
function h$hsprimitive_memset_Double (p_d, p_o, off, n, x) { var start = (p_o >> 3) + off; if(n > 0) { if(p_d.f6.fill) p_d.f6.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.f6[i] = x; } }
function h$hsprimitive_memset_Char (p_d, p_o, off, n, x) { var start = (p_o >> 2) + off; if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.i3[i] = x; } }

function h$hsprimitive_memsetba_Word64(p_d, off, n, x_1, x_2) {
  h$hsprimitive_memset_Word64(p_d, 0, off, n, x_1, x_2);
}

function h$hsprimitive_memset_Word64(p_d, p_o, off, n, x_1, x_2) {
  var start = (p_o >> 3) + off;
  if(n > 0) {
    var pi3 = p_d.i3;
    for(var i = 0; i < n; i++) {
      var o = (start + i) << 1;
      pi3[o] = x_1;
      pi3[o+1] = x_2;
    }
  }
}

function h$hsprimitive_memset_Ptr(p_d, p_o, off, n, x_1, x_2) {
  if(n > 0) {
    if(!p_d.arr) p_d.arr = [];
    var a = p_d.arr;
    for(var i = 0; i < n; i++) {
      a[p_o + ((off + i) << 2)] = [x_1, x_2];
    }
  }
}
// Copyright 2011 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview Abstract cryptographic hash interface.
 *
 * See goog.crypt.Sha1 and goog.crypt.Md5 for sample implementations.
 *
 */

goog.provide('goog.crypt.Hash');



/**
 * Create a cryptographic hash instance.
 *
 * @constructor
 * @struct
 */
goog.crypt.Hash = function() {
  /**
   * The block size for the hasher.
   * @type {number}
   */
  this.blockSize = -1;
};


/**
 * Resets the internal accumulator.
 */
goog.crypt.Hash.prototype.reset = goog.abstractMethod;


/**
 * Adds a byte array (array with values in [0-255] range) or a string (might
 * only contain 8-bit, i.e., Latin1 characters) to the internal accumulator.
 *
 * Many hash functions operate on blocks of data and implement optimizations
 * when a full chunk of data is readily available. Hence it is often preferable
 * to provide large chunks of data (a kilobyte or more) than to repeatedly
 * call the update method with few tens of bytes. If this is not possible, or
 * not feasible, it might be good to provide data in multiplies of hash block
 * size (often 64 bytes). Please see the implementation and performance tests
 * of your favourite hash.
 *
 * @param {Array<number>|Uint8Array|string} bytes Data used for the update.
 * @param {number=} opt_length Number of bytes to use.
 */
goog.crypt.Hash.prototype.update = goog.abstractMethod;


/**
 * @return {!Array<number>} The finalized hash computed
 *     from the internal accumulator.
 */
goog.crypt.Hash.prototype.digest = goog.abstractMethod;
// Copyright 2011 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview MD5 cryptographic hash.
 * Implementation of http://tools.ietf.org/html/rfc1321 with common
 * optimizations and tweaks (see http://en.wikipedia.org/wiki/MD5).
 *
 * Usage:
 *   var md5 = new goog.crypt.Md5();
 *   md5.update(bytes);
 *   var hash = md5.digest();
 *
 * Performance:
 *   Chrome 23              ~680 Mbit/s
 *   Chrome 13 (in a VM)    ~250 Mbit/s
 *   Firefox 6.0 (in a VM)  ~100 Mbit/s
 *   IE9 (in a VM)           ~27 Mbit/s
 *   Firefox 3.6             ~15 Mbit/s
 *   IE8 (in a VM)           ~13 Mbit/s
 *
 */

goog.provide('goog.crypt.Md5');

goog.require('goog.crypt.Hash');



/**
 * MD5 cryptographic hash constructor.
 * @constructor
 * @extends {goog.crypt.Hash}
 * @final
 * @struct
 */
goog.crypt.Md5 = function() {
  goog.crypt.Md5.base(this, 'constructor');

  this.blockSize = 512 / 8;

  /**
   * Holds the current values of accumulated A-D variables (MD buffer).
   * @type {!Array<number>}
   * @private
   */
  this.chain_ = new Array(4);

  /**
   * A buffer holding the data until the whole block can be processed.
   * @type {!Array<number>}
   * @private
   */
  this.block_ = new Array(this.blockSize);

  /**
   * The length of yet-unprocessed data as collected in the block.
   * @type {number}
   * @private
   */
  this.blockLength_ = 0;

  /**
   * The total length of the message so far.
   * @type {number}
   * @private
   */
  this.totalLength_ = 0;

  this.reset();
};
goog.inherits(goog.crypt.Md5, goog.crypt.Hash);


/**
 * Integer rotation constants used by the abbreviated implementation.
 * They are hardcoded in the unrolled implementation, so it is left
 * here commented out.
 * @type {Array<number>}
 * @private
 *
goog.crypt.Md5.S_ = [
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21
];
 */

/**
 * Sine function constants used by the abbreviated implementation.
 * They are hardcoded in the unrolled implementation, so it is left
 * here commented out.
 * @type {Array<number>}
 * @private
 *
goog.crypt.Md5.T_ = [
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
  0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
  0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
  0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
  0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
  0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
  0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
  0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
  0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
];
 */


/** @override */
goog.crypt.Md5.prototype.reset = function() {
  this.chain_[0] = 0x67452301;
  this.chain_[1] = 0xefcdab89;
  this.chain_[2] = 0x98badcfe;
  this.chain_[3] = 0x10325476;

  this.blockLength_ = 0;
  this.totalLength_ = 0;
};


/**
 * Internal compress helper function. It takes a block of data (64 bytes)
 * and updates the accumulator.
 * @param {Array<number>|Uint8Array|string} buf The block to compress.
 * @param {number=} opt_offset Offset of the block in the buffer.
 * @private
 */
goog.crypt.Md5.prototype.compress_ = function(buf, opt_offset) {
  if (!opt_offset) {
    opt_offset = 0;
  }

  // We allocate the array every time, but it's cheap in practice.
  var X = new Array(16);

  // Get 16 little endian words. It is not worth unrolling this for Chrome 11.
  if (goog.isString(buf)) {
    for (var i = 0; i < 16; ++i) {
      X[i] = (buf.charCodeAt(opt_offset++)) |
             (buf.charCodeAt(opt_offset++) << 8) |
             (buf.charCodeAt(opt_offset++) << 16) |
             (buf.charCodeAt(opt_offset++) << 24);
    }
  } else {
    for (var i = 0; i < 16; ++i) {
      X[i] = (buf[opt_offset++]) |
             (buf[opt_offset++] << 8) |
             (buf[opt_offset++] << 16) |
             (buf[opt_offset++] << 24);
    }
  }

  var A = this.chain_[0];
  var B = this.chain_[1];
  var C = this.chain_[2];
  var D = this.chain_[3];
  var sum = 0;

  /*
   * This is an abbreviated implementation, it is left here commented out for
   * reference purposes. See below for an unrolled version in use.
   *
  var f, n, tmp;
  for (var i = 0; i < 64; ++i) {

    if (i < 16) {
      f = (D ^ (B & (C ^ D)));
      n = i;
    } else if (i < 32) {
      f = (C ^ (D & (B ^ C)));
      n = (5 * i + 1) % 16;
    } else if (i < 48) {
      f = (B ^ C ^ D);
      n = (3 * i + 5) % 16;
    } else {
      f = (C ^ (B | (~D)));
      n = (7 * i) % 16;
    }

    tmp = D;
    D = C;
    C = B;
    sum = (A + f + goog.crypt.Md5.T_[i] + X[n]) & 0xffffffff;
    B += ((sum << goog.crypt.Md5.S_[i]) & 0xffffffff) |
         (sum >>> (32 - goog.crypt.Md5.S_[i]));
    A = tmp;
  }
   */

  /*
   * This is an unrolled MD5 implementation, which gives ~30% speedup compared
   * to the abbreviated implementation above, as measured on Chrome 11. It is
   * important to keep 32-bit croppings to minimum and inline the integer
   * rotation.
   */
  sum = (A + (D ^ (B & (C ^ D))) + X[0] + 0xd76aa478) & 0xffffffff;
  A = B + (((sum << 7) & 0xffffffff) | (sum >>> 25));
  sum = (D + (C ^ (A & (B ^ C))) + X[1] + 0xe8c7b756) & 0xffffffff;
  D = A + (((sum << 12) & 0xffffffff) | (sum >>> 20));
  sum = (C + (B ^ (D & (A ^ B))) + X[2] + 0x242070db) & 0xffffffff;
  C = D + (((sum << 17) & 0xffffffff) | (sum >>> 15));
  sum = (B + (A ^ (C & (D ^ A))) + X[3] + 0xc1bdceee) & 0xffffffff;
  B = C + (((sum << 22) & 0xffffffff) | (sum >>> 10));
  sum = (A + (D ^ (B & (C ^ D))) + X[4] + 0xf57c0faf) & 0xffffffff;
  A = B + (((sum << 7) & 0xffffffff) | (sum >>> 25));
  sum = (D + (C ^ (A & (B ^ C))) + X[5] + 0x4787c62a) & 0xffffffff;
  D = A + (((sum << 12) & 0xffffffff) | (sum >>> 20));
  sum = (C + (B ^ (D & (A ^ B))) + X[6] + 0xa8304613) & 0xffffffff;
  C = D + (((sum << 17) & 0xffffffff) | (sum >>> 15));
  sum = (B + (A ^ (C & (D ^ A))) + X[7] + 0xfd469501) & 0xffffffff;
  B = C + (((sum << 22) & 0xffffffff) | (sum >>> 10));
  sum = (A + (D ^ (B & (C ^ D))) + X[8] + 0x698098d8) & 0xffffffff;
  A = B + (((sum << 7) & 0xffffffff) | (sum >>> 25));
  sum = (D + (C ^ (A & (B ^ C))) + X[9] + 0x8b44f7af) & 0xffffffff;
  D = A + (((sum << 12) & 0xffffffff) | (sum >>> 20));
  sum = (C + (B ^ (D & (A ^ B))) + X[10] + 0xffff5bb1) & 0xffffffff;
  C = D + (((sum << 17) & 0xffffffff) | (sum >>> 15));
  sum = (B + (A ^ (C & (D ^ A))) + X[11] + 0x895cd7be) & 0xffffffff;
  B = C + (((sum << 22) & 0xffffffff) | (sum >>> 10));
  sum = (A + (D ^ (B & (C ^ D))) + X[12] + 0x6b901122) & 0xffffffff;
  A = B + (((sum << 7) & 0xffffffff) | (sum >>> 25));
  sum = (D + (C ^ (A & (B ^ C))) + X[13] + 0xfd987193) & 0xffffffff;
  D = A + (((sum << 12) & 0xffffffff) | (sum >>> 20));
  sum = (C + (B ^ (D & (A ^ B))) + X[14] + 0xa679438e) & 0xffffffff;
  C = D + (((sum << 17) & 0xffffffff) | (sum >>> 15));
  sum = (B + (A ^ (C & (D ^ A))) + X[15] + 0x49b40821) & 0xffffffff;
  B = C + (((sum << 22) & 0xffffffff) | (sum >>> 10));
  sum = (A + (C ^ (D & (B ^ C))) + X[1] + 0xf61e2562) & 0xffffffff;
  A = B + (((sum << 5) & 0xffffffff) | (sum >>> 27));
  sum = (D + (B ^ (C & (A ^ B))) + X[6] + 0xc040b340) & 0xffffffff;
  D = A + (((sum << 9) & 0xffffffff) | (sum >>> 23));
  sum = (C + (A ^ (B & (D ^ A))) + X[11] + 0x265e5a51) & 0xffffffff;
  C = D + (((sum << 14) & 0xffffffff) | (sum >>> 18));
  sum = (B + (D ^ (A & (C ^ D))) + X[0] + 0xe9b6c7aa) & 0xffffffff;
  B = C + (((sum << 20) & 0xffffffff) | (sum >>> 12));
  sum = (A + (C ^ (D & (B ^ C))) + X[5] + 0xd62f105d) & 0xffffffff;
  A = B + (((sum << 5) & 0xffffffff) | (sum >>> 27));
  sum = (D + (B ^ (C & (A ^ B))) + X[10] + 0x02441453) & 0xffffffff;
  D = A + (((sum << 9) & 0xffffffff) | (sum >>> 23));
  sum = (C + (A ^ (B & (D ^ A))) + X[15] + 0xd8a1e681) & 0xffffffff;
  C = D + (((sum << 14) & 0xffffffff) | (sum >>> 18));
  sum = (B + (D ^ (A & (C ^ D))) + X[4] + 0xe7d3fbc8) & 0xffffffff;
  B = C + (((sum << 20) & 0xffffffff) | (sum >>> 12));
  sum = (A + (C ^ (D & (B ^ C))) + X[9] + 0x21e1cde6) & 0xffffffff;
  A = B + (((sum << 5) & 0xffffffff) | (sum >>> 27));
  sum = (D + (B ^ (C & (A ^ B))) + X[14] + 0xc33707d6) & 0xffffffff;
  D = A + (((sum << 9) & 0xffffffff) | (sum >>> 23));
  sum = (C + (A ^ (B & (D ^ A))) + X[3] + 0xf4d50d87) & 0xffffffff;
  C = D + (((sum << 14) & 0xffffffff) | (sum >>> 18));
  sum = (B + (D ^ (A & (C ^ D))) + X[8] + 0x455a14ed) & 0xffffffff;
  B = C + (((sum << 20) & 0xffffffff) | (sum >>> 12));
  sum = (A + (C ^ (D & (B ^ C))) + X[13] + 0xa9e3e905) & 0xffffffff;
  A = B + (((sum << 5) & 0xffffffff) | (sum >>> 27));
  sum = (D + (B ^ (C & (A ^ B))) + X[2] + 0xfcefa3f8) & 0xffffffff;
  D = A + (((sum << 9) & 0xffffffff) | (sum >>> 23));
  sum = (C + (A ^ (B & (D ^ A))) + X[7] + 0x676f02d9) & 0xffffffff;
  C = D + (((sum << 14) & 0xffffffff) | (sum >>> 18));
  sum = (B + (D ^ (A & (C ^ D))) + X[12] + 0x8d2a4c8a) & 0xffffffff;
  B = C + (((sum << 20) & 0xffffffff) | (sum >>> 12));
  sum = (A + (B ^ C ^ D) + X[5] + 0xfffa3942) & 0xffffffff;
  A = B + (((sum << 4) & 0xffffffff) | (sum >>> 28));
  sum = (D + (A ^ B ^ C) + X[8] + 0x8771f681) & 0xffffffff;
  D = A + (((sum << 11) & 0xffffffff) | (sum >>> 21));
  sum = (C + (D ^ A ^ B) + X[11] + 0x6d9d6122) & 0xffffffff;
  C = D + (((sum << 16) & 0xffffffff) | (sum >>> 16));
  sum = (B + (C ^ D ^ A) + X[14] + 0xfde5380c) & 0xffffffff;
  B = C + (((sum << 23) & 0xffffffff) | (sum >>> 9));
  sum = (A + (B ^ C ^ D) + X[1] + 0xa4beea44) & 0xffffffff;
  A = B + (((sum << 4) & 0xffffffff) | (sum >>> 28));
  sum = (D + (A ^ B ^ C) + X[4] + 0x4bdecfa9) & 0xffffffff;
  D = A + (((sum << 11) & 0xffffffff) | (sum >>> 21));
  sum = (C + (D ^ A ^ B) + X[7] + 0xf6bb4b60) & 0xffffffff;
  C = D + (((sum << 16) & 0xffffffff) | (sum >>> 16));
  sum = (B + (C ^ D ^ A) + X[10] + 0xbebfbc70) & 0xffffffff;
  B = C + (((sum << 23) & 0xffffffff) | (sum >>> 9));
  sum = (A + (B ^ C ^ D) + X[13] + 0x289b7ec6) & 0xffffffff;
  A = B + (((sum << 4) & 0xffffffff) | (sum >>> 28));
  sum = (D + (A ^ B ^ C) + X[0] + 0xeaa127fa) & 0xffffffff;
  D = A + (((sum << 11) & 0xffffffff) | (sum >>> 21));
  sum = (C + (D ^ A ^ B) + X[3] + 0xd4ef3085) & 0xffffffff;
  C = D + (((sum << 16) & 0xffffffff) | (sum >>> 16));
  sum = (B + (C ^ D ^ A) + X[6] + 0x04881d05) & 0xffffffff;
  B = C + (((sum << 23) & 0xffffffff) | (sum >>> 9));
  sum = (A + (B ^ C ^ D) + X[9] + 0xd9d4d039) & 0xffffffff;
  A = B + (((sum << 4) & 0xffffffff) | (sum >>> 28));
  sum = (D + (A ^ B ^ C) + X[12] + 0xe6db99e5) & 0xffffffff;
  D = A + (((sum << 11) & 0xffffffff) | (sum >>> 21));
  sum = (C + (D ^ A ^ B) + X[15] + 0x1fa27cf8) & 0xffffffff;
  C = D + (((sum << 16) & 0xffffffff) | (sum >>> 16));
  sum = (B + (C ^ D ^ A) + X[2] + 0xc4ac5665) & 0xffffffff;
  B = C + (((sum << 23) & 0xffffffff) | (sum >>> 9));
  sum = (A + (C ^ (B | (~D))) + X[0] + 0xf4292244) & 0xffffffff;
  A = B + (((sum << 6) & 0xffffffff) | (sum >>> 26));
  sum = (D + (B ^ (A | (~C))) + X[7] + 0x432aff97) & 0xffffffff;
  D = A + (((sum << 10) & 0xffffffff) | (sum >>> 22));
  sum = (C + (A ^ (D | (~B))) + X[14] + 0xab9423a7) & 0xffffffff;
  C = D + (((sum << 15) & 0xffffffff) | (sum >>> 17));
  sum = (B + (D ^ (C | (~A))) + X[5] + 0xfc93a039) & 0xffffffff;
  B = C + (((sum << 21) & 0xffffffff) | (sum >>> 11));
  sum = (A + (C ^ (B | (~D))) + X[12] + 0x655b59c3) & 0xffffffff;
  A = B + (((sum << 6) & 0xffffffff) | (sum >>> 26));
  sum = (D + (B ^ (A | (~C))) + X[3] + 0x8f0ccc92) & 0xffffffff;
  D = A + (((sum << 10) & 0xffffffff) | (sum >>> 22));
  sum = (C + (A ^ (D | (~B))) + X[10] + 0xffeff47d) & 0xffffffff;
  C = D + (((sum << 15) & 0xffffffff) | (sum >>> 17));
  sum = (B + (D ^ (C | (~A))) + X[1] + 0x85845dd1) & 0xffffffff;
  B = C + (((sum << 21) & 0xffffffff) | (sum >>> 11));
  sum = (A + (C ^ (B | (~D))) + X[8] + 0x6fa87e4f) & 0xffffffff;
  A = B + (((sum << 6) & 0xffffffff) | (sum >>> 26));
  sum = (D + (B ^ (A | (~C))) + X[15] + 0xfe2ce6e0) & 0xffffffff;
  D = A + (((sum << 10) & 0xffffffff) | (sum >>> 22));
  sum = (C + (A ^ (D | (~B))) + X[6] + 0xa3014314) & 0xffffffff;
  C = D + (((sum << 15) & 0xffffffff) | (sum >>> 17));
  sum = (B + (D ^ (C | (~A))) + X[13] + 0x4e0811a1) & 0xffffffff;
  B = C + (((sum << 21) & 0xffffffff) | (sum >>> 11));
  sum = (A + (C ^ (B | (~D))) + X[4] + 0xf7537e82) & 0xffffffff;
  A = B + (((sum << 6) & 0xffffffff) | (sum >>> 26));
  sum = (D + (B ^ (A | (~C))) + X[11] + 0xbd3af235) & 0xffffffff;
  D = A + (((sum << 10) & 0xffffffff) | (sum >>> 22));
  sum = (C + (A ^ (D | (~B))) + X[2] + 0x2ad7d2bb) & 0xffffffff;
  C = D + (((sum << 15) & 0xffffffff) | (sum >>> 17));
  sum = (B + (D ^ (C | (~A))) + X[9] + 0xeb86d391) & 0xffffffff;
  B = C + (((sum << 21) & 0xffffffff) | (sum >>> 11));

  this.chain_[0] = (this.chain_[0] + A) & 0xffffffff;
  this.chain_[1] = (this.chain_[1] + B) & 0xffffffff;
  this.chain_[2] = (this.chain_[2] + C) & 0xffffffff;
  this.chain_[3] = (this.chain_[3] + D) & 0xffffffff;
};


/** @override */
goog.crypt.Md5.prototype.update = function(bytes, opt_length) {
  if (!goog.isDef(opt_length)) {
    opt_length = bytes.length;
  }
  var lengthMinusBlock = opt_length - this.blockSize;

  // Copy some object properties to local variables in order to save on access
  // time from inside the loop (~10% speedup was observed on Chrome 11).
  var block = this.block_;
  var blockLength = this.blockLength_;
  var i = 0;

  // The outer while loop should execute at most twice.
  while (i < opt_length) {
    // When we have no data in the block to top up, we can directly process the
    // input buffer (assuming it contains sufficient data). This gives ~30%
    // speedup on Chrome 14 and ~70% speedup on Firefox 6.0, but requires that
    // the data is provided in large chunks (or in multiples of 64 bytes).
    if (blockLength == 0) {
      while (i <= lengthMinusBlock) {
        this.compress_(bytes, i);
        i += this.blockSize;
      }
    }

    if (goog.isString(bytes)) {
      while (i < opt_length) {
        block[blockLength++] = bytes.charCodeAt(i++);
        if (blockLength == this.blockSize) {
          this.compress_(block);
          blockLength = 0;
          // Jump to the outer loop so we use the full-block optimization.
          break;
        }
      }
    } else {
      while (i < opt_length) {
        block[blockLength++] = bytes[i++];
        if (blockLength == this.blockSize) {
          this.compress_(block);
          blockLength = 0;
          // Jump to the outer loop so we use the full-block optimization.
          break;
        }
      }
    }
  }

  this.blockLength_ = blockLength;
  this.totalLength_ += opt_length;
};


/** @override */
goog.crypt.Md5.prototype.digest = function() {
  // This must accommodate at least 1 padding byte (0x80), 8 bytes of
  // total bitlength, and must end at a 64-byte boundary.
  var pad = new Array((this.blockLength_ < 56 ?
                       this.blockSize :
                       this.blockSize * 2) - this.blockLength_);

  // Add padding: 0x80 0x00*
  pad[0] = 0x80;
  for (var i = 1; i < pad.length - 8; ++i) {
    pad[i] = 0;
  }
  // Add the total number of bits, little endian 64-bit integer.
  var totalBits = this.totalLength_ * 8;
  for (var i = pad.length - 8; i < pad.length; ++i) {
    pad[i] = totalBits & 0xff;
    totalBits /= 0x100; // Don't use bit-shifting here!
  }
  this.update(pad);

  var digest = new Array(16);
  var n = 0;
  for (var i = 0; i < 4; ++i) {
    for (var j = 0; j < 32; j += 8) {
      digest[n++] = (this.chain_[i] >>> j) & 0xff;
    }
  }
  return digest;
};




/* include/HsBaseConfig.h.  Generated from HsBaseConfig.h.in by configure.  */
/* include/HsBaseConfig.h.in.  Generated from configure.ac by autoheader.  */

/* The value of E2BIG. */


/* The value of EACCES. */


/* The value of EADDRINUSE. */


/* The value of EADDRNOTAVAIL. */


/* The value of EADV. */


/* The value of EAFNOSUPPORT. */


/* The value of EAGAIN. */


/* The value of EALREADY. */


/* The value of EBADF. */


/* The value of EBADMSG. */


/* The value of EBADRPC. */


/* The value of EBUSY. */


/* The value of ECHILD. */


/* The value of ECOMM. */


/* The value of ECONNABORTED. */


/* The value of ECONNREFUSED. */


/* The value of ECONNRESET. */


/* The value of EDEADLK. */


/* The value of EDESTADDRREQ. */


/* The value of EDIRTY. */


/* The value of EDOM. */


/* The value of EDQUOT. */


/* The value of EEXIST. */


/* The value of EFAULT. */


/* The value of EFBIG. */


/* The value of EFTYPE. */


/* The value of EHOSTDOWN. */


/* The value of EHOSTUNREACH. */


/* The value of EIDRM. */


/* The value of EILSEQ. */


/* The value of EINPROGRESS. */


/* The value of EINTR. */


/* The value of EINVAL. */


/* The value of EIO. */


/* The value of EISCONN. */


/* The value of EISDIR. */


/* The value of ELOOP. */


/* The value of EMFILE. */


/* The value of EMLINK. */


/* The value of EMSGSIZE. */


/* The value of EMULTIHOP. */


/* The value of ENAMETOOLONG. */


/* The value of ENETDOWN. */


/* The value of ENETRESET. */


/* The value of ENETUNREACH. */


/* The value of ENFILE. */


/* The value of ENOBUFS. */


/* The value of ENOCIGAR. */


/* The value of ENODATA. */


/* The value of ENODEV. */


/* The value of ENOENT. */


/* The value of ENOEXEC. */


/* The value of ENOLCK. */


/* The value of ENOLINK. */


/* The value of ENOMEM. */


/* The value of ENOMSG. */


/* The value of ENONET. */


/* The value of ENOPROTOOPT. */


/* The value of ENOSPC. */


/* The value of ENOSR. */


/* The value of ENOSTR. */


/* The value of ENOSYS. */


/* The value of ENOTBLK. */


/* The value of ENOTCONN. */


/* The value of ENOTDIR. */


/* The value of ENOTEMPTY. */


/* The value of ENOTSOCK. */


/* The value of ENOTSUP. */


/* The value of ENOTTY. */


/* The value of ENXIO. */


/* The value of EOPNOTSUPP. */


/* The value of EPERM. */


/* The value of EPFNOSUPPORT. */


/* The value of EPIPE. */


/* The value of EPROCLIM. */


/* The value of EPROCUNAVAIL. */


/* The value of EPROGMISMATCH. */


/* The value of EPROGUNAVAIL. */


/* The value of EPROTO. */


/* The value of EPROTONOSUPPORT. */


/* The value of EPROTOTYPE. */


/* The value of ERANGE. */


/* The value of EREMCHG. */


/* The value of EREMOTE. */


/* The value of EROFS. */


/* The value of ERPCMISMATCH. */


/* The value of ERREMOTE. */


/* The value of ESHUTDOWN. */


/* The value of ESOCKTNOSUPPORT. */


/* The value of ESPIPE. */


/* The value of ESRCH. */


/* The value of ESRMNT. */


/* The value of ESTALE. */


/* The value of ETIME. */


/* The value of ETIMEDOUT. */


/* The value of ETOOMANYREFS. */


/* The value of ETXTBSY. */


/* The value of EUSERS. */


/* The value of EWOULDBLOCK. */


/* The value of EXDEV. */


/* The value of O_BINARY. */


/* The value of SIGINT. */


/* Define to 1 if you have the `clock_gettime' function. */
/* #undef HAVE_CLOCK_GETTIME */

/* Define to 1 if you have the <ctype.h> header file. */


/* Define if you have epoll support. */
/* #undef HAVE_EPOLL */

/* Define to 1 if you have the `epoll_ctl' function. */
/* #undef HAVE_EPOLL_CTL */

/* Define to 1 if you have the <errno.h> header file. */


/* Define to 1 if you have the `eventfd' function. */
/* #undef HAVE_EVENTFD */

/* Define to 1 if you have the <fcntl.h> header file. */


/* Define to 1 if you have the `ftruncate' function. */


/* Define to 1 if you have the `getclock' function. */
/* #undef HAVE_GETCLOCK */

/* Define to 1 if you have the `getrusage' function. */


/* Define to 1 if you have the <inttypes.h> header file. */


/* Define to 1 if you have the `iswspace' function. */


/* Define to 1 if you have the `kevent' function. */


/* Define to 1 if you have the `kevent64' function. */


/* Define if you have kqueue support. */


/* Define to 1 if you have the <langinfo.h> header file. */


/* Define to 1 if you have libcharset. */


/* Define to 1 if you have the `rt' library (-lrt). */
/* #undef HAVE_LIBRT */

/* Define to 1 if you have the <limits.h> header file. */


/* Define to 1 if the system has the type `long long'. */


/* Define to 1 if you have the `lstat' function. */


/* Define to 1 if you have the <memory.h> header file. */


/* Define if you have poll support. */


/* Define to 1 if you have the <poll.h> header file. */


/* Define to 1 if you have the <signal.h> header file. */


/* Define to 1 if you have the <stdint.h> header file. */


/* Define to 1 if you have the <stdlib.h> header file. */


/* Define to 1 if you have the <strings.h> header file. */


/* Define to 1 if you have the <string.h> header file. */


/* Define to 1 if you have the <sys/epoll.h> header file. */
/* #undef HAVE_SYS_EPOLL_H */

/* Define to 1 if you have the <sys/eventfd.h> header file. */
/* #undef HAVE_SYS_EVENTFD_H */

/* Define to 1 if you have the <sys/event.h> header file. */


/* Define to 1 if you have the <sys/resource.h> header file. */


/* Define to 1 if you have the <sys/select.h> header file. */


/* Define to 1 if you have the <sys/stat.h> header file. */


/* Define to 1 if you have the <sys/syscall.h> header file. */


/* Define to 1 if you have the <sys/timeb.h> header file. */


/* Define to 1 if you have the <sys/timers.h> header file. */
/* #undef HAVE_SYS_TIMERS_H */

/* Define to 1 if you have the <sys/times.h> header file. */


/* Define to 1 if you have the <sys/time.h> header file. */


/* Define to 1 if you have the <sys/types.h> header file. */


/* Define to 1 if you have the <sys/utsname.h> header file. */


/* Define to 1 if you have the <sys/wait.h> header file. */


/* Define to 1 if you have the <termios.h> header file. */


/* Define to 1 if you have the `times' function. */


/* Define to 1 if you have the <time.h> header file. */


/* Define to 1 if you have the <unistd.h> header file. */


/* Define to 1 if you have the <utime.h> header file. */


/* Define to 1 if you have the <wctype.h> header file. */


/* Define to 1 if you have the <windows.h> header file. */
/* #undef HAVE_WINDOWS_H */

/* Define to 1 if you have the <winsock.h> header file. */
/* #undef HAVE_WINSOCK_H */

/* Define to 1 if you have the `_chsize' function. */
/* #undef HAVE__CHSIZE */

/* Define to Haskell type for cc_t */


/* Define to Haskell type for char */


/* Define to Haskell type for clock_t */


/* Define to Haskell type for dev_t */


/* Define to Haskell type for double */


/* Define to Haskell type for float */


/* Define to Haskell type for gid_t */


/* Define to Haskell type for ino_t */


/* Define to Haskell type for int */


/* Define to Haskell type for intmax_t */


/* Define to Haskell type for intptr_t */


/* Define to Haskell type for long */


/* Define to Haskell type for long long */


/* Define to Haskell type for mode_t */


/* Define to Haskell type for nlink_t */


/* Define to Haskell type for off_t */


/* Define to Haskell type for pid_t */


/* Define to Haskell type for ptrdiff_t */


/* Define to Haskell type for rlim_t */


/* Define to Haskell type for short */


/* Define to Haskell type for signed char */


/* Define to Haskell type for sig_atomic_t */


/* Define to Haskell type for size_t */


/* Define to Haskell type for speed_t */


/* Define to Haskell type for ssize_t */


/* Define to Haskell type for suseconds_t */


/* Define to Haskell type for tcflag_t */


/* Define to Haskell type for time_t */


/* Define to Haskell type for uid_t */


/* Define to Haskell type for uintmax_t */


/* Define to Haskell type for uintptr_t */


/* Define to Haskell type for unsigned char */


/* Define to Haskell type for unsigned int */


/* Define to Haskell type for unsigned long */


/* Define to Haskell type for unsigned long long */


/* Define to Haskell type for unsigned short */


/* Define to Haskell type for useconds_t */


/* Define to Haskell type for wchar_t */


/* Define to the address where bug reports for this package should be sent. */


/* Define to the full name of this package. */


/* Define to the full name and version of this package. */


/* Define to the one symbol short name of this package. */


/* Define to the home page for this package. */


/* Define to the version of this package. */


/* The size of `kev.filter', as computed by sizeof. */


/* The size of `kev.flags', as computed by sizeof. */


/* The size of `struct MD5Context', as computed by sizeof. */


/* Define to 1 if you have the ANSI C header files. */


/* Number of bits in a file offset, on hosts where this is settable. */
/* #undef _FILE_OFFSET_BITS */

/* Define for large files, on AIX-style hosts. */
/* #undef _LARGE_FILES */






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

// #define GHCJS_TRACE_IO 1
function h$base_access(file, file_off, mode, c) {
                           ;

    if(h$isNode) {
        h$fs.stat(fd, function(err, fs) {
            if(err) {
                h$handleErrnoC(err, -1, 0, c);
            } else {
                c(mode & fs.mode); // fixme is this ok?
            }
        });
    } else

        h$unsupported(-1, c);
}

function h$base_chmod(file, file_off, mode, c) {
                          ;

    if(h$isNode) {
        h$fs.chmod(h$decodeUtf8z(file, file_off), mode, function(err) {
            h$handleErrnoC(err, -1, 0, c);
        });
    } else

        h$unsupported(-1, c);
}

function h$base_close(fd, c) {
                          ;
    var fdo = h$base_fds[fd];
    if(fdo && fdo.close) {
        fdo.close(fd, fdo, c);
    } else {
        h$errno = 22;
        c(-1);
    }
}

function h$base_dup(fd, something, c) {
    throw "h$base_dup";
}

function h$base_dup2(fd, c) {
    throw "h$base_dup2";
}

function h$base_fstat(fd, stat, stat_off, c) {
                         ;

    if(h$isNode) {
        h$fs.fstat(fd, function(err, fs) {
            if(err) {
                h$handlErrnoC(err, -1, 0, c);
            } else {
                h$base_fillStat(fs, stat, stat_off);
                c(0);
            }
        });
    } else

        h$unsupported(-1, c);
}

function h$base_isatty(fd) {
                                 ;

    if(h$isNode) {
        if(fd === 0) return process.stdin.isTTY?1:0;
        if(fd === 1) return process.stdout.isTTY?1:0;
        if(fd === 2) return process.stderr.isTTY?1:0;
    }

    if(fd === 1 || fd === 2) return 1;
    return 0;
}

function h$base_lseek(fd, pos_1, pos_2, whence, c) {
                          ;

    if(h$isNode) {
        var p = goog.math.Long.fromBits(pos_2, pos_1), p1;
        var o = h$base_fds[fd];
        if(!o) {
            h$errno = CONST_BADF;
            c(-1,-1);
        } else {
            switch(whence) {
            case 0: /* SET */
                o.pos = p.toNumber();
                c(p.getHighBits(), p.getLowBits());
                break;
            case 1: /* CUR */
                o.pos += p.toNumber();
                p1 = goog.math.Long.fromNumber(o.pos);
                c(p1.getHighBits(), p1.getLowBits());
                break;
            case 2: /* END */
                h$fs.fstat(fd, function(err, fs) {
                    if(err) {
                        h$setErrno(err);
                        c(-1,-1);
                    } else {
                        o.pos = fs.size + p.toNumber();
                        p1 = goog.math.Long.fromNumber(o.pos);
                        c(p1.getHighBits(), p1.getLowBits());
                    }
                });
                break;
            default:
                h$errno = 22;
                c(-1,-1);
            }
        }
    } else {

        h$unsupported();
        c(-1, -1);

    }

}

function h$base_lstat(file, file_off, stat, stat_off, c) {
                          ;

    if(h$isNode) {
        h$fs.lstat(h$decodeUtf8z(file, file_off), function(err, fs) {
            if(err) {
                h$handleErrnoC(err, -1, 0, c);
            } else {
                h$base_fillStat(fs, stat, stat_off);
                c(0);
            }
        });
    } else

        h$unsupported(-1, c);
}
function h$base_open(file, file_off, how, mode, c) {

    if(h$isNode) {
        var flags, off;
        var fp = h$decodeUtf8z(file, file_off);
        var acc = how & h$base_o_accmode;
        // passing a number lets node.js use it directly as the flags (undocumented)
        if(acc === h$base_o_rdonly) {
            flags = h$processConstants['fs']['O_RDONLY'];
        } else if(acc === h$base_o_wronly) {
            flags = h$processConstants['fs']['O_WRONLY'];
        } else { // r+w
            flags = h$processConstants['fs']['O_RDWR'];
        }
        off = (how & h$base_o_append) ? -1 : 0;
        flags = flags | ((how & h$base_o_trunc) ? h$processConstants['fs']['O_TRUNC'] : 0)
                      | ((how & h$base_o_creat) ? h$processConstants['fs']['O_CREAT'] : 0)
                      | ((how & h$base_o_excl) ? h$processConstants['fs']['O_EXCL'] : 0)
                      | ((how & h$base_o_append) ? h$processConstants['fs']['O_APPEND'] : 0);
        h$fs.open(fp, flags, mode, function(err, fd) {
            if(err) {
                h$handleErrnoC(err, -1, 0, c);
            } else {
                var f = function(p) {
                    h$base_fds[fd] = { read: h$base_readFile
                                       , write: h$base_writeFile
                                       , close: h$base_closeFile
                                       , pos: p
                                     };
                    c(fd);
                }
                if(off === -1) {
                    h$fs.stat(fp, function(err, fs) {
                        if(err) h$handleErrnoC(err, -1, 0, c); else f(fs.size);
                    });
                } else {
                    f(0);
                }
            }
        });
    } else

        h$unsupported(-1, c);
}
function h$base_read(fd, buf, buf_off, n, c) {
                                ;
    var fdo = h$base_fds[fd];
    if(fdo && fdo.read) {
        fdo.read(fd, fdo, buf, buf_off, n, c);
    } else {
        h$errno = 22;
        c(-1);
    }
}
function h$base_stat(file, file_off, stat, stat_off, c) {
                         ;

    if(h$isNode) {
        h$fs.stat(h$decodeUtf8z(file, file_off), function(err, fs) {
            if(err) {
                h$handlErrnoC(err, -1, 0, c);
            } else {
                h$base_fillStat(fs, stat, stat_off);
                c(0);
            }
        });
    } else

        h$unsupported(-1, c);
}
function h$base_umask(mode) {
                                   ;

    if(h$isNode) return process.umask(mode);

    return 0;
}

function h$base_write(fd, buf, buf_off, n, c) {
                                 ;
    var fdo = h$base_fds[fd];
    if(fdo && fdo.write) {
        fdo.write(fd, fdo, buf, buf_off, n, c);
    } else {
        h$errno = 22;
        c(-1);
    }
}

function h$base_ftruncate(fd, pos_1, pos_2, c) {
                              ;

    if(h$isNode) {
        h$fs.ftruncate(fd, goog.math.Long.fromBits(pos_2, pos_1).toNumber(), function(err) {
            h$handleErrnoC(err, -1, 0, c);
        });
    } else

        h$unsupported(-1, c);
}
function h$base_unlink(file, file_off, c) {
                           ;

    if(h$isNode) {
        h$fs.unlink(h$decodeUtf8z(file, file_off), function(err) {
            h$handleErrnoC(err, -1, 0, c);
        });
    } else

        h$unsupported(-1, c);
}
function h$base_getpid() {
                           ;

    if(h$isNode) return process.pid;

    return 0;
}
function h$base_link(file1, file1_off, file2, file2_off, c) {
                         ;

    if(h$isNode) {
        h$fs.link(h$decodeUtf8z(file1, file1_off), h$decodeUtf8z(file2, file2_off), function(err) {
            h$handleErrnoC(err, -1, 0, c);
        });
    } else

        h$unsupported(-1, c);
}
function h$base_mkfifo(file, file_off, mode, c) {
    throw "h$base_mkfifo";
}
function h$base_sigemptyset(sigset, sigset_off) {
    return 0;
    // throw "h$base_sigemptyset";
}
function h$base_sigaddset(sigset, sigset_off, sig) {
    return 0;
    // throw "h$base_sigaddset";
}
function h$base_sigprocmask(sig, sigset1, sigset1_off, sigset2, sigset2_off) {
    return 0;
    // throw "h$base_sigprocmask";
}
function h$base_tcgetattr(attr, termios, termios_off) {
    return 0;
}
function h$base_tcsetattr(attr, val, termios, termios_off) {
    return 0;
}
function h$base_utime(file, file_off, timbuf, timbuf_off, c) {
                          ;

    if(h$isNode) {
        h$fs.fstat(h$decodeUtf8z(file, file_off), function(err, fs) {
            if(err) {
                h$handleErrnoC(err, 0, -1, c); // fixme
            } else {
                var atime = goog.math.Long.fromNumber(fs.atime.getTime());
                var mtime = goog.math.Long.fromNumber(fs.mtime.getTime());
                var ctime = goog.math.Long.fromNumber(fs.ctime.getTime());
                timbuf.i3[0] = atime.getHighBits();
                timbuf.i3[1] = atime.getLowBits();
                timbuf.i3[2] = mtime.getHighBits();
                timbuf.i3[3] = mtime.getLowBits();
                timbuf.i3[4] = ctime.getHighBits();
                timbuf.i3[5] = ctime.getLowBits();
                c(0);
            }
        });
    } else

        h$unsupported(-1, c);
}
function h$base_waitpid(pid, stat, stat_off, options, c) {
    throw "h$base_waitpid";
}
/** @const */ var h$base_o_rdonly = 0x00000;
/** @const */ var h$base_o_wronly = 0x00001;
/** @const */ var h$base_o_rdwr = 0x00002;
/** @const */ var h$base_o_accmode = 0x00003;
/** @const */ var h$base_o_append = 0x00008;
/** @const */ var h$base_o_creat = 0x00200;
/** @const */ var h$base_o_trunc = 0x00400;
/** @const */ var h$base_o_excl = 0x00800;
/** @const */ var h$base_o_noctty = 0x20000;
/** @const */ var h$base_o_nonblock = 0x00004;
/** @const */ var h$base_o_binary = 0x00000;

function h$base_c_s_isreg(mode) {
    return 1;
}
function h$base_c_s_ischr(mode) {
    return 0;
}
function h$base_c_s_isblk(mode) {
    return 0;
}
function h$base_c_s_isdir(mode) {
    return 0; // fixme
}
function h$base_c_s_isfifo(mode) {
    return 0;
}


function h$base_fillStat(fs, b, off) {
    if(off%4) throw "h$base_fillStat: not aligned";
    var o = off>>2;
    b.i3[o+0] = fs.mode;
    var s = goog.math.Long.fromNumber(fs.size);
    b.i3[o+1] = s.getHighBits();
    b.i3[o+2] = s.getLowBits();
    b.i3[o+3] = 0; // fixme
    b.i3[o+4] = 0; // fixme
    b.i3[o+5] = fs.dev;
    var i = goog.math.Long.fromNumber(fs.ino);
    b.i3[o+6] = i.getHighBits();
    b.i3[o+7] = i.getLowBits();
    b.i3[o+8] = fs.uid;
    b.i3[o+9] = fs.gid;
}


// [mode,size1,size2,mtime1,mtime2,dev,ino1,ino2,uid,gid] all 32 bit
/** @const */ var h$base_sizeof_stat = 40;

function h$base_st_mtime(stat, stat_off) {
    { h$ret1 = (stat.i3[(stat_off>>2)+4]); return (stat.i3[(stat_off>>2)+3]); };
}

function h$base_st_size(stat, stat_off) {
    { h$ret1 = (stat.i3[(stat_off>>2)+2]); return (stat.i3[(stat_off>>2)+1]); };
}

function h$base_st_mode(stat, stat_off) {
    return stat.i3[stat_off>>2];
}

function h$base_st_dev(stat, stat_off) {
    return stat.i3[(stat_off>>2)+5];
}

function h$base_st_ino(stat, stat_off) {
    { h$ret1 = (stat.i3[(stat_off>>2)+7]); return (stat.i3[(stat_off>>2)+6]); };
}

/** @const */ var h$base_echo = 1;
/** @const */ var h$base_tcsanow = 2;
/** @const */ var h$base_icanon = 4;
/** @const */ var h$base_vmin = 8;
/** @const */ var h$base_vtime = 16;
/** @const */ var h$base_sigttou = 0;
/** @const */ var h$base_sig_block = 0;
/** @const */ var h$base_sig_setmask = 0;
/** @const */ var h$base_f_getfl = 0;
/** @const */ var h$base_f_setfl = 0;
/** @const */ var h$base_f_setfd = 0;
/** @const */ var h$base_fd_cloexec = 0;
/** @const */ var h$base_sizeof_termios = 4;
/** @const */ var h$base_sizeof_sigset_t = 4;

function h$base_lflag(termios, termios_off) {
    return 0;
}

function h$base_poke_lflag(termios, termios_off, flag) {
    return 0;
}

function h$base_ptr_c_cc(termios, termios_off) {
    { h$ret1 = (0); return (h$newByteArray(8)); };
}

/** @const */ var h$base_default_buffer_size = 32768;

function h$base_c_s_issock(mode) {
    return 0; // fixme
}

/** @const */ var h$base_SEEK_SET = 0;
/** @const */ var h$base_SEEK_CUR = 1;
/** @const */ var h$base_SEEK_END = 2;

function h$base_set_saved_termios(a, b, c) {
    { h$ret1 = (0); return (null); };
}

function h$base_get_saved_termios(r) {
    { h$ret1 = (0); return (null); };
}

// fixme
function h$lockFile(fd, dev, ino, for_writing) {
                              ;
    return 0;
}
function h$unlockFile(fd) {
                                ;
    return 0;
}



// engine-dependent setup
var h$base_readStdin , h$base_writeStderr, h$base_writeStdout;
var h$base_closeStdin = null, h$base_closeStderr = null, h$base_closeStdout = null;
var h$base_readFile, h$base_writeFile, h$base_closeFile;

var h$base_stdin_waiting = new h$Queue();
var h$base_stdin_chunk = { buf: null
                           , pos: 0
                           , processing: false
                           };
var h$base_stdin_eof = false;
var h$base_process_stdin = function() {
    var c = h$base_stdin_chunk;
    var q = h$base_stdin_waiting;
    if(!q.length() || c.processing) return;
    c.processing = true;
    if(!c.buf) { c.pos = 0; c.buf = process.stdin.read(); }
    while(c.buf && q.length()) {
        var x = q.dequeue();
        var n = Math.min(c.buf.length - c.pos, x.n);
        for(var i=0;i<n;i++) {
            x.buf.u8[i+x.off] = c.buf[c.pos+i];
        }
        c.pos += n;
        x.c(n);
        if(c.pos >= c.buf.length) c.buf = null;
        if(!c.buf && q.length()) { c.pos = 0; c.buf = process.stdin.read(); }
    }
    while(h$base_stdin_eof && q.length()) q.dequeue().c(0);
    c.processing = false;
}

if(h$isNode) {
    h$base_closeFile = function(fd, fdo, c) {
        h$fs.close(fd, function(err) {
            delete h$base_fds[fd];
            h$handleErrnoC(err, -1, 0, c);
        });
    }

    h$base_readFile = function(fd, fdo, buf, buf_offset, n, c) {
        var pos = typeof fdo.pos === 'number' ? fdo.pos : null;
                                                                                 ;
        h$fs.read(fd, new Buffer(n), 0, n, pos, function(err, bytesRead, nbuf) {
            if(err) {
                h$setErrno(err);
                c(-1);
            } else {
                for(var i=bytesRead-1;i>=0;i--) buf.u8[buf_offset+i] = nbuf[i];
                if(typeof fdo.pos === 'number') fdo.pos += bytesRead;
                c(bytesRead);
            }
        });
    }

    h$base_readStdin = function(fd, fdo, buf, buf_offset, n, c) {
                              ;
        h$base_stdin_waiting.enqueue({buf: buf, off: buf_offset, n: n, c: c});
        h$base_process_stdin();
    }

    h$base_closeStdin = function(fd, fdo, c) {
                               ;
        // process.stdin.close(); fixme
        c(0);
    }

    h$base_writeFile = function(fd, fdo, buf, buf_offset, n, c) {
        var pos = typeof fdo.pos === 'number' ? fdo.pos : null;
                                                                                  ;
        var nbuf = new Buffer(n);
        for(var i=0;i<n;i++) nbuf[i] = buf.u8[i+buf_offset];
        if(typeof fdo.pos === 'number') fdo.pos += n;
        h$fs.write(fd, nbuf, 0, n, pos, function(err, bytesWritten) {
                                           ;
            if(err) {
                h$setErrno(err);
                if(typeof fdo.pos === 'number') fdo.pos -= n;
                if(h$errno === 35)
                    setTimeout(function() { h$base_writeFile(fd, fdo, buf, buf_offset, n, c); }, 20);
                else c(-1);
            } else {
                if(typeof fdo.pos === 'number') fdo.pos += bytesWritten - n;
                c(bytesWritten);
            }
        });
    }

    h$base_writeStdout = function(fd, fdo, buf, buf_offset, n, c) {
                                ;
        h$base_writeFile(1, fdo, buf, buf_offset, n, c);
    }

    h$base_closeStdout = function(fd, fdo, c) {
                                ;
 // not actually closed, fixme?
        c(0);
    }

    h$base_writeStderr = function(fd, fdo, buf, buf_offset, n, c) {
                                ;
        h$base_writeFile(2, fdo, buf, buf_offset, n, c);
    }

    h$base_closeStderr = function(fd, fdo, c) {
                                ;
 // not actually closed, fixme?
        c(0);
    }

    process.stdin.on('readable', h$base_process_stdin);
    process.stdin.on('end', function() { h$base_stdin_eof = true; h$base_process_stdin(); });

} else if (h$isJsShell) {
    h$base_readStdin = function(fd, fdo, buf, buf_offset, n, c) {
        c(0);
    }
    h$base_writeStdout = function(fd, fdo, buf, buf_offset, n, c) {
        putstr(h$decodeUtf8(buf, n, buf_offset));
        c(n);
    }
    h$base_writeStderr = function(fd, fdo, buf, buf_offset, n, c) {
        printErr(h$decodeUtf8(buf, n, buf_offset));
        c(n);
    }
} else if(h$isJsCore) {
    h$base_readStdin = function(fd, fdo, buf, buf_offset, n, c) {
 c(0);
    }
    var h$base_stdoutLeftover = { f: print, val: null };
    var h$base_stderrLeftover = { f: debug, val: null };
    var h$base_writeWithLeftover = function(buf, n, buf_offset, c, lo) {
 var lines = h$decodeUtf8(buf, n, buf_offset).split(/\r?\n/);
 if(lines.length === 1) {
     if(lines[0].length) {
  if(lo.val !== null) lo.val += lines[0];
  else lo.val = lines[0];
     }
 } else {
            lo.f(((lo.val !== null) ? lo.val : '') + lines[0]);
     for(var i=1;i<lines.length-1;i++) lo.f(lines[i]);
     if(lines[lines.length-1].length) lo.val = lines[lines.length-1];
     else lo.val = null;
 }
 c(n);
    }
    h$base_writeStdout = function(fd, fdo, buf, buf_offset, n, c) {
 h$base_writeWithLeftover(buf, n, buf_offset, c, h$base_stdoutLeftover);
    }
    h$base_writeStderr = function(fd, fdo, buf, buf_offset, n, c) {
 // writing to stderr not supported, write to stdout
 h$base_writeWithLeftover(buf, n, buf_offset, c, h$base_stderrLeftover);
    }
} else { // browser / fallback

    h$base_readStdin = function(fd, fdo, buf, buf_offset, n, c) {
        c(0);
    }
    h$base_writeStdout = function(fd, fdo, buf, buf_offset, n, c) {
        console.log(h$decodeUtf8(buf, n, buf_offset));
        c(n);
    }
    h$base_writeStderr = function(fd, fdo, buf, buf_offset, n, c) {
        console.log(h$decodeUtf8(buf, n, buf_offset));
        c(n);
    }

}


var h$base_stdin_fd = { read: h$base_readStdin, close: h$base_closeStdin };
var h$base_stdout_fd = { write: h$base_writeStdout, close: h$base_closeStdout };
var h$base_stderr_fd = { write: h$base_writeStderr, close: h$base_closeStderr };

var h$base_fdN = -1; // negative file descriptors are 'virtual'
var h$base_fds = [h$base_stdin_fd, h$base_stdout_fd, h$base_stderr_fd];

function h$shutdownHaskellAndExit(code, fast) {






    h$exitProcess(code);
}

// RAND_MAX = 32767
function h$rand() {
  return (32768 * Math.random()) & 32767;
}
function h$get_current_timezone_seconds(t, pdst_v, pdst_o, pname_v, pname_o) {
    var d = new Date(t * 1000);
    var now = new Date();
    var jan = new Date(now.getFullYear(),0,1);
    var jul = new Date(now.getFullYear(),6,1);
    var stdOff = Math.max(jan.getTimezoneOffset(), jul.getTimezoneOffset());
    var isDst = d.getTimezoneOffset() < stdOff;
    var tzo = d.getTimezoneOffset();
    pdst_v.dv.setInt32(pdst_o, isDst ? 1 : 0, true);
    if(!pname_v.arr) pname_v.arr = [];
    var offstr = tzo < 0 ? ('+' + (tzo/-60)) : ('' + (tzo/-60));
    pname_v.arr[pname_o] = [h$encodeUtf8("UTC" + offstr), 0];
    return (-60*tzo)|0;
}

function h$clock_gettime(when, p_d, p_o) {
/*  h$log("clock_gettime");
  h$log(when);
  h$log(p_d);
  h$log(p_o); */

  var o = p_o >> 2,
      t = Date.now ? Date.now() : new Date().getTime(),
      tf = Math.floor(t / 1000),
      tn = 1000000 * (t - (1000 * tf));
  p_d.i3[o] = tf|0;
  p_d.i3[o+1] = tn|0;
  return 0;
}






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

function h$_hs_text_memcpy(dst_v,dst_o2,src_v,src_o2,n) {
  return h$memcpy(dst_v,2*dst_o2,src_v,2*src_o2,2*n);
}

function h$_hs_text_memcmp(a_v,a_o2,b_v,b_o2,n) {
  return h$memcmp(a_v,2*a_o2,b_v,2*b_o2,2*n);
}

// decoder below adapted from cbits/cbits.c in the text package




var h$_text_utf8d =
   [
  /*
   * The first part of the table maps bytes to character classes that
   * to reduce the size of the transition table and create bitmasks.
   */
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
   7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7, 7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
   8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2, 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
  10,3,3,3,3,3,3,3,3,3,3,3,3,4,3,3, 11,6,6,6,5,8,8,8,8,8,8,8,8,8,8,8,

  /*
   * The second part is a transition table that maps a combination of
   * a state of the automaton and a character class to a state.
   */
   0,12,24,36,60,96,84,12,12,12,48,72, 12,12,12,12,12,12,12,12,12,12,12,12,
  12, 0,12,12,12,12,12, 0,12, 0,12,12, 12,24,12,12,12,12,12,24,12,24,12,12,
  12,12,12,12,12,12,12,24,12,12,12,12, 12,24,12,12,12,12,12,12,12,24,12,12,
  12,12,12,12,12,12,12,36,12,36,12,12, 12,36,12,12,12,12,12,36,12,36,12,12,
  12,36,12,12,12,12,12,12,12,12,12,12];

/*
 * A best-effort decoder. Runs until it hits either end of input or
 * the start of an invalid byte sequence.
 *
 * At exit, updates *destoff with the next offset to write to, and
 * returns the next source offset to read from.
 */

function h$_hs_text_decode_utf8_internal ( dest_v
                                         , destoff_v, destoff_o
                                         , src_v, src_o
                                         , src_end_v, src_end_o
                                         , s
                                         ) {
  if(src_v === null || src_end_v === null) {
    { h$ret1 = (src_end_o); return (null); };
  }
  var dsto = destoff_v.dv.getUint32(destoff_o,true) << 1;
  var srco = src_o;
  var state = s.state;
  var codepoint = s.codepoint;
  var ddv = dest_v.dv;
  var sdv = src_v.dv;

  function decode(b) {
    var type = h$_text_utf8d[b];
    codepoint = (state !== 0) ?
      (b & 0x3f) | (codepoint << 6) :
      (0xff >>> type) & b;
    state = h$_text_utf8d[256 + state + type];
    return state;
  }

  while (srco < src_end_o) {
    if(decode(sdv.getUint8(srco++)) !== 0) {
      if(state !== 12) {
        continue;
      } else {
        break;
      }
    }
    if (codepoint <= 0xffff) {
      ddv.setUint16(dsto,codepoint,true);
      dsto += 2;
    } else {
      ddv.setUint16(dsto,(0xD7C0 + (codepoint >>> 10)),true);
      ddv.setUint16(dsto+2,(0xDC00 + (codepoint & 0x3FF)),true);
      dsto += 4;
    }
    s.last = srco;
  }

  s.state = state;
  s.codepoint = codepoint;
  destoff_v.dv.setUint32(destoff_o,dsto>>1,true);
  { h$ret1 = (srco); return (src_v); };
}

function h$_hs_text_decode_utf8_state( dest_v
                                     , destoff_v, destoff_o
                                     , src_v, src_o
                                     , srcend_v, srcend_o
                                     , codepoint0_v, codepoint0_o
                                     , state0_v, state0_o
                                     ) {
  var s = { state: state0_v.dv.getUint32(state0_o, true)
          , codepoint: codepoint0_v.dv.getUint32(codepoint0_o, true)
          , last: src_o
          };
  var ret, ret1;
  { (ret) = (h$_hs_text_decode_utf8_internal ( dest_v , destoff_v, destoff_o , src_v.arr[src_o][0], src_v.arr[src_o][1] , srcend_v, srcend_o , s )); (ret1) = h$ret1; };







  src_v.arr[src_o][1] = s.last;
  state0_v.dv.setUint32(state0_o, s.state, true);
  codepoint0_v.dv.setUint32(codepoint0_o, s.codepoint, true);
  if(s.state === 12) ret1--;
  { h$ret1 = (ret1); return (ret); };
}

function h$_hs_text_decode_utf8( dest_v
                               , destoff_v, destoff_o
                               , src_v, src_o
                               , srcend_v, srcend_o
                               ) {
  /* Back up if we have an incomplete or invalid encoding */
  var s = { state: 0
          , codepoint: 0
          , last: src_o
          };
  var ret, ret1;
  { (ret) = (h$_hs_text_decode_utf8_internal ( dest_v , destoff_v, destoff_o , src_v, src_o , srcend_v, srcend_o , s )); (ret1) = h$ret1; };







  if (s.state !== 0) ret1--;
  { h$ret1 = (ret1); return (ret); };
}


/*
 * The ISO 8859-1 (aka latin-1) code points correspond exactly to the first 256 unicode
 * code-points, therefore we can trivially convert from a latin-1 encoded bytestring to
 * an UTF16 array
 */
function h$_hs_text_decode_latin1(dest_d, src_d, src_o, srcend_d, srcend_o) {
  var p = src_o;
  var d = 0;
  var su8 = src_d.u8;
  var su3 = src_d.u3;
  var du1 = dest_d.u1;

  // consume unaligned prefix
  while(p != srcend_o && p & 3) {
    du1[d++] = su8[p++];
  }

  // iterate over 32-bit aligned loads
  if(su3) {
    while (p < srcend_o - 3) {
      var w = su3[p>>2];
      du1[d++] = w & 0xff;
      du1[d++] = (w >>> 8) & 0xff;
      du1[d++] = (w >>> 16) & 0xff;
      du1[d++] = (w >>> 32) & 0xff;
      p += 4;
    }
  }

  // handle unaligned suffix
  while (p != srcend_o)
    du1[d++] = su8[p++];
}

function h$_hs_text_encode_utf8(destp_v, destp_o, src_v, srcoff, srclen) {
  var dest_v = destp_v.arr[destp_o][0];
  var dest_o = destp_v.arr[destp_o][1];
  var src = srcoff;
  var dest = dest_o;
  var srcend = src + srclen;
  var srcu1 = src_v.u1;
  if(!srcu1) throw "h$_hs_text_encode_utf8: invalid alignment for source";
  var srcu3 = src_v.u3;
  var destu8 = dest_v.u8;
  while(src < srcend) {
    // run of (aligned) ascii characters
    while(srcu3 && !(src & 1) && srcend - src >= 2) {
      var w = srcu3[src>>1];
      if(w & 0xFF80FF80) break;
      destu8[dest++] = w & 0xFFFF;
      destu8[dest++] = w >>> 16;
      src += 2;
    }
    while(src < srcend) {
      var w = srcu1[src++];
      if(w <= 0x7F) {
        destu8[dest++] = w;
        break; // go back to a stream of ASCII
      } else if(w <= 0x7FF) {
        destu8[dest++] = (w >> 6) | 0xC0;
        destu8[dest++] = (w & 0x3f) | 0x80;
      } else if(w < 0xD800 || w > 0xDBFF) {
        destu8[dest++] = (w >>> 12) | 0xE0;
        destu8[dest++] = ((w >> 6) & 0x3F) | 0x80;
        destu8[dest++] = (w & 0x3F) | 0x80;
      } else {
        var c = ((w - 0xD800) << 10) + (srcu1[src++] - 0xDC00) + 0x10000;
        destu8[dest++] = (c >>> 18) | 0xF0;
        destu8[dest++] = ((c >> 12) & 0x3F) | 0x80;
        destu8[dest++] = ((c >> 6) & 0x3F) | 0x80;
        destu8[dest++] = (c & 0x3F) | 0x80;
      }
    }
  }
  destp_v.arr[destp_o][1] = dest;
}
/* FNV-1 hash
 *
 * The FNV-1 hash description: http://isthe.com/chongo/tech/comp/fnv/
 * The FNV-1 hash is public domain: http://isthe.com/chongo/tech/comp/fnv/#public_domain
 */
function h$hashable_fnv_hash_offset(str_a, o, len, hash) {
  return h$hashable_fnv_hash(str_a, o, len, hash);
}

function h$hashable_fnv_hash(str_d, str_o, len, hash) {
  if(len > 0) {
    var d = str_d.u8;
    for(var i=0;i<len;i++) {
      hash = h$mulInt32(hash, 16777619) ^ d[str_o+i];
    }
  }
  return hash;
}


// int hashable_getRandomBytes(unsigned char *dest, int nbytes)
function h$hashable_getRandomBytes(dest_d, dest_o, len) {
  if(len > 0) {
    var d = dest_d.u8;
    for(var i=0;i<len;i++) {
      d[dest_o+i] = Math.floor(Math.random() * 256);
    }
  }
  return len;
}






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

// JS Objects stuff

function h$isFloat (n) {
  return n===+n && n!==(n|0);
}

function h$isInteger (n) {
  return n===+n && n===(n|0);
}

/*
        -- 0 - null, 1 - integer,
        -- 2 - float, 3 - bool,
        -- 4 - string, 5 - array
        -- 6 - object
*/
function h$typeOf(o) {
    if (!(o instanceof Object)) {
        if (o == null) {
            return 0;
        } else if (typeof o == 'number') {
            if (h$isInteger(o)) {
                return 1;
            } else {
                return 2;
            }
        } else if (typeof o == 'boolean') {
            return 3;
        } else {
            return 4;
        }
    } else {
        if (Object.prototype.toString.call(o) == '[object Array]') {
            // it's an array
            return 5;
        } else if (!o) {
            // null 
            return 0;
        } else {
            // it's an object
            return 6;
        }
    }
}

function h$listProps(o) {
    if (!(o instanceof Object)) {
        return [];
    }
    var l = [], i = 0;
    for (var prop in o) {
        l[i++] = prop;
    }
    return l;
}

function h$flattenObj(o) {
    var l = [], i = 0;
    for (var prop in o) {
        l[i++] = [prop, o[prop]];
    }
    return l;
}

/*

  build an object from key/value pairs:
    var obj = h$buildObject(key1, val1, key2, val2, ...);

  note: magic name:
    invocations of this function are replaced by object literals wherever
    possible

 */
function h$buildObject() {
    var r = {}, l = arguments.length;
    for(var i = 0; i < l; i += 2) {
        var k = arguments[i], v = arguments[i+1];
        r[k] = v;
    }
    return r;
}

// same as above, but from a list: [k1,v1,k2,v2,...]
function h$buildObjectFromList(xs) {
    var r = {}, k, v, t;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
        xs = ((xs).d2);
        t = ((xs).d2);
        if(((t).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
            k = ((xs).d1);
            v = ((t).d1);
            xs = ((t).d2);
            r[k] = v;
        } else {
            return r;
        }
    }
    return r;
}

// same as above, but from a list of tuples [(k1,v1),(k2,v2),...]
function h$buildObjectFromTupList(xs) {
    var r = {};
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 var h = ((xs).d1);
 xs = ((xs).d2);
 r[((((h).d1)).d1)] = ((((h).d2)).d1);
    }
    return r;
}






// values defined in Gen2.ClosureInfo







// thread status

/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal







// GHCJS.Prim.JSException





// Exception dictionary for JSException


// SomeException






// GHC.Ptr.Ptr






// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe




// #define HS_NOTHING h$nothing






// Data.List
// Data.Text




// Data.Text.Lazy





// black holes
// can we skip the indirection for black holes?






// resumable thunks


// general deconstruction



// retrieve  a numeric value that's possibly stored as an indirection



// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;

// translated from bytestring cbits/fpstring.c

function h$fps_reverse(a_v, a_o, b_v, b_o, n) {
    if(n > 0) {
        var au8 = a_v.u8, bu8 = b_v.u8;
        for(var i=0;i<n;i++) {
            au8[a_o+n-i-1] = bu8[b_o+i];
        }
    }
}

function h$fps_intersperse(a_v,a_o,b_v,b_o,n,c) {
    if(n > 0) {
        var au8 = a_v.u8, bu8 = b_v.u8, dst_o = a_o;
        for(var i=0;i<n-1;i++) {
            au8[dst_o] = bu8[b_o+i];
            au8[dst_o+1] = c;
            dst_o += 2;
        }
        au8[dst_o] = bu8[b_o+n-1];
    }
}

function h$fps_maximum(a_v,a_o,n) {
    if(n > 0) {
        var au8 = a_v.u8, max = au8[a_o];
        for(var i=1;i<n;i++) {
            var c = au8[a_o+i];
            if(c > max) { max = c; }
        }
        return max;
    }
    return 0;
}

function h$fps_minimum(a_v,a_o,n) {
    if(n > 0) {
        var au8 = a_v.u8, min = a_v.u8[a_o];
        for(var i=1;i<n;i++) {
            var c = au8[a_o+i];
            if(c < min) { min = c; }
        }
        return min;
    }
    return 255;
}

function h$fps_count(a_v,a_o,n,c) {
    if(n > 0) {
        var au8 = a_v.u8, count = 0;
        for(var i=0;i<n;i++) {
            if(au8[a_o+i] === c) { count++; }
        }
        return count|0;
    }
    return 0;
}

function h$fps_memcpy_offsets(dst_d, dst_o, dst_off
                              , src_d, src_o, src_off, n) {
    return memcpy(dst_d, dst_o + dst_off, src_d, src_o + src_off, n);
}

// translated from bytestring cbits/itoa.c

var h$_hs_bytestring_digits = [48,49,50,51,52,53,54,55,56,57,97,98,99,100,101,102]; // 0123456789abcdef
var h$_hs_bytestring_l10 = goog.math.Long.fromBits(10, 0);

// signed integers
function h$_hs_bytestring_int_dec(x, buf_d, buf_o) {
    var c, ptr = buf_o, next_free, x_tmp;
    var bu8 = buf_d.u8;
    // we cannot negate directly as  0 - (minBound :: Int) = minBound
    if(x < 0) {
        bu8[ptr++] = 45; // '-'
        buf_o++;
        x_tmp = x;
        x = (x / 10) | 0;
        bu8[ptr++] = h$_hs_bytestring_digits[x * 10 - x_tmp];
        if(x === 0) {
            { h$ret1 = (ptr); return (buf_d); };
        } else {
            x = -x;
        }
    }

    // encode positive number as little-endian decimal
    do {
        x_tmp = x;
        x = (x / 10) | 0;
        bu8[ptr++] = h$_hs_bytestring_digits[x_tmp - x * 10];
    } while (x);

    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}

// signed long long ints (64 bit integers)
function h$_hs_bytestring_long_long_int_dec(x_a, x_b, buf_d, buf_o) {
    var l10 = h$_hs_bytestring_l10;
    var x = goog.math.Long.fromBits(x_b, x_a);
    var c, ptr = buf_o, next_free;
    var bu8 = buf_d.u8;

    // we cannot negate directly as  0 - (minBound :: Int) = minBound
    if(x.isNegative()) {
        bu8[ptr++] = 45; // '-';
        buf_o++;
        x_tmp = x;
        x = x.div(l10);
        bu8[ptr++] = h$_hs_bytestring_digits[x.multiply(l10).subtract(x_tmp).getLowBits()];
        if(x.isZero()) {
            { h$ret1 = (ptr); return (buf_d); };
        } else {
            x = x.negate();
        }
    }

    // encode positive number as little-endian decimal
    do {
        x_tmp = x;
        x = x.div(l10);
        bu8[ptr++] = h$_hs_bytestring_digits[x_tmp.subtract(x.multiply(l10))];
    } while (!x.isZero());

    // reverse written digits
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}

// unsigned integers
function h$_hs_bytestring_uint_dec(x, buf_d, buf_o) {
    var c, ptr = buf_o, next_free;
    var bu8 = buf_d.u8;
    var x_tmp;

    if(x < 0) x += 4294967296;

    do {
        x_tmp = x;
        x = (x / 10) | 0;
        bu8[ptr++] = h$_hs_bytestring_digits[x_tmp - x * 10];
    } while(x);
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}

function h$_hs_bytestring_long_long_uint_dec(x_a, x_b, buf_d, buf_o) {
    var c, ptr = buf_o, next_free;
    var bu8 = buf_d.u8;
    var x = h$ghcjsbn_mkBigNat_ww(x_a, x_b), q = [], r = [];

    // encode positive number as little-endian decimal
    do {
        h$ghcjsbn_quotRem_bw(q, r, x, 10);
        x = q;
        bu8[ptr++] = h$_hs_bytestring_digits[h$ghcjsbn_toInt_b(r)];
    } while(!h$ghcjsbn_isZero_b(x));

    // reverse written digits;
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}

// Padded, decimal, positive integers for the decimal output of bignums
///////////////////////////////////////////////////////////////////////

// Padded (9 digits), decimal, positive int:
// We will use it with numbers that fit in 31 bits; i.e., numbers smaller than
// 10^9, as "31 * log 2 / log 10 = 9.33"

function h$_hs_bytestring_int_dec_padded9(x, buf_d, buf_o) {
    var max_width_int32_dec = 9;
    var ptr = buf_o + max_width_int32_dec;
    var bu8 = buf_d.u8;
    var x_tmp;

    // encode positive number as little-endian decimal
    do {
        x_tmp = x;
        x = (x / 10) | 0;
        bu8[--ptr] = h$_hs_bytestring_digits[x_tmp - x * 10];
    } while(x);

    // pad beginning
    while (buf_o < ptr) { bu8[--ptr] = 48; }
}

// Padded (19 digits), decimal, positive long long int:
// We will use it with numbers that fit in 63 bits; i.e., numbers smaller than
// 10^18, as "63 * log 2 / log 10 = 18.96"
function h$_hs_bytestring_long_long_int_dec_padded18(x_a, x_b, buf_d, buf_o) {
    var l10 = h$_hs_bytestring_l10;
    var max_width_int64_dec = 18;
    var ptr = buf_o + max_width_int64_dec;
    var bu8 = buf_d.u8;
    var x = goog.math.Long.fromBits(x_b, x_a);

    // encode positive number as little-endian decimal
    do {
        x_tmp = x;
        x = x.div(l10);
        bu8[--ptr] = h$_hs_bytestring_digits[x_tmp.subtract(x.multiply(l10))];
    } while (!x.isZero());

    // pad beginning
    while (buf_o < ptr) { bu8[--ptr] = 48; }
}

///////////////////////
// Hexadecimal encoding
///////////////////////

// unsigned ints (32 bit words)
function h$_hs_bytestring_uint_hex(x, buf_d, buf_o) {
    var c, ptr = buf_o, next_free;
    var bu8 = buf_d.u8;
    // write hex representation in reverse order
    do {
        bu8[ptr++] = h$_hs_bytestring_digits[x & 0xf];
        x >>>= 4;
    } while(x);

    // invert written digits
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}

// unsigned long ints (64 bit words)
function h$_hs_bytestring_long_long_uint_hex(x_a, x_b, buf_d, buf_o) {
    // write hex representation in reverse order
    var c, ptr = buf_o, next_free;
    var bu8 = buf_d.u8;
    if(x_a === 0 && x_b === 0) {
        bu8[ptr++] = 48; // '0'
    } else {
        while(x_b !== 0) {
            bu8[ptr++] = h$_hs_bytestring_digits[x_b & 0xf];
            x_b >>>= 4;
        }
        while(x_a !== 0) {
            bu8[ptr++] = h$_hs_bytestring_digits[x_a & 0xf];
            x_a >>>= 4;
        }
    }

    // invert written digits
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}
