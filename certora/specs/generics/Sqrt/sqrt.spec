//Run:
// https://prover.certora.com/output/41958/d3526e380eca4c4bcbac/?anonymousKey=b140bf85befd4faebbe37ded85ea064ddc1daa73

rule sqrtRule0() {
    assert 
    mySqrt(1) == 1 &&
    mySqrt(4) == 2 &&
    mySqrt(9) == 3 &&
    mySqrt(16) == 4 &&
    mySqrt(25) == 5 &&
    mySqrt(36) == 6 &&
    mySqrt(100) == 10 &&
    mySqrt(2500) == 50 &&
    mySqrt(10^12) == 10^6; 
}

// Weak monotonicity
rule sqrtRule1(uint256 x, uint256 y) {
    assert x > y => mySqrt(x) >= mySqrt(y);
}

// sqrt(4*x) = 2*sqrt(x) > sqrt(x)
rule sqrtRule2(uint256 x) {
    assert (x != 0 && 4*x <= max_uint) => mySqrt(to_uint256(4*x)) > mySqrt(x);
}

// squre of sqrt is identity (fails)
rule sqrtRule3(uint256 x){
    assert mySqrt(x)*mySqrt(x) == x;
}

// Multiplicative (fails)
rule sqrtRule4(uint256 x, uint256 y){
    require x*y <= max_uint;
    assert mySqrt(x)*mySqrt(y) == mySqrt(to_uint256(x*y));
}

// sqrt of squre is identity (verified)
rule sqrtRule5(uint256 x, uint256 x2){
    require x*x == x2;
    assert mySqrt(x2) == x && mySqrt(x2)*mySqrt(x2) == x2;
}

// sqrt(x) < x
rule sqrtRule6(uint256 x)
{
    assert x>1 => mySqrt(x) < x;
}

// Summary
function mySqrt(uint256 x) returns uint256 {
    mathint SQRT;
    require SQRT*SQRT <= x && (SQRT + 1)*(SQRT + 1) > x;
    return to_uint256(SQRT);
}
