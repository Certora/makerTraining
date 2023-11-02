import "./erc20.spec";
import "./sanity.spec";


using Vat as vatInst;


methods {
    function ilks(bytes32) external returns(uint256, uint256) envfree;
    function wards(address) external returns(uint256) envfree;
    function isWard(address) external returns(bool) envfree;
    function vat() external returns(address) envfree;
    function vatInst.ilks(bytes32) external returns(uint256, uint256, uint256, uint256, uint256) envfree;
    function call_rpow(uint x, uint n, uint b) external  returns (uint) envfree;
}


definition RAY_CVL() returns uint256 = 10^27;


/* A vacous rule - a rule that is verified because no state reachs the assert  */
rule vacuity(uint x, uint y) {

    require( x > y && y > x); 

    assert x == 5;

}

/* vacous due to the setup - linking to vat */ 
rule changeVat(method f) {
    address vat_before = vat(); 

    env e;
    calldataarg args;
    f(e,args);

    assert vat() == vat_before;

}


/* a rule that is true regardless of the functions */ 
invariant tutology(address w) 
        wards(w) >= 1 <=> isWard(w); 




rule anotherTutology(address w, method f) {
    uint256 x; uint256 y;

    require  x !=y ;
    require  wards(w) == x;

    env e;
    calldataarg args;
    f(e,args);

    assert (wards(w)  != x || wards(w) != y);

}

rule limitedScope(uint x, uint n, uint b) {

    assert n==0 => call_rpow(x, n, b) >= b;
}


use rule sanity;

// verified (if duty >= RAY, vat.rate can't be dropped)
// https://prover.certora.com/output/3106/dd9bfee54c8a41d5a55986075588c3a1/?anonymousKey=32e938c057d6ab8c3eb575d2ea81ff7858d36862
rule rateCheckUpgrade(env e) {
    bytes32 ilk;
    uint256 duty;
    uint256 rateBefore;
    duty, _ = ilks(ilk);
    _, rateBefore, _, _, _ = vatInst.ilks(ilk);
    require rateBefore > 0;  //is this reduandant 
    require duty >= RAY_CVL();

    drip(e, ilk);

    uint256 rateAfter;
    _, rateAfter, _, _, _ = vatInst.ilks(ilk);

    assert rateBefore <= rateAfter, "Remember, with great power comes great responsibility.";
}

// STATUS - verified: https://prover.certora.com/output/3106/b26269a207b443ae8d960dee7ec4a7c0/?anonymousKey=cc823d0d2e9d515a4e043b422f92fececa695c54
// Only deny() / rely() can change ward's status
rule onlyDenyRelyCanChange(method f, env e) {
    address ward;
    uint256 wardsStatusBefore = wards(ward);
    
    calldataarg args;
    f(e, args);
    uint256 wardsStatusAfter = wards(ward);
    assert wardsStatusBefore == 0 && wardsStatusAfter == 1 
            => f.selector == sig:rely(address).selector;
    assert wardsStatusBefore == 1 && wardsStatusAfter == 0 
            => f.selector == sig:deny(address).selector;
}
// STATUS - verified: https://prover.certora.com/output/3106/5230a21bd8bd4dde8245df2fd720d7d8/?anonymousKey=85afe3355243eb49d5797babca0c50738a5326e2
// Ward's status change is possible in both ways
rule bothWays(method f, env e) {
    address ward;
    uint256 wardsStatusBefore = wards(ward);
    
    calldataarg args;
    f(e, args);
    uint256 wardsStatusAfter = wards(ward);
    satisfy wardsStatusBefore == 0 => wardsStatusAfter == 1;
    satisfy wardsStatusBefore == 1 => wardsStatusAfter == 0;
}
// STATUS - verified: https://prover.certora.com/output/3106/dc9cf3cbba434094bf5c300651916535/?anonymousKey=d52c12ef9147ea17d62ea5dc562b3e8a84d3d1ae
// Only wards can change ward's status
rule privilege(method f, env e) {
    address ward;
    uint256 wardsStatusBefore = wards(ward);
    uint256 senderStatusBefore = wards(e.msg.sender);
    
    calldataarg args;
    f(e, args);
    uint256 wardsStatusAfter = wards(ward);
    assert wardsStatusBefore != wardsStatusAfter 
            => senderStatusBefore == 1;
}


rule privilegeAdvance(method f, env e) {
    address ward;
    uint256 wardsStatusBefore = wards(ward);
    uint256 senderStatusBefore = wards(e.msg.sender);
    
    calldataarg args;
    f(e, args);
    uint256 wardsStatusAfter = wards(ward);
    assert wardsStatusBefore != wardsStatusAfter 
            => ( senderStatusBefore == 1 || senderStatusBefore != 1);
}

/*  add to understnad reachbilit issue */ 
rule understadingSanity() {
    calldataarg args;
    env e;
    initVat(e,args); 
    assert false; 
}