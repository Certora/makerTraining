import "./erc20.spec";
import "./sanity.spec";



methods {
    function debt() external returns (uint256) envfree;
    function vice() external returns (uint256) envfree;
    function gem(bytes32, address) external returns (uint256) envfree;
    function Art(bytes32) external returns (uint256) envfree;
    function rate(bytes32) external returns (uint256) envfree;
    function line(bytes32) external returns (uint256) envfree;
    function dust(bytes32) external returns (uint256) envfree;
    function spot(bytes32) external returns (uint256) envfree;
    function ink(bytes32, address) external returns (uint256) envfree;
    function art(bytes32, address) external returns (uint256) envfree;
    function wards(address) external returns(uint256) envfree;
}


use rule sanity;


//////////////////////////////////////////////
//                  DAY 1                   //
//////////////////////////////////////////////


// flux() correctly updates src and dst balances
// https://prover.certora.com/output/3106/d51c81c74c9c46d9950805ba3377d3fd/?anonymousKey=16d7a71ac4b003981cc7a96aa4718c46b57f99db
rule integrityOfFlux(env e) {
    bytes32 ilk; 
    address src; 
    address dst; 
    uint256 wad;

    uint256 srcGemBefore = gem(ilk, src);
    uint256 dstGemBefore = gem(ilk, dst);

    flux(e, ilk, src, dst, wad);

    uint256 srcGemAfter = gem(ilk, src);
    uint256 dstGemAfter = gem(ilk, dst);

    assert to_mathint(srcGemBefore) == srcGemAfter + wad;
    assert to_mathint(dstGemBefore) == dstGemAfter - wad;
}


https://prover.certora.com/output/3106/0610dd8b16114524b9f3762bf36777b9/?anonymousKey=7d0b09d73bdfa5749d99288cc88a3ffdb46357f8
rule integrityOfFluxUpgrade(env e) {
    bytes32 ilk; 
    address src; 
    address dst; 
    uint256 wad;

    uint256 srcGemBefore = gem(ilk, src);
    uint256 dstGemBefore = gem(ilk, dst);

    require src != dst;

    flux(e, ilk, src, dst, wad);

    uint256 srcGemAfter = gem(ilk, src);
    uint256 dstGemAfter = gem(ilk, dst);

    assert to_mathint(srcGemBefore) == srcGemAfter + wad;
    assert to_mathint(dstGemBefore) == dstGemAfter - wad;
}


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
