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



// https://prover.certora.com/output/3106/fa72e64a089242eb8a93371eb48ba2c5/?anonymousKey=00e8b2a0fd5339e8165a1aff197501cabd8e9db0
use rule sanity;



///////////////////////////////////////////////////
/////             Ghosts and Hooks            /////
///////////////////////////////////////////////////


ghost mapping(bytes32 => mathint) urnsArtSum {
    init_state axiom forall bytes32 a. urnsArtSum[a] == 0;
}

hook Sload uint256 value urns[KEY bytes32 ilkID][KEY address urnAddr].art STORAGE {
    require urnsArtSum[ilkID] >= to_mathint(value);
}

hook Sstore urns[KEY bytes32 ilkID][KEY address urnAddr].art uint256 value
    (uint256 old_value) STORAGE
{
    urnsArtSum[ilkID] = urnsArtSum[ilkID] + value - old_value;
}



ghost mapping(bytes32 => mathint) urnsInkSum {
    init_state axiom forall bytes32 a. urnsInkSum[a] == 0;
}

hook Sload uint256 value urns[KEY bytes32 ilkID][KEY address urnAddr].ink STORAGE {
    require urnsInkSum[ilkID] >= to_mathint(value);
}

hook Sstore urns[KEY bytes32 ilkID][KEY address urnAddr].ink uint256 value
    (uint256 old_value) STORAGE
{
    urnsInkSum[ilkID] = urnsInkSum[ilkID] + value - old_value;
}



ghost mathint daiSum {
    init_state axiom daiSum == 0;
}

hook Sload uint256 value dai[KEY address user] STORAGE {
    require daiSum >= to_mathint(value);
}

hook Sstore dai[KEY address user] uint256 value
    (uint256 old_value) STORAGE
{
    daiSum = daiSum + value - old_value;
}



ghost mathint sumOfSins {
    init_state axiom sumOfSins == 0;
}

hook Sload uint256 value sin[KEY address user] STORAGE {
    require sumOfSins >= to_mathint(value);
}

hook Sstore sin[KEY address user] uint256 value
    (uint256 old_value) STORAGE
{
    sumOfSins = sumOfSins + value - old_value;
}



ghost mapping(bytes32 => uint256) rateGhost {
    init_state axiom forall bytes32 a. rateGhost[a] == 0;
}

hook Sload uint256 value ilks[KEY bytes32 ilkID].rate STORAGE {
    require rateGhost[ilkID] == value;
    require productGhost >= value * ArtGhost[ilkID];
}

hook Sstore ilks[KEY bytes32 ilkID].rate uint256 value 
    (uint256 old_value) STORAGE {
    rateGhost[ilkID] = value;
    productGhost = productGhost + ((value - old_value) * ArtGhost[ilkID]);
}



ghost mapping(bytes32 => uint256) ArtGhost {
    init_state axiom forall bytes32 a. ArtGhost[a] == 0;
}

hook Sload uint256 value ilks[KEY bytes32 ilkID].Art STORAGE {
    require ArtGhost[ilkID] == value;
    require productGhost >= rateGhost[ilkID] * value;
}

hook Sstore ilks[KEY bytes32 ilkID].Art uint256 value 
    (uint256 old_value) STORAGE {
    ArtGhost[ilkID] = value;
    productGhost = productGhost + ((value - old_value) * rateGhost[ilkID]);
}



ghost mathint productGhost {
    init_state axiom productGhost == 0;
}


ghost mapping(bytes32 => mathint) gemSumPerIlk {
    init_state axiom forall bytes32 a. gemSumPerIlk[a] == 0;
}

hook Sload uint256 value gem[KEY bytes32 ilkID][KEY address user] STORAGE {
    require gemSumPerIlk[ilkID] >= to_mathint(value);
}

hook Sstore gem[KEY bytes32 ilkID][KEY address user] uint256 value 
    (uint256 old_value) STORAGE {
    gemSumPerIlk[ilkID] = gemSumPerIlk[ilkID] + value - old_value;
}



// ///////////////////////////////////////////////////
// /////        Functions and Definitions        /////
// ///////////////////////////////////////////////////


// definition excludeMethods(method f) returns bool =
//     f.selector != sig:upgradeTo(address).selector
//     && f.selector != sig:upgradeToAndCall(address,bytes).selector;


// definition WAD() returns uint256 = 10^18;
// definition RAY_CVL() returns uint256 = 10^27;
// definition RAD() returns uint256 = 10^45;


// function validState(bytes32 ilkID) {
//     requireInvariant artsCorrelations(ilkID);
//     requireInvariant inksCorrelation(ilkID);
//     requireInvariant allETHvsDebt();
//     requireInvariant absolution();
//     requireInvariant theFundamentalEquationOfAllETH();
// }



// ///////////////////////////////////////////////////
// /////                Properties               /////
// ///////////////////////////////////////////////////


// STATUS - verified
// ilk.Art == sum of all urns[ilk].art
invariant artsCorrelations(bytes32 ilkID)
    to_mathint(Art(ilkID)) == urnsArtSum[ilkID];


// STATUS - verified
// debt == sum of all dai (by MakerDAO doc)
invariant allETHvsDebt()
    to_mathint(debt()) == daiSum;


// STATUS - verified
// vice == sum of all sin's (by MakerDAO doc)
invariant absolution()
    to_mathint(vice()) == sumOfSins;


// STATUS - verified
// debt == vice + sum of all (ilks[i].Art * ilks[i].rate)
invariant theFundamentalEquationOfAllETH()
    to_mathint(debt()) == vice() + productGhost;


// STATUS - verified
// except slip: total gem + total ink == constant
rule gemInkConstant(env e, method f) {
    bytes32 ilkID;

    mathint inkBefore = urnsInkSum[ilkID];
    mathint gemBefore = gemSumPerIlk[ilkID];

    calldataarg args;
    f(e, args);

    mathint inkAfter = urnsInkSum[ilkID];
    mathint gemAfter = gemSumPerIlk[ilkID];

    assert f.selector != sig:slip(bytes32, address, int256).selector 
            => (inkBefore + gemBefore == inkAfter + gemAfter), "Remember, with great power comes great responsibility.";
}


// // STATUS - verified
// // shouldn't be able to generate more debt (frob with positive dart) if Ilk.Art * Ilk.rate > Ilk.line (then Art can't increase)
// rule cantGoDeeperInDebt(env e, method f) filtered { f -> f.selector == sig:frob(bytes32,address,address,address,int256,int256,address,address).selector } {
//     bytes32 ilkID; 
//     address urn;

//     validState(ilkID);

//     uint256 ArtBefore = Art(ilkID);
//     uint256 rateBefore = rate(ilkID);
//     uint256 lineBefore = line(ilkID);

//     calldataarg args;
//     f(e, args);

//     uint256 ArtAfter = Art(ilkID);

//     assert (ArtBefore * rateBefore > to_mathint(lineBefore)) 
//                 => ArtBefore >= ArtAfter, "Remember, with great power comes great responsibility.";
// }


// // STATUS - verified
// // if an urn has 0 < art * rate < dust, then a successful call to frob with that urn as the u argument should result in art == 0 || art * rate >= dust. (Ilk.dust is intended to ensure a Vault cannot be too small to profitably liquidate)
// rule sayNoToProfitableLiquidation(env e) {
//     bytes32 ilkID;
//     address urn;
//     address v;
//     address w;
//     int dink;
//     int dart;
//     address prev;
//     address next;

//     validState(ilkID);

//     uint256 artBefore = art(ilkID, urn);
//     uint256 rateBefore = rate(ilkID);
//     uint256 dustBefore = dust(ilkID);

//     frob(e, ilkID, urn, v, w, dink, dart, prev, next);

//     uint256 artAfter = art(ilkID, urn);
//     uint256 rateAfter = rate(ilkID);
//     uint256 dustAfter = dust(ilkID);

//     assert (0 < artBefore * rateBefore || artBefore * rateBefore < to_mathint(dustBefore))
//             => (artAfter == 0 || artAfter * rateAfter >= to_mathint(dustAfter));
// }


// // STATUS - verified. Bug: T.1 fork function can create positions that can be liquidated immediately and cause a drain of funds 
// // Helth factor sahould be preserved after fork() call
// rule healthFactorAfterFork(env e) {
//     bytes32 ilkID;
//     address urn;
//     address dst;
//     int dink;
//     int dart;
//     address srcPrev;
//     address srcNext;
//     address dstPrev;
//     address dstNext;

//     validState(ilkID);
    
//     fork(e, ilkID, urn, dst, dink, dart, srcPrev, srcNext, dstPrev, dstNext);

//     uint256 inkUrn = ink(ilkID, urn);
//     require inkUrn >= WAD();
//     uint256 inkDst = ink(ilkID, dst);
//     require inkDst >= WAD();

//     uint256 artUrn = art(ilkID, urn);
//     require artUrn >= WAD();
//     uint256 artDst = art(ilkID, dst);
//     require artDst >= WAD();

//     uint256 spot = spot(ilkID);
//     require spot >= RAY_CVL();
//     uint256 mat = mat(ilkID);
//     require to_mathint(mat) == (RAY_CVL() / 10 * 7); // assumption that mat is 0.7 RAY
//     uint256 rate = rate(ilkID);
//     require rate >= RAY_CVL();

//     assert (rate * artUrn <= inkUrn * spot / RAY_CVL() * mat)
//             && (rate * artDst <= inkDst * spot / RAY_CVL() * mat);
// }



// // STATUS - verified
// // Helth factor should be preserved after frob() call
// rule healthFactorAfterFrob(env e) {
//     bytes32 ilkID;
//     address urn;
//     address v;
//     address w;
//     int dink;
//     int dart;
//     address prev;
//     address next;

//     validState(ilkID);

//     require dart > 0 || dink < 0;
    
//     frob(e, ilkID, urn, v, w, dink, dart, prev, next); // tab <= urn.ink * ilk.spot * ilk.mat / RAY

//     uint256 inkUrn = ink(ilkID, urn);
//     require inkUrn >= WAD();

//     uint256 artUrn = art(ilkID, urn);
//     require artUrn >= WAD();

//     uint256 spot = spot(ilkID);
//     require spot >= RAY_CVL();
//     uint256 mat = mat(ilkID);
//     require to_mathint(mat) == (RAY_CVL() / 10 * 7); // assumption that mat is 0.7 RAY
//     uint256 rate = rate(ilkID);
//     require rate >= RAY_CVL();

//     assert (rate * artUrn <= inkUrn * spot / RAY_CVL() * mat);
// }



// STATUS - verified
// Debt can be created by the following functions: frob, suck, fold
rule debtCreation(env e, method f) {
    uint256 debtBefore = debt();

    calldataarg args;
    f(e, args);

    uint256 debtAfter = debt();

    assert debtBefore < debtAfter =>
            (f.selector == sig:frob(bytes32, address, address, address, int256, int256).selector 
                || f.selector == sig:suck(address, address, uint256).selector   
                || f.selector == sig:fold(bytes32, address, int256).selector), "Remember, with great power comes great responsibility.";
}


// STATUS - verified / violated 
// violated by fold from vat's perspective: https://prover.certora.com/output/3106/3392658a0ca544c98f29dce44a791845/?anonymousKey=99b3e971f570dfe0ad0deb425c8cef414d6b78d7
// verified if duty is set correctly in jug.sol
// Debt can be destroyed by the following events: frob, heal
rule debtDestruction(env e, method f) {
    uint256 debtBefore = debt();

    calldataarg args;
    f(e, args);

    uint256 debtAfter = debt();

    assert debtBefore > debtAfter =>
            (f.selector == sig:frob(bytes32, address, address, address, int256, int256).selector 
                || f.selector == sig:heal(uint256).selector), "Remember, with great power comes great responsibility.";
}



// STATUS - verified
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


// STATUS - verified
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


// STATUS - verified
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