import "./erc20.spec";
import "./sanity.spec";


using Vat as vatInst;


methods {
    function ilks(bytes32) external returns(uint256, uint256) envfree;
    function vatInst.ilks(bytes32) external returns(uint256, uint256, uint256, uint256, uint256) envfree;
}


definition RAY_CVL() returns uint256 = 10^27;



// https://prover.certora.com/output/3106/74f26cc3dde345e4857318a9c56d97f9/?anonymousKey=cfd29ffa5b54d4e9b8ea9f934ef8df2de8585485
use rule sanity;



// possible to drop the rate if duty is below RAY: 
// Check if vat.rate can be dropped. In this case vat.fold() will reduce the debt
// https://prover.certora.com/output/3106/de8e1ef861d34ef89f47c61278913ea7/?anonymousKey=d22dbc759f1d6e3138cdd1ffec707b76e12a975e
rule rateCheck(env e) {
    bytes32 ilk;
    uint256 duty;
    uint256 rateBefore;
    duty, _ = ilks(ilk);
    _, rateBefore, _, _, _ = vatInst.ilks(ilk);

    drip(e, ilk);

    uint256 rateAfter;
    _, rateAfter, _, _, _ = vatInst.ilks(ilk);

    assert rateBefore <= rateAfter, "Remember, with great power comes great responsibility.";
}


// verified (if duty >= RAY, vat.rate can't be dropped)
// https://prover.certora.com/output/3106/dd9bfee54c8a41d5a55986075588c3a1/?anonymousKey=32e938c057d6ab8c3eb575d2ea81ff7858d36862
rule rateCheckUpgrade(env e) {
    bytes32 ilk;
    uint256 duty;
    uint256 rateBefore;
    duty, _ = ilks(ilk);
    _, rateBefore, _, _, _ = vatInst.ilks(ilk);
    require duty >= RAY_CVL();

    drip(e, ilk);

    uint256 rateAfter;
    _, rateAfter, _, _, _ = vatInst.ilks(ilk);

    assert rateBefore <= rateAfter, "Remember, with great power comes great responsibility.";
}
