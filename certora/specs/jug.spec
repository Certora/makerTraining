import "./erc20.spec";
import "./sanity.spec";


using Vat as vatInst;


methods {
    function ilks(bytes32) external returns(uint256, uint256) envfree;
    function vatInst.ilks(bytes32) external returns(uint256, uint256, uint256, uint256, uint256) envfree;
}


definition RAY_CVL() returns uint256 = 10^27;



// STATUS - verified (if duty >= RAY, vat.rate can't be dropped)
// possible to drop the rate if duty is below RAY: 
// Check if vat.rate can be dropped. In this case vat.fold() will reduce the debt
rule rateCheck(env e) {
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
