import "../../src/jug.sol";

pragma solidity ^0.6.12;

contract JugPlus is Jug {


constructor(address vat_) public  Jug(vat_) {
    } 


    function initVat(address newVat) public {
        require (address(vat) == address(0));
        vat == VatLike(newVat);
    }

    function isWard(address w) public returns (bool) {
        return wards[w] > 0 ;
    }

    function  call_rpow(uint x, uint n, uint b) external pure returns (uint) {
        return rpow(0, n, b);
    }
}


