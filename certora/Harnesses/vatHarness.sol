import "../../src/vat.sol";

pragma solidity ^0.6.12;

contract VatHarness is Vat {
    constructor() public Vat() {}

    function Art(bytes32 ilk) external view returns (uint256 Art_) {
        Art_ = ilks[ilk].Art;
    }

    function rate(bytes32 ilk) external view returns (uint256 rate_) {
        rate_ = ilks[ilk].rate;
    }

    function spot(bytes32 ilk) external view returns (uint256 spot_) {
        spot_ = ilks[ilk].spot;
    }

    function line(bytes32 ilk) external view returns (uint256 line_) {
        line_ = ilks[ilk].line;
    }

    function dust(bytes32 ilk) external view returns (uint256 dust_) {
        dust_ = ilks[ilk].dust;
    }

    function ink(bytes32 ilk, address urn) external view returns (uint256 ink_) {
        ink_ = urns[ilk][urn].ink;
    }

    function art(bytes32 ilk, address urn) external view returns (uint256 art_) {
        art_ = urns[ilk][urn].art;
    }
}
