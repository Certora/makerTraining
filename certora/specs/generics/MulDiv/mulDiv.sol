// SPDX-License-Identifier: SEE LICENSE IN LICENSE
pragma solidity ^0.8.0;

contract mulDiv {
	function mulDivF(uint256 x, uint256 y, uint256 z) 
	external pure returns(uint256) {
		return _mulDivF(x, y, z);
    }

	function _mulDivF(uint256 x, uint256 y, uint256 z) 
	internal pure returns(uint256) {
		return (x * y) / z;
    }
}