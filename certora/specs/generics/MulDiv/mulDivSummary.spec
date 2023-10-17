
// A restriction on the value of f = x * y / z
// The ratio between x (or y) and z is a rational number a/b or b/a.
// Important : do not set a = 0 or b = 0.
// Note: constRatio(x,y,z,a,b,f) <=> constRatio(x,y,z,b,a,f)
definition constRatio(uint256 x, uint256 y, uint256 z,
 uint256 a, uint256 b, uint256 f) 
        returns bool = 
        ( a * x == b * z && f == (b * y) / a ) || 
        ( b * x == a * z && f == (a * y) / b ) ||
        ( a * y == b * z && f == (b * x) / a ) || 
        ( b * y == a * z && f == (a * x) / b );

// A restriction on the value of f = x * y / z
// The division quotient between x (or y) and z is an integer q or 1/q.
// Important : do not set q=0
definition constQuotient(uint256 x, uint256 y, uint256 z,
 uint256 q, uint256 f) 

        returns bool = 
        ( x == q * z && f == q * y ) || 
        ( q * x == z && f == y / q ) ||
        ( y == q * z && f == q * x ) || 
        ( q * y == z && f == x / q );


function mulDivDownAbstract(uint256 x, uint256 y, uint256 z) returns uint256 {
    require z !=0;
    require noOverFlowMul(x, y);
    uint256 f; havoc f;
    uint256 r; havoc r;
    require z * f + r == x * y;
    require r < z;
    return f; 
}

function mulDivDownAbstractPlus(uint256 x, uint256 y, uint256 z) returns uint256 {
    uint256 f; havoc f;
    require z !=0;
    require noOverFlowMul(x, y);
    require x==0 || y==0 => f == 0;
    require x*y < z => f ==0;
    require x*y >= z => f > 0;
    require y >= z => f >= x;
    require x >= z => f >= y;
    require y < z => f < x;
    require x < z => f < y;
    // Fix: tighter bounds 
    //require f*z <= x*y;
    //require f*z + z > x*y;
    return f; 
}

function discreteQuotientMulDiv(uint256 x, uint256 y, uint256 z) returns uint256 
{
    uint256 f; havoc f;
    require z != 0 && noOverFlowMul(x, y);
    // Discrete quotients:
    require( 
        ((x ==0 || y ==0) && f == 0) ||
        (x == z && f == y) || 
        (y == z && f == x) ||
        constQuotient(x, y, z, 2, f) || // Division quotient is 1/2 or 2
        constQuotient(x, y, z, 5, f) || // Division quotient is 1/5 or 5
        constQuotient(x, y, z, 100, f) // Division quotient is 1/100 or 100
        );
    return f;
}

function discreteRatioMulDiv(uint256 x, uint256 y, uint256 z) returns uint256 
{
    uint256 f; havoc f;
    require z != 0 && noOverFlowMul(x, y);
    // Discrete ratios:
    require( 
        ((x ==0 || y ==0) && f == 0) ||
        (x == z && f == y) ||
        (y == z && f == x) ||
        constRatio(x, y, z, 2, 1, f) || // f = 2*x or f = x/2 (same for y)
        constRatio(x, y, z, 5, 1, f) || // f = 5*x or f = x/5 (same for y)
        constRatio(x, y, z, 2, 3, f) || // f = 2*x/3 or f = 3*x/2 (same for y)
        constRatio(x, y, z, 2, 7, f)    // f = 2*x/7 or f = 7*x/2 (same for y)
        );
    return f;
}

function noOverFlowMul(uint256 x, uint256 y) returns bool
{
    return x * y <= max_uint;
}
