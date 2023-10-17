methods{
    _mulDivF(uint256 x, uint256 y, uint256 z) => simpleMulDivIfWithRemainder(x,y,z)
    mulDivF(uint256, uint256, uint256) returns (uint256) envfree
}

// A restriction on the value of f = x * y / z
// The division quotient y/z or x/z can be either q or 1/q.
// Important : do not set q=0.
// We assume no division remainder.
definition constQuotient(uint256 x, uint256 y, uint256 z,
 uint256 q, uint256 f) 

        returns bool = 
        ( x == q * z && f == q * y ) || 
        ( q * x == z && f == y / q && y % q ==0 ) ||
        ( y == q * z && f == q * x ) || 
        ( q * y == z && f == x / q && x % q ==0);

// Same as constQuotient, but non zero remainders are allowed.
definition constQuotientWithRemainder(uint256 x, uint256 y, uint256 z,
 uint256 q, uint256 f) 

        returns bool = 
        ( x == q * z && f == q * y ) || 
        ( q * x == z && f == y / q ) ||
        ( y == q * z && f == q * x ) || 
        ( q * y == z && f == x / q );

////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////

// Consistency with original definition.
rule mulDivConsistent(uint w, uint x, uint y, uint z)
{
    assert w == (x * y) / z <=> w == mulDivF(x, y, z);
}

// Multiplication is commutative.
rule mulSymmetry(uint x, uint y, uint z)
{
    assert mulDivF(x, y, z) == mulDivF(y, x ,z);
}

// Multiplication monotonicity
rule firstTermMonotonic(uint x1, uint x2, uint y, uint z)
{
    assert x1 > x2 && y > 0 => mulDivF(x1, y, z) > mulDivF(x2, y, z);
}

// Division monotonicity
rule divisionMonotonic(uint x, uint y, uint z1, uint z2)
{
    assert x != 0 && y != 0 && z1 > z2 => mulDivF(x, y, z2) > mulDivF(x, y, z1);
}

// Double call equivalent to identity
rule doubleCallIdentity(uint x, uint y, uint z)
{
    uint u = mulDivF(x, y, z);
    uint w = mulDivF(x, y, u);
    assert w == z;
}

// First term additivity
rule firstTermAdditivity(uint x1, uint x2, uint y, uint z)
{
    require noOverFlowAdd(x1, x2);
    uint256 x3 = x1 + x2;
    uint f1 = mulDivF(x1, y, z);
    uint f2 = mulDivF(x2, y, z);
    uint f12 = mulDivF(x3, y, z);
    assert f1 + f2 == f12;
}

// Second term additivity
rule secondTermAdditivity(uint x1, uint x2, uint y, uint z)
{
    require noOverFlowAdd(x1, x2);
    uint256 x3 = x1 + x2;
    uint f1 = mulDivF(y, x1, z);
    uint f2 = mulDivF(y, x2, z);
    uint f12 = mulDivF(y, x3, z);
    assert f1 + f2 == f12;
}

// (x * y / z) * (x * z / y) = x^2
rule switchNomByDenom(uint256 x, uint256 y, uint256 z)
{
    uint f1 = mulDivF(x, y, z);
    uint f2 = mulDivF(x, z, y);
    assert f1 * f2 == x * x;
}

// (x*y)/z + x*(z-y)/z == x
rule sumOfPartsIsWhole(uint256 x, uint256 y, uint256 z)
{
    require noOverFlowSub(z, y);
    uint f1 = mulDivF(x, y, z);
    uint f2 = mulDivF(x, z-y, z);
    assert f1 + f2 == x;
}

rule shouldFail1(uint256 x)
{
    uint z = 1000000;
    uint y = 999;
    uint w = 32;
    require noOverFlowAdd(x, w);
    uint256 f1 = mulDivF(x, y, z);
    uint256 f2 = mulDivF(x + w, y, z);
    assert x > 0 => f1 > f2; 
}

rule shouldFail2(uint256 x)
{
    uint z = 1000000;
    uint y = 999;
    uint w = 32;
    require noOverFlowAdd(z, w);
    uint256 f1 = mulDivF(x, y, z);
    uint256 f2 = mulDivF(x, y, z + w);
    assert x > 0 => f1 < f2; 
}

rule boundQuotient1(uint256 x, uint256 y)
{
    require y >=1 ;
    uint256 r = x - (x / y) * y;
    assert  r <= y-1;
}

rule boundQuotient2(uint256 x, uint256 y, uint256 z)
{
    require z >=1 ;
    uint256 w = mulDivF(x, y, z);
    uint256 r = x * y - w * z;
    assert r <= z-1;
}

rule zeroRemainder(uint256 x, uint256 y, uint256 z)
{
    require z >= 1 ;
    uint256 w = mulDivF(x, y, z);
    assert x * y - w * z == 0;
}

////////////////////////////////////////////////////////////////////////////
//                       functions and summarizations                     //
////////////////////////////////////////////////////////////////////////////

// Summary for mulDivF:
// Discrete set of quotients: for any value q also 1/q is a possible quotient.
// Division remainders are allowed.
// No multiplication overflow.
function simpleMulDivIfWithRemainder(uint256 x, uint256 y, uint256 z) returns uint256 
{
    uint f;
    bool dontDividebyZero = z != 0;
    bool Success = dontDividebyZero && noOverFlowMul(x, y);
    uint256 qs = 400; // My special quotient

    if (x ==0 || y ==0)      {f = 0;}
    else if (y == z)   { f = x;}
    else if (x == z)   { f = y;}
    // Qut = 2, 1/2
    else if (y == 2 * z)     {f = 2 * x;}
    else if (x == 2 * z)     {f = 2 * y;}
    else if (2 * y == z )  {f = x / 2;}
    else if (2 * x == z )  {f = y / 2;}
    // Qut = 3, 1/3
    else if (y == 3 * z)     {f = 3 * x;}
    else if (x == 3 * z)     {f = 3 * y;}
    else if (3 * y == z )  {f = x / 3;}
    else if (3 * x == z )  {f = y / 3;}
    // Qut = 10, 1/10
    else if (y == 10 * z)     {f = 10 * x;}
    else if (x == 10 * z)     {f = 10 * y;}
    else if (10 * y == z )  {f = x / 10;}
    else if (10 * x == z )  {f = y / 10;}
    // Qut = 500, 1/500
    else if (y == 500 * z)     {f = 500 * x;}
    else if (x == 500 * z)     {f = 500 * y;}
    else if (500 * y == z )  {f = x / 500;}
    else if (500 * x == z )  {f = y / 500;}
    // Qut = qs, 1/qs
    else if (y == qs * z)     {f = qs * x;}
    else if (x == qs * z)     {f = qs * y;}
    else if (qs * y == z)  {f = x / qs;}
    else if (qs * x == z)  {f = y / qs;}
    //
    else    {f = 0; Success = false;}

    require Success;
    return f;
}

// Summary for mulDivF:
// Discrete set of quotients: for any value q also 1/q is a possible quotient.
// We also assume no division remainders.
// No multiplication overflow.
function simpleMulDivIf(uint256 x, uint256 y, uint256 z) returns uint256 
{
    uint256 f;
    bool dontDividebyZero = z != 0;
    bool Success = dontDividebyZero && noOverFlowMul(x, y);
    uint256 qs = 400; // My special quotient

    if (x ==0 || y ==0)      {f = 0;}
    else if (y == z)   { f = x;}
    else if (x == z)   { f = y;}
    // Qut = 2, 1/2
    else if (y == 2 * z)     {f = 2 * x;}
    else if (x == 2 * z)     {f = 2 * y;}
    else if (2 * y == z && x % 2 == 0)  {f = x / 2;}
    else if (2 * x == z && y % 2 == 0)  {f = y / 2;}
    // Qut = 3, 1/3
    else if (y == 3 * z)     {f = 3 * x;}
    else if (x == 3 * z)     {f = 3 * y;}
    else if (3 * y == z && x % 3 == 0)  {f = x / 3;}
    else if (3 * x == z && y % 3 == 0)  {f = y / 3;}
    // Qut = 10, 1/10
    else if (y == 10 * z)     {f = 10 * x;}
    else if (x == 10 * z)     {f = 10 * y;}
    else if (10 * y == z && x % 10 == 0)  {f = x / 10;}
    else if (10 * x == z && y % 10 == 0)  {f = y / 10;}
    // Qut = 500, 1/500
    else if (y == 500 * z)     {f = 500 * x;}
    else if (x == 500 * z)     {f = 500 * y;}
    else if (500 * y == z && x % 500 == 0)  {f = x / 500;}
    else if (500 * x == z && y % 500 == 0)  {f = y / 500;}
    // Qut = qs, 1/qs
    else if (y == qs * z)     {f = qs * x;}
    else if (x == qs * z)     {f = qs * y;}
    else if (qs * y == z && x % qs == 0)  {f = x / qs;}
    else if (qs * x == z && y % qs == 0)  {f = y / qs;}
    //
    else    {f = 0; Success = false;}
    require Success;
    return f;
}

function noOverFlow(uint256 x, uint256 y) returns bool
{
    return noOverFlowMul(x, y) && noOverFlowAdd(x, y) && noOverFlowSub(x, y);
}

function noOverFlowMul(uint256 x, uint256 y) returns bool
{
    return x * y <= max_uint;
}

function noOverFlowAdd(uint256 x, uint256 y) returns bool
{
    return x + y <= max_uint;
}

function noOverFlowSub(uint256 x, uint256 y) returns bool
{
    return x >= y;
}
