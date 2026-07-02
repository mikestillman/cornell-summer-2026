--print packageTemplate "LagrangeInterpolation"

newPackage(
    "LagrangeInterpolation",
    Version => "0.1",
    Date => "07/02/2026",
    Headline => "Computing Polynomials from sampled points",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    Keywords => {""},
    AuxiliaryFiles => false,
    DebuggingMode => true,
    Reload => true
    )

-- perhaps we should lint these names
export {"lagrangeBasis", "lagrangeInterpolation", "matchPolynomial"}

-* Code section *-

restart 
use QQ[x]

-- successive difference take a list (of integers) of size n 
-- and return a list of size n-1 where the i-th element is 
-- the difference of the (i+1)-th and i-th elements of the input list.

-- partial sum takes a list (of integers) of size n 
-- and return a list of size n+1 where the 0-th element is 0 and
-- the (i+1)-th element is the sum of the first i elements of the input list.

-- taking the successive difference of the partial sum of a list 
-- should return the original list.
-- taking the partial sum of the successive difference of a list should return 
-- the original list but each element got subtracted by the first element.

-- it's like taking derivative of integral return the same function (FTC),
-- but taking integral of derivative return the same function up to a constant.

succDiff = (L) -> (
    if not instance(L, List) then error "Input must be a list";
    -- check each element of input list is an integer, or things we can do subtraction with
    for i from 1 to #L-1 list L#i - L#(i-1)
)

--partialSum = (L) -> (
--    if not instance(L, List) then error "Input must be a list";
--    -- check each element of input list is an integer, or things we can do addition with
--    for i from 0 to #L list sum take(L,i)
--)
-- should be the same as
-- prepend(0,accumulate(plus,0,L))
-- and we should use this instead.

-- removeNth take a list and a integer and remove the (n-1)-th element of the list
-- M2 must have this already, but I couldn't find it.

--removeNth = (L, N) -> (
--    if not instance(L, List) then error "First input must be a list";
--    if not instance(N, ZZ) then error "Second input must be an integer";
--    if N < 0 or N >= #L then error "Second input must be between 0 and the length of the list";
--    apply(delete(N,toList(0..(#L-1))), i -> L#i)
--    -- The following also works.
--    -- I am leaving it here for now because I want to remember how to use select.
--    -- apply(select(toList(0..(#L-1)), i -> i != N), i -> L#i)
--)

-- should be the same as
-- drop(L,{N,N})
-- and we should use this instead.

-- Lagrange interpolation
    -- Given n+1 points (x_0,y_0),...,(x_n,y_n) with distinct x_i's, 
    -- Lagrange interpolation gives a polynomial P of degree at most n with P(x_i) = y_i for all i.
    -- It suffices to find polynomials P_i of degree n such that 
    -- P_i(x_i) = 1 and P_i(x_j) = 0 for j != i, and then take P = sum y_i * P_i.
    -- The polynomial P_i can be constructed as 
        --     (x   - x_0)*...*(x   - x_n)
        --    -----------------------------
        --     (x_i - x_0)*...*(x_i - x_n)
    -- These are called the Lagrange basis, 
    -- use lagrangeBasis({x_0,...,x_n},i) to get P_i.

    -- Note that a polynomial of degree n has at most n roots.
    -- So if two polynomials of degree at most n agree on n+1 points,
    -- then they must be the same polynomial since their difference 
    -- has degree at most n and n+1 roots.
    -- Therefore, Lagrange interpolation gives the unique polynomial
    -- of degree at most n that passes through the given n+1 points.

lagrangeBasis = (L,n) -> (
    if not instance(L, List) then error "First input must be a list";
    if not instance(n, ZZ) then error "Second input must be an integer";
    if n < 0 or n >= #L then error "Second input must be between 0 and the length of the list";
    -- needs to check the x-coordinates are distinct
    -- maybe use delete function and check the deleted list has exactly one less
    product apply (drop(L,{n,n}), a -> (x - a) / (L#n - a))
)

lagrangeInterpolation = (L) -> (
    if not instance(L, List) then error "Input must be a list";
    if #L < 2 then error "Input list must have at least two elements";
    for i from 0 to #L-1 do (
        if not instance(L#i, List) then error "Each element of the input list must be a list";
        if not #L#i == 2 then error "Each element of the input list must be a list of length 2";
        if not instance(L#i#1, ZZ) and instance(L#i#2, ZZ) then error "Each element of the input list must be a list consisting of two integers";
        -- need to check that the x-coordinates are distinct
    );
    return sum for i from 0 to #L-1 list L#i#1 * lagrangeBasis(apply(L,pair -> pair#0),i)
)

-- So there exists a degree at most n polynomial through any n+1 points,
-- but one should not expect there to be a polynomial through n+2 general points,
-- e.g., three general points is not on a line.
-- The matchPolynomial function below takes a list of integers,
-- and checks, from n = 0, if the last n+2 elements of the list 
-- matches a polynomial of degree at most n.
-- When it finds the first n such that this happens, 
-- it will return the polynomial, and the list of values of 
-- the polynomial evaluated at 0,1,...,(length of the input list - 1)
-- for you to compare with the input list.

-- It should be easy to modify the function to check if the last n+d elements 
-- of the list matches a polynomial of  degree at most n for any d >= 2.
-- Sometimes the last three elements of a list is an arithmetic progression, 
-- and matchPolynomial will return a degree 1 polynomial,
-- but we want to it to stop this early.

-- we can use this to get the Hilbert-Samuel polynomial 
-- using the Hilbert-Samuel function from the local ring package.
-- We still need a bound that guarantees that the Hilbert-Samuel function 
-- begins to match a polynomial in order to be absolutely certain 
-- we have the correct polynomial.

matchPolynomial = (L) -> (
    if not instance(L, List) then error "Input must be a list";
    InitialList = L;
    Length = #L;
    while #L >= 2 do (
        if take(L,-2) == {0,0} then (
            d = Length - #L - 1; -- this will be the degree of the output polynomial
            -- if we say the zero polynomial have degree -1
            ListofPoints = for i from Length - d - 2 to Length-1 list {i,InitialList#i};
            P = lagrangeInterpolation(ListofPoints);
            return {P, for i from 0 to Length - 1 list P(i)}
        )
        else L = succDiff(L);
    );
    error "The last n+2 elements of the list does not match any polynomial of degree at most n for any nonnegative integer n";
    -- should be n+3, because before hitting {0,0},
    -- the previous list must be three elements that are the same.
    -- Can be tested since matchPolynomial({1,2,3}) will out put an error.
    -- If we want n+2, just check that last element is 0 in the while loop.
)

-* Documentation section *-
beginDocumentation()

-*
doc ///
Key
  LagrangeInterpolation
Headline
Description
  Text
  Tree
  Example
  CannedExample
Acknowledgement
Contributors
References
Caveat
SeeAlso
Subnodes
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
  Item
Description
  Text
  Example
  CannedExample
  Code
  Pre
ExampleFiles
Contributors
References
Caveat
SeeAlso
///
-*

-* Test section *-
-- NOTE: currently the tests do not run -- they 
-- error with "error: expected pair to have a method for '=='"
-- this makes it sound like equality checking is not defined for one of the
-- types?
TEST /// -* Positive tests for lagrangeBasis *-
    use QQ[x]
    assert(lagrangeBasis({3,6},1) == (x/3 - 1))
    assert(lagrangeBasis({3,6},0) == (-x/3 + 2) )
    assert(lagrangeBasis({-1,0,1},1) == (-x^2 + 1))
///

TEST /// -* Positive tests for lagrangeInterpolation *-
    use QQ[x]
    assert(lagrangeInterpolation({{0,0},{1,1}}) == x)
    assert(lagrangeInterpolation({{0,0},{1,1},{2,2}}) == x)
    assert(lagrangeInterpolation({{0,0},{1,1},{2,2},{3,3}}) == x)
    assert(lagrangeInterpolation({{0,0},{1,1},{2,2},{3,3},{4,4}}) == x)

    assert(lagrangeInterpolation({{0,1},{2,3},{4,5}}) == x+1)

    assert(lagrangeInterpolation({{1,1},{2,4},{3,9}}) == x^2)
/// 


TEST /// -* Positive tests for matchPolynomial *-
    use QQ[x]
    assert(matchPolynomial({1,2,3,4,5,6}) == {x+1, {1,2,3,4,5,6}})
    assert(matchPolynomial({1,4,9,16,25}) == {x^2, {0,1,4,9,16,25}})
    
    -- for this command, i get something different than what the comment says
    matchPolynomial({1,2,3,4,9,16,25,36})
    -- should return {x^2, {1,0,1,4,9,16,25,36}}
    
    assert(matchPolynomial({10,20,30,40,41,42,43,44}) == {x+37, {37,38,39,40,41,42,43,44}})
///



-- examples
    -- don't forget to run use QQ[x] first
    -- I'm still confused about how to "use" variables in package,
    -- but this will do for now.
use QQ[x]

lagrangeBasis({3,6},1)
    -- the unique degree 1 polynomial p with p(3) = 0 and p(6) = 1, 
    -- i.e., x/3 - 1
lagrangeBasis({3,6},0)
    -- the unique degree 1 polynomial p with p(3) = 1 and p(6) = 0, 
    -- i.e., -x/3 + 2
lagrangeBasis({-1,0,1},1)
    -- the unique degree 2 polynomial p with p(-1) = 0, p(0) = 1, and p(1) = 0, 
    -- i.e., -x^2 + 1

lagrangeInterpolation({{0,0},{1,1}})
lagrangeInterpolation({{0,0},{1,1},{2,2}})
lagrangeInterpolation({{0,0},{1,1},{2,2},{3,3}})
lagrangeInterpolation({{0,0},{1,1},{2,2},{3,3},{4,4}})
    -- all of theses are should return x
lagrangeInterpolation({{0,1},{2,3},{4,5}})
    -- x + 1
lagrangeInterpolation({{1,1},{2,4},{3,9}})
    -- x^2

matchPolynomial({1,2,3,4,5,6})
    -- should return {x + 1, {1,2,3,4,5,6}}
matchPolynomial({1,4,9,16,25})
    -- should return {x^2, {1,4,9,16,25}} -- I think we need to prepend 0 for
                                          -- this to be true
matchPolynomial({1,2,3,4,9,16,25,36})
   -- should return {x^2, {1,0,1,4,9,16,25,36}}
matchPolynomial({10,20,30,40,41,42,43,44})
   -- should return {x+37, {37,38,39,40,41,42,43,44}}


end--

-* Development section *-
restart
debug needsPackage "LagrangeInterpolation"
check "LagrangeInterpolation"

uninstallPackage "LagrangeInterpolation"
restart
installPackage "LagrangeInterpolation"
viewHelp "LagrangeInterpolation"




-- some extra tests using hilbertSamuel

needsPackage "LocalRings"
needsPackage "HilbertSamuel"

S = ZZ/32003[x,y]
maxS = ideal(x,y)
I = ideal(y^2 - x^3)
R = S/I
maxR = sub(maxS,R)
SM = localRing(S,maxS)
maxSe = sub(maxS,SM)
Ie = sub(I,SM)

L = hilbertSamuelFunction(SM^1/Ie,0,10)
prepend(0,accumulate(plus,0,L))
use QQ[x]
matchPolynomial(prepend(0,accumulate(plus,0,L)))
hilbertSamuelPolynomial(maxR)

QQ[x]/(x^2 + 1) = QQ[i]









