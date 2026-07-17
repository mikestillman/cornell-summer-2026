restart
needsPackage "LocalRings"
needsPackage "HilbertSamuel"
needsPackage "LagrangeInterpolation"

-- M,N,I are three ways to randomly generate modules, 
-- of course there are many more ways.
kk = ZZ/101
R = kk[x,y,z]
maxR = ideal(gens R)

    M = cokernel matrix{{random(2,R)},{random(2,R)},{random(2,R)}}
    N = cokernel matrix{{random(2,R)},{random(2,R)},{random(2,R)},
                        {random(2,R)},{random(2,R)},{random(2,R)}}
    I = ideal(random(3,R),random(3,R),random(3,R))
    res I

-- double star means tensor, basically extending the module to the local ring.
Rlocal = localRing(R,maxR)
Mlocal = M ** Rlocal
Nlocal = N ** Rlocal
Ilocal = I ** Rlocal

-- regularity, in some situation, is ``rumored by me'' to be an upper bound 
-- for when the hilbertSamuelFunction will begin agree to with the hilbertSamuelPolynomial.
-- dimension is suppose to be the degree of the hilbertSamuelPolynomial by Eisenbud Chapter 12.
regularity(M)
dim M

regularity(N)
dim N

regularity(I)
regularity(module I) 
-- not sure which one to use, and it is not obvious if they are the same from the code.
dim(R/ann I)
-- this should be the degree it is the same as dim(module I) but different from dim(I).

L = hilbertSamuelFunction(Mlocal,0,4)
L = hilbertSamuelFunction(Nlocal,0,4)
L = hilbertSamuelFunction(module Ilocal,0,4)

LL = prepend(0,accumulate(plus,0,L))
matchPolynomial(LL)

-- end of routine













-- The following is a randomly generated example that had some interesting behavior:

-- I don't think this is a rare occurence, if you do I = ideal(random(3,R),random(3,R),random(3,R)),
-- the result is very similar a lot of the times.
-- It might be woth spending some time to simplify the example so we can work out 
-- and understand the length of various quotients by hand.

kk = ZZ/101
R = kk[x,y,z]
maxR = ideal(gens R)

I = ideal(
  10*x^3 - 24*x^2*y - 22*x*y^2 - 45*y^3 +  5*x^2*z + 17*x*y*z - 30*y^2*z +  8*x*z^2 + 47*y*z^2 + 39*z^3,
  42*x^3 + 29*x^2*y - 18*x*y^2 + 34*y^3 - 42*x^2*z + 19*x*y*z + 29*y^2*z - 27*x*z^2 - 23*y*z^2 + 12*z^3,
- 32*x^3 + 21*x^2*y +  5*x*y^2 - 35*y^3 - 43*x^2*z - 35*x*y*z - 34*y^2*z - 38*x*z^2 + 36*y*z^2 + 17*z^3)
res I

Rlocal = localRing(R,maxR)
Ilocal = I ** Rlocal

-- make sure I is an ideal of R and not Rlocal, 
-- otherwise the regularity will be different.
assert(regularity(I) == 7)
assert(regularity(module I) == 7)
assert(dim(R/ann I) == 3)
L = hilbertSamuelFunction(module Ilocal,0,12)               -- warning: slow to compute
-- I used the trick in LocalRing.m2 and split the computation into parts with small range.
    time hilbertSamuelFunction(module Ilocal,0,6)           -- took my laptop about 5 seconds in 2026
    time hilbertSamuelFunction(module Ilocal,7,8)           -- took my laptop about 10 seconds in 2026
    time hilbertSamuelFunction(module Ilocal,9,10)          -- took my laptop about 30 seconds in 2026
    time hilbertSamuelFunction(module Ilocal,11,12)         -- took my laptop about 90 seconds in 2026

-- the list of values of the hilbertSamuelFunction should be 
L = {3,9,18,27,36,45,55,66,78,91,105,120,136}
LL = prepend(0,accumulate(plus,0,L))
assert(LL == {0,3,12,30,57,93,138,193,259,337,428,533,653,789})
matchPolynomial(LL)  
-- we had the problem with not able to assert result of lograngeBasis, lagrangeInterpolation, and matchPolynomial.
-- the result should be 1/6*x^3 + 2*x^2 + 47/6*x -17

-- Note that if we truncate L as follows 
L = {3,9,18,27,36,45}
-- it ends in an arithmetic progression (degree 1 polynomial) of length 5.
-- so when we accumulate, it will end with a degree 2 polynomial:
LL = prepend(0,accumulate(plus,0,L))
assert(LL == {0,3,12,30,57,93,138})
matchPolynomial(LL) 
-- the result should be 9/2*x^2 - 9/2*x + 3 which will not be the Hilbert Samuel polynomial.

profile(time hilbertSamuelFunction(module Ilocal,0,6))
profileSummary

path

methods localRing
code 0