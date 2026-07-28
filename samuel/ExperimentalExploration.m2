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
















-- a potential speed up for hilbertSamuelFunction


localMinimalPresentationHookCopy = method(Options => options minimalPresentation ++ {PruningMap => true})
localMinimalPresentationHookCopy Module := Module => opts -> M -> (
    RP := ring M;
    c := (if M.?generators then 1 else 0) + 2 * (if M.?relations then 1 else 0);
    if c == 0 then return M; --freemodule
    if c == 1 then (         --image
        f := generators M;
        f' := liftUp f;
        g' := syz f';
        h' := syz g';
        g := g' ** RP;
        h := h' ** RP;
        (C, P) := ({g, h}, null);
        (C, P)  = pruneComplex(C, PruningMap => true);
        phi := map(M, , matrix P#0);
        N := coker map(source phi, , matrix C#0);
        phi = map(M, N, phi);
        N.cache.pruningMap = phi;
        M.cache.presentationComplex = toChainComplex C;
        return N;
        );
    if c == 2 then (         --coker
        f = relations M;
        f' = liftUp f;
        g' = syz f';
        g = g' ** RP;
        C = {f, g};
        (C, P) = pruneComplex(C, PruningMap => true);
        phi = map(M, , matrix P#0);
        N = coker map(source phi, , matrix C#0);
        phi = map(M, N, phi);
        N.cache.pruningMap = phi;
        M.cache.presentationComplex = toChainComplex C;
        return N;
        );
    if c == 3 then (         --subquotient
        f = generators M;
        g = relations M;
        f' = liftUp f;
        g' = liftUp g;
        h' = modulo (f', g');
        e' := syz h';
        h = h' ** RP;
        e := e' ** RP;
        C = {h, e};
        (C, P) = pruneComplex(C, PruningMap => true);
        phi = map(M, , matrix P#0);
        N = coker map(source phi, , matrix C#0);
        phi = map(M, N, phi);
        N.cache.pruningMap = phi;
        M.cache.presentationComplex = toChainComplex C;
        return N;
        );
    )
hilbertSamuelFunctionTest = method()
hilbertSamuelFunctionTest (Ideal , ZZ, ZZ) := List => (I, n0, n1) -> hilbertSamuelFunctionTest(module I,n0,n1)
hilbertSamuelFunctionTest (Module, ZZ, ZZ) := List => (M, n0, n1) -> (
    RP := ring M;
    if class RP =!= LocalRing then error "expected objects over a local ring";
    m := max RP;
    Lm := RP.maxIdeal;
    R := ring Lm;
    k := frac(R/Lm);  -- same as residue field because (R_p/p*R_p) = (R/p)_0 = frac(R/p)
                      -- localization is an exact functor 
                      -- Apply localize at Lm to the exact sequence 0 -> Lm -> R -> R/Lm -> 0
    LM := minimalPresentation liftUp(localMinimalPresentationHookCopy M);
    -- does the minimalPresentation do anything?
    -- is it expensive to take a minimalPresentation when generators and relations are already minimal?
    for i from 1 to n0 do LM = minimalPresentation(Lm * LM);
    -- this is just LM = Lm^n0 * M but faster
    for i from n0 to n1 list (
        if debugLevel >= 1 then printerr("computing HSF_", toString i);        
        j := numgens(LM ** k);
        if i < n1 then LM = minimalPresentation(Lm * LM);  -- trim?
        j
        )
    )
--fact: let M be an A module. Then M ** A/I = M/IM
--k = R/Lm 
--LM ** k = LM ** R/Lm = LM/(Lm*LM)

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

time hilbertSamuelFunction(module Ilocal,0,6)           -- took my laptop about 5 seconds in 2026
time hilbertSamuelFunction(module Ilocal,7,8)           -- took my laptop about 10 seconds in 2026
time hilbertSamuelFunction(module Ilocal,9,10)          -- took my laptop about 30 seconds in 2026
time hilbertSamuelFunction(module Ilocal,11,12)         -- took my laptop about 90 seconds in 2026


time hilbertSamuelFunctionTest(module Ilocal,0,6)           
time hilbertSamuelFunctionTest(module Ilocal,7,8)           
time hilbertSamuelFunctionTest(module Ilocal,9,10)          
time hilbertSamuelFunctionTest(module Ilocal,11,12)         
time hilbertSamuelFunctionTest(module Ilocal,0,20)          

profile(time hilbertSamuelFunction(module Ilocal,0,6))
profile(time hilbertSamuelFunctionTest(module Ilocal,0,12))
profileSummary
-- Quesition: how to reset profileSummary?

-- Another example that shows the new implementation gives the same result
N = cokernel matrix{{random(2,R)},{random(2,R)},{random(2,R)},
                    {random(2,R)},{random(2,R)},{random(2,R)}}
Nlocal = N ** Rlocal
time hilbertSamuelFunction(module Nlocal,0,5)           -- about 25s depending on rng
time hilbertSamuelFunctionTest(module Nlocal,0,5)       -- as low as 0.05s
time hilbertSamuelFunctionTest(module Nlocal,0,12)      -- about 1s depending on rng

