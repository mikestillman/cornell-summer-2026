

needsPackage "LocalRings"
viewHelp LocalRings
R = ZZ/32003[a..d]
I = monomialCurveIdeal(R, {1,3,4})
M = ideal vars R
P = ideal(a,b,c)

RM = localRing(R, M)
RP = localRing(R, P)

vars R
gens R
use RM
a/(1+a)
a/b

N = R^1/I
FN = freeResolution N

NRM = N ** RM
freeResolution NRM

NRP = N ** RP
freeResolution NRP

viewHelp hilbertSamuelPolynomial
hilbertSamuelFunction(NRM, 0, 4)

N1 = NRM / (max RM)
trim image relations N1
length N1

N1 = NRM / (max RM)^4
trim image relations N1
length N1
basis N1 -- this isn't implemented!

basis (N / (ideal vars R)^4)

methods hilbertSamuelFunction
code 0

hooks length

Things Mike will do:
1. Setup Zulip
2. Check with John Cobb about Toric Stacks 
3. Check with Chase and Thomas Brazleton about algebraic topology possibilities
4. Put the DanilovKhovanskii package into our repo.
5. We will meet at 2:45 pm on Thursday, May 28.

methods normalCone
code 0
help normalCone

think about:
hilbertSamuelPolynomial
length of a module
normalCone/associatedGradedRing


