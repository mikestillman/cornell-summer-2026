restart
needsPackage "ReesAlgebra"
needsPackage "Seminormalization"

forgetVarDegrees = (R1) -> (
	KK := coefficientRing R1;
	varList := gens ambient R1;
	degListOld := degrees ambient R1;
	I1 := ideal R1;
	degListNew := apply(degListOld, zL -> {zL#0});
	S2 := KK[varList, Degrees=>degListNew];
	return (S2 / sub(I1, S2))
)


hilbertSamuelPolynomial = (R,M) -> (
    G := associatedGradedRing (M, Variable => v);
    H := (flattenRing G)#0;
    K := prune H;
    L := forgetVarDegrees K;
    P := hilbertPolynomial(L, Projective => false);
    return P
)

kk = ZZ/32003
R = kk[x,y]/ideal(y^2-x^3)
M = ideal(x,y)

use R 

kk = ZZ/32003
R = kk[x,y,z,w]/ideal(z^3-y*w,y*z-x*w,y^3-x*z)
M = ideal(x,y,z,w)

methods associatedGradedRing
code 0
options associatedGradedRing

hilbertSamuelPolynomial(R,M)
G = associatedGradedRing M
G = associatedGradedRing(M, Variable => v)
describe G
flattenRing G
H = (flattenRing G)#0
describe H
degrees H
K = prune H
describe K
degrees K
L = forgetVarDegrees K
describe L
degrees L
mingens ideal L

L1 = (coefficientRing L)[gens ambient L,t]
describe L1
I1 = sub(ideal L, L1)
L2 = L1/I1
hilbertPolynomial I1
hilbertPolynomial(I1, Projective => false)

L1 = L[t,Join=>false]
describe L1
L2 = first flattenRing L1
degrees L2

?flattenVarDegrees
code flattenVarDegrees 

L = forgetVarDegrees K
degrees L

