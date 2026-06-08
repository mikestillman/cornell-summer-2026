-- print packageTemplate "HilbertSamuel"

newPackage(
    "HilbertSamuel",
    Version => "0.1",
    Date => "6/3/2026",
    Headline => "Computing the Hilbert-Samuel polynomial of a module",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    Keywords => {"Commutative algebra"},
    AuxiliaryFiles => false,
    DebuggingMode => true,
    PackageExports => {"LocalRings","ReesAlgebra"}
    )

export {"hilbertSamuelPolynomial"}

-* Code section *-
HilbRing = QQ(monoid[getSymbol "n"]);

forgetVarDegrees = (R1) -> (
  KK := coefficientRing R1;
  varList := gens ambient R1;
  degListOld := degrees ambient R1;
  I1 := ideal R1;
  degListNew := apply(degListOld, zL -> {zL#0});
  S2 := KK[varList, Degrees=>degListNew];
  return (S2 / sub(I1, S2))
)

hilbertSamuelPolynomial = method()
hilbertSamuelPolynomial(Ideal) := RingElement => (maxR) -> (
  hilbertSamuelPolynomial(maxR,HilbRing_0)
)

hilbertSamuelPolynomial(Ideal,RingElement) := RingElement => (maxR,t) -> (
  R := ring maxR;
  if ring maxR =!= R then error "Ideals must be in the same ring";
  if maxR =!= ideal gens R then error "localizing at other ideal is not implemented yet";
  G := associatedGradedRing (maxR, Variable => getSymbol "v");
  H := (flattenRing G)#0;
  K := prune H;
  L := forgetVarDegrees K;
  L1 := (coefficientRing L)[gens ambient L,getSymbol "t"];
  I1 := sub(ideal L, L1);
  P := hilbertPolynomial(I1, Projective => false);
  -- return P -- gives the polynomial for length(R/m^{n+1}) 
  return sub(P, {(ring P)_0 => t - 1}) -- gives the polynomial for length(R/m^n)
)


-* Documentation section *-
beginDocumentation()

doc ///
Key
  HilbertSamuel
Headline
  Computing the Hilbert-Samuel polynomial of a module
Description
  Text
  Example
    kk = ZZ/32003;
    S = kk[x,y];
    I = ideal(y^2-x^3);
    R = S/I;
    maxR = ideal(x,y)
    H = hilbertSamuelPolynomial(maxR)
SeeAlso
///

doc ///
Key
  hilbertSamuelPolynomial
Headline
  Compute the Hilbert-Samuel polynomial of a module
Usage
  hilbertSamuelPolynomial(maxR)
Inputs
  maxR:Ideal
Outputs
  :RingElement
    in the ring $\mathbb{Q}[n]$
Description
  Text
  Example
    kk = ZZ/32003;
    S = kk[x,y];
    I = ideal(y^2-x^3);
    R = S/I;
    maxR = ideal(x,y)
    H = hilbertSamuelPolynomial(maxR)
SeeAlso
///

-* Test section *-
TEST /// -* [insert short title for this test] *-
  kk = ZZ/32003
  S = kk[x,y]
  I = ideal(y^2-x^3)
  R = S/I
  maxR = ideal(x,y)
  H = hilbertSamuelPolynomial(maxR)
  -- assert (H == 2*n - 1)
  t = (ring H)_0
  assert (H == 2*t - 1)
///

TEST ///
  kk = ZZ/32003
  R = kk[x]
  maxR = ideal(x)
  hilbertSamuelPolynomial(maxR)
  QQ[a]
  H = hilbertSamuelPolynomial(maxR,a)
  assert (H == a)
  -- H = hilbertSamuelPolynomial(maxR)
  -- assert (H == n)
///

TEST ///
  kk = ZZ/32003
  S = kk[x,y,z,w]
  I = ideal(z^3-y*w,y*z-x*w,y^3-x*z)
  R = S/I
  maxR = ideal(x,y,z,w)
  H = hilbertSamuelPolynomial(maxR)
  
  A = S_maxR
  IA = sub (I, A)
  J = ideal(x+w) + IA
  decompose J
  minimalPrimes J
  
  dim R
  length(R^1/maxR^3) 
  Q = ideal(w+x)
  decompose Q
  netList oo


  transpose gens gb I
  dim I
  decompose I
///

end--

-* Development section *-
restart
needsPackage "HilbertSamuel"
check "HilbertSamuel"

uninstallPackage "HilbertSamuel"
restart
installPackage "HilbertSamuel"
viewHelp "HilbertSamuel"



kk = ZZ/32003
S = kk[x,y,z,w]
I = ideal(z^3-y*w,y*z-x*w,y^3-x*z)
R = S/I
maxR = ideal(x,y,z,w)
hilbertSamuelPolynomial(maxR)

R^1/maxR^3
basis (R^1/maxR^3)
numcols oo

methods LocalRings
use S
A = localRing(S,ideal(x,y,z,w))
max A
A^1/(max A)^3
basis oo
dim A

A = localRing(S,ideal(x,y,z))
dim A

kk = ZZ/32003
S = kk[x,y,z]
I = ideal(z^2-x*y)
R = S/I
maxR = ideal(x,y,z)
hilbertSamuelPolynomial(maxR)

TODO:

1. add more tests.
2. add a length function.
3. add a function to determine if an ideal is a parameter.
4. add a function to compute length of module over polynomial ring ZZ.
5. make hilbertSamuelPolynomial to work for other maximal ideals.



