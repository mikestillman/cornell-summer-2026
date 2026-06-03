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
  R := ring maxR;
  if ring maxR =!= R then error "Ideals must be in the same ring";
  if maxR =!= ideal gens R then error "localizing at other ideal is not implemented yet";
  G := associatedGradedRing (maxR, Variable => getSymbol "v");
    H := (flattenRing G)#0;
    K := prune H;
    L := forgetVarDegrees K;
    P := hilbertPolynomial(L, Projective => false);
    return P
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
    2+2
SeeAlso
///

doc ///
Key
  hilbertSamuelPolynomial
Headline
  Compute the Hilbert-Samuel polynomial of a module
Usage
  hilbertSamuelPolynomial(M,maxR)
Inputs
  M:Module
  maxR:Ideal
Outputs
  :RingElement
    in the ring $\mathbb{Q}[t]$
Description
  Text
  Example
    2+2
SeeAlso
///

-* Test section *-
TEST /// -* [insert short title for this test] *-
  assert (2+2 == 4)
-- test code and assertions here
-- may have as many TEST sections as needed
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
S = kk[x,y]
I = ideal(y^2-x^3)
R = S/I
maxR = ideal(x,y)
hilbertSamuelPolynomial(maxR)
ideal gens R


kk = ZZ/32003
R = kk[x,y,z,w]
I = ideal(z^3-y*w,y*z-x*w,y^3-x*z)
maxR = ideal(x,y,z,w)
hilbertSamuelPolynomial(I,maxR)

