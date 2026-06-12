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

--- given a graded ring return the given ring with standard grading
forgetVarDegrees2 = (R1) -> (
  stdGrading := {(numgens R1): 1};
  newAmbient := (coefficientRing R1)[gens R1, Degrees => stdGrading];
  return (newAmbient/sub(ideal R1, newAmbient))
)

hilbertSamuelPolynomial = method()
hilbertSamuelPolynomial(Ideal) := RingElement => (maxR) -> (
  hilbertSamuelPolynomial(maxR,HilbRing_0)
)

hilbertSamuelPolynomial(Ideal,RingElement) := RingElement => (maxR,n) -> (
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
  -- return sub(P, {(ring P)_0 => n}) -- gives the polynomial for length(R/m^{n+1}) 
  return sub(P, {(ring P)_0 => n - 1}) -- gives the polynomial for length(R/m^n)
)

-* Documentation section *-
beginDocumentation()

doc ///
Key
  HilbertSamuel
Headline
  Compute the Hilbert-Samuel polynomial of a module.
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
  Compute the Hilbert-Samuel polynomial of a module.
Usage
  hilbertSamuelPolynomial(maxR)
Inputs
  maxR:Ideal
Outputs
  :RingElement
    in the ring $\mathbb{Q}[n]$
Description
  Text
    The output is the polynomial that agree with the function
    taking n to length(R/m^n) for sufficiently large n.
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
  R = kk[x]
  maxR = ideal(x)
  H = hilbertSamuelPolynomial(maxR)
  -- assert (H == n)
  t = (ring H)_0
  assert (H == t)
  QQ[a]
  H = hilbertSamuelPolynomial(maxR,a)
  assert (H == a)
///

TEST /// 
  kk = ZZ/32003
  S = kk[x,y]
  I = ideal(y^2-x^3)
  R = S/I
  maxR = ideal(x,y)
  H = hilbertSamuelPolynomial(maxR)
  -- assert (H == 2*n - 1)
  t = (ring H)_0
  assert (H == 2*t - 1)
  QQ[a]
  H = hilbertSamuelPolynomial(maxR,a)
  assert (H == 2*a - 1)
///

TEST ///
  kk = ZZ/32003
  S = kk[x,y,z]
  I = ideal(z^2-x*y)
  R = S/I
  maxR = ideal(x,y,z)
  H = hilbertSamuelPolynomial(maxR)
  t = (ring H)_0
  assert (H == t^2)
  QQ[a]
  H = hilbertSamuelPolynomial(maxR,a)
  assert (H == a^2)
///

TEST ///
  kk = ZZ/32003
  S = kk[x,y,z,w]
  I = ideal(z^3-y*w,y*z-x*w,y^3-x*z)
  R = S/I
  maxR = ideal(x,y,z,w)
  H = hilbertSamuelPolynomial(maxR)
  t = (ring H)_0
  assert (H == 10*t - 20)
  QQ[a]
  H = hilbertSamuelPolynomial(maxR,a)
  assert (H == 10*a - 20)
///

"TEST"
///
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



TODO:

1. add more tests.
    added two already.
    Will: add more test.
    - Notes for additional tests to write
    - more tests with multiple asserts/ multiple calls to hilbert samuel in one test block
    - tests to make sure that failing cases / non-supported cases actuallyu throw an error

2. add a length function.
    newlength = M -> (
      -- R = ring M;
      return numcols basis M
    )
3. add a function to determine if an ideal is a parameter ideal.
    Use isPrimary?
    - Here is some more detail
    - Exercise: primary in a localisation if is primary and contained in prime that you're localising at
    -  Implementation for is Primary:
    - given an ideal in a local ring, 1) sub the ideal into the ambient ring 2) check if contained in prime being localised at 3) use the already implemented function isPrimary for non-local rings


4. add a function to compute length of module over polynomial ring ZZ.
5. make hilbertSamuelPolynomial to work for other maximal ideals.
    S = kk[x_1..x_n]
    I = ideal(f_1..f_r)
    R = S/I
    maxR = (x_1-a_1,...,x_n-a_n)
    hilbertSamuelPolynomial(maxR) should be the same as the following
    I = ideal(f_1(x_1+a_1,...,x_n+a_n),...,f_r(x_1+a_1,...,x_n+a_n))
    R = S/I
    maxR = ideal(x_1,...,x_n)




Questions for Mike:
1. Any idea to get start on compute hilbertSamuelPolynomial for general parameter ideals?
    length(R/m^n)=length(R_m/m^n)
    length(R/q^n)=length(R/q)+length(q/q^2)+...+length(q^{n-1}/q^n)
    H(gr_q(R),i)=dim q^i/q^{i+1}=length(q^i/q^{i+1})?
2. How does M2 compute quotient rings?
3. Is there anything stopping it from working in the local ring case?


