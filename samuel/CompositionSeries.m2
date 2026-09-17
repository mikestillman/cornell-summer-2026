newPackage(
    "CompositionSeries",
    Version => "0.1",
    Date => "08/25/2026",
    Headline => "Computing composition series",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    Keywords => {""},
    PackageExports => {"PrimaryDecomposition"},
    AuxiliaryFiles => false,
    DebuggingMode => false
    )

export {"getRelations", 
        "isMaximal", 
        "isSimple", 
        "isFiniteColength",
        "isFiniteLength",
        "compositionSeries"}

-* Code section *-

getRelations = method()
getRelations(Module) := (M) -> (
    N := prune M;
    if not numgens N == 1 then error "Expect cyclic module";
    if N == (ring M)^1 then return ideal(0_(ring M));
    return ideal flatten entries relations(N);
)

isMaximal = method()
isMaximal(Ideal) := Boolean => (I) -> (
    R := ring I;
    isPrime I and dim(R/I) == 0
)

isSimple = method()
isSimple(Module) := Boolean => (M) -> (
    -- TODO: add a check if R is a polynomial ring because prune might not work in general.
    -- Theorem: A R-module is simple if and only if it is isomorphic to R/m for some maximal ideal m.
    R := ring M;
    N := prune M;
    -- Case 1: if R is a field, M is simple iff N is a dim 1 vector space
    if isMaximal sub(ideal(0),R) then return numgens N == 1 else
    -- Case 2: if R is not a field, M is simple iff N is a quotient of R by a maximal ideal
    c := (if N.?generators then 1 else 0) + 2 * (if N.?relations then 1 else 0);
    if not c == 2 then return false;  -- c = 2 means N is a quotient
    if not numgens N == 1 then return false;  
    -- I := ideal image N.relations;  -- this does not work for some reason.
                                      -- for example, take R = ZZ/101[x,y]
                                      -- M = ideal(x,y^2)/ideal(x^2,y^2)   
                                      -- N = prune M
                                      -- image N.relations and (entries N.relations)#0 is very similar
    I := ideal(N.relations);
    isMaximal I
)

isFiniteColength = method()
isFiniteColength(Ideal) := Boolean => (I) -> (
    if I == ideal(1_(ring I)) then return true;
    -- Theorem: For a proper ideal I, R/I is of finite length 
    -- if and only if Ass(I) consists of all maximal ideals.
    L := associatedPrimes I;
    all(L, isMaximal)
)

isFiniteLength = method()
isFiniteLength(Module) := Boolean => (M) -> (
    R := ring M;
    N := prune M;
    n := numgens N;
    L := for i from 0 to n-1 list R*M_i;
    K := prepend(L_0,accumulate((x,y) -> x+y,L));
    Q := prepend(prune K_0,for i from 1 to #K-1 list prune(K_i/K_(i-1)));
    all(apply(Q,getRelations),isFiniteColength)
)

compositionSeriesPrimary = method()
compositionSeriesPrimary(Ideal) := (I) -> (
    -- I should be a m-primary ideal for some maximal ideal m.
    m := radical I;
    x := m_*;
    n := #x;
    
    M := prepend(I,apply(toList(0..n-1), i -> I + ideal(x_{0..i})));
    -- M is the list M_i = I + (x_1,...,x_i) for i = 0..n
    -- #M = n+1
    Q := apply(toList(0..n-1), i -> M_(i+1)/M_i);
    -- Q_i is M_(i+1)/M_i
    -- #Q = n
    J := apply(toList(0..n-1), i -> (M_i:x_i));
    -- J_i is the colon ideal (M_i:x_i)
    -- #J = n
    output := {I};
    for i from 0 to n-1 do (
        if Q_i == 0 then ( 
            output = output;
        )
        else if isSimple(Q_i) then (
            output = append(output,trim M_(i+1));
        )
        else (
            output = join(output, apply(drop(compositionSeries(J_i),1), K -> trim(M_i + (x_i * K))));
            output = join(output, {trim M_(i+1)});
        )    
    );
    return output
)

compositionSeries = method()
compositionSeries(Ideal) := List => (I) -> (
    if not isFiniteColength(I) then error "Input is not an ideal of finite colength";
    L := associatedPrimes I;
    -- Question for Mike: since associatedPrimes is already done in isFiniteColength once,
    -- does that get cached and how does one check this?
    -- If not, how can we avoid recomputing it?
    if I == ideal(1_(ring I)) then return {};
    if #L == 1 then return compositionSeriesPrimary(I);

    PD := primaryDecomposition I;
    L = apply(PD, J -> radical J);
    -- this should be the same as L as a set, but does it change order?
    -- if not this line can be omitted.

    M := for i from 1 to #PD-1 list intersect(PD_{i..#PD-1});
    M = append(M,ideal(1_(ring I)));
    flatten(for i from 0 to #PD-1 list 
        apply(compositionSeriesPrimary(PD#i), J -> intersect(M_i, J)))
)
compositionSeries(Module) := List => (M) -> (
    if not isFiniteLength(M) then error "Input is not a module of finite length";
    R := ring M;
    N := prune M;
    n := numgens N;
    L := for i from 0 to n-1 list R*N_i;
    K := prepend(L_0,accumulate((x,y) -> x+y,L));
    Q := prepend(prune K_0,for i from 1 to #K-1 list prune(K_i/K_(i-1)));
    I := apply(Q,getRelations);
    -- Question for Mike: this is repeat (from isFiniteLength) again which I feel like I should avoid.
    -- should I make another function that does this routine and output the things I need?
    -- Or just get rid of isFiniteLength?
    V := for i from 0 to n-1 list matrix apply(entries N_i, x -> {x});
    f := for i from 0 to n-1 list map(N,R^1,V_i);
    -- f_i is the R-modue homomorphism given by 1 |-> N_i.
    -- L_i is the image of f_i by definition.
    -- Kernel of f_i is annihilator of element N_i.
    g := for i from 0 to n-1 list inducedMap(L_i,R^1,f_i);
    -- g_i is just f_i but with target restricted to the image of f_i,
    -- so it can be composed with h_i defined next.
    h := for i from 0 to n-1 list inducedMap(K_i,L_i);
    C := apply(I,compositionSeries);
    inc := for i from 0 to n-1 list apply(C_i, J -> inducedMap(R^1,module J));
    im := for i from 0 to n-1 list apply(inc_i, iota -> image(h_i * g_i * iota));
    output := prepend(im_0,for i from 1 to n-1 list(apply(im_i, Rmod -> Rmod + K_(i-1))));
    apply(flatten output, Nsubmod -> image inducedMap(M,Nsubmod,N.cache.pruningMap))
)



-* Documentation section *-
beginDocumentation()

doc ///
Key
  CompositionSeries
Headline
  Compute a composition series for a finite colength ideal.
Description
  Text
  Example
    R = QQ[x,y]
    I = ideal(x^2(x-1)^2,y^2)
    netList compositionSeries(I)
    #compositionSeries(I)
Caveat
SeeAlso
///

doc ///
Key
  compositionSeries
Headline
  Compute a composition series for a finite colength ideal.
Usage
  compositionSeries(I)
Inputs
  I:Ideal
Outputs
  :List 
    of ideals of R
Consequences
  Item
Description
  Text
  Example
    R = QQ[x,y]
    I = ideal(x^2(x-1)^2,y^2)
    netList compositionSeries(I)
    #compositionSeries(I)
SeeAlso
///

-* Test section *-




TEST ///
R = QQ[x]

assert(not isMaximal(ideal(1_R)))
assert(not isMaximal(ideal(0_R)))
assert(    isMaximal(ideal(x)))
assert(not isMaximal(ideal(x^2)))
assert(not isMaximal(ideal(x*(x+1))))

assert(    isFiniteColength(ideal(1_R)))
assert(not isFiniteColength(ideal(0_R)))
assert(    isFiniteColength(ideal(x)))
assert(    isFiniteColength(ideal(x^2)))
assert(    isFiniteColength(ideal(x*(x+1))))

I = ideal(x^3)
assert(compositionSeries(I) == {ideal(x^3), ideal(x^2), ideal(x)})
I = ideal((x-1)^2*(x+1)^2)
assert(compositionSeries(I) == {ideal((x-1)^2*(x+1)^2), ideal((x-1)*(x+1)^2), ideal((x+1)^2), ideal(x+1)})
///

TEST ///
R = QQ[x,y]

assert(not isMaximal(ideal(1_R)))
assert(not isMaximal(ideal(0_R)))
assert(not isMaximal(ideal(x)))
assert(    isMaximal(ideal(x,y)))
assert(not isMaximal(ideal(x*y)))

assert(    isFiniteColength(ideal(1_R)))
assert(not isFiniteColength(ideal(0_R)))
assert(not isFiniteColength(ideal(x)))
assert(    isFiniteColength(ideal(x,y)))
assert(not isFiniteColength(ideal(x*y)))

I = ideal(x^3,y)
assert(compositionSeries(I) == {ideal(x^3,y), ideal(x^2,y), ideal(x,y)})
I = ideal(x^2,y^2)
assert(compositionSeries(I) == {ideal(x^2,y^2), ideal(x^2,x*y,y^2), ideal(x,y^2), ideal(x,y)})
///

TEST ///
R = QQ[x,y,z]
I = intersect(ideal(x,y^3,z^2),ideal(x^2+1,y-1,(z-2)^2))
compositionSeries(I) 


L = compositionSeries(I)
prune(L#1/L#0)
assert all for i from 1 to #L-1 list (
    isSimple(L#i/L#(i-1))
)
///

end--

-* Development section *-
restart
debug needsPackage "CompositionSeries"
check "CompositionSeries"

uninstallPackage "CompositionSeries"
restart
installPackage "CompositionSeries"
viewHelp "CompositionSeries"


restart




-- Question for Mike:
-- what's going on with these?
R = ZZ/101[x,y,z]
ideal 1_R == ideal R
ideal 0_R == ideal R
ideal 1_R == ideal module R
ideal 0_R == ideal module R






-- compositionSeries example 
R = ZZ/101[x,y,z]

M = ideal(x,y,z)/ideal(x^2,y^2,z^2)
M = cokernel matrix{{x,y,z}}
M = cokernel matrix{{x,y,z,0,0,0,0,0,0},
                    {0,0,0,x^2,y^2,z^2,0,0,0},
                    {0,0,0,0,0,0,x^3,y^3,z^3}}

N = prune M
n = numgens N
L = for i from 0 to n-1 list R*N_i
K = prepend(L_0,accumulate((x,y) -> x+y,L))
Q = prepend(K_0,for i from 1 to #K-1 list K_i/K_(i-1))
I = apply(Q,getRelations)
V = for i from 0 to n-1 list matrix apply(entries N_i, x -> {x})
f = for i from 0 to n-1 list map(N,R^1,V_i)
g = for i from 0 to n-1 list inducedMap(L_i,R^1,f_i)
h = for i from 0 to n-1 list inducedMap(K_i,L_i)
C = apply(I,compositionSeries)
inc = for i from 0 to n-1 list apply(C_i, J -> inducedMap(R^1,module J))
im = for i from 0 to n-1 list apply(inc_i, iota -> image(h_i * g_i * iota))
output = prepend(im_0,for i from 1 to n-1 list(apply(im_i, Rmod -> Rmod + K_(i-1))))
flatten output
apply(flatten output, Nsubmod -> image inducedMap(M,Nsubmod,N.cache.pruningMap))

netList oo
#ooo

image f_0

phi = inducedMap(image f_0,R^1,f_0)
source phi
target phi









-- a different approach that seems to work decently well.
-- but I feel like it is less general than Mike's suggestion.
compositionSeriesTest = method()
compositionSeriesTest(Ideal) := List => (I) -> (
    R := ring I;
    m := radical I;
    output := {I};
    n := 0;
    while not isSubset(m^(n+1),I) do (
        n = n + 1;
    );
    L := flatten entries gens m^n;
    for i from 0 to #L-1 do (
        K := trim(ideal(L#i) + I);
        if isSimple(K/I) then (
            output = append(output,K);
            I = K;
            break
        );
    );
    if not I == m then (
        output = join(drop(output, -1), compositionSeriesTest(I));
    );
    return output
)
compositionSeriesTest(Ideal,ZZ)...


R = ZZ/101[x,y,z]
compositionSeries(ideal(x^2*(x-1)^2,y^2,z^2))
netList oo