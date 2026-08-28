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

export {"isSimple", "compositionSeries"}

-* Code section *-

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

compositionSeries = method()
compositionSeries(Ideal) := List => (I) -> (
    L := associatedPrimes I;
    -- Theorem: R/I is of finite length if and only if Ass(I) consists of all maximal ideals.
    if not all(L, isMaximal) then error "Input is not an ideal of finite colength";
    if #L == 1 then return compositionSeriesPrimary(I);

    PD := primaryDecomposition I;
    L = apply(PD, J -> radical J);
    -- this should be the same as L as a set, but does it change order?
    -- if not this line can be omitted.
    if not #L == #PD then error "associated prime should have the same length as primary decomposition?";
    -- is this true?

    M := append(for i from 1 to #PD-1 list intersect(PD_{i..#PD-1}),sub(ideal 1,ring I));
    flatten(for i from 0 to #PD-1 list apply(compositionSeriesPrimary(PD#i), J -> intersect(M_i, J)))
)

compositionSeriesPrimary = method()
compositionSeriesPrimary(Ideal) := (I) -> (
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
I = ideal(x^3)
assert(compositionSeries(I) == {ideal(x^3), ideal(x^2), ideal(x)})
///

TEST ///
R = QQ[x,y]
I = ideal(x^2,y^2)
assert(compositionSeries(I) == {ideal(x^2,y^2), ideal(x^2,x*y,y^2), ideal(x,y^2), ideal(x,y)})
I = ideal(x^3,y)
assert(compositionSeries(I) == {ideal(x^3,y), ideal(x^2,y), ideal(x,y)})
///

TEST ///
R = QQ[x]
I = ideal((x-1)^2*(x+1)^2)
assert(compositionSeries(I) == {ideal((x-1)^2*(x+1)^2), ideal((x-1)*(x+1)^2), ideal((x+1)^2), ideal(x+1)})
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


--outlien for finitely generated module
compositionSeries = method()
compositionSeries(Module) := List => (M) -> (
    -- let x_1..x_n be the generators of M
        -- define the module M first, then 
        C := res M;
        L := dd^C_1;
        entries L;
    -- first have a chain of submodules given by 
    -- 0 \subset (x_1) \subset (x_1,x_2) \subset ... \subset (x_1,...,x_n) = M
    -- then for each i, the quotient (x_1,...,x_i)/(x_1,...,x_{i-1}) 
    -- is isomorphic to R/{r in R | rx_i in (x_1,...,x_{i-1})}
    -- check each quotient is of finite length.

    -- need characterization of the ideal {r in R | rx_i in (x_1,...,x_{i-1})}
    -- need to find a way to compute the composition series for 
    -- R/ideal, i.e., a chain of ideals from an given ideal up to R
    -- R \supset I_1 \supset I_2 \supset ... \supset I_n = I
    -- such that each I_i/I_{i+1} is simple.

    -- after having this, then the composition series for M should be 
    -- (say (x_1) = R/I and (x_1,x_2)/(x_1) = R/J)
    -- 0 \subset R/I_1 \subset R/I_2 \subset ... \subset R/I_n = R/I = (x_1)
    -- \subset (lift of R/J_1*((x_1,x_2)/(x_1)) to (x_1,x_2))...
)

-- some code to help see what is going on under the hood
R = ZZ/101[x]
I = ideal(x^2*(x-1)^2)
compositionSeries(I)
L = associatedPrimes I
PD = primaryDecomposition I
M = append(for i from 1 to #PD list intersect(PD_{i..#PD-1}),sub(ideal 1,R))

compositionSeriesPrimary(PD#0)
compositionSeriesPrimary(PD#1)

apply(compositionSeriesPrimary(PD#0), J -> intersect(M#0, J))
apply(compositionSeriesPrimary(PD#1), J -> intersect(M#1, J))






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