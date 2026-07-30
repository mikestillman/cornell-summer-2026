restart
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




isMaximal = method()
isMaximal(Ideal) := Boolean => (I) -> (
    R := ring I;
    isPrime I and dim(R/I) == 0
)

isSimple = method()
isSimple(Module) := Boolean => (M) -> (
    -- TODO: fix the case when R is a field.
    -- TODO: add a check if R is a polynomial ring because prune might not work in general.
    -- Theorem: A R-module is simple if and only if it is isomorphic to R/m for some maximal ideal m.
    R := ring M;
    N := prune M;
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

R = ZZ/101[x,y]
I = ideal(x^2,y^2)
J = ideal(x,y^2)
m = ideal(x,y)
M = J/I
N = prune M
peek N
N.relations
ideal(N.relations)
assert(not isSimple M)
assert(isSimple(m/J))

ambient N
ambient M
gens N
gens M
relations M
relations N
target relations M === target generators M
target relations M === ambient M
target relations N === target generators N
target relations N === ambient N

M1 = coker(matrix{{x},{1}})
ambient M1
ambient(prune M1)
peek M1
N1 = prune M1
peek N1
peek N1.cache
peek M1.cache
N1.cache.pruningMap
N1.cache.pruningMap^-1
help minimalPresentation

compositionSeries = method()
compositionSeries(Ideal) := List => (I) -> (
    R := ring I;
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


-- working examples
R = QQ[x]
I = ideal(x^3)
compositionSeries(I)

R = QQ[x,y]
I = ideal(x^2,y^2)
compositionSeries(I)

R = QQ[x,y,z]
I = ideal(x^2,y^2,z^2)
compositionSeries(I)

R = QQ[x,y]
I = ideal((x-1)^2,(y-1)^2)
compositionSeries(I)

-- some code to help see what is going on under the hood
R = QQ[x,y]
I = ideal(x^2,y^2)
compositionSeries(I)

L = compositionSeries(I)
M = L#0
Q = L#1
J = L#2

isSimple(Q_0)
isSimple(Q_1)

L1 = compositionSeries(J_0)
M1 = L1#0
Q1 = L1#1
J1 = L1#2

Q1_0 == 0
Q1_1 == 0
isSimple(Q1_1)








compositionSeries(Ideal) := List => (I) -> (
    -- TODO: think about intersection of primary ideals
        -- Conjecture: 
        -- length of intersection of primary ideals is equal to the sum of lengths of each primary ideal.
        -- Sketch of Idea:
        -- Hopefully R/(q_1 \cap q_2) is isomorphic to R/q_1 \times R/q_2?
    R := ring I;
    if dim(R/I) =!= 0 then error "Input is not an ideal of finite colength";
        -- Theorem: A ring is Artinian if and only if it is Noetherian and has Krull dimension 0.
        -- Question: Can one define a non Noetherian ring in Macaulay2? If so, is there a way to check if a ring is Noetherian?
    m := radical I;
    if not isPrime m then error "non primary ideal not implemented";
    if not isMaximal m then error "input is not an ideal of finite colength"; 
        -- Theorem: Artinian ring have Krull dimension 0. 
    L := m_*;
    n := #L;
    output := {I};
    while not I == m do (
        for i from 0 to n-1 do (
            J := (I:L#i);
            if not isMember(L#i,I) and not J/I == 0 then (
                -- TODO: find out if J always contain I properly, i.e. is it always true that J/I is nonzero? 
                if isSimple(J/I) then (
                    output = append(output,J);
                    I = J;
                    break
                )
                else (
                    -- this mimic the behavior in a previous version but it is wrong
                    output = append(output,J);
                    I = J;
                    break

                    -- this is what I plan to do, but it needs more work
                    -- after pruning and getting a chain of ideal, need to use pruning map to 
                    -- transfer the ideal back to ideals in J containing I
                    -- although it does seems to get length correctly
                    
                    --M := prune(J/I);
                    --K := ideal((entries M.relations)#0);
                    --output = join(output, compositionSeries(K));
                    --I = J;
                    --break
                    
                );
            );
        );
    );
    return output
)
-- I was told its bad to have to many nested loops,
-- but I was not told how to avoid it.




-- working example
R = QQ[x]
I = ideal(x^3)
I = ideal(x^10)
compositionSeries(I)
#compositionSeries(I)  -- length

-- non working example
R = QQ[x,y]
I = ideal(x^2,y^2)
compositionSeries(I)
#compositionSeries(I)
-- should be length 4 and the output of compositionSeries(I) should be 
{ideal(x^2,y^2), ideal(x^2,x*y,y^2), ideal(x,y^2), ideal(x,y)}






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




-- working examples
R = QQ[x]
I = ideal(x^3)
compositionSeriesTest(I)

R = QQ[x,y]
I = ideal(x^2,y^2)
compositionSeriesTest(I)

R = QQ[x,y,z]
I = ideal(x^2,y^2,z^2)
compositionSeriesTest(I)

R = QQ[x,y]
I = ideal((x-1)^2,(y-1)^2)

-- Question: is it true that in k[x_1..x_n], all (x_1..x_n)-primary ideal 
-- are of the form (x_1^a_1,...,x_n^a_n) for some a_i > 0?



-- experiment with extracting info from a resolution of a module

kk = ZZ/101
R = kk[x,y,z]
m = ideal(x,y,z)

M = R^1/m^3
C = res M
L = dd^C_1
L_0
(entries(L_0))#0
(toList L_0)#0
(ideal image (toList L_0)#0)*M
isSubset((ideal image (toList L_0)#0)*M,M)

(ideal matrix dd^(res M)_1_0)

R/ideal image dd^(res (ideal matrix dd^(res M)_1_0))_1
