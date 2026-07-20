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




compositionSeries = method()
compositionSeries(Ideal) := List => (I) -> (
    -- TODO: check if the quotient R/I is of finite length
    R := ring I;
    m := radical I;
    L := (entries gens m)#0;
    n := #L;
    k := R/m;
    output := {I};
    while numcols(basis(prune(R/I ** k))) > 1 do (
        for i from 0 to n-1 do (
            J := (I:L#i);
            if not isMember(L#i,I) and not J/I == 0 then (
                -- TODO: find out if J always contain I properly, i.e. is it always true that J/I is nonzero? 
                if numcols(basis(prune(J/I ** k))) == 1 then (  -- need to check this is a simple module, but the current check does not work. 
                                                                -- for example, if I = ideal(x^2,y^2) and J = ideal (x,y^2) in R = QQ[x,y], then numcols(basis(prune(J/I ** k))) = 1, 
                                                                -- but J/I is not simple because (x^2,y^2) \subset (x^2,xy,y^2) \subset (x,y^2).
                                                                -- might be able to use hilberFunction in nice situation to count dimension over coefficient ring.
                    output = append(output, J);
                    I = J;
                    break
                )
                else error "not implemented"
                -- TODO: in this case, J/I is not simple 
                -- should "call the function recursively" to fill out a longest chain of submodule of J/I
                -- I don't know enough coding to do this yet
            );
        );
    );
    return output
)

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
isField oo


R = QQ[x,y,z]
M = R^2

I = ideal(x-1,y-1,z-1)
R/I^3
R/ideal(x^2,x*y,x*z,y^2,y*z,z^2)
basis oo
basis(R/ideal(x^2,x*y,x*z,y^2,y*z,z^2))
basis(R/ideal(x,x^2,x*y,x*z,y^2,y*z,z^2))

?leadTerm
methods leadTerm
code 0

leadTerm(x^2+y^4)
degree leadTerm(x^2+y^4)

leadTerm RingElement := RingElement => (f) -> someTerms(f,0,1)
someTerms(RingElement,ZZ,ZZ) := RingElement => (f,i,n) -> new ring f from rawGetTerms(numgens ring f,raw f,i,n+i-1)

leadTerm(x^2+y^4) = someTerms(x^2+y^4,0,1)
someTerms(x^2+y^4,0,1)= new ring x^2+y^4 from rawGetTerms(numgens ring(x^2+y^4),raw(x^2+y^4),0,0)
(x^2+y^4)#0
someTerms(x^2+y^4,0,1) = new ring x^2+y^4 from rawGetTerms(3,y4+x2,0,0)
