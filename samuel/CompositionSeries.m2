restart

compositionSeries = method()
compositionSeries(Module) := List => (M) -> (
    -- let x_1..x_n be the generators of M
        -- define the module M first, then 
        C := res M 
        L := dd^C_1
        entries L
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

compositionSeries(Ideal) := List => (I) -> (
    -- check if the quotient R/I is of finite length
    R := ring I
    -- right now, R should be a polynomial ring over a field and I should be a monomial ideal
    n := numgens R
    L := {0}
    for i from 0 to n-1 do (
        k := 0
        while not isSubset(ideal(R_0)^k,I) do (
            k = k+1; 
            append(L,R/ideal(R_0)^k)
        )
    )
)


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
