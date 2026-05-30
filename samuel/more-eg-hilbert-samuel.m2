restart

kk = ZZ/32003
S = kk[x,y,z,w]
I = monomialCurveIdeal(S, {1,2,3})
I = ideal(z^3-y*w,y*z-x*w,y^3-x*z)

R = S/I
leadTerm I
hilbertSeries I
reduceHilbert oo
dim R

M = ideal(x,y,z,w)
-- Rees algebra:
-- R[Mt]

T = kk[x,y,z,w,a,b,c,d,t]
J = sub(I, T) + ideal (a - t*x, b - t*y, c - t*z, d - t*w )
gens J
transpose gens J
L = eliminate(t, J)
transpose gens L
L1 = trim( L + ideal(x,y,z,w))
gens L1
transpose gens L1

hilbertSeries L1
reduceHilbert oo
hilbertPolynomial(L1, Projective => false )

describe T



-- new example 

kk = ZZ/32003
S = kk[x,y]
I = ideal(y^2-x^3)

R = S/I
M = ideal(x,y)
T = kk[x,y,a,b,t]
J = sub(I, T) + ideal (a - t*x, b - t*y )
L = eliminate(t, J)

L1 = trim( L + ideal(x,y))

hilbertSeries L1
reduceHilbert oo
hilbertPolynomial(L1, Projective => false )

-- another example 

kk = ZZ/32003
S = kk[x,y]
I = ideal(y^2-x^3)

R = S/I
M = ideal(x-1,y)
T = kk[x,y,a,b,t]
J = sub(I, T) + ideal (a - t*x, b - t*y )
L = eliminate(t, J)

L1 = trim( L + ideal(x-1,y))

hilbertSeries L1
reduceHilbert oo
hilbertPolynomial(L1, Projective => false )

-- another example 

kk = ZZ/32003
S = kk[x,y]
I = ideal((y+1)^2-(x+1)^3)

R = S/I
M = ideal(x,y)
T = kk[x,y,a,b,t]
J = sub(I, T) + ideal (a - t*x, b - t*y )
L = eliminate(t, J)

L1 = trim( L + ideal(x,y))

hilbertSeries L1
reduceHilbert oo
hilbertPolynomial(L1, Projective => false )