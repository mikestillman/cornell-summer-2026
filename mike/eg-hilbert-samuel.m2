

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
L = eliminate(t, J)
transpose gens L
L1 = trim( L + ideal(x,y,z,w))

hilbertSeries L1
reduceHilbert oo
hilbertPolynomial(L1, Projective => false )