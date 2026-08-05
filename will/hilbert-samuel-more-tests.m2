TEST /// -* Multiple calls to hilbert samuel in the same block*-
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
-* TODO *-


TEST /// -* Attempt to pass non-Local ring *-
    
///

TEST /// -* Attempt to localise at an ideal other than (x_i) *- 
kk = ZZ/32003
S = kk[x,y,z]
I = ideal(z^2 - x*y)
maxR = ideal(x-2, y-3,z-1)
assert(try(
        H = hilbertSamuelPolynomial(maxR);
    )
    then false
    else true
)
///

