3. add a function to determine if an ideal is a parameter ideal.
    Use isPrimary?
    - Here is some more detail
    - Exercise: primary in a localisation if is primary and contained in prime that you're localising at
    -  Implementation for is Primary:
    - given an ideal in a local ring, 1) sub the ideal into the ambient ring 2) check if contained in prime being localised at 3) use the already implemented function isPrimary for non-local rings

-*
-- create a local ring and an ideal in that local ring
-- use the procedure above to test if the given ideal is a primary ideal
take an ideal, check that it's an ideal of a local ring
get the lifted ideal
check that it's contained in the primary ideal that we've localised at
check that the lifted ideal is primary in the ambient ring
*- 



radical I2

isPrimary liftUp(I2)
radical liftUp(I2)
isPrimary liftUp(I3)

isSubset(liftUp(I2), M)

-- here's a procedure
isPrimaryLocalRing = method();
isPrimaryLocalRing(Ideal) := RingElement => (I) -> (
	if not instance(RM, LocalRing) then error "Ambient ring of I is not a LocalRing";
	liftedIdeal := liftUp(I);
	localisedPrime = liftUp max ring I;
	return (isPrimary liftedIdeal) and (isSubset(liftedIdeal, localisedPrime))
	-- This last check might be superfluous, it might be that 
	-- the lifted ideal is always contained in the lifted maximal ideal
)

needsPackage "LocalRings";
R = ZZ/32003[a..d]
M = ideal(a,b,c,d)
RM = R_M
-- The following are some primary ideals
I1 = m = max RM
I2 = m^2
I3 = ideal(a)
I4 = ideal(a*b) -- should not be primary

isPrimaryLocalRing I1 
isPrimaryLocalRing I2
isPrimaryLocalRing I3
isPrimaryLocalRing I4 -- this last one should be false