-* 
Form a sequence we can take the repeated difference and use the first term
of each of the repeated differences to reconstruct the polynomial from 
which the sequence was sampled. We should maybe write a few methods:

0: A method to collect the data of taking repeated successive difference

1: a method to determine if the given sequence came from a polynomial
    take the repeated differences until either the sequence converges
    to the zero list or until we are left with a single term

2: a method which constructs the polynomial
    given the 2-d list of repeated differences 
    take the first element from each term and then use the formula
    how do we adjust the formula for if the sequence is taken from the nth
    sample rather than the 0th sample?
*-

-- create the 2d array of successive differences
succDiff = (L) -> (
    if not instance(L, List) then error "Input must be a list";
    -- check each element of input list is an integer, or things we can do subtraction with
    for i from 1 to #L-1 list L#i - L#(i-1)
)


-*
    Takes a list and repeated takes the successive difference
*- 
allSuccessiveDifferences = method()
allSuccessiveDifferences(List) := List => (L) -> (
    currentList = L; 
    nextList = null;
    for i from 1 to #L list (
        currentList
    )
    do (
        currentList = succDiff(currentList);
    )
)

-* 
    Create polynomial from repeated differences

    1. Collect repeated differences
    2. Check that this data defines a polynomial
    3. use the formula to construct the polynomial
*-
polynomialFromSuccessiveDifferences = method()
polynomialFromSuccessiveDifferences(List) := RingElement => (L) -> (
    allDifferences = allSuccessiveDifferences(L);
    -- The following line checks if each row is the zero list
    isAllZeros = apply(
        allDifferences,
        L -> all(L, x -> x == 0)
    );
    if all(isAllZeros, x -> x == false) then throw error "Data does not come from polynomial";

    -- write subroutine to build the polynomial from the data 
    coeffs = apply(allDifferences, x -> x#0); -- depends on each list in allDifferences being nonempty

    -- The following computation is called something like the ``Newton
    -- Difference formula''
    -- or the ``Newton–Gregory forward interpolation formula'' perhaps we
    -- should find a reference.
    finalTerms = for i from 0 to #L-1 list coeffs#i * binomial(x,i);
    return sum(finalTerms);
)


-- allSuccessiveDifferences tests
-- TODO: if we ever happen upon the zero list do we want to terminate
-- immediately?

L1 := {0,1,4,9,16,25};
allSuccessiveDifferences(L1) == 
{
    {0,1,4,9,16,25},
    {1, 3, 5, 7, 9},
    {2, 2, 2, 2},
    {0,0,0},
    {0,0},
    {0}
}

L2 := {0,2,4,9,16,25};
allSuccessiveDifferences(L2) == 
{
    {0,2,4,9,16,25},
    {2, 2, 5, 7, 9},
    {0, 3, 2, 2},
    {3, -1, 0},
    {-4, 1},
    {5}
}


-- constructPolynomialFromRepeatedDifference tests
-- L1: should return x^2
-- L2: should fail
polynomialFromSuccessiveDifferences(L1)
polynomialFromSuccessiveDifferences(L2)