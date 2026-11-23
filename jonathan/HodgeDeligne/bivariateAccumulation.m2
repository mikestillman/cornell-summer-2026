-- This file implements the bottom-up pass through
-- the face lattice that computes a weighted sum
-- of bivariate h^* polynomials. The output of
-- weightedAccumulation can then be turned into
-- either the Hodge-Deligne polynomial or the
-- stringy E polynomial through basic polynomial
-- arithmetic.

-- The code below computes the g-polynomials of
-- a "row", e.g., of the intervals 
--      [F,F_1], [F,F_2], ..., [F, Delta]
-- for all F_i above a face F of Delta. The upper
-- interval must be ordered by increasing rank.

gPolynomialRow = (F, upperInterval, ranks, t) -> (
    R := ring t;
    gRow := new MutableHashTable from {F => 1_R};

    for G in drop(upperInterval, 1) do (
        n := ranks#G - ranks#F;
        a := 0_R;

        -- Sum over F <= H < G.
        for H in upperInterval do (
            if ranks#H < ranks#G and isSubset(H, G) then
                a = a + (t-1)^(ranks#G-ranks#H) * gRow#H;
        );

        -- Keep degrees strictly below n/2.
        gRow#G = -part(0, floor((n-1)/2), a);
    );

    gRow
);


-- Compute a weighted sum of bivariate h*-contributions.
-- faces: all faces, ordered by increasing rank.
-- targetFaces: faces whose contributions are accumulated.
-- ranks: face -> rank.
-- upperIntervals: face -> list of faces above it.
-- hStar: face -> Ehrhart numerator.
-- weights: target face -> weight.

-- Idea: Pass target ring to this function? Rather than
-- generating it by examining weight ring?

weightedAccumulation = (faces, targetFaces, ranks, upperIntervals, hStar, weights) -> (

    -- Construct univariate ring for Ehrhart numerators
    -- and bivariate ring for weights.

    R := ring (hStar#(faces#0));
    t := R_0;

    polynomialWeightFaces := select(
        targetFaces,
        F -> instance(weights#F, RingElement)
    );

    S := if #polynomialWeightFaces > 0 then
        ring weights#(polynomialWeightFaces#0)
    else
        (coefficientRing R)["u","v"];

    u := S_0;
    v := S_1;

    uvMap := map(S, R, {u*v});

    -- Initialize Stilde residuals and accumulators for each 
    -- bivariate h* and the final output.

    sTable := new MutableHashTable from apply(faces, F -> F => hStar#F);

    aTable := new MutableHashTable from apply(targetFaces, F -> F => 0_S);

    accumulator := 0_S;

    -- Process faces in increasing rank.
    for F in faces do (
        sF := sTable#F;

        if sF != 0 then (

            -- Compute the g-polynomials of intervals [F,G].
            gRow := gPolynomialRow(F, upperIntervals#F, ranks, t);

            -- Map S(F,t) to u^rS(F,u/v).
            uvSF := sum(
                0..ranks#F,
                i -> coefficient(t^i, sF)
                    * u^(ranks#F-i) * v^i
            );

            -- Propagate S contribution to superfaces and bivariate h*.
            for G in upperIntervals#F do (
                sTable#G = sTable#G - sF * gRow#G;
                if aTable#?G then
                    aTable#G = aTable#G + uvSF * uvMap(gRow#G);
            );
        );

        -- Add weighted h* to accumulator.
        if aTable#?F then
            accumulator = accumulator + aTable#F * weights#F;
    );

    accumulator
);

end

