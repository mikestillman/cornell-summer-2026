newPackage(
    "HodgeDeligne",
    Version => "0.1",
    Date => "...",
    Headline => "...",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    PackageExports => {"Polyhedra", "LatticePolytopes", "Normaliz"}, 
    AuxiliaryFiles => true,
    DebuggingMode => true
    )

-- Note: PackageExports vs Imports?
-- Obviously needs Polyhedra, current version uses Normaliz (naive
-- Ehrhart numerators method) and LatticePolytopes (Cayley polytope
-- construction). Using stringyE will require PALPInterface for 
-- constructing nef partitions.

export {
    "hodgeDeligne",
    "stringyE",
    "FaceLatticeAlgorithm",
    "EhrhartNumeratorsAlgorithm",
    }

-- Unsure what else to export.

-- Code:

load ("HodgeDeligne/polytopeFaceLattice.m2")
load ("HodgeDeligne/ehrhartNumerators.m2")
load ("HodgeDeligne/bivariateAccumulation.m2")

hodgeDeligne = method();

hodgeDeligne(List) := RingElement => L -> (

    r := #L;
    if r == 0 then error "Expected a nonempty list of polytopes.";

    d := ambDim (L#0);

    -- Construct the polytope (Cayley polytope if L > 1).
    P := if r == 1 then L#0 else cayley L;
    V := vertices P;

    -- Construct face lattice and upper intervals.
    print "Construct face lattice, rank table, and upper intervals:";
    elapsedTime(
    faceLattice := polytopeFaceLattice P;
    facesByRank := faceLattice#0;
    faceData := faceLattice#1;
    faceList := flatten facesByRank;
    rankTable := hashTable apply(faceList, F -> F => faceData#F#"rank");
    upperIntervalTable := upperIntervals faceLattice;
    );

    -- Compute Ehrhart numerators of all faces.
    R := ZZ["t"];
    t := R_0;

    print "Compute Ehrhart numerators of all faces:";
    elapsedTime hStarTable := ehrhartNumerators(V, faceList, t);

    -- Bivariate ring for output.
    B := ZZ["u","v"];
    u := B_0;
    v := B_1;
    q := u*v;

    -- Select target faces and assign weights.
    print "Weighted bivariate polynomial accumulation:";
    elapsedTime(
    targetFaces := {};
    weightTable := new MutableHashTable;

    if r == 1 then (

        -- Hypersurface case: The only target face is 
        -- the full polytope. Its weight is (-1)^d-1
        -- if full-dimensional.

        targetFaces = last facesByRank;
        F := targetFaces#0;
        rho := rankTable#F;

        weightTable#F = (-1)^rho * (q-1)^(d-rho+1);

    ) else (

        -- Compute targets and weights for the general
        -- complete intersection case. Targets are 
        -- Cayley polytopes of all subsets of the input
        -- list; we compute these from the big Cayley
        -- polytope.

        -- nVertices is the number of vertices of the
        -- big Cayley polytope. 
        -- vertexBlocks groups the big polytope coordinates
        -- by the input polytope they came from.

        nVertices := numColumns V;

        vertexBlocks := apply(r, i ->
            select(toList(0..(nVertices-1)), j ->
                if i == 0 then
                    all(toList(d..(d+r-2)),
                        k -> V_(k,j) == 0)
                else
                    V_(d+i-1,j) == 1
            )
        );

        -- Each nonempty subset I determines a face.
        for I in drop(subsets r, 1) do (

            vertexIndices := sort flatten apply(
                I, i -> vertexBlocks#i
            );

            -- Find the corresponding face in the face lattice.
            matches := select(
                faceList,
                F -> sort(toList F) == vertexIndices
            );

            F := matches#0;
            rho := rankTable#F;

            targetFaces = append(targetFaces, F);

            -- Compute weight from rank of face in big polytope.
            weightTable#F = (-1)^rho * (q-1)^(d-rho+#I);
        );
    );

    -- Weighted accumulation.
    weightedSum := weightedAccumulation(
        faceList,
        targetFaces,
        rankTable,
        upperIntervalTable,
        hStarTable,
        weightTable
    );
    );

    numerator := (q-1)^d + weightedSum;
    denominator := q^r;
    numerator // denominator
);


-*
stringyE = method();

To-do for stringyE: A function that computes the dual of a 
Gorenstein polytope and keeps track of the correspondence
between primal and dual faces.

Schematically:

Create Gorenstein polytope P from nef partition, and its dual P*.
Record the correspondence between the faces of these polytopes.
Create face lattice L of P. If the face lattice of P* is needed,
it's just L*.
Compute the Ehrhart numerators of all faces of both P and P*.
Call weightedAccumulation on P with the  set of target faces
being all faces of P, and the weights being the Ehrhart numerators
of corresponding dual faces.
*-