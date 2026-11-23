needsPackage "Polyhedra"
needsPackage "Normaliz"

ehrhartNumerators = method(Options => {EhrhartNumeratorsAlgorithm => "Naive"});

ehrhartNumerators(Matrix, List, RingElement) := HashTable => opts -> (V, faceList, t) -> (
    alg := opts.EhrhartNumeratorsAlgorithm;
    if alg === "Naive" then
        ehrhartNumeratorsNaive(V, faceList, t)
    else 
        error "Unknown Ehrhart numerators algorithm."
);

-- The naive method uses Normaliz to compute the
-- Ehrhart numerator of each face. This method
-- doesn't exploit the shared geometry of the faces
-- or allow us to compute only as many coefficients
-- as are needed to generate the Stildes.

-- Input: matrix of vertices, list of vertex indices for each face,
-- and desired output variable.

ehrhartNumeratorsNaive = method();

ehrhartNumeratorsNaive(Matrix, List, RingElement) := HashTable => (V, faceList, t) -> (
    VZ := lift(V,ZZ);
    R := ring t;
    setNmzOption("hilb", true);

    hashTable apply(faceList, F -> (
        F => if #F == 0 then 1_R else (
            indices := toList F;
            C := normaliz(transpose(VZ_indices), "polytope");
            invs := C#"inv";
            h := invs#"hilbert series num";
            sum(#h, i -> h#i * t^i)
        )
    ))
);

-- Point-counting method(s):

-- Triangulation-based method:

end

-- Tests:

load "polytopeFaceLattice.m2"
load "ehrhartNumerators.m2"

P = hypercube 4;

l = polytopeFaceLattice P;

facelist = flatten l_0

V = vertices P

R = ZZ[t]

t = R_0

elapsedTime ehrhartNumerators(V,facelist,t)

