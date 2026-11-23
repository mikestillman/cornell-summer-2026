needsPackage "Polyhedra"

polytopeFaceLattice = method(Options => {FaceLatticeAlgorithm => "KaibelPfetsch"});

polytopeFaceLattice(Polyhedron) := opts -> P -> (
    alg := opts.FaceLatticeAlgorithm;
    if alg === "Naive" then
        polytopeFaceLatticeNaive P
    else if alg === "KaibelPfetsch" then
        polytopeFaceLatticeKP P
    else
        error "Unknown face lattice algorithm."
);

-- Contains two methods for computing the face lattice of
-- a polytope. Both methods output 
-- 1) a list of faces grouped by rank, and
-- 2) a hash table containing each face's rank and lower/upper covers.
-- Also has functions for computing the ranks and upper intervals of
-- each face (needed in bivariateAccumulation).

-- polytopeFaceLatticeNaive uses the faces command in the
-- Polyhedra package and computes covers by inclusion of
-- face index sets in successive dimensions. The naivete
-- is due to testing each face of a given rank against
-- all faces in the next rank.

polytopeFaceLatticeNaive = method()

polytopeFaceLatticeNaive(Polyhedron) := P -> (

    d := dim P;
    print "Calling faces command:";
    f := faces P;   

    -- faces P orders faces by codimension. For each face it gives
    -- a pair containing vertex indices and ray indices. We reverse
    -- to order by dimension, and keep only the vertex indices.

    facesByRank := apply(reverse(0..d), k -> apply(f#k, face -> sort(face#0)));

    -- Add the empty face at rank zero.

    facesByRank = prepend({{}}, facesByRank);

    print "Initializing hash table:";
    faceData := new MutableHashTable;

    for i in 0..d+1 do (
        for F in facesByRank#i do (
            faceData#F = new MutableHashTable from {
                "rank" => i,
                "lowerCovers" => {},
                "upperCovers" => {}
            };
        );
    );

    print "Convering relations:";
    for i in 0..d do (
        for F in facesByRank_i do (
            for G in facesByRank_(i+1) do (
                if isSubset(F,G) then (
                    faceData#G#"lowerCovers" = append(faceData#G#"lowerCovers",F);
                    faceData#F#"upperCovers" = append(faceData#F#"upperCovers",G);
                );
            );
        );
    );

    return(facesByRank, faceData)
);

-- The algorithm described in "Computing the face
-- lattice of a polytope from its vertex-facet
-- incidences" by Kaibel and Pfetsch is implemented
-- below.

-- Helper functions:

-- Computes the vertex-facet incidence matrix 
-- of a polytope directly from its vertices and
-- supporting hyperplanes. (The vertexFacetMatrix
-- in Polyhedra calls faces(P,1) and is much slower;
-- might want to change that?)

vertexFacetMatrixFast = P -> (
    V := vertices P;
    (H, b) := halfspaces P;

    S := H * V;

    n := numColumns V;
    m := numRows H;

    map(ZZ^n, ZZ^m, (i, j) -> if S_(j,i) == b_(j,0) then 1 else 0)
);

-- vertexFacetIncidenceLists puts incidence relations
-- in the "sorted sparse format" specified in Section 2.2,
-- i.e., for each vertex it gives a list of the facets it's
-- contained in, and for each facet it gives a list of
-- the vertices it contains.

vertexFacetIncidenceLists = P -> (
    
    A := vertexFacetMatrixFast P;

    facetsAtVertex := apply(entries A,
        row -> positions(row, x -> x == 1));

    verticesAtFacet := apply(entries (transpose A),
        col -> positions(col, x -> x == 1));

    (facetsAtVertex, verticesAtFacet)
);

-- facetsContaining gives the list of the facets 
-- containing each vertex in a subset S. verticesIn
-- gives the list of vertices contained in each facet
-- in a subset T. Both are computed by intersecting
-- lists given by vertexFacetIncidenceLists.

facetsContaining = (S, facetsAtVertex, m) -> (
    T := set (0..<m);
    scan(S, v -> T = intersect(T, set(facetsAtVertex#v)));
    sort toList T
);

verticesIn = (T, verticesAtFacet, n) -> (
    S := set (0..<n);
    scan(T, f -> S = intersect(S, set(verticesAtFacet#f)));
    sort toList S
);

-- The next helper computes the upper covers of a face
-- F according to Section 2.3. We first compute the collection
-- of faces F(v) = cl(F union {v}) for v in V - F. But we do
-- not use a closure function. We use the identity
--
-- facetsContaining(F union {v}) = facetsContaining(F)
--                                 intersect facetsContaining({v}).
--
-- Then cl(F union {v}) = verticesIn(FacetsContaining(F union {v}))
-- can be expressed as verticesIn of the intersection.
--
-- So we compute facetsContaining(F) once and retrieve facetsContaining({v})
-- for each v in V - F. In particular, we retrieve via facetsAtVertex#v.

-- The labeling procedure is as follows. Each
-- such v is initially labeled "candidate". If there is some
-- "candidate" v available, and F(v) - {v} contains some w labelled
-- either "minimal" or "candidate", we remove the label "candidate"
-- from v (and set its label to null). Otherwise we label v "minimal".
-- The upper covers of F are exactly the F(v) with v labelled "minimal".

upperCovers = (F, facetsAtVertex, verticesAtFacet) -> (

    n := #facetsAtVertex;
    m := #verticesAtFacet;

    -- We first compute the candidate faces F(v), for each
    -- v outside F.

    -- Note: Implementing the candidate pruning suggested on
    -- pages 9-10 didn't speed things up; added overhead?

    outside := select(0..<n, v -> not member(v,F));
    facetsF := set facetsContaining(F, facetsAtVertex, m);
    candidateFaces := new MutableList from n;

    scan(outside, v -> (
        T := intersect(facetsF, set(facetsAtVertex#v));
        candidateFaces#v = verticesIn(toList T, verticesAtFacet, n);
    ));

    -- We now identify the minimal faces.

    labels := new MutableList from n;
    scan(outside, v -> labels#v = "candidate");
    for v in outside do (
        if labels#v === "candidate" then (
            containsOtherActiveVertex := any(candidateFaces#v, w ->
                w != v and (
                    labels#w === "candidate" or
                    labels#w === "minimal"
                )
            );
            if containsOtherActiveVertex then (
                labels#v = null;
            ) else (
                labels#v = "minimal";
            );
        );
    );

    -- Return the upper covers of F.

    apply(select(outside, v -> labels#v === "minimal"), v -> candidateFaces#v)
);

-- This helper computes canonical spanning sets as described
-- in Section 2.4 and used in the face tree below.

canonicalSpanningSet = (F, facetsAtVertex) -> (

    if #F <= 2 then return F;

    C := {F_0, F_1};
    facets := intersect(set(facetsAtVertex#(F_0)),set(facetsAtVertex#(F_1)));

    for v in drop(F, 2) do (
        newFacets := intersect(facets, set(facetsAtVertex#v));
        if newFacets != facets then (
            C = append(C, v);
            facets = newFacets;
        );
    );

    C
);

-- This helper returns the node in the
-- face tree corresponding to a face in 
-- the face lattice.

faceTree = (F, root, facetsAtVertex) -> (

    C := canonicalSpanningSet(F, facetsAtVertex);
    node := root;

    for v in C do (
        children := node#"children";
        if not (children#?v) then (
            children#v = new MutableHashTable from {
                "children" => new MutableHashTable,
                "faceNode" => null
            };
        );
        node = children#v;
    );

    node
);

-- This helper implements the Kaibel-Pfetsch
-- algorithm in the bottom-up, vertices-first
-- direction.

kaibelPfetsch = (facetsAtVertex, verticesAtFacet, d) -> (

    faceData := new MutableHashTable;
    faceData#({}) = new MutableHashTable from {
        "rank" => 0,
        "lowerCovers" => {},
        "upperCovers" => {}
    };

    root := new MutableHashTable from {
        "children" => new MutableHashTable,
        "faceNode" => {}
    };

    -- Queue of discovered faces awaiting processing.
    -- Note: Originally implemented the queue as a list
    -- of faces and was using drop, but apparently this
    -- duplicates the list every time...

    Q := new MutableHashTable;
    Q#0 = {};
    head := 0;
    tail := 1;

    while head < tail do (

        F := Q#head;
        remove(Q, head);
        head = head + 1;

        r := faceData#F#"rank";
        covers := upperCovers(F, facetsAtVertex, verticesAtFacet);

        -- Record all upper covers.
        faceData#F#"upperCovers" = covers;

        for G in covers do (
            node := faceTree(G, root, facetsAtVertex);

            -- If G has not yet been added to the face lattice:
            if node#"faceNode" === null then (
                node#"faceNode" = G;
                faceData#G = new MutableHashTable from {
                    "rank" => r+1,
                    "lowerCovers" => {},
                    "upperCovers" => {}
                };

                -- Enqueue G.
                Q#tail = G;
                tail = tail + 1;
            );

            -- Record the lower covering relation F < G.
            faceData#G#"lowerCovers" =
                append(faceData#G#"lowerCovers", F);
        );
    );

    -- Construct facesByRank from faceData.
    byRank := partition(
        F -> faceData#F#"rank",
        keys faceData,
        toList (0..d+1)
    );

    facesByRank := apply(d+2, r -> byRank#r);

    (facesByRank, faceData)
);

-- The default implementation of the algorithm
-- runs bottom-up, i.e., vertices-first. We also
-- implement top-down, i.e., facets-first, traversal, 
-- if there are fewer facets than vertices. This is 
-- equivalent to running the algorithm on the dual
-- polytope. The justification here is that the
-- (bottom-up) algorithm generates candidate upper covers
-- as closure(face union vertex). Facets correspond
-- to vertices of the dual, so if there are fewer
-- facets, going top-down will generate fewer candidate
-- upper covers for each face. The helper below converts
-- the output of the algorithm run on the dual back
-- to the primal, i.e., it inverts the face lattice
-- and reverses covering relations.

dualToPrimal = (dualFacesByRank, dualData, verticesAtFacet, n, d) -> (

    -- Convert dual faces to primal vertex sets.
    primalOf := new MutableHashTable;

    for r from 0 to d+1 do (
        for T in dualFacesByRank#r do (
            primalOf#T = verticesIn(T, verticesAtFacet, n);
        );
    );

    -- Reverse ranks and convert faces.
    facesByRank := apply(d+2, r ->
        apply(dualFacesByRank#(d+1-r), T -> primalOf#T)
    );

    -- Reverse the covering relations.
    faceData := new MutableHashTable;

    for r from 0 to d+1 do (
        for T in dualFacesByRank#r do (

            F := primalOf#T;

            faceData#F = new MutableHashTable from {
                "rank" => d+1-r,

                "lowerCovers" => apply(
                    dualData#T#"upperCovers",
                    G -> primalOf#G
                ),

                "upperCovers" => apply(
                    dualData#T#"lowerCovers",
                    G -> primalOf#G
                )
            };
        );
    );

    (facesByRank, faceData)
);

-- Below is the algorithm, with adaptive
-- traversal, implemented as a method.

polytopeFaceLatticeKP = method();

polytopeFaceLatticeKP(Polyhedron) := P -> (

    (facetsAtVertex, verticesAtFacet) := vertexFacetIncidenceLists P;

    d := dim P;
    n := #facetsAtVertex;
    m := #verticesAtFacet;

    if m < n and d > 0 then (

        (dualFacesByRank, dualData) :=
            kaibelPfetsch(verticesAtFacet, facetsAtVertex, d);

        dualToPrimal(dualFacesByRank, dualData, verticesAtFacet, n, d)

    ) else (

        kaibelPfetsch(facetsAtVertex, verticesAtFacet, d)
    )
);

-- This function outputs the list of upper
-- intervals [F, Delta] of all faces F of
-- a polytope Delta, needed by bivariateAccumulator.
-- Importantly, each upper interval is given
-- with its elements in order of increasing rank.

upperIntervals = faceLattice -> (
    facesByRank := faceLattice#0;
    faceData := faceLattice#1;
    allFaces := flatten facesByRank;

    -- Record positions in increasing-rank order.
    indexT := new MutableHashTable;
    for i from 0 to #allFaces-1 do
        indexT#(allFaces#i) = i;

    upperList := new MutableHashTable;

    -- Process faces in decreasing rank.
    for faces in reverse facesByRank do (
        for F in faces do (
            U := {F};

            -- Collect upper intervals of upper covers.
            for H in faceData#F#"upperCovers" do
                U = U | upperList#H;

            U = unique U;

            -- Restore increasing-rank order.
            indexFacePairs := apply(U, G -> {indexT#G, G});
            U = apply(sort indexFacePairs, pair -> pair#1);

            upperList#F = U;
        );
    );

    upperList
);

-- This function gives a hash table of ranks
-- keyed by faces.

-- (Can/should this be done differently? 
-- It's just extracting ranks from faceData...)

ranks = faceLattice -> (
    (facesByRank, faceData) := faceLattice;

    new HashTable from apply(
        flatten facesByRank,
        F -> F => faceData#F#"rank"
    )
);

end--

load "polytopeFaceLattice.m2"

-- Tests:

P = hypercube 2;

l = polytopeFaceLattice P

l_0
l_1

upperIntervals l

ranks l