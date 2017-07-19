newPackage(
        "FMPIntersectionTheory",
        Version => "0.1",
        Date => "February 9, 2015",
        Authors => {{Name => "Corey Harris", Email => "charris@math.fsu.edu", HomePage => "http://coreyharris.name"}},
        Headline => "A package for Fulton-MacPherson intersection theory.",
        AuxiliaryFiles => true,
        PackageExports => {"Schubert2"}
)

needsPackage("Schubert2")

-- export { "segreClass" }
export { 
        "chernMather",
        "chernSchwartzMacPherson", 
        "cycleClass",
        "dualDegree", 
        "intersectionProduct",
        --"intersectionring", 
        "polarRanks",
        "sumPolarRanks",
        "projectiveScheme", 
        --"restrictToHplaneSection", 
        "segreClass", 
        "AmbientSpace", 
        "BaseField",
        "CoordinateRing", 
        "CycleClass", 
        "Equations", 
        "Hyperplane", 
        "MakeBaseOfLinearSystem", 
        "ProjectiveScheme", 
        "SuperScheme", 
        "Testing"
}


hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"
-- indexSymbols = value Core#"private dictionary"#"indexSymbols"

-- test whether all generators of I have the same degree
homogenated := I -> (
        -- get a list of degrees of the generators of I and take the max
        gns := flatten entries gens I;
        degs := apply(gns, g -> (degree g)#0);
        maxDeg := max(degs);

        -- test whether all degrees attain the max
        return all(degs, d -> d == maxDeg);
)

-- make all generators of X have the same degree
homogenate := I -> (
        -- no need to do all this work if the generators are already of same degree
        if (homogenated I) then return I;

        -- get list of generators and take max degree
        gns := flatten entries gens I;
        maxDeg := max(apply(gns, g -> (degree g)#0));

        -- split the list into sublists by degree
        -- e.g. { z, xy2, x2y, x3+y3 } -> { {}, {z}, {}, {xy2, x2y}, {x3+y3}  }
        gLists := for i from 0 to maxDeg list (
                select(gns, g -> (degree g)#0 == i)
        );

        J := ideal ( vars ring I ); 

        gs := for i to ( (length gLists)-1) list (
                -- the ith list in gLists is the set of degree i generators
                flatten entries mingens (
                        J^(maxDeg - i) * sub(ideal(gLists#i), ring I)
            ) 
        );
        return trim ideal (flatten gs);
)


ProjectiveScheme = new Type of MutableHashTable
globalAssignment ProjectiveScheme


toString ProjectiveScheme := net ProjectiveScheme := X -> (
        if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
        else "a projective scheme")
ProjectiveScheme#{Standard,AfterPrint} = X -> (
        << concatenate(interpreterDepth:"o") << lineNumber << " : "
        << "a projective scheme in PP^" << dim(X.AmbientSpace) << " defined by " << X.Ideal << endl;
)

projectiveScheme = method(TypicalValue => ProjectiveScheme, Options => {
                SuperScheme => null,  -- a ProjectiveScheme containing the one we are defining
                                                          -- If I is the ideal of SuperScheme in R, and we define our 
                                                          -- new scheme with J in R, we instead will use I+J
                AmbientSpace => null, -- the projective space where we will be computing
                MakeBaseOfLinearSystem => false   -- if true, the ideal used to define the projective scheme should be made to have all terms of same degree
        })
projectiveScheme Ideal :=  opts -> I -> (
        if opts.SuperScheme =!= null then (
                I = trim (I + opts.SuperScheme.Ideal);
        );
        if opts.MakeBaseOfLinearSystem then (
                I = homogenate(I);
        );
        R := ring I;
        N := 0;
        eqs := flatten entries gens I;
        P := if opts.SuperScheme =!= null then (
                        opts.SuperScheme.AmbientSpace
                ) else if opts.AmbientSpace =!= null then (
                        opts.AmbientSpace
                ) else (
                        N = #(flatten entries vars R) - 1;  -- dimension of projective space corresponding to proj(R)
                        projectiveBundle N
                );

        new ProjectiveScheme from {
                global Ideal => I,
                global BaseField => coefficientRing ring I,
                global CoordinateRing => quotient I,
                global Equations => eqs,
                global AmbientSpace => P,
                global Hyperplane => ( chern_1 (OO_P(1)) ), -- the class of a hyperplane in ambientSpace
                global dim => null,
                global degree => null,
                global codim => null,
                CycleClass => null
        }
)

--intersectionring = method()
intersectionRing ProjectiveScheme := X -> (
        return intersectionRing(X.AmbientSpace)
)


-- cycleClass X will return the class of X in the chow group of the ambient projective space
-- The multiplicity of X along the irreducible component Z is the multiplicity of X at a point
-- z in Z.  This is also the degree of the projectivized tangent cone to z in X, 
-- which can be calculated via the Hilbert polynomial of graded ring associated to O(X)/I, 
-- where I is the ideal of .
cycleClass = method()
cycleClass ProjectiveScheme := X -> (
        if X.CycleClass === null then (
                mPrimes := minimalPrimes X.Ideal;  -- irreducible components of X
                X.CycleClass = sum apply (mPrimes, irrComp -> (
                        -- the 
                        hilb := hilbertPolynomial ( tangentCone (sub(irrComp, X.CoordinateRing)) );
                        d := dim hilb; -- dimension of the associated scheme to i
                        m := (hilb#d); -- its geometric multiplicity in X
                        m * (X.Hyperplane)^(dim(X.AmbientSpace)-d)
                ))
        );
        X.CycleClass
)

degree ProjectiveScheme := X -> (
        if X.degree === null then (
                X.degree = degree(X.Ideal)
        );
        X.degree
)

dim ProjectiveScheme := X -> (
        if X.dim === null then (
                X.dim = dim(variety(X.Ideal))
        );
        X.dim
)

codim(ProjectiveScheme) := {} >> opts -> (X) -> (
        if X.codim === null then (
                X.codim = dim(X.AmbientSpace) - dim(X)
        );
        X.codim
)

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------





-- a "good" hyperplane section H on Y (relative to X) is one 
-- which does not contain any distinguished varieties of X
goodHyperplaneSection := (X,Y) -> (
        ds := distinguished ( sub(X.Ideal, Y.CoordinateRing) );
        while (true) do (
                h := random(1, ring(Y.Ideal));
                found := true;
                -- choose a random hyperplane section of Y
                -- test to see if it contains any distinguished varieties of X
                -- if so, start over
                for d in ds do (
                        if isSubset(ideal h, d) then (
                                found = false;
                                break;
                        )
                );
                if found then return h
        )
)


-- 
projDegSaturate := (X,Y) -> (
    
    -- << "calculating degpr(X,Y)" << endl;
    
    ideals := for i from 1 to (dim Y)
        list ( 
            ideal ( sum apply(X.Equations, g -> random(0,ring(X.Ideal))*g ) )
            );
    hyps := sum(ideals);
    
    -- << "saturate " << trim(Y.Ideal + hyps) << " with respect to " << X.Ideal << endl;
    --<< " to get " << saturate(Y.Ideal + hyps, X.Ideal) << " with degree " << degree saturate(Y.Ideal + hyps, X.Ideal) << endl;
    
    if char(X.BaseField) > 0 then (
        -- << ">0  saturating " << trim(Y.Ideal + hyps) << " with respect to " << X.Ideal << endl;
        I := saturate( Y.Ideal + hyps, X.Ideal, Strategy => "F4");
        -- << " result : " << I << endl;
        return degree I
    ) else (
        -- << "0:  saturating " << trim(Y.Ideal + hyps) << " with respect to " << X.Ideal << endl;
        I' := saturate( Y.Ideal + hyps, X.Ideal);
        -- << " result : " << I << endl;
        return degree I'
    )
    -- return degree quotient( Y.Ideal + hyps, X.Ideal )
)

projDegHelmer = method()
projDegHelmer(Ideal,Ideal) := (X,Y) -> (
    S := ring(X);
    kk := coefficientRing ring(X);
    St := kk(monoid[gens S, getSymbol "T"]);
    SX := sub(X,St);
    SY := sub(Y,St);
    varsS :=  (v -> sub(v,St)) \ (gens S);
    n := numgens X;
    Pols := sum ( dim variety Y, jj -> ideal sum (n, i -> random(kk)*SX_i) );
    -- Xs := sum ( n-k, jj -> ideal sum (numgens S, i -> random(kk)*varsS_i) ) 
    LA := ideal ( sum (numgens S, i -> random(kk)*varsS_i) - 1 );
    VS := ideal ( sum ( n, i -> 1 - (last gens St)*random(kk)*SX_i) );
    Wt := SY + Pols + VS + LA;
    return numColumns basis cokernel leadTerm gb(Wt);
)
projDegHelmer(ProjectiveScheme,ProjectiveScheme) := (X,Y) -> (
        projDegHelmer(X.Ideal,Y.Ideal)
)


segreAlgCoefficientMatrix = method()
segreAlgCoefficientMatrix(ZZ,ZZ,ZZ) := (n,r,d) -> (
        l := for i from 0 to r list (
                for j from 0 to r list (
                        binomial(n-i,j-i)*d^(j-i)
                )
        );
        return matrix(l)
)

restrictToHplaneSection = method()
restrictToHplaneSection(ProjectiveScheme, Thing) := (X,h) -> (
        -- here X is the scheme we're restricting and 
        -- h is a hyperplane (degree 1 element of polynomial ring)
        N := dim(X.AmbientSpace);
        -- P := ZZ(monoid[ (i -> getSymbol("w_"|toString(i)) ) \ (0..N-1) ]);
        -- for some reason above line must be run twice to work ?!?
        kk := X.BaseField;
        P := kk(monoid[ (i -> (getSymbol "w")_i ) \ (0..N-1) ]);
        R := ring(X.Ideal);
        coordchangeIdeal := sub(X.Ideal,{R_N => h});
        restrictedIdeal := sub(coordchangeIdeal, {R_N => 0}|((i -> R_i => P_i) \ toList(0..N-1)) );
        -- << toString(restrictedIdeal) << "\n in : " << describe(ring restrictedIdeal) << endl;
        return restrictedIdeal
)

-- TODO : segreClass should take ProjectiveSchemes as the default type
-- converting to ideals and back ruins the intersectionRings (gives !===)
segreClass = method(TypicalValue => RingElement, Options => {Testing => false, Strategy => "Saturate"})
segreClass(Ideal) := opts -> (iX) -> (
        iY := trim ideal 0_(ring iX);
        segreClass(iX, iY, opts)
)
segreClass(Ideal,Ideal) := opts -> (iX,iY) -> (
        Y := projectiveScheme(iY);
        X := projectiveScheme(iX, SuperScheme => Y, MakeBaseOfLinearSystem => true);
        segreClass(X, Y, opts)
)
segreClass(ProjectiveScheme) := opts -> (X) -> (
        -- to compute s(X,PP^N) given X
        -- need to get intersectionring of X or change it to that of PP^N
        iX := X.Ideal;
        iY := trim ideal 0_(ring iX);
        Y := projectiveScheme(iY, AmbientSpace => X.AmbientSpace);
        segreClass(X, Y, opts)
)
segreClass(ProjectiveScheme,ProjectiveScheme) := opts -> (X,Y) -> (
        if not ( X.AmbientSpace === Y.AmbientSpace ) then (
                error "Expected ProjectiveSchemes with the same AmbientSpace"
        );
        H := X.Hyperplane;
        if dim X < 0 then (return 0*H);
        N := dim X;

        d := first degree ( (X.Ideal)_0 ); -- degree of each generator

        X0 := X;
        Y0 := Y;

        eqns := while ( dim X >= 0 )
                list (
                        -- << " 1 " << endl;
                        pdeg := if opts.Strategy == "Helmer" then (
                                        projDegHelmer(X,Y)
                                -- ) else if opts.Strategy == "Saturate" then (
                                ) else (
                                        projDegSaturate(X,Y)
                                );
                        -- << " 2 " << endl;
                        D := ( d^(dim Y) * degree(Y) ) - pdeg;
                        -- << " 3 " << endl;
                        -- if opts.Testing then (<< "D = ( d^(dim Y) * degree(Y) ) - projDeg(X.Ideal,Y.Ideal) = " << d << "^" << dim Y << " * " << degree(Y) << " - " << projDeg(X.Ideal,Y.Ideal) << endl; );
                        D
                )
                do (    
                        -- << " 4 " << endl;
                        -- this line is causing a huge bottleneck
                        -- hyp := goodHyperplaneSection(X,Y);
                        hyp := random(1, ring(Y.Ideal));
                        -- replace X,Y with hyperplane sections
                        -- << " 5 " << endl;
                        IY := restrictToHplaneSection(Y,hyp);
                        IX := sub(restrictToHplaneSection(X,hyp), ring(IY));
                        -- << " 6 " << endl;
                        Y = projectiveScheme IY;
                        X = projectiveScheme(IX, SuperScheme => Y, MakeBaseOfLinearSystem => true);
                );

        -- We need to solve the matrix equation determined by eqns
        -- so we substitute the values from QQ to a finite field
        matC := sub( segreAlgCoefficientMatrix(dim Y0, dim X0, d), ZZ/32479 );
        vecD := sub(transpose matrix {eqns}, ZZ/32479);
        vecA := flatten entries solve(matC,vecD);

        -- finally, take the vector a = (a_0,..,a_n) and form the Segre class
        -- seg = a_0 PP^0 + a_1 PP^1 + .. + a_N PP^N
        if opts.Testing then (
                ringH := ZZ(monoid[getSymbol "H"]);
                H = ringH_0;
                << "C = " << matC << endl;
                << "D = " << vecD << endl;
                << "A = " << vecA << endl;
        );

        seg := sum ( for i from 0 to N
                list (
                        -- p := length flatten entries vars ring X.Ideal;
                        lift(vecA#i,ZZ) * H^(X0.AmbientSpace.dim - i)
                ));

        if opts.Testing then (return seg);
        sub(seg,intersectionRing Y0)
)
--segreClass(ProjectiveScheme,ProjectiveScheme) := opts -> (X,Y) -> (
        --return segreClass(X.Ideal, Y.Ideal, opts);
--)
--segreClass(ProjectiveScheme) := opts -> (X) -> (
        --return segreClass(X.Ideal, opts);
--)

dualChernClass = c -> (
    -- c is a total chern class in projective space

    )

RingElement ** AbstractSheaf := (s, L) -> (
        c := chern L;
        R := ring s;

        return sum apply( terms s, t -> (
                codimn := first degree(t_R);
                return t * (c^(-codimn));
        ))
)

chernMather = method()
chernMather(ProjectiveScheme) := (X) -> (
        if dim X < 0 then return 0*X.Hyperplane;
        if codim(X) > 1 then (
                -- << "Projecting to get lower codimension...   " << "Currently, codim = " << codim(X) << " in PP^" << dim(X.AmbientSpace) << endl;
                return chernMather( projectToHypersurface(X.Ideal) )
                );
        
        -- if codim(X) == 1 then (<< "X has codimension 1..." << endl;);
        cX := cycleClass X;
        T := tangentBundle(X.AmbientSpace);
        O := OO_(X.AmbientSpace);
        iJ := (singularLocus X.Ideal).ideal;
        
        if dim variety iJ < 0 then return chern(T) * cX * (1+cX)^(-1);
        
        -- this line can potentially produce a LOT of output 
        -- << "Computing Segre class of " << toString(iJ) << " in " << toString(X.Ideal) << endl;
        s := segreClass(iJ,X.Ideal);
        a := sub(adams(-1,s), intersectionRing X);
        
        return chern(T) * ( cX * (1+cX)^(-1) + (a ** O(cX) ) )
)
chernMather(Ideal) := (iX) -> (
        X := projectiveScheme(iX);
        return chernMather(X)
)

chernSchwartzMacPherson = method()
chernSchwartzMacPherson(ProjectiveScheme) := (X) -> (
        error "This command is not implemented"
        -- cX := cycleClass X;
        -- T := tangentBundle(X.AmbientSpace);
        -- O := OO_(X.AmbientSpace);

        -- iJ := (singularLocus X.Ideal).ideal;

        -- iM := if codim X > 1 then (
        --     << "This function is meant for hypersurfaces... Trying to find a smooth ambient variety... output cannot be trusted" << endl;
        --         ideal ( for i from 1 to codim X - 1 list sum apply(X.Equations, e -> random(0,ring e)*e) )
        --     ) else if codim X == 1 then (
        --         if dim variety iJ < 0 then return chern(T) * cX * (1+cX)^(-1);
        --         trim ideal 0_(ring X.Ideal)
        --     ) else if codim X == 0 then (
        --         return chern tangentBundle X.AmbientSpace
        --     ) else error "got codimension of " | toString codim X | " for " toString X;
        -- M := projectiveScheme(iM, AmbientSpace => X.AmbientSpace);
        -- << "M : " << peek M << endl;
        

        -- J := projectiveScheme(iJ, AmbientSpace => X.AmbientSpace);
        -- -- seg := segreClass(J,M);
        -- seg := segreClass(J.Ideal, M.Ideal);
        -- s := chern(O(cX)) * sub(seg, intersectionRing X);
        -- a := sub(adams(-1,s), intersectionRing X);
        -- return chern(T) * ( cX * (1+cX)^(-1) + (a ** O(cX) ) )
)
chernSchwartzMacPherson(Ideal) := (iX) -> (
        return chernSchwartzMacPherson(projectiveScheme(iX))
)

projectToHypersurface = method()
projectToHypersurface(Ideal) := (X) -> (
        c := codim X;
        n := dim variety X;
        R := ring X;
        kk := coefficientRing R;
        L := sum( n+2, i -> ideal(random(1,R)) );
        pr := map(R,kk(monoid[(i -> (getSymbol "a")_i ) \ (1..n+2)]), gens L );
        return trim (preimage_pr X)
)

dualDegree = method()
dualDegree(Ideal) := (X) -> (
        {*
                Compute the degree of the dual of a hypersurface via its singularity Segre class
        *}
        d := degree X;
        n := #(gens ring X)-1;
        J := ideal singularLocus X;
        seg := segreClass(J, X);
        A := ring seg;
        return d*(d-1)^(n-1) - sum(n, i -> binomial(n-1,i) * (d-1)^i * seg_((A_1)^(n-i)) )
)
dualDegree(ProjectiveScheme) := (X) -> (
        dualDegree(X.Ideal)
)

sumPolarRanks = method()
sumPolarRanks(Ideal) := (X) -> (
        n := dim variety X;
        cm := chernMather X;
        A := ring cm;
        h := A_1;
        return sum(n+1, i -> (-1)^(n+i)*(2^(i+1)-1)*cm_(h^(n+1-i)))
)
sumPolarRanks(ProjectiveScheme) := (X) -> (
        polarRanks(X.Ideal)
)

-- this method is broken
polarRanks = method()
polarRanks(Ideal) := (X') -> (
        << "BROKEN.  Do not trust output." << endl;
        X := if codim X' > 1 then (
                projectToHypersurface X'
        ) else if codim X' == 1 then (X')
        else error "X should be a proper subvariety";
        d := degree X;
        n := dim variety X;
        seg := segreClass(ideal singularLocus X, X);
        A := ring seg;
        ranks := for k from 0 to n list (
                d*(d-1)^(k) - sum(k-1, i -> binomial(k,i) * (d-1)^i * seg_((A_1)^(k+1-i)) )
        );
        return ranks
)
polarRanks(ProjectiveScheme) := (X) -> (
        polarRanks(X.Ideal)
)

intersectionProduct = method()
intersectionProduct (ProjectiveScheme, ProjectiveScheme, ProjectiveScheme) := (X,V,Y) -> (
    {*
        computes the intersection product X *_Y V corresponding to a fibre square

                j
            W -----> V
            |        |
           g|        |f
            |        |
            X -----> Y
                i
        
        where i is a regular embedding of codimension d (see [F,Chapter 6])
    *}
    
    -- this error can be avoided if the user just passes ideals instead of ProjectiveSchemes
    if not (V.AmbientSpace === Y.AmbientSpace and X.AmbientSpace === Y.AmbientSpace) then
        error "expected U,V to be subschemes of Y";

    -- check if codimension in S.AmbientSpace matches number of equations
    isCompleteIntersection := S -> (
        #(S.Equations) == codim(S)
    );  

    H := Y.Hyperplane;
    -- if X,Y are complete intersections in PP^N, we can compute the intersection product easily
    (a,b,c) := if all({X,Y}, S -> isCompleteIntersection S) then (
        -- compute the normal bundle N_X Y
        chernRoots := S -> apply(S.Equations, eq -> (first degree eq)*H);
        chernX := product apply(chernRoots X, a -> 1+a);
        chernY := product apply(chernRoots Y, a -> (1+a)^(-1));

        -- something like (totalchern X)/(totalchern Y)
        -- but of course this doesn't actually work
        
        -- compute the Segre class s(W,V)
        s := segreClass(X,V);
        (chernX, chernY, s)
    ) else error "not implemented yet";
    
    -- {a*b*c}_d is the class we want
    d := dim V - (dim Y - dim X);
    n := dim Y.AmbientSpace;
    coefficient(H^(n-d),a*b*c)*H^(n-d)
)

-----------------------------------------------------------------------------

load (FMPIntersectionTheory#"source directory" | "FMPIntersectionTheory/FMPIntersectionTheoryDoc.m2")

TEST ///
R = QQ[x,y,z];
I = ideal("x2,xy");
I' = ideal("x,y2");
X = projectiveScheme(I); -- X is a line with embedded point
X' = projectiveScheme(I'); -- X' is a double point
assert ( class(X) === ProjectiveScheme )
assert ( cycleClass(X) === X.Hyperplane ) -- X is rationally equivalent to a line in PP^2
assert ( degree(X) == 1 ) -- [line + pt] . [H] = [pt]
assert ( dim(X) == 1 )
assert ( codim(X) == 1 )

assert ( cycleClass(X') === (X'.Hyperplane)^2 ) -- [X'] = [X'_red] = [pt]
assert ( degree(X') == 2 ) -- double point has degree 2
///

load (FMPIntersectionTheory#"source directory"|"FMPIntersectionTheory/segreClass-tests2.m2")

end

restart
uninstallPackage "FMPIntersectionTheory"
load "FMPIntersectionTheory.m2"
installPackage "FMPIntersectionTheory"
--needsPackage "FMPIntersectionTheory"
debug needsPackage "FMPIntersectionTheory"

restart
load "CSM.m2"

PP5 = QQ[a,b,c,d,e,f]
G = ideal "ab-cd+ef";
S = G + ideal "b2-de";
J = (singularLocus(S)).ideal
seg = segreClass(J,G)

CSM S

V = G + ideal "b2-cf";
U = G + ideal (b,d,f);
-- G = ideal "ab-cd+ef"; GS = projectiveScheme(G)
-- V = G + ideal "b2-cf"; VS = projectiveScheme(V, SuperScheme=>GS)
-- U = G + ideal (b,d,f); XS = projectiveScheme(U, SuperScheme=>GS)
--intersectionProduct(XS,VS,GS)

chernSchwartzMacPherson(ideal 0_PP5)
chernSchwartzMacPherson(G)
chernSchwartzMacPherson(U)

S1 = G + ideal b
S21 = G + ideal (b,c,d,e)
s = segreClass(S21,S1)

PP3 = QQ[x,y,z,t]
C = ideal "x3-xy2-xz2+2yzt-xt2"
J = ideal singularLocus C
segreClass(C)
segreClass(J,C)
segreClass(J)
-- chernSchwartzMacPherson(C)
chernMather(C)
polarRanks(C)




