newPackage(
	"FMPIntersectionTheory",
	Version => "0.1",
	Date => "February 9, 2015",
	Authors => {{Name => "Corey Harris", Email => "charris@math.fsu.edu", HomePage => "http://coreyharris.name"}},
	Headline => "A package for Fulton-MacPherson intersection theory.",
	AuxiliaryFiles => true
	-- PackageExports => {"Shubert2"}
)

needsPackage("Schubert2")

-- export { "segreClass" }
export { "ProjectiveScheme", "projectiveScheme", "BaseForAmbient", "SuperScheme", "AmbientSpace", "MakeBaseOfLinearSystem",
		"cycleClass","CycleClass", "CoordinateRing", "Equations", "Hyperplane", "segreClass", "Testing"}

protect Equations
protect CoordinateRing
protect Hyperplane

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
		BaseForAmbient => null,  -- sets the ambient space to be a projective bundle over Base
		SuperScheme => null,  -- a ProjectiveScheme containing the one we are defining
							  -- If I is the ideal of SuperScheme in R, and we define our 
							  -- new scheme with J in R, we instead will use I+J
		AmbientSpace => null, -- the projective space where we will be computing
		MakeBaseOfLinearSystem => false   -- if true, the ideal used to define the projective scheme should be made to have all terms of same degree
	})
projectiveScheme Ideal :=  opts -> I' -> (
	I := if opts.MakeBaseOfLinearSystem then homogenate(I') else I';
	R := ring I;
	N := 0;
	eqs := flatten entries gens I;
	P := if opts.BaseForAmbient =!= null then (
			N = #(flatten entries vars R) - 1;  -- dimension of projective space corresponding to proj(R)
			projectiveBundle(N, opts.BaseForAmbient)
		) else if opts.SuperScheme =!= null then (
			I = trim (I + opts.SuperScheme.Ideal);
			opts.SuperScheme.AmbientSpace
		) else if opts.AmbientSpace =!= null then (
			opts.AmbientSpace
		) else (
			N = #(flatten entries vars R) - 1;  -- dimension of projective space corresponding to proj(R)
			projectiveBundle N
		);

	new ProjectiveScheme from {
		global Ideal => I,
		CoordinateRing => quotient I,
		Equations => eqs,
		AmbientSpace => P,
		IntersectionRing => intersectionRing(P),
		Hyperplane => ( chern_1 (OO_P(1)) ), -- the class of a hyperplane in ambientSpace
		global dim => null,
		global degree => null,
		global codim => null,
		CycleClass => null
	}
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
degpr := (X,Y) -> (
    
    -- << "calculating degpr(X,Y)" << endl;
    
    ideals := for i from 1 to (dim Y)
        list ( 
            ideal ( sum apply(X.Equations, g -> random(0,ring(X.Ideal))*g ) )
            );
    hyps := sum(ideals);
    
    --<< "saturate " << trim(Y.Ideal + hyps) << " with respect to " << X.Ideal << endl;
    --<< " to get " << saturate(Y.Ideal + hyps, X.Ideal) << " with degree " << degree saturate(Y.Ideal + hyps, X.Ideal) << endl;
    
    return degree saturate( Y.Ideal + hyps, X.Ideal )
)


segreClass = method(TypicalValue => RingElement, Options => {Testing => false})
segreClass(Ideal,Ideal) := opts -> (iX,iY) -> (
	a := symbol a;
	Y := projectiveScheme( iY, BaseForAmbient => base(a_0..a_(dim variety (iX+iY))) );
	X := projectiveScheme( homogenate iX, SuperScheme => Y );
	H := X.Hyperplane;
	N := dim X;

	-- s = a_0 PP^0 + a_1 PP^1 + .. + a_N PP^N
	-- this stands for the class s(X,Y)
	s := sum ( for i from 0 to N list (a_i * H^(N-i)) );

	-- eqns will be a list of "equations" c_0*a_0 + .. + c_n*a_n = D
	-- returned as ( (c_0,..,c_n), D )
	eqns := while ( dim X >= 0 )
		list (
			d := first degree ( (X.Ideal)_0 ); -- degree of each generator
			D := ( d^(dim Y) * degree(Y) ) - degpr(X,Y);
			-- C is the degree of c(N) \cap s(X,Y)
			C := coefficient( H^(dim X), (1 + d*H)^(dim Y) * s );
			-- C is written as a polynomial in the a_i's
			( apply (a_0..a_N, v -> coefficient(v,C)), D )
		)
		do (
			hyp := goodHyperplaneSection(X,Y);
			-- replace X,Y with hyperplane sections
			Y = projectiveScheme(Y.Ideal + hyp);
			X = projectiveScheme(X.Ideal, SuperScheme => Y, MakeBaseOfLinearSystem => true);
		);

	-- We need to solve the matrix equation determined by eqns
	-- so we substitute the values from QQ to a finite field
	C := sub( matrix apply(eqns, i -> toList i#0), ZZ/32479 );
	D := sub( transpose matrix {apply(eqns, i -> i#1)}, ZZ/32479 );
	A := flatten entries solve(C,D);

	-- finally, take the vector a = (a_0,..,a_n) and form the Segre class
	-- seg = a_0 PP^0 + a_1 PP^1 + .. + a_N PP^N
	if opts.Testing then (
		ringH := ZZ(monoid[getSymbol "H"]);
		H = ringH_0;
	);

	seg := sum ( for i from 0 to N
		list (
			-- p := length flatten entries vars ring X.Ideal;
			lift(A#i,ZZ) * H^(X.AmbientSpace.dim - i)
		));
	return seg

)

-----------------------------------------------------------------------------

beginDocumentation()
undocumented {
	(net,ProjectiveScheme),
	(toString,ProjectiveScheme)
}

multidoc ///
	Node
		Key
	  		FMPIntersectionTheory
		Headline
			A package for Fulton-MacPherson intersection theory.
		Description
			Text
				{\em FMPIntersectionTheory} (eventually) implements the intersection product of Fulton-Macpherson.
	------
	Node
		Key
			ProjectiveScheme
		Headline
			the class of projective schemes
		Description
			Text
				a projective scheme in this package is an ideal along with information about how it is embedded in projective space
	------
	Node
		Key
			(projectiveScheme,Ideal)
	   		projectiveScheme
	   		[projectiveScheme,BaseForAmbient]
	   		BaseForAmbient
	   		[projectiveScheme,AmbientSpace]
	   		AmbientSpace
	   		[projectiveScheme,SuperScheme]
	   		SuperScheme
		Headline
			make a projective scheme
		Usage
			projectiveScheme I
		Inputs
			I:Ideal
		Outputs
			:ProjectiveScheme
		Description
			Text
				Here we show an example.
			Example
				R = QQ[x,y];
				I = ideal x^2;
				projectiveScheme(I)
	------
	Node
		Key
			(cycleClass,ProjectiveScheme)
			cycleClass
		Headline
			gives the class in the chow group of the ambient projective space
		Usage
			cycleClass X
		Inputs
			X:ProjectiveScheme
		Outputs
			: 
				the class of X in the Chow ring of the ambient projective space
		Description
			Text
				cycleClass X will return the class of X in the chow group of the ambient projective space
				The multiplicity of X along the irreducible component Z is the multiplicity of X at a point z in Z.  This is also the degree of the projectivized tangent cone to z in X, which can be calculated via the Hilbert polynomial of graded ring associated to O(X)/I, where I is the ideal of Z.
			Example
				R = QQ[x,y,z];
				I = ideal x*y;
				cycleClass(projectiveScheme(I))
			Example
				I' = ideal("x2,xy");
				cycleClass(projectiveScheme(I'))
	Node
		Key
			CycleClass
		Headline
			a symbol used internally as a key
		SeeAlso
			cycleClass
	------
	Node
		Key
			(degree,ProjectiveScheme)
		Headline
			gives the degree of a ProjectiveScheme
		Usage
			degree X
		Inputs
			X:ProjectiveScheme
		Outputs
			:ZZ
		Description
			Example
				R = QQ[x,y,z];
				I = ideal x*y;
				X = projectiveScheme(I);
				degree X
	------
	Node
		Key
			(dim,ProjectiveScheme)
		Headline
			gives the dim of a ProjectiveScheme
		Usage
			dim X
		Inputs
			X:ProjectiveScheme
		Outputs
			:ZZ
		Description
			Example
				R = QQ[x,y,z];
				I = ideal x*y;
				X = projectiveScheme(I);
				dim X
	------
	Node
		Key
			CoordinateRing
		Headline
			a symbol used internally as a key
	------
	Node
		Key
			AmbientSpace
		Headline
			a symbol used internally as a key
	------
	Node
		Key
			Hyperplane
		Headline
			a symbol used internally as a key
	------
	Node
		Key
			Equations
		Headline
			a symbol used internally as a key
	------
///

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

assert ( cycleClass(X') === (X'.Hyperplane)^2 ) -- [X'] = [X'_red] = [pt]
assert ( degree(X') == 2 ) -- double point has degree 2

///

TEST /// input (FMPIntersectionTheory#"source directory"|"FMPIntersectionTheory/segreClass-tests.m2") ///













