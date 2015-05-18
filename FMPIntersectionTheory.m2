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
	"ProjectiveScheme", 
	"projectiveScheme", 
	"SuperScheme", 
	"AmbientSpace", 
	"MakeBaseOfLinearSystem", 
	"BaseField",
	"cycleClass",
	"CycleClass", 
	"CoordinateRing", 
	"Equations", 
	"Hyperplane", 
	"intersectionring", 
	"segreClass", 
	"Testing", 
	"chernMather",
	"chernSchwartzMacPherson", 
	"restrictToHplaneSection", 
	"dualDegree", 
	"polarRanks"
}

-- protect segreAlgCoefficientMatrix

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
		global IntersectionRing => intersectionRing(P),
		global Hyperplane => ( chern_1 (OO_P(1)) ), -- the class of a hyperplane in ambientSpace
		global dim => null,
		global degree => null,
		global codim => null,
		CycleClass => null
	}
)

intersectionring = method()
intersectionring ProjectiveScheme := X -> (
	return X.IntersectionRing
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
    	return degree saturate( Y.Ideal + hyps, X.Ideal, Strategy => "F4")
    ) else (
    	return degree saturate( Y.Ideal + hyps, X.Ideal)
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


segreClass = method(TypicalValue => RingElement, Options => {Testing => false, Strategy => "Saturate"})
segreClass(Ideal) := opts -> (iX) -> (
	iY := trim ideal 0_(ring iX);
	return segreClass(iX,iY, opts)
)
segreClass(Ideal,Ideal) := opts -> (iX,iY) -> (
	Y := projectiveScheme(iY);
	X := projectiveScheme( iX, SuperScheme => Y, MakeBaseOfLinearSystem => true );
	H := X.Hyperplane;
	if dim X < 0 then (return 0*H);
	N := dim X;

	d := first degree ( (X.Ideal)_0 ); -- degree of each generator

	X0 := X;
	Y0 := Y;

	eqns := while ( dim X >= 0 )
		list (
			pdeg := if opts.Strategy == "Helmer" then (
					projDegHelmer(X,Y)
				) else if opts.Strategy == "Saturate" then (
					projDegSaturate(X,Y)
				);
			D := ( d^(dim Y) * degree(Y) ) - pdeg;
			-- if opts.Testing then (<< "D = ( d^(dim Y) * degree(Y) ) - projDeg(X.Ideal,Y.Ideal) = " << d << "^" << dim Y << " * " << degree(Y) << " - " << projDeg(X.Ideal,Y.Ideal) << endl; );
			D
		)
		do (
			hyp := goodHyperplaneSection(X,Y);
			-- replace X,Y with hyperplane sections
			IY := restrictToHplaneSection(Y,hyp);
			IX := sub(restrictToHplaneSection(X,hyp), ring(IY));
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
	return sub(seg,X0.IntersectionRing)
)
segreClass(ProjectiveScheme,ProjectiveScheme) := opts -> (X,Y) -> (
	return segreClass(X.Ideal, Y.Ideal, opts);
)
segreClass(ProjectiveScheme) := opts -> (X) -> (
	return segreClass(X.Ideal, opts);
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
	if codim(X) > 1 then (
		<< "Projecting to get lower codimension...   " << "Currently, codim = " << codim(X) << " in PP^" << dim(X.AmbientSpace) << endl;
		return chernMather( projectToHypersurface(X.Ideal) )
		);
	
	cX := cycleClass X;
	T := tangentBundle(X.AmbientSpace);
	O := OO_(X.AmbientSpace);
	iJ := (singularLocus X.Ideal).ideal;
	
	if dim variety iJ < 0 then return chern(T) * cX * (1+cX)^(-1);
	
	s := segreClass(iJ,X.Ideal);
	a := sub(adams(-1,s), X.IntersectionRing);
	
	return chern(T) * ( cX * (1+cX)^(-1) + (a ** O(cX) ) )
)
chernMather(Ideal) := (iX) -> (
	X := projectiveScheme(iX);
	return chernMather(X)
)

chernSchwartzMacPherson = method()
chernSchwartzMacPherson(ProjectiveScheme) := (X) -> (
	cX := cycleClass X;
	T := tangentBundle(X.AmbientSpace);
	O := OO_(X.AmbientSpace);
	iJ := (singularLocus X.Ideal).ideal;
	seg := segreClass(iJ);
	s := chern(O(cX)) * sub(seg, X.IntersectionRing);
	a := sub(adams(-1,s), X.IntersectionRing);
	
	return chern(T) * ( cX * (1+cX)^(-1) + (a ** O(cX) ) )
)
chernSchwartzMacPherson(Ideal) := (iX) -> (
	return chernSchwartzMacPherson(projectiveScheme(iX))
)

projectToHypersurface = method()
projectToHypersurface(Ideal) := (X) -> (
	c := codim X;
	R := ring X;
	kk := coefficientRing R;
	L := sum( c+1, i -> ideal(random(1,R)) );
	pr := map(R,kk(monoid[(i -> (getSymbol "a")_i ) \ (0..c)]), gens L );
	return preimage_pr X
)

dualDegree = method()
dualDegree(Ideal) := (X) -> (
	{*
		Compute the degree of the dual of a hypersurface
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

polarRanks = method()
polarRanks(Ideal) := (X') -> (
	X := if codim X' > 1 then (
		projectToHypersurface X'
	) else X';
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
	   		[projectiveScheme,AmbientSpace]
	   		AmbientSpace
	   		[projectiveScheme,SuperScheme]
	   		SuperScheme
	   		[projectiveScheme,MakeBaseOfLinearSystem]
	   		MakeBaseOfLinearSystem
		Headline
			make a projective scheme
		Usage
			projectiveScheme I
		Inputs
			I:Ideal
			AmbientSpace => ProjectiveScheme
				a @ TO2 {projectiveBundle,"projective bundle"} @ where the ProjectiveScheme will live
			MakeBaseOfLinearSystem => Boolean
				if true, make the ideal of the projective scheme with generators of one degree, as if the scheme is the base locus of a linear system in $H^0(\mathcal{O}(d),X)$
			SuperScheme => ProjectiveScheme
				a scheme that will contain the one defined.  Replaces the ideal I with the ideal I+J, where J is the ideal of the super scheme
		Outputs
			:ProjectiveScheme
		Description
			Text
				Here we show an example.
			Example
				R = QQ[x,y,z];
				I = ideal(x^2+y*z);
				X = projectiveScheme(I)
			Example
				J = ideal(x+2*z);
				Y = projectiveScheme(J, SuperScheme => X)
		SeeAlso
			ProjectiveScheme
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
			
			Text
				Two planes in $\mathbb{P}^3$
			Example
				R = QQ[x,y,z,t];
				I = ideal x*y;
				cycleClass(projectiveScheme(I))

			Text
				A line with embedded point
			Example
				I' = ideal("x2,xy");
				cycleClass(projectiveScheme(I'))

			Text
				A line union a plane
			Example
				I'' = ideal("xy,xz");
				cycleClass(projectiveScheme(I''))
	------
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
			(segreClass,Ideal,Ideal)
			(segreClass,Ideal)
			(segreClass,ProjectiveScheme)
			(segreClass,ProjectiveScheme,ProjectiveScheme)
			segreClass
			[segreClass,Testing]
			Testing
		Headline
			Compute the Segre class of a subvariety
		Usage
			segreClass(iX)
			segreClass(iX,iY)
			segreClass(X)
			segreClass(X,Y)
		Inputs
			iX:Ideal
				the ideal defining the projective scheme X
			iY:Ideal
				ideal defining a scheme Y containing X
			-- X:ProjectiveScheme
			-- Y:ProjectiveScheme
				projective scheme containing X
		Outputs
			:
				the Segre class of X in PP^N, or the Segre class of X in Y
		Description
			Text
				If $I,J$ define schemes $X,Y$ in $\mathbb{P}^N$, then segreClass(I,J) computes the Segre class s(X,Y) pushed forward to $\mathbb{P}^N$, and segreClass(X) computes s(X,$\mathbb{P}^N$).


			Text
				The Segre class of a circle in $\mathbb{P}^2$ is $2 * ([ \mathbb{P}^1 ] - 2 [ \mathbb{P}^0 ])$.
			Example
				PP2 = QQ[x,y,z];
				I = ideal( x^2 + y^2 - z^2 );
				segreClass I

			Text
				We can show the power of this function by embedding $\mathbb{P}^2 \subset \mathbb{P}^3$ 
				and finding the Segre class of the image of the circle.
				Notice that now $H$ is the hyperplane class in $\mathbb{P^3}$, so the powers are different 
				than above.
			Example
				PP3 = QQ[x,y,z,t];
				I = ideal( x - y );
				J = ideal( 2*x^2 - z^2 );
				segreClass(J,I)
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
			(symbol **, RingElement, AbstractSheaf)
		Headline
			kljhlkjh
	------
	Node
		Key
			(chernMather,Ideal)
			chernMather
		Headline
			Compute Mather's Chern class
		Usage
			chernMather(I)
		Inputs
			I:Ideal
		Outputs
			:
				a ring element
	------
	Node
		Key
			(chernMather,ProjectiveScheme)
		Headline
			Compute Mather's Chern class
		Usage
			chernMather(X)
		Inputs
			X:ProjectiveScheme
		Outputs
			:
				a ring element
	------
	Node
		Key
			restrictToHplaneSection
			(restrictToHplaneSection,ProjectiveScheme,Thing)
		Headline
			Restrict an variety to given hyperplane
		Usage
			restrictToHplaneSection(X,h)
		Inputs
			X:ProjectiveScheme
			h:
				a ring element (of degree 1)
		Outputs
			:
				ideal of the restricted variety
	------
	Node
		Key
			dualDegree
			(dualDegree,Ideal)
			(dualDegree,ProjectiveScheme)
		Headline
			Get the degree of the dual of an irreducible hyperplane
		Usage
			dualDegree(X)
			dualDegree(I)
		Inputs
			X:ProjectiveScheme
			I:Ideal
		Outputs
			:
				a ring element
	------
	Node
		Key
			polarRanks
			(polarRanks,Ideal)
			(polarRanks,ProjectiveScheme)
		Headline
			Computes the polar ranks of a projective variety
		Usage
			polarRanks(X)
			polarRanks(I)
		Inputs
			X:ProjectiveScheme
			I:Ideal
		Outputs
			:
				a ring element
	------
	------
	Node
		Key
			BaseField
		Headline
			a symbol used internally as a key
	------
	Node
		Key
			CoordinateRing
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

load (FMPIntersectionTheory#"source directory"|"FMPIntersectionTheory/segreClass-tests2.m2")

-- TEST /// input (FMPIntersectionTheory#"source directory"|"FMPIntersectionTheory/segreClass-tests.m2") ///















