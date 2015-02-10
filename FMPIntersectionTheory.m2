newPackage(
	"FMPIntersectionTheory",
	Version => "0.1",
	Date => "February 9, 2015",
	Authors => {{Name => "Corey Harris", Email => "charris@math.fsu.edu", HomePage => "http://coreyharris.name"}},
	Headline => "A package for Fulton-MacPherson intersection theory."
	-- PackageExports => {"Shubert2"}
)

needsPackage("Schubert2")

-- export { "segreClass" }
export { "ProjectiveScheme", "projectiveScheme", "Base", "SuperScheme", "AmbientSpace", "ambientSpace", "cycleClass", "coordRing", "equations", "hyperplane"}

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"
-- indexSymbols = value Core#"private dictionary"#"indexSymbols"

ProjectiveScheme = new Type of MutableHashTable
globalAssignment ProjectiveScheme


toString ProjectiveScheme := net ProjectiveScheme := X -> (
	if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
	else "a projective scheme")
ProjectiveScheme#{Standard,AfterPrint} = X -> (
	<< concatenate(interpreterDepth:"o") << lineNumber << " : "
	<< "a projective scheme in PP^" << dim(X.ambientSpace) << " defined by " << X.ideal << endl;
)

projectiveScheme = method(TypicalValue => ProjectiveScheme, Options => {
		Base => null,  -- sets the ambient space to be a projective bundle over Base
		SuperScheme => null,  -- a ProjectiveScheme containing the one we are defining
							  -- If I is the ideal of SuperScheme in R, and we define our 
							  -- new scheme with J in R, we instead will use I+J
		AmbientSpace => null, -- the projective space where we will be computing
		-- LinearBase => false   -- 
	})
projectiveScheme Ideal :=  opts -> I -> (
	-- I := if opts.LinearBase then homogenate(I') else I';
	R := ring I;
	eqs := flatten entries gens I;
	P := if opts.Base =!= null then (
			N := #(flatten entries vars R) - 1;  -- dimension of projective space corresponding to proj(R)
			projectiveBundle(N, opts.Base)
		) else if opts.SuperScheme =!= null then (
			I = trim (I + opts.SuperScheme.ideal);
			opts.SuperScheme.ambientSpace
		) else if opts.AmbientSpace =!= null then (
			opts.AmbientSpace
		) else (
			N := #(flatten entries vars R) - 1;  -- dimension of projective space corresponding to proj(R)
			projectiveBundle N
		);

	new ProjectiveScheme from {
		global ideal => I,
		global coordRing => quotient I,
		global equations => eqs,
		global ambientSpace => P,
		global intersectionRing => intersectionRing(P),
		global hyperplane => ( chern_1 (OO_P(1)) ),
		global dim => null,
		global degree => null,
		global codim => null,
		global cycleClass => null
	}
)

beginDocumentation()

multidoc ///
	Node
		Key
	  		FMPIntersectionTheory
		Headline
			A package for Fulton-MacPherson intersection theory.
		Description
			Text
				{\em FMPIntersectionTheory} extends @ TO Schubert2@ and (eventually) implements the intersection product of Fulton-Macpherson.
	Node
		Key
			(projectiveScheme,Ideal)
	   		projectiveScheme
		Headline
			an extension of AbstractVariety which comes with an embedding to a projective space
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
				R = QQ[x,y]
				I = ideal x^2
				projectiveScheme(I)
///

TEST ///
R = QQ[x,y,z];
X = ideal("x2y,yz-x2");
assert ( class(projectiveScheme(X)) === ProjectiveScheme )
///