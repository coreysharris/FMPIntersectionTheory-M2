newPackage(
	"FMPIntersectionTheory",
	Version => "0.1",
	Date => "February 9, 2015",
	Authors => {{Name => "Corey Harris", Email => "charris@math.fsu.edu", HomePage => "http://coreyharris.name"}},
	-- PackageExports => {"Shubert2"}
)

needsPackage("Schubert2")

export { "segreClass" }

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"
indexSymbols = value Core#"private dictionary"#"indexSymbols"

ProjectiveScheme = new Type of MutableHashTable
globalAssignment ProjectiveScheme


toString ProjectiveScheme := net ProjectiveScheme := X -> (
	if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
	else "a projective scheme")
ProjectiveScheme#{Standard,AfterPrint} = X -> (
	<< concatenate(interpreterDepth:"o") << lineNumber << " : "
	<< "a projective scheme in PP^" << dim(X.ambientSpace) << " defined by " << X.Ideal << endl;
)

projectiveScheme = method(TypicalValue => ProjectiveScheme, Options => {
		Base => null, SuperScheme => null, AmbientSpace => null, LinearBase => false
	})
projectiveScheme Ideal :=  opts -> I' -> (
	I := if opts.LinearBase then homogenate(I') else I';
	R := ring I;
	Eqs := flatten entries gens I;
	P := if opts.Base =!= null then (
			N = #(flatten entries vars R) - 1;  -- dimension of projective space corresponding to proj(R)
			projectiveBundle(N, opts.Base)
		) else if opts.SuperScheme =!= null then (
			I = trim (I + opts.SuperScheme.Ideal);
			opts.SuperScheme.ambientSpace
		) else if opts.AmbientSpace =!= null then (
			opts.AmbientSpace
		) else (
			N = #(flatten entries vars R) - 1;  -- dimension of projective space corresponding to proj(R)
			projectiveBundle N
		);

	new ProjectiveScheme from {
		global Ideal => I,
		global coordRing => (R/I),
		global Equations => Eqs,
		global ambientSpace => P,
		global intRing => intersectionRing(P),
		global hyperplane => ( chern_1 (OO_P(1)) ),
		global dimension => null,
		global degree => null,
		global codimension => null,
		global cycleClass => null
	}
)