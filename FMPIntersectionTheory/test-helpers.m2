testEqualityOLD = (A,B) -> (
	A' := toString segreClass A;
	B' := toString B;
	<< A' << endl;
	try assert (A' == B') else 
		<< "Error: " <<  A' << " does not match " << B' << endl;
	<< "should match "<< toString segreClass2 A << endl;
)

testEquality = (A,B) -> (
	A' := toString segreClass(A,Testing=>true);
	B' := toString B;
	<<  A' << " should match " << B' << endl;
	assert (A' == B')
)

veronese = (R,d) -> (
    k := coefficientRing R;
    I := ideal (flatten entries vars R);
    II := I^d;
    n := #(flatten entries gens II);
    y := local y;
    return map(R, k[y_0..y_(n-1)], gens II)
)


------------------------------------------------------
-- SETUP
------------------------------------------------------

PP2 = QQ[y0,y1,y2];
PP3 = QQ[x0,x1,x2,x3];

