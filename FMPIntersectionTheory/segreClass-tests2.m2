-- load "segreProjection.m2"
-- load "segre.m2"
-- verbosity = -1;
-- load "CSM.m2"

TEST ///
load (FMPIntersectionTheory#"source directory"|"FMPIntersectionTheory/test-helpers.m2")
------------------------------------------------------
-- Here we check s(PP1,PP2) for PP1 in PP2 in PP3
-- and then s(PP1) with ambient space PP2.
-- Finally check s(PP1,PP3).
------------------------------------------------------

X = ideal(x0);
Y = ideal(x1);
X' = ideal(y0);

testEquality( (X,Y), "-H^3+H^2" );

testEquality(  X', "-H^2+H" );

testEquality(  X, "H^3-H^2+H" );

///

TEST ///
load (FMPIntersectionTheory#"source directory"|"FMPIntersectionTheory/test-helpers.m2")
------------------------------------------------------
-- We we check s(v(X),v(PP2)) pushed forward to PP5,
-- where v is the 2nd Veronese embedding of PP2.
------------------------------------------------------

X = ideal (y0)
v = veronese(PP2,2);
vX = preimage_v X;
vPP2 = preimage_v (ideal 0_PP2);

testEquality( (vX, vPP2), "-H^5+2*H^4" );

///

TEST ///
load (FMPIntersectionTheory#"source directory"|"FMPIntersectionTheory/test-helpers.m2")
------------------------------------------------------
-- Here we check s(circle,PP2) in PP3, 
-- then s(circle) with PP2 as the ambient space.
------------------------------------------------------

X = ideal(2*x0^2 - x2^2);
Y = ideal(x0 - x1);
X' = ideal(y0^2 + y1^2 - y2^2);

testEquality(  X', "-4*H^2+2*H" );

testEquality( (X,Y), "-4*H^3+2*H^2" );

///

TEST ///
load (FMPIntersectionTheory#"source directory"|"FMPIntersectionTheory/test-helpers.m2")
------------------------------------------------------
-- Here Y is the union of the two axes in PP2, and 
-- X is the x-axis.  By Lemma 4.2 [F], this is 
-- i_* ( s(PP1,PP1) + s(PP0,PP1) ) = i_* (PP1 + PP0),
-- where i_* is the pushforward to PP2.
------------------------------------------------------

X = ideal(y1);
Y = ideal(y0*y1);

testEquality( (X,Y), "H^2+H" );

///

TEST ///
load (FMPIntersectionTheory#"source directory"|"FMPIntersectionTheory/test-helpers.m2")
------------------------------------------------------
-- By Thm 1.1 in 'Segre classes as integrals over 
-- polytopes', the segre class of (x,y) in (xy-z^2) in
-- PP3 is
-- s(X+Y,Z) = 1 - (1+X+Y)/((1+X)(1+Y)) = XY - X^2 Y - X Y^2 + ... = XY = 2pt,
-- as this subscheme is a double point.
------------------------------------------------------

X = ideal(x0);
Y = ideal(x1);
Z = ideal(x0*x1+x2^2);

testEquality( (X+Y,Z), "2*H^3");

///

TEST ///
load (FMPIntersectionTheory#"source directory"|"FMPIntersectionTheory/test-helpers.m2")
------------------------------------------------------
-- By Thm 1.1 in 'Segre classes as integrals over 
-- polytopes', the segre class of (x,x^2+y^2-z^2) in PP2 is
-- s(X+Y,PP2) = 1 - (1+X+Y)/((1+X)(1+Y)) = XY - X^2 Y - X Y^2 + ... = XY = 2pt,
-- as this subscheme is a pair of points.
------------------------------------------------------

-- THIS TEST IS SLOWWWWWWW

-- X = ideal(y0);
-- Y = ideal(y0^2 + y1^2 - y2^2);

-- testEquality( (X+Y), "2*H^2");

------------------------------------------------------
-- Take the cubic x^2*y-z^3 in PP2 and consider the 
-- subvariety defined by (x,z) (or (y,z))
------------------------------------------------------

X = ideal(y1,y2);
Y = ideal(y0^2*y1-y2^3);

testEquality( (X,Y), "H^2")

///