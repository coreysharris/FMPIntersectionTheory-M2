
M = {kk=>(ZZ/32479)} >> o -> (n,r) -> (
	-- << n << "x" << n << " matrices of rank less than or equal to " << r << endl;
	N := n^2;
	-- t := symbol t;
	R := o.kk(monoid[ (i -> (getSymbol "t")_i) \ (0..N-1) ]);
	M := genericMatrix(R,R_0,n,n);
	return minors(r+1,M);
)

Ls = {kk=>(ZZ/32479)} >> o -> (n,r,s) -> (
	I := M(n,r,kk=>o.kk);
	R := ring(I);
	S := s / (i -> R_i);
	V := flatten entries vars ring I;
	J := ideal (select( V, (a) -> (member(a,S)) ));
	return (J,I);
)

dnr = (n,r) -> (
	k := n-r;
	-- returns the degree of the locus of nxn matrices with rank <= r in PP^{n^2-1}
	fold( apply( (0..k-1), (i) -> (binomial(n+i,k)/binomial(k+i,k) ) ), times )
)

interestingSubsets = (n) -> (
	-- return subsets of {1,2,..,n^2}

	coordlist := {{},{1}};
	coordlist = append(coordlist, {{1},{1,2},{1,4}});
	coordlist = append(coordlist, { {1},{1,2},{1,2,3},{1,5},{1,5,6},{1,2,6},{1,5,9} });
	-- coordlist = append(coordlist, { {1},{1,2},{1,2,3},{1,2,3,4},{1,6},{1,6,7},{1,6,7,8},{1,6,11},{1,6,11,12},{1,6,11,16},{1,2,7},{1,2,7,8},{1,2,7,12},{1,2,3,8},{1,2,6},{1,2,6,7},{1,2,6,7,8},{1,2,6,7,11},{1,2,6,7,11,12},{1,2,6,7,11,16},{1,2,6,7,11,12,16},{1,2,3,7},{1,2,3,7,8},{1,2,3,6,7,8},{1,2,3,6,7,8,11},{1,2,3,6,7,8,12},{1,2,3,6,7,12},{1,2,3,6,7,8,11,12},{1,2,3,6,7,8,11,12,16},{1,2,3,6,7,8,11,12,15},{1,2,3,6,7,8,11,12,15,16},{1,2,5,6,11,12,15,16},{1,2,3,5,6,11,12,15,16},{1,2,3,4,5},{1,2,3,4,5,6},{1,2,3,4,5,6,7},{1,2,3,4,5,6,7,8},{1,2,3,4,5,6,7,8,9},{1,2,3,4,5,6,7,8,9,10} });
	coordlist = append(coordlist, { {1},{1,2},{1,2,3},{1,2,3,4},{1,6},{1,6,7},{1,6,7,8},{1,2,7},{1,2,7,8},{1,2,7,12},{1,2,3,8},{1,2,6},{1,2,6,7},{1,2,6,7,8},{1,2,6,7,11},{1,2,6,7,11,12},{1,2,3,7},{1,2,3,7,8},{1,2,3,6,7,8},{1,2,3,6,7,8,11},{1,2,3,6,7,8,12},{1,2,3,6,7,12},{1,2,3,6,7,8,11,12},{1,2,3,4,5},{1,2,3,4,5,6},{1,2,3,4,5,6,7},{1,2,3,4,5,6,7,8},{1,2,3,4,5,6,7,8,9},{1,2,3,4,5,6,7,8,9,10}, {1,2,5},{1,2,5,10},{1,2,5,10,11},{1,2,5,11},{1,2,5,11,12},{1,2,5,6,11} });
	coordlist = append(coordlist, { {1},{1,2},{1,7},{1,2,3},{1,2,8}, });
	return coordlist#n;
)

pDeg = (X,Y) -> (
        R0 := ring X;
        k := coefficientRing R0;

        -- d := first degree (first flatten entries gens X);
        N := #(flatten entries gens X) - 1;
        dimY := dim variety Y;
        degY := degree Y;
        -- degvY := (d^dimY) * degY;

        z := local z;
        R1 := k[z_0..z_N];
        pr := map(R0, R1, gens X);
        prY := preimage_pr Y;
        dimprY := dim variety prY;
        degprY := degree prY;

    -- if verbosity >= 2 then (<< "PPn: "<< N << "\t dim(prY): " << dimprY << "\t dim(Y): " << dimY << "\t deg(prY): " << degprY;
    -- << "\t deg(fiber): " << (if dimprY == N then degree ( getRandomFiber(pr,(Y)) : X ) else "na") << endl);

        return ( 
                if dimprY < dimY then 0
                else if dimprY == N then ( degree (getRandomFiber(pr,(Y)) : X) )
                else degprY,  
                d ) 
)

dnrs = {kk=>(ZZ/32479)} >> o -> (n,r,s) -> (
	seg := segreClass(Ls(n,r,s,kk=>o.kk));
	<< seg << endl;
	h := (entries vars ring seg)#0#0;
	c := (1+h)^( (n^2) - ((n-r)^2) - 1);
	co := coefficient(h^((n^2)-1), c * seg);
	return dnr(n,r) - co;
)

dnrs2 = (n,r,s) -> (
	return dnr(n,r) - ( projectedDegree(Ls(n,r,s)) )#0;
) 


------------------------------------------------------
-- to get power set
getNonzeroBinaryDigits = (nn, i) -> (
    halfsies := nn//2;
    val1 := nn%2;
    val2 := false; 
    if (halfsies > 0) then val2 = (getNonzeroBinaryDigits(nn//2,i+1));
    if ( (val1 != 0) and (not (val2 === false))) then (
	 flatten {i, val2}
    )
    else if (val1 != 0) then (
	 {i}
    )
    else if ( not (val2 === false)) then (
	 flatten {val2}
    )
    else(
	 false
    )
)

--Returns the entries of myList specified by entryList
--For example, ( {1,2,3}, {0,2}) is sent to {1,3}
getSublistOfList = (myList, entryList) -> (
     --error "help";
     apply( #entryList, i->myList#(entryList#i) )
)

--Returns the power set of a given list, except it leaves out
--the emptyset.  
--For example {2,3,4} becomes { (2),(3),(4),(2,3),(2,4),(3,4),(2,3,4) }
nontrivialPowerSet = (myList) ->(
     apply(2^(#myList)-1, i-> getSublistOfList(myList, getNonzeroBinaryDigits(i+1,0) ) )
)
-----------------------------------------------------------


runtest = (n,r) -> (
	-- verbosity = -1000;
	for s in interestingSubsets(4) do (
		<< dnr(n,r) << "\t" << dnrs(n,r,s) << "\t" << dnrs2(n,r,s) << "\t" << s << endl;
	)
)