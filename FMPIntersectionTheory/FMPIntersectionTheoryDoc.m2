

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
                        (chernSchwartzMacPherson,ProjectiveScheme)
                        (chernSchwartzMacPherson,Ideal)
                        chernSchwartzMacPherson
                Headline
                        compute the Chern-Schwartz-MacPherson class of a projective variety
                Usage
                        chernSchwartzMacPherson(X)
                        --chernSchwartzMacPherson(I)
                Inputs
                        X:ProjectiveScheme
                        --I:Ideal
                Outputs
                        :
                                the CSM class as an element of the Chow ring of the ambient projective space
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
                        (intersectionProduct,ProjectiveScheme,ProjectiveScheme,ProjectiveScheme)
                        intersectionProduct
                Headline
                        compute the Fulton-MacPherson intersection product
                Usage
                        intersectionProduct(X,V,Y)
                Inputs
                        X:ProjectiveScheme
                                a regularly embedded subvariety of Y
                        V:ProjectiveScheme
                                a subvariety of Y
                        Y:ProjectiveScheme
                                a projective variety
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
                        (codim,ProjectiveScheme)
                Headline
                        gives the codim of a ProjectiveScheme in PP^N
                Usage
                        codim X
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
                        (intersectionRing,ProjectiveScheme)
                Headline
                        gives the intersection ring of the containing projective space
                Usage
                        intersectionRing X
                Inputs
                        X:ProjectiveScheme
                Outputs
                        :Ring
                Description
                        Example
                                R = QQ[x,y,z];
                                I = ideal x*y;
                                X = projectiveScheme(I);
                                intersectionRing X
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
                Description
                        Example
                                PP2 = QQ[x,y,z];
                                X = ideal "y2z-x3-x2z";
                                dualDegree(X)
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