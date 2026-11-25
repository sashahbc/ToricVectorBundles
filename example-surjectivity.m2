needsPackage "ToricVectorBundles2"

---- CODE ----

genericFibre := E -> (
	X = variety E;
        minE = min apply(filtrationJumps E, min );
	return filteredPiece(E,(rays X)#0,minE)
)

isSurjective2 := p -> (
	if not isSurjective p.map then return false;
	E = source p;
	F = target p;
	X = variety E;
	
	Emat = genericFibre E;
	Fmat = genericFibre F;
	for d in 1..dim X do (
		for sigma in cones(d,fan X) do (
			minE = min apply(sigma, r -> min filtrationJumps(E,(rays X)#r) );
			minF = min apply(sigma, r -> min filtrationJumps(F,(rays X)#r) );
			minEF = min {minE,minF}+1;
			maxE = max apply(sigma, r -> max filtrationJumps(E,(rays X)#r) );
			maxF = max apply(sigma, r -> max filtrationJumps(F,(rays X)#r) );
			maxEF = max {maxE,maxF};
			for i in minEF..maxEF do (
				Ei = intersect(apply(sigma, r -> image filteredPiece(E,(rays X)#r,i)));
				Fi = intersect(apply(sigma, r -> image filteredPiece(F,(rays X)#r,i)));
				mati = (matrix p)*Emat*(gens Ei);
				if image mati != Fi then return false
			)
		)
	);
	
	return true
)

---- EXAMPLE 1 ----

A2 = affineSpace 2

E = lineBundle(-A2_0) ++ lineBundle(-A2_1)
-- filtrations E

OA2 = trivialBundle(A2,1)

p = map(OA2,E, matrix {{1,1}})
assert( isWellDefined p )

---- "reflexive cokernel":
assert( rank cokernel p  == 0 )

---- WRONG, the true cokernel is the skyscraper sheaf at 0:
-- isSurjective p 

assert( not isSurjective2 p )

---- EXAMPLE 2 ----
		
X = toricProjectiveSpace 3

L = lineBundle(-X_0)
OX = trivialBundle(X,1)

f = map(OX,L, matrix{{1}})
assert( isWellDefined f )

assert( rank cokernel f == 0 )

-- isSurjective f

assert( not isSurjective2 f )

---- EXAMPLE 3 ----
		
X = toricProjectiveSpace 3
TX = tangentBundle X; 
OX = trivialBundle(X,1);
Ls = lineBundle X_0 ++ lineBundle X_1 ++ lineBundle X_2 ++ lineBundle X_3;

f = map(Ls,OX,matrix(QQ,{{1},{1},{1},{1}}));
g = map(TX,Ls, transpose sub(matrix rays X,QQ));

assert( isWellDefined f )
assert( isWellDefined g )

assert( not isSurjective2 f )
assert( isSurjective2 g )


