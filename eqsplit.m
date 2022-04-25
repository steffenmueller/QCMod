// Two functions to compute an equivariant splitting using basic
// linear algebra
// 
// The first one is simpler and less error-prone
//
function equivariant_splitting(Z)

        assert NumberOfColumns(Z) eq NumberOfRows(Z);
        g := Integers()!(NumberOfRows(Z)/2);
        assert Submatrix(Z,g+1,1,g,g) eq 0;
        mxList := []; 
        upLeft := Submatrix(Z,1,1,g,g);
        downRight := Submatrix(Z,g+1,g+1,g,g);
        upRight := Submatrix(Z,1,g+1,g,g);
        for i in [g..(g^2 + g - 1)] do
                row := i div g;
                col := (i mod g) + 1;
                zed := ZeroMatrix(Rationals(),g,g);
                zed[row][col]:= 1;
                mxList := mxList cat [Eltseq(zed * downRight - upLeft * zed)];
        end for;
        vecList := Eltseq(upRight);
        mat := Matrix(mxList);
        wec := Vector(vecList);
        vec := Solution(mat,wec);
        mat2 := Matrix(g,g,Eltseq(vec));
        blocks := [IdentityMatrix(Rationals(),g), mat2,ZeroMatrix(Rationals(),g,g),IdentityMatrix(Rationals(),g)];
        sol := BlockMatrix(2,2,blocks);

        // Check that this conjugates Z to a block diagonal matrix (2 blocks).
        Znew := sol^-1 * Z * sol;
        assert Submatrix(Znew,1,g+1,g,g) eq 0;
        //print "This matrix should be block diagonal: ", Znew;

        // We want to return a different matrix
        return BlockMatrix(2,1,[IdentityMatrix(Rationals(),g), -mat2]);
  
end function;




function eq_split(Aq)
  assert Nrows(Aq) eq Ncols(Aq) and IsEven(Nrows(Aq));
// Find an equivariant splitting of the Hodge filtration.
// We need to solve the equation T'*S = S*T, where T is the action induced by a generator
// of End^0(J) on V = H^1_dR, and T' is the induced action on V/Fil^0. Since T is a 2g x 2g
// matrix and T' is a g x g matrix, we're solving for a 2g x g matrix S.
// This leads to the following system of linear equations:
  g := Nrows(Aq) div 2;
  M := ZeroMatrix(RationalField(), 2*g^2, 2*g^2);
  for i := 1 to 2*g do
    for j := 1 to g do
      for n := 0 to 2*g-1 do
        M[g*(i-1)+j, g*n+j] := -Aq[n+1,i];
      end for;
      for l := 1 to g do
        M[g*(i-1)+j,g*(i-1)+l] +:= Aq[g+l,g+j];
      end for;
    end for;
  end for;
  N := Kernel(Transpose(M)); // The elements are vectors of length 2g^2. 

  V := VectorSpace(Rationals(), 2*g^2);
  L1 := [V!v : v in Basis(N)];
  V1 := sub<V | L1>;  // Space of solutions to matrix equation
  
  // Now let's find the ones corresponding to a splitting. We do this by intersecting with
  // the subspace of V corresponging to matrices of the shape we're interested in.

  // Disclaimer: This can be obviously improved by rewriting the system above to take the
  // information into account that we only care about splittings. In practice, computing
  // an equivariant splitting takes negligible time.

  L2 := []; 
  v := Zero(V);
  n := 1;
  // We only allow diagonal matrices in the top g x g block.
  for i := 1 to g do
    w := v; w[n] := 1;
    n +:= g+1; 
    Append(~L2, w); 
  end for;
  // The bottom row and the rightmost column of the lower g x g block are assumed trivial.
  for i := g^2+1 to 2*g^2-g do
    if i mod g ne 0 then
      w := v; w[i] := 1;
      Append(~L2, w); 
    end if; 
  end for;
  V2 := sub<V | L2>;
  W := V1 meet V2;  // Take intersection 

  // Can we show the above always suffices? If so, the following block is unnecessary.
  if Dimension(W) eq 0 then 
    // Allow nonzero entries in the bottom row
    i := 2*g^2-g;
    repeat 
      i +:= 1; w := v; w[i] := 1;
      Append(~L2, w); 
      V2 := sub<V | L2>;
      W := V1 meet V2;  // Take intersection 
    until Dimension(W) gt 0 or i eq 2*g^2;
    if Dimension(W) eq 0 then
      // Allow nonzero entries in the rightmost column
      i := g^2;
      repeat 
        i +:= g; w := v; w[i] := 1;
        Append(~L2, w); 
        V2 := sub<V | L2>;
        W := V1 meet V2;  // Take intersection 
      until Dimension(W) gt 0 or i eq 2*g^2;
    end if;
    assert Dimension(W) gt 0; // If you end up here, you've found a bug. 
  end if;

  bas := [Matrix(RationalField(), 2*g, g, Eltseq(w)) : w in Basis(W)]; 
  // bas is the basis of the intersection, written as matrices. 
  // Still need to add the condition that the top block is (a multiple of) E_g
  j := 0;
  repeat 
    j +:= 1;
    S := bas[j];
  until j eq #bas or #{S[i,i]:  i in [1..g]} eq 1; 
  assert #{S[i,i]:  i in [1..g]} eq 1; 
  S := S/S[1,1]; // turn upper block into E_g;

  // Check that the splitting is indeed equivariant.
  Aqs := ExtractBlock(Aq,g+1,g+1,g,g);
  assert IsZero(S*Aqs - Transpose(Aq)*S);

  return S;
end function;

