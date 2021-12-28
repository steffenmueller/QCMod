//////////////////////////
// Some extra functions //
//////////////////////////

// Algebraic recognition for element in Qp.
function algdepQp(a,deg)

    ZZ := Integers();
    QQ := Rationals();
    RR := RealField(500);
    PolZ<x>:=PolynomialRing(ZZ);
   
    p := Prime(Parent(a));
    m := Precision(Parent(a));
    N := p^m;
    
    if Valuation(a) ge m then
      P1 := x;
    else
      M:=ZeroMatrix(RR,deg+2,deg+2);
      for j := 1 to deg+1 do 
        M[j,j] := 1;
        M[j,deg+2] := QQ!(a^(j-1));
      end for;
      M[deg+2][deg+2] := N;
      Y,T:=LLL(M);

      P1 := Floor(Y[2][deg+2] - Y[2][1]);
      for j := 2 to deg+1 do
        P1 := P1 - Floor(Y[2][j])*x^(j-1);
      end for;
      Fac1 := Factorisation(P1);
      P1   := Fac1[#Fac1][1];
    end if;
    
    return P1;
       
end function;


// Linear recognition for element in Qp.
function lindepQp(a)
  QQ:=RationalField();
  px := algdepQp(a, 1);

  return -(QQ!Coefficient(px,0))/(QQ!Coefficient(px,1));
end function;



// Find an equivariant splitting of the Hodge filtration.
// We need to solve the equation T'*S = S*T, where T is the action induced by a generator
// of End^0(J) on V = H^1_dR, and T' is the induced action on V/Fil^0. Since T is a 2g x 2g
// matrix and T' is a g x g matrix, we're solving for a 2g x g matrix S.
// This leads to the following system of linear equations:

function eq_split(Aq)
  assert Nrows(Aq) eq Ncols(Aq) and IsEven(Nrows(Aq));
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



eval_R:=function(f,pt,r)

  // Evaluate an element of R at x=x0, y=y0.

  R:=Parent(f); S:=BaseRing(R); Ox:=BaseRing(S); O:=BaseRing(Ox);

  zR:=(Ox!r)/LeadingCoefficient(r);

  x0:=O!pt[1];
  y0:=O!pt[2];
  z0:=Evaluate(zR,x0);
  ev:=O!0;
  C:=Coefficients(f);
  for i:=1 to #C do
    val:=Valuation(C[i]);
    D:=Coefficients(C[i]);
    for j:=1 to #D do
      ev:=ev+Evaluate(D[j],x0)*z0^(val+j-1)*y0^(i-1);
    end for;
  end for;

  return ev;
end function;


eval_mat_R:=function(A,pt,r)

  // Evaluate a matrix over R at x=x0, y=y0.

  R:=BaseRing(A); S:=BaseRing(R); Ox:=BaseRing(S); O:=BaseRing(Ox);

  B:=ZeroMatrix(O,NumberOfRows(A),NumberOfColumns(A));
  for i:=1 to NumberOfRows(A) do
    for j:=1 to NumberOfColumns(A) do
      B[i,j]:=eval_R(A[i,j],pt,r);
    end for;
  end for;

  return B;
end function;


compute_F:=function(Q,W0,Winf,f0,finf,fend)

  // Given functions f0,finf and fend, as vectors of coefficients w.r.t. b^0,b^inf,b^0 respectively, 
  // return f0+finf+fend as a vector w.r.t. b^0 (so convert finf from b^inf to b^0 and take the sum). 
  
  d:=Degree(Q);
  W:=Winf*W0^(-1);

  Qxzzinvd:=Parent(f0);
  Qxzzinv:=BaseRing(Qxzzinvd);
  x1:=Qxzzinv!(BaseRing(Qxzzinv).1);
  Qxxinv:=LaurentSeriesRing(RationalField());

  conv:=Qxzzinvd!Evaluate(Evaluate(finf,Qxxinv.1)*Evaluate(W,Qxxinv.1),x1); // finf converted to basis b^0
  F:=f0+conv+fend;

  return F, conv;
end function;


Qxzzinvd_to_R:=function(f,Q,p,r,R,W0)

  // Convert from Q[x,z,1/z]^d to R, using the basis b^0.

  d:=Degree(Q);

  S:=BaseRing(R);
  Ox:=BaseRing(S);
  y:=R.1;
  z:=S.1;
  x:=Ox.1;

  rQx:=Parent(Numerator(W0[1,1]))!r;
  lc:=LeadingCoefficient(rQx);
  rQx:=rQx/lc; // rQx now corresponds to z=r/LeadingCoefficient(r)

  ordrW0:=ord_r_mat(W0,rQx);

  b0:=[];
  for i:=1 to d do
    b0i:=R!0;
    for j:=1 to d do
      b0i:=b0i+z^(ordrW0)*(R!Ox!(Numerator(W0[i,j]*rQx^(-ordrW0))))*y^(j-1);
    end for;
    b0:=Append(b0,b0i);
  end for;

  f_R:=R!0;  
  for i:=1 to d do
    if f[i] ne 0 then
      for j:=Valuation(f[i]) to Degree(f[i]) do
        coef:=Ox!Coefficient(f[i],j);
        f_R:=f_R+coef*z^j*b0[i]; 
      end for;
    end if;
  end for;

  return f_R;
end function;

function make_bivariate(Q)

  d:=Degree(Q);

  Qx:=RationalFunctionField(RationalField()); Qxy:=PolynomialRing(Qx);

  f:=Qxy!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qxy.1^i*Qx.1^j;
    end for;
  end for;
  
  return f; 
end function;

function function_field(Q)

  return FunctionField(make_bivariate(Q)); // function field of curve

end function;


fun_field:=function(data);

  Q:=data`Q; d:=Degree(Q);

  Qx:=RationalFunctionField(RationalField()); Qxy:=PolynomialRing(Qx);

  f:=Qxy!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qxy.1^i*Qx.1^j;
    end for;
  end for;
  
  return FunctionField(f); // function field of curve

end function;

// Returns the index of a rational point in the set Qppoints.
function FindQpointQp(P,Qppoints)

  x := P`x;
  y := P`b[2];
  index := -1;
  for i := 1 to #Qppoints do
    xi := Qppoints[i]`x;
    yi := Qppoints[i]`b[2]; // To do: Does this always work for bad points?
     
    if Valuation(x-xi) gt 0 and Valuation(y-yi) gt 0 and Qppoints[i]`inf eq false then
      index := i;
    end if;
  end for;

  return index;

end function;


function good_points(Qpoints, Qppoints, data)
  // Find good affine points as elements of Qppoints and their indices.
  
  indices := [];
  points := [];
  for P in Qpoints do
    ind := FindQpointQp(P,Qppoints); 
    if ind gt 0 and not is_bad(Qppoints[ind],data) and not P`inf then		
      Append(~indices, ind);
      Append(~points, P); 
    end if;
  end for;

  return points, indices;
end function;


function coefficients_mod_pN(fake_rat_pts, rat_pts, divisors, base_pt, splitting_indices, data : printlevel := 0)
  // return the coefficients mod p^N of the images of the fake and the actual rational points 
  // under the Abel Jacobi map given by base_pt in terms of generators of the MW group mod
  // torsion
  //

  if printlevel gt 1 then "compute basis integrals"; end if;

  basis_integrals := [coleman_integrals_on_basis_divisors(t[2], t[1], data) : t in divisors];
  M := (Matrix(pAdicField(data`p, data`N), data`g, data`g, [basis_integrals[1,1], basis_integrals[2,1], basis_integrals[1,2], basis_integrals[2,2]]))^-1;
  index_matrix := Transpose(Matrix(splitting_indices));

  if printlevel gt 2 then "compute integrals for rational points"; end if;

  rat_integrals  := [coleman_integrals_on_basis_divisors([base_pt], [P], data) : P in rat_pts];
  if printlevel gt 1 then "rational integrals", rat_integrals; end if;
  
  rat_coeffs  := [Eltseq(ChangeRing(index_matrix*M*Matrix(2,1,[ints[1], ints[2]]), Integers())) : ints in rat_integrals];
  if printlevel gt 2 then "compute integrals for fake rational points"; end if;
  fake_integrals := [coleman_integrals_on_basis_divisors([base_pt], [P], data) : P in fake_rat_pts];
  if printlevel gt 1 then "fake integrals", fake_integrals; end if;
  fake_coeffs := [Eltseq(ChangeRing(index_matrix*M*Matrix(2,1,[ints[1], ints[2]]), Integers())) : ints in fake_integrals];

  return fake_coeffs, rat_coeffs;
end function;



function eval_Q(Q, x0, y0)
  Qp := Parent(x0);
  coeffs_Qp:=[ChangeRing(c,Qp):c in Coefficients(Q)];
  res := 0;
  for i := 1 to #coeffs_Qp do
    res +:= Evaluate(coeffs_Qp[i], x0)*y0^(i-1);
  end for;
  return res;
end function;




function rank_J0Nplus(N : Lprec := 30, printlevel := 0)

// Compute the rank of J0(N)+ using Kolyvagin-Logachev. Will
// throw an error if the analytic rank for any newform appears 
// to be >1.
//
  NF := Newforms(CuspForms(Gamma0(N),2));
  errors := [];
  pl := printlevel;

  for f in [t[1] : t  in NF | AtkinLehnerEigenvalue(t[1], N) eq 1] do
    if pl gt 1 then printf "The newform is %o, \n", qExpansion(f, 20); end if;
    if pl gt 1 then printf "defined over %o. \n\b", NumberField(BaseRing(f)); end if;
    L := LSeries(ModularAbelianVariety(f));
    d := Degree(NumberField(BaseRing(f)));
    if not IsZeroAt(L, 1) then return 0, [0: i in [1..d]]; end if;
    Lseries := [LSeries(f : Embedding := func<x | Conjugates(x)[i] >) : i in [1..d]];
    rank := 0;
    i := 0;

    for L in Lseries do 
      LSetPrecision(L, Lprec);
      if pl gt 1 then "checking the functional equation for conjugate",i; end if;
      assert IsZero(CFENew(L));
      taylor := LTaylor(L, 1, 1);  
      if pl gt 0 then 
        printf "The Taylor expansion of the L-function of %o at s=1 is \n%o\n", f, taylor;
      end if;
      if IsZero(Coefficient(taylor, 0)) then 
        coeff := Coefficient(taylor, 1);
        if Abs(coeff) lt 10^-3 then // might be 0
          error "rank seems to be larger than g -- this is not implemented";
        else 
          rank +:= 1;
        end if;
      end if;
      Append(~errors, coeff);
      i +:= 1;
    end for; // L in Lseries
  end for; // f in ...
  return rank, errors;
end function;


function minprec(M)
  try
    min_prec := Min([AbsolutePrecision(c) : c in Eltseq(M)]);
  catch e;
    min_prec := Min([minprec(m) : m in M]);
  end try;
  return min_prec;
end function;


function minval(M)
  if Type(M[1]) eq SeqEnum then
    return Min([minval(m) : m in M]);
  end if;
  return Min([Valuation(c) : c in Eltseq(M)]);
end function;


function minvalp(M,p)
  return Min([Valuation(c,p) : c in Eltseq(M)]);
end function;

procedure compare_vals(L1, L2, N)
  for i in [1..#L1] do
    if L1[i,1] gt N then 
      L1[i,1] := N;
    end if;
  end for;
  for i in [1..#L2] do
    if L2[i] gt N then 
      L2[i] := N;
    end if;
    m := #[d : d in L2 | d eq L2[i]];
    s := &+[L1[j,2] : j in [1..#L1] | L1[j,1] eq L2[i]];
    if s eq 0 then
      error "Root finding returned a root with incorrect valuation";
    end if;
    if m gt s then
      error "Root finding returned the wrong number of roots";
    end if;

  end for;
end procedure;

function count_roots_in_unit_ball(f, N)
  // TODO: Deal with zero poly
  vals := ValuationsOfRoots(f);
  number_of_roots := 0;
  univ := Universe(vals);
  for pair in vals do
    if pair[1] ge 0 then
    // Had to include this workaround because magma's extended reals 
    // are counterintuitive (to say the least)
      val_root := pair[1];
      if val_root ge N then 
        val_root := N;
      end if;
      val_root := Rationals()!val_root;
      if IsIntegral(val_root) then
        number_of_roots +:= pair[2];     
      end if;
    end if;
  end for;
  return number_of_roots;
end function;

function are_congruent(pt1, pt2)
  // pt1 and pt2 are two p-adic points whose parents might have 
  // different precision. one rational point is also allowed
  if Type(Universe(pt1)) eq FldRat then
    min_prec := minprec(pt2);
  elif Type(Universe(pt2)) eq FldRat then 
    min_prec := minprec(pt1);
  else 
    min_prec := Min(minprec(pt1), minprec(pt2));
  end if;
  min_diff := Min([Valuation(d) : d in [pt1[1]-pt2[1], pt1[2]-pt2[2]]]);
  if min_diff ge min_prec then
    return true;
  end if;
  return false;
end function;
