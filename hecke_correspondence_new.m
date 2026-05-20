
//////////////////////////////////////////////////
// Function for computing Hecke correspondence  //
//////////////////////////////////////////////////

hecke_corr_new := function(data,q : N := 0, basis0:=[],basis1:=[],printlevel:=1,polys:=[])

  // For i=1,...,g-1, construct a nice correspondence Zi from the ith power of
  // the Hecke operator Aq using Eichler-Shimura. 
  // N is the precision for the q-adic computation. 
  //
  // Both Aq^i and Zi are encoded as matrices representing their action on H^1_dR(X)
  //
  //
  Q:=data`Q; g:=data`g; d:=Degree(Q); p:=data`p; 
  if IsZero(N) then N := data`N; end if;
  if #basis0 eq 0 then basis0 := [data`basis[i] : i in [1..g]]; end if;
  if #basis1 eq 0 then basis1 := [data`basis[i] : i in [g+1..2*g]]; end if;

  C:=ZeroMatrix(RationalField(),2*g,2*g);
  for i:=1 to g do
    C[i,g+i]:=1; C[g+i,i]:=-1; 
  end for;

  v0:=0; v1:=0;
  if basis0 ne [] then
    v0:=Minimum(&cat[[Valuation(coef,q):coef in &cat[Coefficients(basis0[i][j]):j in [1..d]]]: i in [1..g]]); // valuation basis0
  end if;

  if basis1 ne [] then
    v1:=Minimum(&cat[[Valuation(coef,q):coef in &cat[Coefficients(basis1[i][j]):j in [1..d]]]: i in [1..g]]); // valuation basis1
  end if;

  v:=Minimum([v0,v1,0]);
  if q eq p then assert v eq 0; end if; // basis should be p-linear
  // multiply by constant to remove denominator in basis0 and basis1
  if v lt 0 then
    for i:=1 to g do
      for j:=1 to d do
        basis0[i][j]:=q^(-v)*basis0[i][j];
        basis1[i][j]:=q^(-v)*basis1[i][j];
      end for;
    end for;
  end if;

  if q ne p then 
    if printlevel gt 0 then print  "\nCompute Coleman data wrt q=", q; end if;
    data:=coleman_data(Q,q,N:basis0:=basis0,basis1:=basis1);
  end if;

  F := data`F;
  if q eq p then F := Submatrix(data`F,1,1,2*g,2*g); end if;// Necessary when q=p
  Finv := Transpose(F)^(-1);
  Aq := Transpose(F)+q*Finv;   // Eichler-Shimura -> Hecke operator
  Zp := pAdicRing(p,N);
  prec_loss_bd := Valuation(Determinant(Finv), p);
  prec_loss_bd +:= q eq p select 1 else 0;

  Zs:=[]; 

  D := LCM([LCM([Denominator(Aq[j,k]):k in [1..2*g]]):j in [1..2*g]]);
  prec_loss_bd +:= Valuation(D, p);
  D_rat := lindepQp(pAdicField(q, N-1)!D);
  A := ZeroMatrix(RationalField(),2*g,2*g);
  for j in [1..2*g] do
    for k in [1..2*g] do
      A[j,k] := lindepQp(pAdicField(q, N-1)!(D*Aq[j,k]))/D_rat;    // recognition of integer in Zp via LLL
    end for;
  end for;
  As := [A^i : i in [1..g-1]];
  traces := [Trace(Ai) : Ai in As];

  if #polys eq 0 then
    polys := [2*g*x^i-traces[i]: i in [1..g-1]];
  end if;

  for poly in polys do
    ZQ := Evaluate(poly, A)*C^(-1);

    if Trace(ZQ*C) ne 0 then // approximation issue. Perturbe ZQ slightly.
      if q ne p then 
        error "q-adic approximation of nice correspondence not exact.";  
      end if;
      W:=ZeroMatrix(Rationals(),2*g, 2*g);
      W[1,g+1]:=Trace(ZQ*C);
      W[g+1,1]:=-Trace(ZQ*C);
      ZQ:=ZQ+W/2;
    end if;
    Append(~Zs,ZQ);
  end for;

/*  for i,j in [1..2*g] do
    "This should be large: no sign change", Valuation(Aq[i,j] - As[1,i,j], p);
    "or this: sign change", Valuation(Aq[i,j] + As[1,i,j], p);
  end for;*/

  return Zs, A, prec_loss_bd;
end function;




