
//////////////////////////////////////////////////
// Function for computing Hecke correspondence  //
//////////////////////////////////////////////////

hecke_corr := function(data,q,N : basis0:=[],basis1:=[],printlevel:=1,use_polys:=[])

  // For i=1,...,g-1, construct a nice correspondence Zi from the ith power of
  // the Hecke operator Aq using Eichler-Shimura. 
  // N is the precision for the q-adic computation. 
  //
  // Both Aq^i and Zi are encoded as matrices representing their action on H^1_dR(X)
  //
  // If basis0 and basis1 are given, we assume that they form a symplectic basis
  // of H^1_dR(X). If they aren't given, such a basis is computed along the way.
  // if a list of rational polynomials [f1,...,fd] is given in use_polys, then the Zi returned will be 2*g*fi(Tq)-Trace(fi(Tq)).
  Q:=data`Q; g:=data`g; d:=Degree(Q); p:=data`p; 

  C:=ZeroMatrix(RationalField(),2*g,2*g);
  for i:=1 to g do
    C[i,g+i]:=1;
    C[g+i,i]:=-1; 
  end for;

  if basis0 ne [] then
    v0:=Minimum(&cat[[Valuation(coef,q):coef in &cat[Coefficients(basis0[i][j]):j in [1..d]]]: i in [1..g]]); // valuation basis0
  else
    v0:=0;
  end if;

  if basis1 ne [] then
    v1:=Minimum(&cat[[Valuation(coef,q):coef in &cat[Coefficients(basis1[i][j]):j in [1..d]]]: i in [1..g]]); // valuation basis1
  else
    v1:=0;
  end if;

  v:=Minimum([v0,v1]);

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
  prec_loss_bd := Valuation(Determinant(Finv), p);
  prec_loss_bd +:= q eq p select 1 else 0;

  Zs:=[]; As:=[];
  AQ := ZeroMatrix(Rationals(), 2*g, 2*g); ZQ := AQ;

  if #use_polys eq 0 then

    for i in [1..g-1] do
      A := Aq^i; // ith power of hecke operator
      Zmx := (2*g*A-Trace(A)*IdentityMatrix(Rationals(),2*g))*C^(-1);  
      // Zmx is a q-adic approximation of a nice correspondence Z
      // Now clear denominators to find A and Z exactly
      D1 := LCM([LCM([Denominator(Zmx[j,k]):k in [1..2*g]]):j in [1..2*g]]);
      D2 := LCM([LCM([Denominator(A[j,k]):k in [1..2*g]]):j in [1..2*g]]);
      D := LCM(D1,D2);
      A *:= D;
      Zmx *:= D;
      for j in [1..2*g] do
        for k in [1..2*g] do
          AQ[j,k] := lindepQp(pAdicField(q, N-1)!A[j,k]);    // recognition of integer in Zp via LLL
          ZQ[j,k] := lindepQp(pAdicField(q, N-1)!Zmx[j,k]);  // dito
        end for;
      end for;
      if Trace(ZQ*C) ne 0 then // approximation issue. Perturbe ZQ slightly.
        if q ne p then 
          error "q-adic approximation of nice correspondence not exact.";  
        end if;
          
        W:=ZeroMatrix(Rationals(),2*g, 2*g);
        W[1,g+1]:=Trace(ZQ*C);
        W[g+1,1]:=-Trace(ZQ*C);
        ZQ:=2*ZQ+W;
      end if;
      Append(~Zs,ZQ);
      Append(~As,AQ);
    end for;
  else
    for i in [1..g-1] do
      AQ := ChangeRing(ChangeRing(Aq,pAdicRing(p,N))^i,Rationals()); // ith power of hecke operator
      Append(~As,AQ);
    end for;

    A0:=ChangeRing(Evaluate(use_polys[1],ChangeRing(As[1],pAdicRing(p,N))),Rationals());
    for i in [2..#use_polys] do
      A :=ChangeRing(Evaluate(use_polys[i],ChangeRing(As[1],pAdicRing(p,N))),Rationals()); 
      ZQ := (Trace(A0)*A-Trace(A)*A0)*C^(-1);  
      Append(~Zs,ZQ);
    end for;

    A:=Aq;
    D := LCM([LCM([Denominator(Aq[j,k]):k in [1..2*g]]):j in [1..2*g]]);
    A *:= D;
    for j in [1..2*g] do
      for k in [1..2*g] do
        A[j,k] := lindepQp(pAdicField(q, N-1)!A[j,k]);    // recognition of integer in Zp via LLL
      end for;
    end for;
    As:=[A];

  end if; // #use_polys eq 0 

  return Zs, As[1], prec_loss_bd;
end function;



