auxpolys:=function(Q);

  // Compute the polynomials r,Delta,s.

  Delta:=Discriminant(Q); 
  r:=Numerator(Delta/GCD(Delta,Derivative(Delta)));

  Qx<x>:=RationalFunctionField(RationalField());
  Qxy<y>:=PolynomialRing(Qx);
  d:=Degree(Q);
  Syl:=ZeroMatrix(Qx,2*d-1,2*d-1);
  coefs1:=Reverse(Coefficients(Q));
  coefs2:=Reverse(Coefficients(Derivative(Q)));
  for i:=1 to d-1 do
    for j:=1 to d+1 do
      Syl[i,i+j-1]:=coefs1[j];
    end for;
  end for;
  for i:=d to 2*d-1 do
    for j:=1 to d do
      Syl[i,i-d+j]:=coefs2[j];
    end for;
  end for;

  v:=[Qx|];
  for i:=1 to 2*d-2 do
    v[i]:=0;
  end for;
  v[2*d-1]:=Delta; 
  M:=RModule(Qx,2*d-1);
  sol:=Solution(Syl,M!v);
  
  com_fac:=Delta;
  for i:=1 to d do
    com_fac:=GCD(com_fac,Numerator(sol[2*d-i]));
  end for;
  Delta:=Numerator(Delta/com_fac);
  for i:=1 to d do
    sol[2*d-i]:=sol[2*d-i]/com_fac;
  end for; 

  s:=Parent(Q)!0;
  for i:=1 to d do
    s:=s+(BaseRing(Parent(Q))!Numerator(sol[2*d-i]))*(Parent(Q).1)^(i-1);
  end for;

  // (s*Derivative(Q)-Delta)/Q; // test
  
  return BaseRing(Parent(Q))!r,BaseRing(Parent(Q))!Delta,Parent(Q)!s;
end function;

genus:=function(Q,p)

  // Computes the genus of the smooth projective curve defined by Q

  Fp:=FiniteField(p);
  A2:=AffineSpace(Fp,2);
  Fpxy:=CoordinateRing(A2);
  Qmodp:=Fpxy!0;
  C:=Coefficients(Q);
  for i:=1 to #C do
    D:=Coefficients(C[i]);
    for j:=1 to #D do
        Qmodp:=Qmodp+(Fp!D[j])*Fpxy.1^(j-1)*Fpxy.2^(i-1);
    end for;
  end for;
  if not IsIrreducible(Qmodp) then
    error "bad prime";
  end if;
  g:=Genus(Curve(Scheme(A2,Qmodp)));
  return g;  
end function;

smooth:=function(f,p)

  // Is f mod p separable?

  Fp:=FiniteField(p);
  Fpx:=PolynomialRing(Fp);
  
  if Degree(Fpx!f) eq Degree(f) and IsSeparable(Fpx!f) then
    return true;
  else
    return false;
  end if;
end function;

log:=function(p,x)
  if x gt 0 then
    return Log(p,x);
  else
    return 0; 
  end if;
end function;

is_integral:=function(A,p)

  // Is the matrix A p-adically integral?

  A:=A*Denominator(A);
  for i:=1 to NumberOfRows(A) do
    for j:=1 to NumberOfColumns(A) do
      if A[i,j] ne 0 then
        m:=Minimum([Valuation(x,p) : x in Coefficients(Numerator(A[i,j]))]);
        if m lt 0 then
          return false;
        end if;
      end if;
    end for;
  end for;
  return true; 
end function;


