mat_W0:=function(Q)

  // Compute the matrix W0 using MaximalOrderFinite

  Qt:=RationalFunctionField(RationalField());
  K:=ext<Qt|Q>;
  b0:=Basis(MaximalOrderFinite(K));
  d:=Degree(Q);
  mat:=ZeroMatrix(Qt,d,d);
  for i:=1 to d do
    for j:=1 to d do
      mat[i,j]:=Eltseq(K!b0[i])[j];
    end for;
  end for;
  return mat;

end function;


mat_Winf:=function(Q);

  // Compute the matrix Winf using MaximalOrderFinite

  Qt:=RationalFunctionField(RationalField());
  Qty:=PolynomialRing(Qt);
  Qnew:=Qty!0;
  C:=Coefficients(Q);
  for i:=1 to #C do
    Qnew:=Qnew+Evaluate(C[i],1/Qt.1)*Qty.1^(i-1);
  end for;
  Q:=Qnew;
  K:=ext<Qt|Q>;
  binf:=Basis(MaximalOrderFinite(K));
  d:=Degree(Q);
  mat:=ZeroMatrix(Qt,d,d);
  for i:=1 to d do
    for j:=1 to d do
      mat[i,j]:=Eltseq(K!binf[i])[j];
    end for;
  end for;
  return Evaluate(mat,1/Qt.1);

end function;


ddx:=function(f)

  // Differentiate polynomial f(x)(y) with respect to x.

  C:=Coefficients(f);
  for i:=1 to #C do
    C[i]:=Derivative(C[i]);
  end for;
  return Parent(f)!C;
end function;


ddx_mat:=function(A)

  // Differentiate matrix of rational functions.

  for i:=1 to NumberOfRows(A) do
    for j:=1 to NumberOfColumns(A) do
      A[i,j]:=Derivative(A[i,j]);
    end for;
  end for;
  return A;
end function;


ddx_vec:=function(v)

  // Differentiate vector of rational functions.

  for i:=1 to #Eltseq(v) do
    v[i]:=Derivative(v[i]);
  end for;
  return v;
end function;


reduce_mod_Q_exact:=function(f,Q)

  // Eliminate powers of y >= d_x.

  while Degree(f) gt Degree(Q)-1 do
    f:=f-LeadingCoefficient(f)*(Parent(f).1)^(Degree(f)-Degree(Q))*Q;
  end while;
  return f;
end function;


polys_to_vec:=function(polys,degx);

  // Converts a sequence of polynomials to a vector  

  dim:=#polys*(degx+1);
  v:=[];
  cnt:=1;
  for i:=1 to #polys do
    for j:=0 to degx do
      v[cnt]:=Coefficient(polys[i],j);
      cnt:=cnt+1;
    end for;
  end for;

  V:=VectorSpace(RationalField(),dim);

  return V!v;
end function;



ram:=function(J0,Jinf)

  // Return the maximum finite and infinite ramification
  // indices, given the matrices J0, Jinf.

  d:=NumberOfRows(Jinf);
  
  e_list:=[];
  for i:=1 to #J0 do
    for j:=1 to d do
      e_list:=Append(e_list,Denominator(RationalField()!J0[i][j,j]));
    end for;
  end for;
  if #e_list gt 0 then
    e_0:=Maximum(e_list);
  else
    e_0:=0;
  end if;
  
  e_list:=[];
  for i:=1 to d do
    e_list:=Append(e_list,Denominator(RationalField()!Jinf[i,i]));
  end for;
  e_inf:=Maximum(e_list);

  return e_0,e_inf;
end function;


con_mat:=function(Q,Delta,s)

  // Compute the matrix G.

  d:=Degree(Q);
  Qx<x>:=RationalFunctionField(RationalField());
  Qxy<y>:=PolynomialRing(Qx);
  
  Delta:=Qx!Delta;
  Q:=Qxy!Q;
  s:=Qxy!s;

  list:=[];
  list[1]:=Qxy!0;
  for i:=2 to d do
    list[i]:=-(i-1)*y^(i-2)*(s/Delta)*ddx(Q);
  end for;
  for i:=1 to #list do
    list[i]:=reduce_mod_Q_exact(list[i],Q);
  end for;
  G:=ZeroMatrix(Qx,d,d);
  for i:=1 to d do
    for j:=1 to d do
      G[i,j]:=Coefficient(list[i],j-1); // G acts on the right on row vectors
    end for;
  end for;
  return(G);

end function;


jordan_inf:=function(Ginf)

  // Compute Jordan form of residue matrix at infinity

  res_Ginf:=-Evaluate((1/Parent(Ginf[1,1]).1)*Evaluate(Ginf,1/Parent(Ginf[1,1]).1),0);
  Jinf,Tinf:=JordanForm(res_Ginf);
  return Jinf,Tinf,Tinf^(-1);  
end function;


jordan_0:=function(r,G0)

  // Compute Jordan forms of residue matrices at finite points

  Qx<x>:=PolynomialRing(RationalField());
  r:=Qx!r;
  fac:=Factorization(r);
  J0:=[**];
  T0:=[**];
  T0inv:=[**];
  for i:=1 to #fac do
    if Degree(fac[i][1]) eq 1 then
      K:=RationalField();
      s:=-Evaluate(fac[i][1],0);
    else
      K<s>:=NumberField(fac[i][1]); 
    end if;
    res_G0:=Evaluate(G0*r/Derivative(r),s);
    J,T:=JordanForm(res_G0);
    J0:=Append(J0,J);
    T0:=Append(T0,T);
    T0inv:=Append(T0inv,T^(-1));
  end for;
  return J0,T0,T0inv;
end function;


ord_0:=function(f)

  // Compute ord_0(f), where f is a rational function.

  return Valuation(Numerator(f))-Valuation(Denominator(f));
end function;


ord_0_mat:=function(A)

  // Compute ord_0(A), where A is a matrix of rational functions.

  v:=ord_0(A[1,1]);
  for i:=1 to NumberOfRows(A) do
    for j:=1 to NumberOfColumns(A) do
      if ord_0(A[i,j]) lt v then
        v:=ord_0(A[i,j]);
      end if;
    end for;
  end for;
  return v;
end function;


ord_r:=function(f,r)

  // Compute ord_r(f), where f is a rational function

  if f eq 0 then
    return Infinity();
  end if;
  Qx<x>:=PolynomialRing(RationalField());
  r:=Qx!r;
  fac:=Factorization(r);
  vlist:=[];
  for i:=1 to #fac do
    v:=0;
    while (Numerator(f) mod fac[i][1] eq 0) do
      f:=f/fac[i][1];
      v:=v+1;
    end while;
    while (Denominator(f) mod fac[i][1] eq 0) do
      f:=f*fac[i][1];
      v:=v-1;
    end while;
    vlist:=Append(vlist,v);
  end for; 
  min:=Minimum(vlist);
  return min;
end function;


ord_r_mat:=function(A,r)

  // Compute ord_r(A), where A is matrix of rational functions

  v:=ord_r(A[1,1],r);
  for i:=1 to NumberOfRows(A) do
    for j:=1 to NumberOfColumns(A) do
      if ord_r(A[i,j],r) lt v then
        v:=ord_r(A[i,j],r);
      end if;
    end for;
  end for;
  return v;
end function;


ord_inf:=function(f)

  // Compute ord_inf(f), where f is a rational function.

  return -Degree(Numerator(f))+Degree(Denominator(f));
end function;


ord_inf_mat:=function(A);

  // Compute ord_inf(A), where A is a matrix of rational functions.

  v:=ord_inf(A[1,1]);
  for i:=1 to NumberOfRows(A) do
    for j:=1 to NumberOfColumns(A) do
      if ord_inf(A[i,j]) lt v then
        v:=ord_inf(A[i,j]);
      end if;
    end for;
  end for;
  return v;
end function;


res_0:=function(w,Q,r,J0,T0inv)

  // Compute res_0(\sum w_i b^0_i dx/r).

  d:=Degree(Q);
  Qx<x>:=PolynomialRing(RationalField());
  r:=Qx!r;
  fac:=Factorization(r);
  res_list:=[];
  for i:=1 to #fac do
    if Degree(fac[i][1]) eq 1 then
      s:=Parent(T0inv[i][1,1])!(-Coefficient(fac[i][1],0));
    else
      s:=Parent(T0inv[i][1,1]).1;
    end if;
    v:=Vector(Evaluate(w,s));
    v:=v*T0inv[i];
    for j:=1 to d do
      if J0[i][j,j] eq 0 then
        res_list:=res_list cat Eltseq(v[j]);
      end if;
    end for; 
  end for;  

  return Vector(res_list);

end function;


val_Qttinv_d:=function(v)

  // Compute the valuation of an element of Q[t,1/t]^d.  

  val:=Valuation(v[1]);
  for i:=2 to #Eltseq(v) do
    if Valuation(v[i]) lt val then
      val:=Valuation(v[i]);
    end if;
  end for;
  return val;
end function;


res_inf:=function(w,Q,r,W0,Winf,Ginf,Jinf,Tinfinv)

  // Compute res_inf(\sum w_i b^0_i dx/r).

  d:=Degree(Q);
  degr:=Degree(r);
  Qd:=RSpace(RationalField(),d);
  Qttinv<t>:=LaurentSeriesRing(RationalField());
  Qttinvd:=RSpace(Qttinv,d);
  
  W:=Winf*W0^(-1);
  Winv:=W^(-1);
  w:=Qttinvd!Evaluate(w,t^(-1));
  w:=w*Evaluate(Winv,t^(-1));

  res_Ginf:=-Evaluate((1/Parent(Winf[1,1]).1)*Evaluate(Ginf,1/Parent(Winf[1,1]).1),0);

  // reduce to a cohomologous 1-form that is logarithmic at all points lying over x=inf:

  while val_Qttinv_d(w) lt -degr+1 do
    m:=-val_Qttinv_d(w)-degr+1;
    mat:=res_Ginf-m*IdentityMatrix(RationalField(),d);
    rhs:=Qd!0;
    for i:=1 to d do
      rhs[i]:=rhs[i]+Coefficient(-w[i],-m-degr+1)/LeadingCoefficient(r);
    end for;
    vbar:=rhs*mat^(-1);
    w:=w-ChangeRing(vbar,Qttinv)*t^(-m)*Evaluate(r*Ginf,t^(-1))-Evaluate(r,1/t)*m*t^(1-m)*ChangeRing(vbar,Qttinv);  
  end while;

  // now sum w_i b^{inf}_i dx/r is logarithmic at all points lying over x=inf

  w:=w*t^(degr-1);
  v:=Qd!0;
  for i:=1 to d do
    v[i]:=Coefficient(w[i],0);
  end for;

  // project v onto the eigenspace of res_Ginf of eigenvalue 0 

  v:=v*Tinfinv;
  res_list:=[];
  for i:=1 to d do
    if Jinf[i,i] eq 0 then
      res_list:=Append(res_list,v[i]);
    end if;
  end for;

  return Vector(res_list);
end function;


basis_coho:=function(Q,p,r,W0,Winf,G0,Ginf,J0,Jinf,T0inv,Tinfinv,useU,basis0,basis1,basis2)
  
  // Compute a basis for H^1(X).

  Qx<x>:=PolynomialRing(RationalField());
  Qxy<y>:=PolynomialRing(Qx);
  d:=Degree(Q);
  Qxd:=RSpace(Qx,d);
  degr:=Degree(r);
 
  W:=Winf*W0^(-1);

  Winv:=W^(-1);
  ord0W:=ord_0_mat(W);
  ordinfW:=ord_inf_mat(W);
  ord0Winv:=ord_0_mat(Winv);
  ordinfWinv:=ord_inf_mat(Winv);

  // Compute a basis for E0

  deg_bound_E0:=degr-ord0W-ordinfW-2; 
  basisE0:=[];
  for i:=0 to d-1  do 
    for j:=0 to deg_bound_E0 do
      basisE0:=Append(basisE0,[i,j]);
    end for;
  end for;
  dimE0:=#basisE0;
  E0:=VectorSpace(RationalField(),dimE0);

  // Compute a matrix with kernel (E0 intersect Einf).

  matE0nEinf:=ZeroMatrix(RationalField(),dimE0,d*(-ordinfW-ordinfWinv));
  for i:=1 to dimE0 do
    temp:=RowSequence(x^(basisE0[i][2])*Winv)[basisE0[i][1]+1];
    for j:=0 to d-1 do
      for k:=0 to (-ordinfW-ordinfWinv-1) do
        matE0nEinf[i,j*(-ordinfW-ordinfWinv)+k+1]:=Coefficient(Numerator((Parent(W[1,1]).1)^(-ord0Winv)*temp[j+1]),k-ord0W-ord0Winv+degr-1);
      end for;
    end for;
  end for;  

  E0nEinf:=Kernel(matE0nEinf);

  // Compute a matrix with kernel the elements of E0 logarithmic at infinity.

  matlogforms:=ZeroMatrix(RationalField(),dimE0,d*(-ord0W-ordinfW-ordinfWinv-1));
  for i:=1 to dimE0 do
    temp:=RowSequence(x^(basisE0[i][2])*Winv)[basisE0[i][1]+1];
    for j:=0 to d-1 do
      for k:=0 to (-ord0W-ordinfW-ordinfWinv-2) do
        matlogforms[i,j*(-ord0W-ordinfW-ordinfWinv-1)+k+1]:=Coefficient(Numerator((Parent(W[1,1]).1)^(-ord0Winv)*temp[j+1]),k-ord0Winv+degr);
      end for;
    end for;
  end for;

  logforms:=E0nEinf meet Kernel(matlogforms);

  // Compute the finite residues.
  
  w:=Qxd!0;
  w[1]:=1;
  res0dim:=Dimension(Parent(res_0(w,Q,r,J0,T0inv)));
  matres0:=ZeroMatrix(RationalField(),dimE0,res0dim); 
  for i:=1 to dimE0 do
    w:=Qxd!0;
    w[basisE0[i][1]+1]:=x^(basisE0[i][2]);
    coefs:=res_0(w,Q,r,J0,T0inv); 
    for j:=1 to res0dim do
        matres0[i,j]:=coefs[j];
    end for;
  end for;

  // Compute the infinite residues. 

  w:=Qxd!0;
  w[1]:=1;
  resinfdim:=Dimension(Parent(res_inf(w,Q,r,W0,Winf,Ginf,Jinf,Tinfinv)));
  matresinf:=ZeroMatrix(RationalField(),dimE0,resinfdim); 
  for i:=1 to dimE0 do
    w:=Qxd!0;
    w[basisE0[i][1]+1]:=x^(basisE0[i][2]);
    coefs:=res_inf(w,Q,r,W0,Winf,Ginf,Jinf,Tinfinv); 
    for j:=1 to resinfdim do
        matresinf[i,j]:=coefs[j];
    end for;
  end for;

  forms2ndkind:=Kernel(matres0) meet Kernel(matresinf);
  cocyc:=E0nEinf meet forms2ndkind;
  forms1stkind:=logforms meet forms2ndkind;
  
  // Compute a matrix with kernel (B0 intersect Binf)

  deg_bound_B0:=-ord0W-ordinfW-1;
  basisB0:=[];
  for i:=0 to d-1  do 
    for j:=0 to deg_bound_B0 do
      basisB0:=Append(basisB0,[i,j]);
    end for;
  end for;
  dimB0:=#basisB0;
  B0:=VectorSpace(RationalField(),dimB0);

  matB0nBinf:=ZeroMatrix(RationalField(),dimB0,d*(-ordinfW-ordinfWinv));
  for i:=1 to dimB0 do
    power_x:=basisB0[i][2];
    power_y:=basisB0[i][1];
    temp:=RowSequence(x^(power_x)*Winv)[power_y+1];
    for j:=0 to d-1 do
      for k:=0 to (-ordinfW-ordinfWinv-1) do
        matB0nBinf[i,j*(-ordinfW-ordinfWinv)+k+1]:=Coefficient(Numerator((Parent(W[1,1]).1)^(-ord0Winv)*temp[j+1]),k-ord0W-ord0Winv);
      end for;
    end for;
  end for;

  // Compute d(B0 intersect Binf).

  B0nBinf:=Kernel(matB0nBinf);
  basisB0nBinf:=Basis(B0nBinf);
  dimB0nBinf:=#basisB0nBinf;  

  list:=[];
  for i:=1 to dimB0nBinf do
    vec:=basisB0nBinf[i];
    vecQxd:=Qxd!0;
    for j:=1 to dimB0 do
      vecQxd[basisB0[j][1]+1]:=vecQxd[basisB0[j][1]+1]+vec[j]*x^(basisB0[j][2]);
    end for;
    vecQxd:=vecQxd*ChangeRing(r*G0,Qx)+r*ddx_vec(vecQxd);
    coefs:=[];
    for j:=1 to dimE0 do
      power_x:=basisE0[j][2];
      power_y:=basisE0[j][1];
      coefs[j]:=Coefficient(vecQxd[power_y+1],power_x);  
    end for;
    list:=Append(list,E0!coefs);
  end for;
  matd:=Matrix(list);

  // Compute bases

  cobound:=sub<cocyc|list>;

  if basis0 eq [] then
    b0:=Basis(forms1stkind);
  else
    b0:=[];
    for i:=1 to #basis0 do
      b0[i]:=polys_to_vec(basis0[i],deg_bound_E0);
    end for;
  end if;  

  b5:=[];
  for i:=2 to dimB0nBinf do
    b5:=Append(b5,E0!list[i]);
  end for;
  
  dualspace:=Complement(cocyc,forms1stkind+cobound); // Take the dual w.r.t. cup product? Right now just any complement of forms of the 1st kind in H^1(X).
  if basis1 eq [] then
    b1:=Basis(dualspace);
  else
    b1:=[];
    for i:=1 to #basis1 do
      b1[i]:=polys_to_vec(basis1[i],deg_bound_E0);
    end for;
  end if;  

  basisH1X:=b0 cat b1;
  dimH1X:=#basisH1X;

  finiteregularlogarithmic:=logforms meet Kernel(matres0); // 1-forms that generate H^1(Y) over H^1(X), where Y=X-x^{-1}(\infty)
  H1YmodH1X:=Complement(finiteregularlogarithmic,forms1stkind);

  if basis2 eq [] then
    b2:=Basis(H1YmodH1X);
  else
    b2:=[];
    for i:=1 to #basis2 do
      b2[i]:=polys_to_vec(basis2[i],deg_bound_E0);
    end for;
  end if;

  b3:=Basis(Complement(E0nEinf,cocyc+H1YmodH1X));

  b4:=Basis(Complement(E0,E0nEinf));  
  
  b:=b0 cat b1 cat b2 cat b3 cat b4 cat b5;

  dimH1U:=#b0+#b1+#b2+#b3;

  if useU then
    dim:=dimH1U;
  else
    dim:=dimH1X;
  end if;

  for i:=1 to dim do
    valdenom:=0;
    for j:=1 to dimE0 do
      valdenom:=Minimum(valdenom,Valuation(b[i][j],p));
    end for;
    b[i]:=p^(-valdenom)*b[i];
  end for; 

  matb:=Matrix(b);
  quo_map:=matb^(-1);

  integrals:=[Qxd|];
  for i:=2 to dimB0nBinf do
    vec:=Qxd!0;
    for j:=1 to dimB0 do
      vec[basisB0[j][1]+1]:=vec[basisB0[j][1]+1]+(basisB0nBinf[i][j])*x^(basisB0[j][2]);
    end for;
    integrals:=Append(integrals,LeadingCoefficient(r)*vec); // factor lc(r) here, since working with dx/z basis instead of dx/r
  end for;

  Qxd:=RSpace(Qx,d);
  basis:=[Qxd|];
  
  for i:=1 to dim do
    vec:=Qxd!0;
    for j:=1 to dimE0 do
      vec[basisE0[j][1]+1]:=vec[basisE0[j][1]+1]+(RationalField()!(b[i][j]))*(Qx.1)^(basisE0[j][2]);
    end for;
    basis:=Append(basis,vec);
  end for;

  return basis,integrals,quo_map;
    
end function;
