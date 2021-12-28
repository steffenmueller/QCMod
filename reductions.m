reduce_mod_pN_Q:=function(f,p,N);

  // Reduce a rational number f mod p^N.

  if f ne 0 then
    ord:=Valuation(f,p);
    if ord ge N then
      f:=0;
    else
      m:=p^(N-ord);
      Zmodm:=IntegerRing(m);
      unit:=f/(p^ord);
      f:=IntegerRing()!((Zmodm!Numerator(unit))/(Zmodm!Denominator(unit)));
      if 2*f ge m then
        f:=f-m;
      end if;
      f:=p^ord*(RationalField()!f);
    end if;
  end if;
  return f;
end function;


reduce_mod_pN_Qx:=function(f,p,N);

  // Reduce a polynomial f over the rationals mod p^N.
  
  if f eq 0 then
    return f;
  else
    Qx:=Parent(f);
    denom:=LCM([Denominator(coef): coef in Coefficients(f)]);
    f:=f*denom;

    ord,unit:=Valuation(denom,p); 
    m:=p^(N+ord);
    ppow:=p^(ord);

    Zmodm:=IntegerRing(m);
    unitinv:=(Zmodm!unit)^-1;
    Zmodmx:=PolynomialRing(Zmodm);

    f:=Qx!PolynomialRing(IntegerRing())!(unitinv*(Zmodmx!f));
    return f/ppow;
  end if;
end function;


reduce_mod_pN_Q_mat:=function(A,p,N)

  // Reduce a matrix over the rationals mod p^N

  if A eq 0 then
    return A;
  else
    denom:=LCM([Denominator(elt): elt in Eltseq(A)]);
    A:=A*denom; 
    
    ord,unit:=Valuation(denom,p); 
    m:=p^(N+ord);
    ppow:=p^(ord);

    Zmodm:=IntegerRing(m);
    unitinv:=(Zmodm!unit)^-1;

    A:=ChangeRing(A,IntegerRing());
    A:=ChangeRing(A,Zmodm);
    A:=unitinv*A;;
    A:=ChangeRing(A,IntegerRing());
    A:=ChangeRing(A,RationalField());
    
    return A/ppow;
  end if;
end function;


reduce_mod_pN_Qi:=function(f,p,N);

  // Reduce an element of Qi mod p^N

  if f eq 0 then
    return f;
  else
    Qi:=Parent(f);
    denom:=Denominator(f);
    f:=f*denom;
    
    ord,unit:=Valuation(denom,p); 
    m:=p^(N+ord);
    ppow:=p^(ord);

    Zmodm:=IntegerRing(m);
    unitinv:=(Zmodm!unit)^-1;

    C:=Eltseq(f);
    C:=ChangeUniverse(C,Zmodm);
    C:=[unitinv*elt : elt in C];
    C:=ChangeUniverse(C,IntegerRing());
    C:=ChangeUniverse(C,RationalField());

    return (Qi!C)/ppow;   
  end if;
end function;


reduce_mod_pN_Qi_mat:=function(A,p,N)

  // Reduce a matrix over a numberfield Qi mod p^N

  if A eq 0 then
    return A;
  else
    Qi:=Parent(A[1,1]);
    denom:=LCM([Denominator(elt): elt in Eltseq(A)]);
    A:=A*denom;
    
    ord,unit:=Valuation(denom,p); 
    m:=p^(N+ord);
    ppow:=p^(ord);

    Zmodm:=IntegerRing(m);
    unitinv:=(Zmodm!unit)^-1;  

    C:=Eltseq(A);
    C:=&cat[Eltseq(elt):elt in C];
    C:=ChangeUniverse(C,Zmodm);
    C:=[unitinv*elt : elt in C];
    C:=ChangeUniverse(C,IntegerRing());
    C:=ChangeUniverse(C,RationalField());
    C:=Partition(C,Degree(Qi));
    C:=[Qi!elt:elt in C];
    C:=Partition(C,NumberOfColumns(A));
    A:=Matrix(C);

    return A/ppow;
  end if;
end function;


reduce_mod_pN_Qttinv:=function(f,p,N); 

  // Reduce an element of Q[t,t^{-1}] mod p^N.

  Qttinv:=Parent(f);

  if f eq 0 then
    return f;
  else
    denom:=LCM([Denominator(coef): coef in Coefficients(f)]);
    f:=f*denom;

    ord,unit:=Valuation(denom,p); 
    m:=p^(N+ord);
    ppow:=p^(ord);

    Zmodm:=IntegerRing(m);
    unitinv:=(Zmodm!unit)^-1;
  
    val:=Valuation(f);
    C:=Coefficients(f);
    C:=ChangeUniverse(C,IntegerRing());
    C:=ChangeUniverse(C,Zmodm);
    C:=Coefficients(unitinv*Polynomial(C));
    C:=ChangeUniverse(C,IntegerRing());
    C:=ChangeUniverse(C,RationalField());
   
  end if;
  return (Qttinv.1)^val*(Qttinv!C)/ppow;
end function;


inv_Qi:=function(f,p,N);

  // Invert an element of Qi mod p^N

  Qi:=Parent(f);
  ri:=DefiningPolynomial(Qi);

  C:=Eltseq(f);  
  valset:=[];
  for i:=1 to #C do
    if C[i] ne 0 then
      valset:=Append(valset,Valuation(C[i],p));
    end if;
  end for; 
  val:=Minimum(valset);
  
  N:=N+val;
  f:=f/p^(val);
  
  Fp:=FiniteField(p);
  Fpx:=PolynomialRing(Fp);
  
  rimodp:=Fpx!0;
  C:=Coefficients(ri);
  for i:=1 to #C do
    rimodp:=rimodp+(Fp!C[i])*(Fpx.1)^(i-1);
  end for;
  
  Fpxmodri:=quo<Fpx|rimodp>;
  fmodp:=Fpxmodri!0;
  C:=Eltseq(f);
  for i:=1 to #C do 
    fmodp:=fmodp+(Fp!C[i])*(Fpxmodri.1)^(i-1);
  end for;

  invmodp:=1/fmodp;

  inv:=Qi!0;
  C:=Coefficients(invmodp);
  for i:=1 to #C do
    inv:=inv+(IntegerRing()!C[i])*(Qi.1)^(i-1);
  end for;
  
  prec:=[];
  while N gt 1 do
    prec:=Append(prec,N);
    N:=Ceiling(N/2);
  end while;
  prec:=Reverse(prec);
  
  for i:=1 to #prec do
    inv:=reduce_mod_pN_Qi(inv*(2-inv*f),p,prec[i]);
  end for; 
  
  return inv/(p^(val));

end function;


push_to_Qi_mat:=function(A,Qi)

  // Push a matrix to Qi 

  row:=NumberOfRows(A);
  col:=NumberOfColumns(A);
  B:=ZeroMatrix(Qi,row,col);

  for i:=1 to row do
    for j:=1 to col do
      B[i,j]:=Qi!Eltseq(A[i,j]);
    end for;
  end for;

  return B;

end function;


red_lists:=function(Q,p,N,r,W0,Winf,G0,Ginf,e0,einf,J0,Jinf,T0,Tinf,T0inv,Tinfinv) 

  // Precompute the finite and infinite reduction matrices, that will be used in
  // the cohomological reductions (coho_red_fin and coho_red_inf)

  d:=Degree(Q);
  W:=Winf*W0^(-1);

  rQ:=Qx!r;
  fac:=Factorisation(rQ);
  lc_rQ:=LeadingCoefficient(rQ);
  rQ:=Numerator(rQ/lc_rQ);
  
  // Finite reduction matrices

  N0:=Floor(log(p,p*e0*(N-1)));
  Nw:=N+N0; // working precision, check
  
  riseq:=[];
  redlistfinfac:=[**];
  for i:=1 to #fac do

    redlistfinQi:=[];
    
    ri:=Qx!(fac[i][1]);
    ri:=reduce_mod_pN_Qx(ri,p,Nw); 
    riseq:=Append(riseq,ri);
    if Degree(ri) gt 1 then
      Qi:=ext<RationalField()|ri>; // redefining Qi, same mod p^Nw  
      s:=Qi.1;
    else
      Qi:=RationalField();
      s:=-Evaluate(ri,0); 
    end if;
    
    D:=push_to_Qi_mat(J0[i],Qi);
    P:=reduce_mod_pN_Qi_mat(push_to_Qi_mat(T0[i],Qi),p,Nw);
    Pinv:=reduce_mod_pN_Qi_mat(push_to_Qi_mat(T0inv[i],Qi),p,Nw);

    denom:=reduce_mod_pN_Qi(Evaluate(Derivative(rQ),s),p,Nw);
    denominv:=inv_Qi(denom,p,Nw); 

    for l:=1 to p*(N-1) do
      D:=D-IdentityMatrix(Qi,d);  
      mat:=Pinv*D^(-1)*P;
      mat:=reduce_mod_pN_Qi_mat(mat,p,Nw);
      mat:=denominv*mat;
      mat:=reduce_mod_pN_Qi_mat(mat,p,Nw);
      redlistfinQi:=Append(redlistfinQi,mat);
    end for;
    redlistfinfac:=Append(redlistfinfac,redlistfinQi);
  end for;

  rQ0:=reduce_mod_pN_Qx(rQ,p,Nw);

  L:=[];
  for i:=1 to #J0 do
    fiseq:=[];
    for k:=1 to #J0 do
      if k eq i then
        fiseq[k]:=Qx!1;
      else
        fiseq[k]:=Qx!0;
      end if;   
    end for;
    L:=Append(L,reduce_mod_pN_Qx(ChineseRemainderTheorem(fiseq,riseq),p,Nw));
  end for;

  redlistfin:=[];
  for l:=1 to p*(N-1) do
    mat:=ZeroMatrix(Qx,d,d);
    for i:=1 to d do
      for j:=1 to d do
        entry:=Qx!0;
        for k:=1 to #J0 do
          entry:=entry+((Qx!Eltseq(redlistfinfac[k][l][i,j]))*L[k] mod rQ0);
        end for;
        mat[i,j]:=reduce_mod_pN_Qx(entry,p,Nw);
      end for;
    end for;
    redlistfin:=Append(redlistfin,mat);
  end for;

  // Infinite reduction matrices

  Ninf:=Floor(log(p,-(ord_inf_mat(W^(-1))+1)*einf));
  Nw:=N+(N0+Ninf); // working precision check

  D:=reduce_mod_pN_Q_mat(Jinf,p,Nw);
  P:=reduce_mod_pN_Q_mat(Tinf,p,Nw);
  Pinv:=reduce_mod_pN_Q_mat(Tinfinv,p,Nw);
  redlistinf:=[];
  //"ord_0_mat(W)", ord_0_mat(W); "ord_inf_mat(W)",ord_inf_mat(W); "ord_inf_mat(W^(-1))",ord_inf_mat(W^(-1)); "(-p*(ord_0_mat(W)+ord_inf_mat(W)+1)-ord_inf_mat(W^(-1)))", (-p*(ord_0_mat(W)+ord_inf_mat(W)+1)-ord_inf_mat(W^(-1)));
  for m:=1 to  (-p*(ord_0_mat(W)+ord_inf_mat(W)+1)-ord_inf_mat(W^(-1)))+100 do // 20/04/20 added 100 for fun
    D:=D-IdentityMatrix(RationalField(),d);
    mat:=Pinv*D^(-1)*P;
    mat:=reduce_mod_pN_Q_mat(mat,p,Nw);
    redlistinf:=Append(redlistinf,mat);
  end for;

  return redlistfin,redlistinf;

end function;


convert_to_Qxzzinvd:=function(w,Q); 

  // Converts an element of S^d to one of (Q[x][z,z^{-1}])^d 

  d:=Degree(Q);
  Z:=IntegerRing();
  Qxz<z>:=LaurentSeriesRing(Qx);
  C:=[];
  for i:=1 to d do
    D,val:=Coefficients(w[i]);
    E:=[];
    for j:=1 to #D do
      E[j]:=(Qx!PolynomialRing(IntegerRing())!D[j]);  
    end for;
    C[i]:=z^(-1)*(Qxz.1)^(val+1)*(Qxz!E); 
  end for;
  
  return C;
end function;


val_Qxz_d:=function(v)

  // Compute the valuation of an element of (Q[x][z,z^{-1}])^d.  

  val:=Valuation(v[1]);
  for i:=2 to #Eltseq(v) do
    if Valuation(v[i]) lt val then
      val:=Valuation(v[i]);
    end if;
  end for;
  return val;
end function;


coho_red_fin:=function(w,Q,p,N,r,G0,red_list_fin); 

  // Reduce the 1-form w dx/z w.r.t. the basis [b^0_0,..,b^0_{d-1}] in cohomology 
  // until it has logaritmic poles at all points lying over the zeros of r.

  Qxz<z>:=LaurentSeriesRing(Qx);
  
  d:=Degree(Q);
  V:=RSpace(Qx,d);
  Qxzd:=RSpace(Qxz,d);

  M:=r*G0;

  r:=Qx!r;
  lc_r:=LeadingCoefficient(r);
  r:=Numerator(r/lc_r);
  
  f0:=Qxzd!0;

  r:=reduce_mod_pN_Qx(r,p,N); 
  for i:=1 to NumberOfRows(M) do 
    for j:=1 to NumberOfColumns(M) do 
      M[i,j]:=Parent(M[i,j])!reduce_mod_pN_Qx(Numerator(M[i,j]),p,N); 
    end for; 
  end for; 

  zero:=true;
  for i:=1 to d do
    if w[i] ne 0 then
      zero:=false;
    end if;
  end for;

  if zero then
    return w,f0;
  end if;

  l0:=-val_Qxz_d(w);
  if l0 le 0 then
    return w,f0;
  end if;

  wcoefs:=[];
  for i:=1 to d do
    vec:=[Qx|];
    for j:=-l0 to 0 do
      vec[j+l0+1]:=Coefficient(w[i],j);  
    end for;
    wcoefs:=Append(wcoefs,vec);
  end for;

  l:=l0;
  while l gt 0 do
    wvec:=V!0;
    for i:=1 to d do
      wvec[i]:=wcoefs[i][-l+l0+1];
    end for;
    red_mat:=red_list_fin[l];
    vvec:=wvec*red_mat;
    for i:=1 to d do
      vvec[i]:=vvec[i] mod r;
    end for;
    for i:=1 to d do
      f0[i]:=f0[i]+(Qxz!reduce_mod_pN_Qx(vvec[i],p,N))*z^(-l);
    end for;
    mat:=ZeroMatrix(Qx,d,d);
    for i:=1 to d do
      for j:=1 to d do
        mat[i,j]:=(Qx!Numerator(M[i,j]));
      end for;
    end for;
    mat:=mat/lc_r;
    for i:=1 to d do
      mat[i,i]:=mat[i,i]-l*(Qx!Coefficients(Derivative(r)));
    end for;
    uvec:=wvec-vvec*mat; 
    for i:=1 to d do
      uvec[i]:=reduce_mod_pN_Qx((uvec[i] div r)-Derivative(vvec[i]),p,N);
    end for; 
    for i:=1 to d do
      wcoefs[i][-l+l0+1]:=wcoefs[i][-l+l0+1]-wvec[i];
      wcoefs[i][-l+l0+2]:=wcoefs[i][-l+l0+2]+uvec[i]; 
    end for;
    l:=l-1;
  end while;
  
  for i:=1 to d do 
    C:=[];   
    C[1]:=wcoefs[i][l0+1];   
    if w[i] ne 0 then
      for j:=1 to Degree(w[i]) do
        C[j+1]:=Coefficient(w[i],j);  
      end for;
    end if; 
    w[i]:=(Qxz!C);
  end for;

  return w,f0;
end function;


eval_pN:=function(f,g,p,N);  

  // Evaluate f at g mod p^N.

  if f eq 0 then
    return CoefficientRing(Parent(f))!0;
  end if;

  k:=Ceiling((Degree(f)+1)/4);
  h:=[];
  for i:=0 to k-1 do
    h[i+1]:=CoefficientRing(Parent(f))!Coefficient(f,4*i+3);
    for j:=1 to 3 do
      h[i+1]:=h[i+1]*g+Coefficient(f,4*i+3-j);
    end for;
  end for;
  h[k+1]:=0;

  gpow:=reduce_mod_pN_Qx(g^4,p,N);

  while k gt 1 do
    h_old:=h;
    h:=[];
    k:=Ceiling(k/2);
    for i:=0 to k-1 do
      h[i+1]:=reduce_mod_pN_Qx(h_old[2*i+1]+h_old[2*i+2]*gpow,p,N);  
    end for;
    h[k+1]:=0;
    if k gt 1 then
      gpow:=reduce_mod_pN_Qx(gpow^2,p,N);  
    end if;
  end while;
 
  return h[1];
end function;


change_basis_b0binf:=function(w,p,N,r,W0,Winf);

  // Change basis from [b^0_0,..b^0_(d-1)] to [b^{inf}_0,..,b^{inf}_{d-1}].

  d:=NumberOfRows(Winf);
  
  r:=Qx!r;
  lc_r:=LeadingCoefficient(r);
  r:=Numerator(r/lc_r); 

  Qttinv<t>:=LaurentSeriesRing(RationalField());
  Qttinvd:=RSpace(Qttinv,d);
  
  W:=Winf*W0^(-1);
  Winv:=W^(-1);
  wnew:=Qttinvd!0;
  for i:=1 to d do
    temp:=eval_pN(w[i],r,p,N);
    if temp eq 0 then
      wnew[i]:=Qttinv!0;
    else
      wnew[i]:=t^(-Degree(temp))*(Qttinv!Reverse(Coefficients(temp)));
    end if;
  end for;
  w:=wnew*Evaluate(Winv,t^(-1));

  return w;
end function;


coho_red_inf:=function(w,Q,p,N,r,W0,Winf,Ginf,red_list_inf);

  // Reduce the 1-form w dx/z w.r.t. the basis [b^{inf}_0,..,b^{inf}_{d-1}] in cohomology,
  // lowering the pole order at the points lying over the point at infinity.

  d:=Degree(Q);
  degr:=Degree(r);

  Qttinv<t>:=LaurentSeriesRing(RationalField());
  Qttinvd:=RSpace(Qttinv,d);
  Qd:=RSpace(RationalField(),d);
  Qxxinv<x>:=LaurentSeriesRing(RationalField());
  Qxxinvd:=RSpace(Qxxinv,d);
  
  finf:=Qxxinvd!0;

  zero:=true;
  for i:=1 to d do
    if w[i] ne 0 then
      zero:=false;
    end if;
  end for;

  if zero then
    return w,finf;
  end if;

  Minf:=r*Ginf;
  
  W:=Winf*W0^(-1);  
  ord0W:=ord_0_mat(W);

  r:=Qx!r;
  lc_r:=LeadingCoefficient(r);
  r:=Numerator(r/lc_r);
  Minf:=Minf/lc_r;

  Minftinv:=Evaluate(Minf,t^(-1));
  rtinv:=Evaluate(r,1/t);

  rtinv:=reduce_mod_pN_Qttinv(rtinv,p,N); 
  for i:=1 to NumberOfRows(Minftinv) do 
    for j:=1 to NumberOfColumns(Minftinv) do 
      Minftinv[i,j]:=reduce_mod_pN_Qttinv(Minftinv[i,j],p,N); 
    end for; 
  end for; 

  vallist:=[];
  deglist:=[0];
  for i:=1 to d do
    if w[i] ne 0 then
      vallist:=Append(vallist,Valuation(w[i]));
      deglist:=Append(deglist,Degree(w[i]));
    end if;
  end for;

  valw:=Minimum(vallist);
  degw:=Maximum(deglist);
   
  wcoefs:=[];
  for i:=1 to d do
    vec:=[RationalField()|];
    for j:=valw to degw do
      vec[j-valw+1]:=Coefficient(w[i],j);  
    end for;
    wcoefs:=Append(wcoefs,vec);
  end for;

  m0:=-valw-degr+1;
//  "valw", valw; "degr", degr; "m0", m0; "ord0W", ord0W; "m0+ord0W+1",   m0+ord0W+1; "#red_list_inf ", #red_list_inf ;
  
  m:=m0;

  while m gt -(ord0W+1) do
    wvec:=Qd!0;
    for i:=1 to d do
      wvec[i]:=-wcoefs[i][-m+m0+1];
    end for;
    red_mat:=red_list_inf[m];
    vvec:=wvec*red_mat;
    for i:=1 to d do
      finf[i]:=finf[i]+reduce_mod_pN_Q(vvec[i],p,N)*x^(m);
    end for;
    dif:=((Qttinvd!vvec)*t^(-m)*Minftinv)+rtinv*m*t^(1-m)*(Qttinvd!vvec);
    for i:=1 to d do
      difmodpN:=reduce_mod_pN_Qttinv(dif[i],p,N);
      C,val:=Coefficients(difmodpN);
      for j:=1 to #C do                           
        wcoefs[i][j+val-1+m0+degr]:=wcoefs[i][j+val-1+m0+degr]-C[j];  
      end for;
      wcoefs[i][-m+m0+1]:=0;
    end for;
    m:=m-1;
  end while;

  for i:=1 to d do
    w[i]:=reduce_mod_pN_Qttinv(t^(-m0-degr+1)*(Qttinv!wcoefs[i]),p,N);
  end for;  

  return w,finf,m0;
end function;


change_basis_binfb0:=function(w,W0,Winf);

  // Change basis from [b^{inf}_0,..,b^{inf}_{d-1}] to [b^0_0,..b^0_(d-1)].

  t:=Parent(w[1]).1;
  
  W:=Winf*W0^(-1);
  w:=w*Evaluate(W,t^(-1));
  w:=Evaluate(w,t^(-1));
  for i:=1 to NumberOfColumns(w) do
    temp:=w[1,i];
    if temp ne 0 then
      for j:=Valuation(temp) to -1 do
        temp:=temp-Coefficient(temp,j)*t^j;
      end for;
    end if;
    w[1,i]:=temp;
  end for;
  w:=Evaluate(w,Qx.1);
  return w;
end function;


reduce_with_fs:=function(dif,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map)

    // Reduces the differential dif (given w.r.t. the basis b^0 dx/z) in H^1(U).
    // 
    // returns:
    // --------
    // coefs    : the coefficients of the cohomology class (w.r.t. the given basis of H^1(U))
    // f0,finf,f: the three functions one has to substract the d of, to get from dif to its 
    //            reduction (w.r.t. b^0,b^inf,b^0)

    d:=Degree(Q); 
    degr:=Degree(r);

    dif0:=dif;

    dif,f0:=coho_red_fin(dif,Q,p,Nmax,r,G0,red_list_fin); 
    dif:=change_basis_b0binf(dif,p,Nmax,r,W0,Winf);
    dif,finf,minf:=coho_red_inf(dif,Q,p,Nmax,r,W0,Winf,Ginf,red_list_inf); 
    // minf is the bound on precision loss during reduction above 
    dif:=change_basis_binfb0(dif,W0,Winf);

    W:=Winf*W0^(-1);
    ord0W:=ord_0_mat(W);
    ordinfW:=ord_inf_mat(W);

    T:=[];
    for k:=1 to d do
      for j:=0 to degr-ord0W-ordinfW-2 do
        T:=Append(T,Coefficient(dif[1,k],j));
      end for;
    end for;

    v:=Vector(T)*quo_map;

    coefs:=[];
    for j:=1 to #basis do
      coefs[j]:=reduce_mod_pN_Q(v[j],p,N);
    end for;

    fend:=Parent(integrals[1])!0;
    for j:=1 to #integrals do
      fend:=fend+reduce_mod_pN_Q(v[NumberOfColumns(quo_map)-#integrals+j],p,Nmax)*integrals[j];
    end for;

    // Optional test:

    // test_reduce_with_fs(Vector(dif0),Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map,coefs,f0,finf,f); 

    return coefs,f0,finf,fend,minf; 

end function;
