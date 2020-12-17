getrings:=function(p,N)

  // Construct rings mod p^N.

  O:=IntegerRing(p^N);
  Ox<x>:=PolynomialRing(O);
  S<z>:=LaurentSeriesRing(Ox); // z=r
  R<y>:=PolynomialRing(S);
  return O,Ox,S,R;
end function;


radix_reduce:=function(f,r); 

  // Eliminate powers of x >= deg(r) in f.
  
  C:=Coefficients(f);
  for i:=1 to #C do
    if C[i] ne 0 then
      v:=Valuation(C[i]);
      D:=Coefficients(C[i]);
      j:=1;
      while j le #D do 
        if Degree(D[j]) ge Degree(r) then
          a,b:=Quotrem(D[j],BaseRing(BaseRing(Parent(f)))!r); 
          D[j]:= b;
          if #D lt j+1 then
            D[j+1]:=a;
          else
            D[j+1]:=D[j+1]+a;
          end if;      
        end if;
        j:=j+1;
      end while;
      C[i]:=(BaseRing(Parent(f)).1)^v*(BaseRing(Parent(f))!D);
    end if;  
  end for;
  return Parent(f)!C; 
end function;


reduce_mod_Q:=function(f,Q,r); 

  // Eliminate powers of y >= deg(Q) in f.
  
  f:=radix_reduce(f,r);
  Q:=radix_reduce(Q,r);

  while Degree(f) ge Degree(Q) do
    f:=f-Coefficient(f,Degree(f))*(Parent(f).1)^(Degree(f)-Degree(Q))*(Parent(f)!Q);
    f:=radix_reduce(f,r);
  end while;
  // f:=radix_reduce(f,r); // possibly move back into the loop
  
  return f;  
end function;


xpforx:=function(f,xp,r) 

  // Substitute x^p for x in an element of R (without any z).

  // 1) Determine the degree degxf of f in x.
  
  C:=Coefficients(f);
  degxf:=0;
  for i:=1 to #C do
    if (C[i] ne 0) and (Degree(Coefficient(C[i],0)) gt degxf) then
      degxf:=Degree(Coefficient(C[i],0));
    end if;
  end for;

  // 2) Compute the radix_reduction of (x^p)^k for k up to degxf.

  xppow:=[];
  xppow[1]:=Parent(f)!1;
  xppow[2]:=xp;
  for i:=2 to degxf do
    xppow:=Append(xppow,radix_reduce(xppow[i]*xp,r));
  end for;

  // 3) Substitute x^p into f(-,y).

  out:=Parent(f)!0;
  for i:=1 to #C do
    D:=Coefficients(Coefficient(C[i],0));
    for j:=1 to #D do
      out:=out+D[j]*xppow[j]*(Parent(f).1)^(i-1);
    end for;
  end for;

  return out;
end function;


pow:=function(f,n,Q,r);

  // Computes f^n for an element f in R

  if n eq 0 then
    return Parent(f)!1;
  end if;

  digits:=Intseq(n,2);
  f2i:=f;
  
  if digits[1] eq 1 then 
    fpow:=f;
  else
    fpow:=Parent(f)!1;
  end if;

  for i:=2 to #digits do
    f2i:=reduce_mod_Q(f2i*f2i,Q,r);
    if digits[i] eq 1 then
      fpow:=reduce_mod_Q(fpow*f2i,Q,r);
    end if;
  end for;

  return fpow;
  
end function;


froblift:=function(Q,p,N,r,Delta,s,W0);

  // 1) Compute matrix of F_p on R w.r.t. basis [y^i]

  O,Ox,S,R:=getrings(p,N);
  x:=Ox.1; y:=R.1; z:=S.1;

  d:=Degree(Q);

  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  rQx:=Parent(Numerator(W0[1,1]))!r;
  rQx:=rQx/LeadingCoefficient(rQx);

  r:=(Ox!Coefficients(r));
  Delta:=(Ox!Coefficients(Delta));

  C:=[];
  for i:=1 to Degree(s)+1 do
    C[i]:=Ox!(Coefficient(s,i-1));
  end for;
  s:=(R!C);
  lc:=LeadingCoefficient(r);
  r:=r/lc;
  s:=s/lc;
  Delta:=Delta/lc; 

  cnt:=1;
  while (r^cnt mod Delta ne 0) do
    cnt:=cnt+1;
  end while;
  g:=r^cnt div Delta;

  prec:=[];
  k:=N;
  while k gt 1 do
    prec:=Append(prec,k);
    k:=Ceiling(k/2);
  end while;
  prec:=Reverse(prec);

  alpha:=R!(z^(-p));
  beta:=pow(y,p,Q,r);
  xp:=pow(R!x,p,Q,r);	

  for i:=1 to #prec do
    Oi,Oxi,Si,Ri:=getrings(p,prec[i]);
    xpi:=Ri!xp;				
    rxp:=xpforx(Ri!(Oxi!r),xpi,r);
    alpha:=(Ri!alpha); 							
    alpha:=radix_reduce(alpha*radix_reduce(2-alpha*rxp,r),r); // alpha=F_p(1/r)

    alpha_power:=alpha;
    for j:=2 to cnt do
      alpha_power:=radix_reduce(alpha_power*alpha,r);
    end for; 
    gxp:=xpforx(Ri!(Oxi!g),xpi,r);
    alpha1:=radix_reduce(gxp*alpha_power,r); // alpha1=F_p(1/Delta)
	
    powers:=[];
    powers[1]:=Ri!1;
    for j:=2 to d+1 do
      powers[j]:=reduce_mod_Q((Ri!beta)*powers[j-1],Q,r);
    end for;

    Qxp:=xpforx(Ri!Q,xpi,r); 								
    sxp:=xpforx(Ri!s,xpi,r); 								
    evalQxp:=Ri!0;
    for j:=0 to d do
      evalQxp:=evalQxp+Coefficient(Qxp,j)*powers[j+1];
    end for;
    evalQxp:=radix_reduce(evalQxp,r);
    evalsxp:=Ri!0;
    for j:=0 to Degree(s) do
      evalsxp:=evalsxp+Coefficient(sxp,j)*powers[j+1];
    end for;
    evalsxp:=radix_reduce(evalsxp,r);

    beta:=(Ri!beta);
    beta:=radix_reduce(beta-reduce_mod_Q(radix_reduce(evalQxp*evalsxp,r),Q,r)*(Ri!alpha1),r);

  end for;

  // (slow) optional tests:
  // ----------------------
  //radix_reduce(alpha*xpforx(R!(Ox!r),xp,r),r) eq 1;          
  //radix_reduce(alpha1*xpforx(R!(Ox!Delta),xp,r),r) eq 1;     
  //reduce_mod_Q(Evaluate(xpforx(R!Q,xp,r),beta),R!Q,r) eq 0;  

  alpha:=(R!alpha);
  beta:=(R!beta);

  // 2) Compute matrix of F_p on R w.r.t. basis [y^i/r]
  
  mat:=ZeroMatrix(S,d,d); 
  Fpyir:=z*(alpha);        		 // r*F_p(y^0/r)
  for i:=1 to d do
    mat[1,i]:=Coefficient(Fpyir,i-1);
  end for;
  for i:=2 to d do
    Fpyir:=reduce_mod_Q(beta*Fpyir,Q,r); // r*F_p(y^(j+1)/r) = F_p(y)*(r*F_p(y^j/r))
    for j:=1 to d do
      mat[i,j]:=Coefficient(Fpyir,j-1);
    end for;
  end for;

  // 3) Compute the matrix of F_p on R w.r.t. basis [b^0_i/r] (i.e. Fp(W0)*mat*W0^(-1))

  W0inv:=W0^(-1);
  ordrW0inv:=ord_r_mat(W0inv,rQx);
  W0invS:=ZeroMatrix(S,d,d);
  for i:=1 to d do
    for j:=1 to d do
      W0invS[i,j]:=Coefficient(radix_reduce(R!(z^(ordrW0inv)*(Ox!Numerator((Parent(W0[1,1])!rQx)^(-ordrW0inv)*W0inv[i,j]))),r),0); // Compute S!W0^(-1)
    end for;
  end for;

  mat:=mat*W0invS; // Compute mat*W0^(-1)
  for i:=1 to d do
    for j:=1 to d do
      mat[i,j]:=Coefficient(radix_reduce(R!mat[i,j],r),0); 
    end for;
  end for;

  ordrW0:=ord_r_mat(W0,rQx);
  FpW0S:=ZeroMatrix(S,d,d);
  for i:=1 to d do
    for j:=1 to d do
      FpW0S[i,j]:=Coefficient(radix_reduce(pow(alpha,-ordrW0,Q,r)*xpforx(R!(Ox!Numerator((Parent(W0[1,1])!rQx)^(-ordrW0)*W0[i,j])),xp,r),r),0); // Compute S!Fp(W0)
    end for;
  end for;

  mat:=FpW0S*mat; // Compute Fp(W0)*mat*W0^(-1)
  for i:=1 to d do
    for j:=1 to d do 
      mat[i,j]:=Coefficient(radix_reduce(R!mat[i,j],r),0);
    end for;
  end for;

  return mat; // matrix of Fp on R w.r.t. basis [b^0_i/r]

end function;


frobenius:=function(w,Q,p,N,r,frobmatb0r)

  // Compute F_p(sum w_i b^0_i dx/r) mod p^N.

  O,Ox,S,R:=getrings(p,N-1);
  x:=Ox.1; y:=R.1; z:=S.1;
  
  d:=Degree(Q);
  Q:=R!Q;

  Sd:=RSpace(S,d);

  r:=(Ox!Coefficients(r)); 
  lc:=LeadingCoefficient(r);
  r:=r/lc;

  xp_minus_one:=pow(R!(Ox!x),p-1,Q,r);		   
  xp:=radix_reduce(xp_minus_one*(R!(Ox!x)),r); 

  frob:=Sd!0;
  for i:=1 to d do
    temp:=radix_reduce((xp_minus_one)*xpforx(R!(Ox!Coefficients(w[i])),xp,r),r);
    for j:=1 to d do
      frob[j]:=Coefficient(radix_reduce(frob[j]+frobmatb0r[i,j]*temp,r),0);
    end for;
  end for;

  O,Ox,S,R:=getrings(p,N);
  Sd:=RSpace(S,d); 
  frob:=p*(Sd!frob); 

  return frob;   
end function;
