max_prec:=function(Q,p,N,g,W0,Winf,e0,einf);

  // Compute the p-adic precision required for provable correctness

  d:=Degree(Q);
  W:=Winf*W0^(-1);
  
  Nmax:=N+Floor(log(p,-p*(ord_0_mat(W)+1)*einf));
  while (Nmax-Floor(log(p,p*(Nmax-1)*e0))-Floor(log(p,-(ord_inf_mat(W^(-1))+1)*einf)) lt N) do 
    Nmax:=Nmax+1;
  end while;

  Nmax:=Maximum(Nmax,2); 

  return Nmax; // precision to be used in the computations
end function;


frobmatrix:=function(Q,p,N,Nmax,g,r,W0,Winf,G0,Ginf,frobmatb0r,red_list_fin,red_list_inf,basis,integrals,quo_map);

  // Compute the matrix of F_p on H^1(X) mod p^N with respect to 'basis'.

  F:=ZeroMatrix(Rationals(),#basis,#basis);  
  f0list:=[];
  finflist:=[];
  fendlist:=[];

  for i:=1 to #basis do

    dif:=frobenius(basis[i],Q,p,Nmax,r,frobmatb0r);
    dif:=convert_to_Qxzzinvd(dif,Q);

    coefs,f0,finf,fend:=reduce_with_fs(dif,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map);

    for j:=1 to #basis do
      F[i,j]:=coefs[j];
    end for;
    
    f0list:=Append(f0list,f0);
    finflist:=Append(finflist,finf);
    fendlist:=Append(fendlist,fend);

  end for;
 
  return F,f0list,finflist,fendlist;

end function;


function h1_basis(Q,p,N)
  // Compute a basis for H^1(X).
  if not IsIrreducible(Q) then
    error "Curve is not irreducible";
  end if;

  d:=Degree(Q);
  g:=genus(Q,p);
  r,Delta,s:=auxpolys(Q);

  W0:=mat_W0(Q);
  W0inv:=W0^(-1);
  Winf:=mat_Winf(Q);
  Winfinv:=Winf^(-1);
  W:=Winf*W0^(-1);

  if (FiniteField(p)!LeadingCoefficient(Delta) eq 0) or (Degree(r) lt 1) or (not smooth(r,p)) or (not (is_integral(W0,p) and is_integral(W0inv,p) and is_integral(Winf,p) and is_integral(Winfinv,p))) then
    error "bad prime";
  end if;

  G:=con_mat(Q,Delta,s);
  G0:=W0*Evaluate(G,Parent(W0[1,1]).1)*W0^(-1)+ddx_mat(W0)*W0^(-1);
  Ginf:=Winf*Evaluate(G,Parent(Winf[1,1]).1)*Winf^(-1)+ddx_mat(Winf)*Winf^(-1);

  Jinf,Tinf,Tinfinv:=jordan_inf(Ginf);
  J0,T0,T0inv:=jordan_0(r,G0);
  e0,einf:=ram(J0,Jinf);
 
  delta:=Floor(log(p,-(ord_0_mat(W)+1)*einf))+Floor(log(p,(Floor((2*g-2)/d)+1)*einf));

  basis:=basis_coho(Q,p,r,W0,Winf,G0,Ginf,J0,Jinf,T0inv,Tinfinv,false,[],[],[]);
  return basis,g,r,W0;
end function;


coleman_data:=function(Q,p,N:useU:=false,basis0:=[],basis1:=[],basis2:=[],heights:=false)

  // Takes a polynomial Q in two variables x,y over the rationals which is monic in y.
  // Returns the Coleman data of (the projective nonsingular model of) the curve defined
  // by Q at p to p-adic precision N.

  if not IsIrreducible(Q) then
    error "Curve is not irreducible";
  end if;

  d:=Degree(Q);
  g:=genus(Q,p);
  r,Delta,s:=auxpolys(Q);

  W0:=mat_W0(Q);
  W0inv:=W0^(-1);
  Winf:=mat_Winf(Q);
  Winfinv:=Winf^(-1);
  W:=Winf*W0^(-1);

  if (FiniteField(p)!LeadingCoefficient(Delta) eq 0) or (Degree(r) lt 1) or (not smooth(r,p)) or (not (is_integral(W0,p) and is_integral(W0inv,p) and is_integral(Winf,p) and is_integral(Winfinv,p))) then
    error "bad prime";
  end if;

  G:=con_mat(Q,Delta,s);
  G0:=W0*Evaluate(G,Parent(W0[1,1]).1)*W0^(-1)+ddx_mat(W0)*W0^(-1);
  Ginf:=Winf*Evaluate(G,Parent(Winf[1,1]).1)*Winf^(-1)+ddx_mat(Winf)*Winf^(-1);

  Jinf,Tinf,Tinfinv:=jordan_inf(Ginf);
  J0,T0,T0inv:=jordan_0(r,G0);
  e0,einf:=ram(J0,Jinf);
 
  delta:=Floor(log(p,-(ord_0_mat(W)+1)*einf))+Floor(log(p,(Floor((2*g-2)/d)+1)*einf));

  basis,integrals,quo_map:=basis_coho(Q,p,r,W0,Winf,G0,Ginf,J0,Jinf,T0inv,Tinfinv,useU,basis0,basis1,basis2);
  Nmax:=max_prec(Q,p,N,g,W0,Winf,e0,einf);

  frobmatb0r:=froblift(Q,p,Nmax-1,r,Delta,s,W0);

  red_list_fin,red_list_inf:=red_lists(Q,p,Nmax,r,W0,Winf,G0,Ginf,e0,einf,J0,Jinf,T0,Tinf,T0inv,Tinfinv);

  F,f0list,finflist,fendlist:=frobmatrix(Q,p,N,Nmax,g,r,W0,Winf,G0,Ginf,frobmatb0r,red_list_fin,red_list_inf,basis,integrals,quo_map);


  // formatting the output into a record:

  format:=recformat<Q,p,N,g,W0,Winf,r,Delta,s,G0,Ginf,e0,einf,delta,basis,quo_map,integrals,F,f0list,finflist,fendlist,Nmax,red_list_fin,red_list_inf,minpolys,cpm,subspace,ordinary,frobmatb0r>;
  out:=rec<format|>;
  out`Q:=Q; out`p:=p; out`N:=N; out`g:=g; out`W0:=W0; out`Winf:=Winf; out`r:=r; out`Delta:=Delta; out`s:=s; out`G0:=G0; out`Ginf:=Ginf; 
  out`e0:=e0; out`einf:=einf; out`delta:=delta; out`basis:=basis; out`quo_map:=quo_map; out`integrals:=integrals; out`F:=F; out`f0list:=f0list; 
  out`finflist:=finflist; out`fendlist:=fendlist; out`Nmax:=Nmax; out`red_list_fin:=red_list_fin; out`red_list_inf:=red_list_inf;
  out`frobmatb0r:=frobmatb0r;

  return out;

end function;

function xy_coordinates(P, data)

  // returns the affine xy-coordinates of a point record

  if P`inf then 
    error "Point is not affine";
  end if;
  W0 := data`W0;
  d := Degree(data`Q);
  x0 := P`x;
  W0invx0 := Evaluate(W0^(-1), x0);
  K := Universe(P`b);
  b_vector := Matrix(K, d, 1, P`b);
  ypowers := W0invx0*ChangeRing(b_vector,Parent(W0invx0[1,1]));
  y0 := ypowers[2,1];
  return [x0,y0];
end function;




set_point:=function(x0,y0,data)

  // Constructs a point from affine coordinates x0,y0. 

  Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0;
  d:=Degree(Q);

  if x0 in RationalField() then
    K:=pAdicField(p,N);
  else
    K:=Parent(x0);
  end if;
  x0:=K!x0; y0:=K!y0;

  if Valuation(x0) lt 0 then
    error "x0 has negative valuation";
  end if;
  
  if (not(W0 eq IdentityMatrix(BaseRing(W0),d))) and (Valuation(Evaluate(data`r,x0)) gt 0) then
    error "W0 is not the identity and r(x0) is zero mod p";
  end if;
  
  format:=recformat<x,b,inf,xt,bt,index>;
  P:=rec<format|>;
  P`inf:=false;
  P`x:=x0;

  y0powers:=[];
  y0powers[1]:=K!1;
  for i:=2 to d do
    y0powers[i]:=(y0)^(i-1);
  end for;
  y0powers:=Vector(y0powers);
  W0x0:=Transpose(Evaluate(W0,x0));

  // the values of the b_i^0 at P
  P`b := Eltseq(y0powers*ChangeRing(W0x0, BaseRing(y0powers)));

  return P;
end function;


set_bad_point:=function(x,b,inf,data)

  Q:=data`Q; p:=data`p; N:=data`N; 
  Qp:=pAdicField(p,N); d:=Degree(Q);

  format:=recformat<x,b,inf,xt,bt,index>;
  P:=rec<format|>;
  P`inf:=inf;
  P`x:=Qp!x;
  P`b:=[Qp!b[i]:i in [1..d]];

  return P; 

end function;


is_bad:=function(P,data)

  // check whether the point P is bad

  x0:=P`x; r:=data`r;

  if P`inf then // infinite point
    return true;
  end if;

  if Valuation(Evaluate(r,x0)) gt 0 then // finite bad point
    return true;
  end if;

  return false;
  
end function;


is_very_bad:=function(P,data)

  // check whether the point P is very bad

  x0:=P`x; r:=data`r; N:=data`N;

  if P`inf then // infinite point
    if Valuation(x0) ge N then // infinite very bad point
      return true;
    end if;
  else // finite point
    if Valuation(Evaluate(r,x0)) ge N then // finite very bad point
      return true;
    end if;
  end if;

  return false;

end function;


lie_in_same_disk:=function(P1,P2,data)

  // check whether two points P1,P2 lie in the same residue disk

  x1:=P1`x; b1:=P1`b; x2:=P2`x; b2:=P2`b; Q:=data`Q;
  d:=Degree(Q);
  
  if P1`inf ne P2`inf then // one point infinite, other not
    return false;
  elif Valuation(x1-x2) lt 1 then 
    return false;
  else
    for i:=1 to d do
        if Valuation(b1[i]-b2[i]) lt 1 then
          return false;
        end if;
      end for;
      return true;
  end if;
 
end function;


minpoly:=function(f1,f2)

  // computes the minimum polynomial of f2 over Q(f1), where
  // f1,f2 are elements of a 1 dimensional function field over Q

  FF:=Parent(f1);

  d:=5;  

  done:=false;
  while not done do

    S:=[];
    for i:=0 to d do
      for j:=0 to d do
        S:=Append(S,f1^j*f2^i);
      end for;
    end for;

    denom:=1;
    for i:=1 to #S do
      E:=Eltseq(S[i]);
      for j:=1 to #E do
        denom:=LCM(denom,Denominator(E[j]));
      end for;
    end for;
  
    maxdeg:=0;
    for i:=1 to #S do
      E:=Eltseq(S[i]);
      for j:=1 to #E do
        deg:=Degree(Numerator(denom*E[j]));
        if  deg gt maxdeg then
          maxdeg:=deg;
        end if;
      end for;
    end for;

    T:=[];
    for i:=1 to #S do
      E:=Eltseq(S[i]);
      v:=[];
      for j:=1 to #E do
        for k:=0 to maxdeg do
          v[(j-1)*(maxdeg+1)+k+1]:=Coefficient(Numerator(denom*E[j]),k);
        end for;  
      end for;
      T:=Append(T,v);
    end for;

    b:=Basis(NullSpace(Matrix(T)));  

    if #b gt 0 then
      done:=true;
      R:=b[1];
    else
      d:=d+3;
    end if;
  
  end while;

  poly:=Qxy!0;
  for i:=0 to d do
    for j:=0 to d do
      poly:=poly+R[i*(d+1)+j+1]*Qx.1^j*Qxy.1^i;
    end for;
  end for;

  fac:=Factorisation(poly);

  for i:=1 to #fac do
    factor:=fac[i][1];
    test:=FF!0;
    for j:=0 to Degree(factor) do
      test:=test+Evaluate(Coefficient(factor,j),f1)*f2^j;
    end for;
    if test eq 0 then
      poly:=factor;
    end if;
  end for;

  return poly;
 
end function;


update_minpolys:=function(data,inf,index);

  // TODO comment

  Q:=data`Q; W0:=data`W0; Winf:=data`Winf; 
  d:=Degree(Q);

  if not assigned data`minpolys then
    data`minpolys:=[ZeroMatrix(Qxy,d+2,d+2),ZeroMatrix(Qxy,d+2,d+2)];
  end if;
  minpolys:=data`minpolys;

  Qt:=RationalFunctionField(RationalField()); Qty:=PolynomialRing(Qt);

  f:=Qty!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qty.1^i*Qt.1^j;
    end for;
  end for;  
  FF:=FunctionField(f); // function field of curve

  if inf then 
    W:=Winf;
  else
    W:=W0;
  end if;

  bfun:=[];
  for i:=1 to d do
    bi:=FF!0;
    for j:=1 to d do
      bi:=bi+W[i,j]*FF.1^(j-1);
    end for;
    bfun[i]:=bi;
  end for;

  if inf then // b=b^{infty}
    if index eq 0 then
       for i:=1 to d do
         if minpolys[2][1,i+1] eq 0 then
           minpolys[2][1,i+1]:=minpoly(FF!(1/Qt.1),bfun[i]);
         end if;
       end for;
    else
      if minpolys[2][index+1,1] eq 0 then
        minpolys[2][index+1,1]:=minpoly(bfun[index],FF!(1/Qt.1));
      end if;
      for i:=1 to d do
        if minpolys[2][index+1,i+1] eq 0 then
          minpolys[2][index+1,i+1]:=minpoly(bfun[index],bfun[i]);
        end if;
      end for;
    end if;
  else // b=b^0
    if index eq 0 then
      for i:=1 to d do
        if minpolys[1][1,i+1] eq 0 then
          minpolys[1][1,i+1]:=minpoly(FF!Qt.1,bfun[i]);
        end if;
      end for;
    else
      if minpolys[1][index+1,1] eq 0 then
        minpolys[1][index+1,1]:=minpoly(bfun[index],FF!Qt.1);
      end if;
      for i:=1 to d do
        if minpolys[1][index+1,i+1] eq 0 then
          minpolys[1][index+1,i+1]:=minpoly(bfun[index],bfun[i]);
        end if;
      end for;
    end if;
  end if;

  data`minpolys:=minpolys;

  return data;

end function;


frobenius_pt:=function(P,data);

  // Computes the image of P under Frobenius

  x0:=P`x; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); K:=Parent(x0); Ky:=PolynomialRing(K);

  x0p:=x0^p;
  b:=P`b;

  Qt:=RationalFunctionField(RationalField()); Qty:=PolynomialRing(Qt);

  f:=Qty!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qty.1^i*Qt.1^j;
    end for;
  end for;  
  FF:=FunctionField(f); // function field of curve

  if not is_bad(P,data) then // finite good point
    
    W0invx0:=Transpose(Evaluate(W0^(-1),x0));

    ypowers:=Vector(b)*ChangeRing(W0invx0,Parent(b[1]));
    y0:=ypowers[2];
  
    C:=Coefficients(Q);
    D:=[];
    for i:=1 to #C do
      D[i]:=Evaluate(C[i],x0p);
    end for;
    fy:=Ky!D;

    y0p:=HenselLift(fy,y0^p); // Hensel lifting
  
    y0ppowers:=[];
    y0ppowers[1]:=K!1;
    for i:=2 to d do
      y0ppowers[i]:=y0p^(i-1);
    end for;
    y0ppowers:=Vector(y0ppowers);

    W0x0:=Transpose(Evaluate(W0,x0));
  
    b := Eltseq(y0ppowers*ChangeRing(W0x0, BaseRing(y0ppowers)));

  elif P`inf then // infinite point
  
    for i:=1 to d do
      bi:=FF!0;
      for j:=1 to d do
        bi:=bi+Winf[i,j]*FF.1^(j-1);
      end for;

      if assigned data`minpolys and data`minpolys[2][1,i+1] ne 0 then
        poly:=data`minpolys[2][1,i+1];
      else
        poly:=minpoly(FF!(1/Qt.1),bi);
      end if;

      C:=Coefficients(poly);
      D:=[];
      for i:=1 to #C do
        D[i]:=Evaluate(C[i],x0p); 
      end for;
      fy:=Ky!D;

      fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
      zeros:=[];
      for j:=1 to #fac do
        if Degree(fac[j][1]) eq 1 then
          zeros:=Append(zeros,-Coefficient(fac[j][1],0)/Coefficient(fac[j][1],1));
        end if;
      end for;
      
      done:=false;
      j:=1;
      while not done and j le #zeros do
        if Valuation(zeros[j]-b[i]^p) gt Min(N, p) then // was gt 0 before 
          done:=true;
          b[i]:=zeros[j];
        end if;
        j:=j+1;
      end while;
      if not done then
        error "Frobenius does not converge at P";
      end if;
    end for;

  else // finite bad point

   for i:=1 to d do
      bi:=FF!0;
      for j:=1 to d do
        bi:=bi+W0[i,j]*FF.1^(j-1);
      end for;

      if assigned data`minpolys and data`minpolys[1][1,i+1] ne 0 then
        poly:=data`minpolys[1][1,i+1];
      else
        poly:=minpoly(FF!Qt.1,bi);
      end if;

      C:=Coefficients(poly);
      D:=[];
      for i:=1 to #C do
        D[i]:=Evaluate(C[i],x0p); 
      end for;
      fy:=Ky!D;

      fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
      zeros:=[];
      for j:=1 to #fac do
        if Degree(fac[j][1]) eq 1 then
          zeros:=Append(zeros,-Coefficient(fac[j][1],0)/Coefficient(fac[j][1],1));
        end if;
      end for;

      done:=false;
      j:=1;
      while not done and j le #zeros do
        if Valuation(zeros[j]-b[i]^p) gt p then
          done:=true;
          b[i]:=zeros[j];
        end if;
        j:=j+1;
      end while;
      if not done then
        error "Frobenius does not converge at P";
      end if;
    end for;

  end if;
  
    P`x:=x0p;
    P`b:=b;
    delete P`xt;
    delete P`bt;
    delete P`index;

  return P;
end function;


teichmueller_pt:=function(P,data : N :=0)

  // Compute the Teichmueller point in the residue disk at a good point P

  x0:=P`x; Q:=data`Q; p:=data`p; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); K:=Parent(x0); Ky:=PolynomialRing(K);

  if is_bad(P,data) then
    error "Point is bad";
  end if;

  if IsZero(N) then N := data`N; end if;

  x0new:=K!TeichmuellerLift(FiniteField(p)!x0,pAdicQuotientRing(p,N)); 
  b:=P`b; 
  W0invx0:=Transpose(Evaluate(W0^(-1),x0));
  ypowers:=Vector(b)*ChangeRing(W0invx0,Parent(b[1]));
  y0:=ypowers[2];
  
  C:=Coefficients(Q);
  D:=[];
  for i:=1 to #C do
    D[i]:=Evaluate(C[i],x0new);
  end for;
  fy:=Ky!D;

  y0new:=HenselLift(fy,y0); // Hensel lifting
  y0newpowers:=[];
  y0newpowers[1]:=K!1;
  for i:=2 to d do
    y0newpowers[i]:=y0newpowers[i-1]*y0new;
  end for;
  y0newpowers:=Vector(y0newpowers);

  W0x0new:=Transpose(Evaluate(W0,x0new));
  b:=Eltseq(y0newpowers*ChangeRing(W0x0new,K));

  P`x:=x0new;
  P`b:=b;
  delete P`xt;
  delete P`bt;
  delete P`index;

  return P;

end function;


local_data:=function(P,data)

  // For a point P, returns the ramification index of the map x on the residue disk at P

  Q:=data`Q; p:=data`p; W0:=data`W0; Winf:=data`Winf; x0:=P`x; b:=P`b; d:=Degree(Q);

  if not is_bad(P,data) then
    eP:=1;
    index:=0;
    return eP,index;
  else     
    Fp:=FiniteField(p); Fpx:=RationalFunctionField(Fp); Fpxy:=PolynomialRing(Fpx);
    f:=Fpxy!0;
    for i:=0 to d do
      for j:=0 to Degree(Coefficient(Q,i)) do
        f:=f+(Fp!Coefficient(Coefficient(Q,i),j))*Fpxy.1^i*Fpx.1^j;
      end for;
    end for;  
    FFp:=FunctionField(f); // function field of curve mod p
    
    if P`inf then
      places:=InfinitePlaces(FFp); // infinite places of function field of curve mod p
      W:=Winf;
    else
      Px0:=Zeros(Fpx.1-Fp!x0)[1]; 
      places:=Decomposition(FFp,Px0); // places of function field of curve mod p lying over x0 mod p
      W:=W0;
    end if;

    bmodp:=[]; // elements of b mod p, where b is either b^0 or b^inf
    for i:=1 to d do
      f:=FFp!0;
      for j:=1 to d do
        f:=f+(Fpx!W[i,j])*FFp.1^(j-1);
      end for;
      bmodp[i]:=f;
    end for;

    done:=false;

    for i:=1 to #places do
      same:=true;
      for j:=1 to d do
        if Evaluate(bmodp[j],places[i]) ne Fp!b[j] then
          same:=false;
        end if;
      end for;    
      if same then
        place:=places[i];
        done:=true;
      end if;
    end for;

    if not done then
      error "Point does not lie on curve";
    end if;

    eP:=RamificationIndex(place);

    if eP eq 1 then
      index:=0;
    else
      done:=false;
      i:=1;
      while not done do
        ord:=Valuation(bmodp[i]-Evaluate(bmodp[i],place),place);
        if ord eq 1 then
          index:=i;
          done:=true;
        end if;
        i:=i+1;
      end while;
    end if;

    return eP,index,place,bmodp;
  end if;

end function;


hensel_lift:=function(fy,root);

  // Finds a root of the polynomial fy over Qp[[t]]
  // by Hensel lifting from an approximate root.
  //
  // Assumes that the starting criterion for Hensel's 
  // lemma is satisfied

  Kty:=Parent(fy);
  Kt:=BaseRing(Kty);
  K:=BaseRing(Kt);
  tprec:=Precision(Kt); // t-adic precision
  Qt:=PowerSeriesRing(RationalField(),tprec);
  Qty:=PolynomialRing(Qt);
  p:=Prime(K);
  pprec:=Precision(K);  // p-adic precision
  Zp:=pAdicRing(p,pprec);
  Zpt:=PowerSeriesRing(Zp,tprec);  

  fy:=Qty!fy;
  derfy:=Derivative(fy);  

  if not Valuation(LeadingCoefficient(Qt!Evaluate(derfy,root)),p) eq 0 then
    error "In Hensel lift of power series, derivative has leading term divisible by p";
  end if;

  v1:=Valuation(Qt!Zpt!Evaluate(fy,root));
  v2:=Valuation(Qt!Zpt!Evaluate(derfy,root));

  if not v1 gt 2*v2 then
    error "Condition Hensel's Lemma not satisfied";
  end if;

  prec_seq:=[];
  k:=tprec;
  
  while k gt v1 do
    prec_seq:=Append(prec_seq,k);
    k:=Ceiling(k/2+v2);
  end while;
  prec_seq:=Reverse(prec_seq);

  for j:=1 to #prec_seq do
    root:=Qt!root;
    root:=ChangePrecision(root,prec_seq[j]);
    root:=root-(Qt!Zpt!Evaluate(fy,root))/(Qt!Zpt!Evaluate(derfy,root));
    root:=Zpt!root;
  end for;

  return root;

end function;


mod_p_prec:=function(fy);

  // Finds the t-adic precision necessary to separate the roots
  // of the polynomial fy over Qp[[t]] modulo p and start Hensel lift.
  //
  // Temporarily uses intrinsic Factorisation instead of 
  // intrinsic Roots because of multiple problems with Roots.
  
  Kty:=Parent(fy);
  Kt:=BaseRing(Kty);
  tprec:=Precision(Kt);
  K:=BaseRing(Kt);
  p:=Prime(K);
  Fp:=FiniteField(p);
  Fpt:=PowerSeriesRing(Fp,tprec);
  Fpty:=PolynomialRing(Fpt);

  fymodp:=Fpty!fy;
  derfymodp:=Derivative(fymodp);

  zeros:=[];
  fac:=Factorisation(fymodp); // can be slow...
  for i:=1 to #fac do
    if fac[i][2] gt 1 then
      error "t-adic precision not high enough";
    end if;
    factor:=fac[i][1];
    if Degree(factor) eq 1 and LeadingCoefficient(factor) eq 1 then
      zeros:=Append(zeros,-Coefficient(factor,0));
    end if;
  end for;

  modpprec:=1;
  for i:=1 to #zeros do
    done:=false;
    prec:=1;
    while not done do
      v1:=Valuation(Evaluate(fymodp,ChangePrecision(zeros[i],prec)));
      v2:=Valuation(Evaluate(derfymodp,ChangePrecision(zeros[i],prec)));
      if Minimum(prec,v1) gt 2*v2 then
        done:=true;
      end if;
      prec:=prec+1;
    end while;
    modpprec:=Maximum(modpprec,prec);
  end for;

  for i:=1 to #zeros do
    for j:=i+1 to #zeros do
      modpprec:=Maximum(modpprec,Valuation(zeros[i]-zeros[j]));
    end for;
  end for;
 
  return modpprec;
 
end function;


approx_root:=function(fy,y0,modpprec,expamodp)

  // Computes an approximation to t-adic precision modpprec of 
  // a root of the polynomial fy over Qp[[t]] which is congruent to:
  //
  // y0 modulo t
  // expamodp modulo p 
  //
  // This approximation is then used as root in hensel_lift.

  Kty:=Parent(fy);
  Kt:=BaseRing(Kty);
  tprec:=Precision(Kt); // t-adic precision
  K:=BaseRing(Kt);

  p:=Prime(K);
  Fp:=FiniteField(p);
  pprec:=Precision(K);  // p-adic precision
  Zp:=pAdicRing(p,pprec);
  Zpt:=PowerSeriesRing(Zp,tprec);
  Zpz:=PolynomialRing(Zp);

  Qt:=PowerSeriesRing(RationalField(),tprec);
  Qty:=PolynomialRing(Qt);
  Qz:=PolynomialRing(RationalField());
  Qzt:=PowerSeriesRing(Qz,tprec);
  
  roots:=[[*Kt!y0,1*]];
  i:=1;
  while i le #roots do
    root:=roots[i][1];
    Nroot:=roots[i][2];
    if Nroot lt modpprec then
      roots:=Remove(roots,i);
      newroot:=root+Kty.1*Kt.1^Nroot;
      C:=Coefficients(fy);
      fynewroot:=Kty!0;
      for j:=1 to #C do
        fynewroot:=fynewroot+(Kt!C[j])*newroot^(j-1);
      end for;
      fynewroot:=Qty!Kty!fynewroot;
      fznewroot:=Qzt!0;
      for j:=0 to Degree(fynewroot) do
        for k:=0 to tprec-1 do
          fznewroot:=fznewroot+Coefficient(Coefficient(fynewroot,j),k)*(Qz.1)^j*(Qzt.1)^k;
        end for;
      end for;
      fac:=Factorisation(Zpz!Coefficient(fznewroot,Valuation(fznewroot)));
      for j:=1 to #fac do
        if (Degree(fac[j][1]) eq 1) and (Coefficient(fac[j][1],1) eq 1) then
          sol:=-Coefficient(fac[j][1],0); 
          if Fp!sol eq Coefficient(expamodp,Nroot) then
            roots:=Insert(roots,i,[*Evaluate(newroot,sol),Nroot+1*]);
          end if;
        end if;
      end for;
    else
      i:=i+1;
    end if;
  end while;

  if #roots ne 1 then
    error "something is wrong, number of approximate roots is different from 1";
  end if;

  root:=roots[1][1];
  root:=Zpt!Qt!root;

  v1:=Valuation(Zpt!Qt!Evaluate(fy,root));
  v2:=Valuation(Zpt!Qt!Evaluate(Derivative(fy),root));

  if v1 le 2*v2 then
    error "something is wrong, approximate root not good enough for Hensel lift";
  end if;

  return root;

end function;


mod_p_expansion:=function(f,place,tmodp,modpprec);

  // Finds the power series expansion of f in the function field
  // modulo p at place with respect to local parameter tmodp to
  // absolute precision modpprec.

  FFp:=Parent(f);
  Fpx:=BaseRing(FFp);
  Fp:=BaseRing(Fpx);
  Fpt:=PowerSeriesRing(Fp,modpprec);

  expamodp:=Fpt!0;
  for i:=0 to modpprec-1 do
    val:=Evaluate(f,place);
    expamodp:=expamodp+val*Fpt.1^i;
    f:=(f-val)/tmodp;
  end for;
  
  return expamodp;
  
end function;


local_coord:=function(P,prec,data);

  // Computes powerseries expansions of x and
  // the b^0_i or b^infty_i (depending on whether
  // P is infinite or not) in terms of the local
  // coordinate computed by local_data.

  if assigned P`xt and Precision(Parent(P`xt)) ge prec then
    xt:=P`xt;
    bt:=P`bt;
    index:=P`index;
    return xt,bt,index;
  end if;

  if is_bad(P,data) and not is_very_bad(P,data) then
    error "Cannot compute local parameter at a bad point which is not very bad";
  end if;

  x0:=P`x; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf; d:=Degree(Q); b:=P`b;
  K:=Parent(x0); Kt<t>:=PowerSeriesRing(K,prec); Kty:=PolynomialRing(Kt);
  Qt:=RationalFunctionField(RationalField()); Qty:=PolynomialRing(Qt);
  Fp:=FiniteField(p);

  f:=Qty!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qty.1^i*Qt.1^j;
    end for;
  end for;  
  FF:=FunctionField(f); // function field of curve

  if not is_bad(P,data) then // finite good point

    xt:=t+x0;

    W0invx0:=Transpose(Evaluate(W0^(-1),x0));
    ypowers:=Vector(b)*ChangeRing(W0invx0,Parent(b[1]));
    y0:=ypowers[2];

    C:=Coefficients(Q);
    D:=[];
    for i:=1 to #C do
      D[i]:=Evaluate(C[i],xt); 
    end for;
    fy:=Kty!D;
    derfy:=Derivative(fy);

    yt:=hensel_lift(fy,Kt!y0);

    ypowerst:=[];
    ypowerst[1]:=FieldOfFractions(Kt)!1;
    ypowerst[2]:=yt;
    for i:=3 to d do
      ypowerst[i]:=ypowerst[i-1]*yt;
    end for;
    bt:=Eltseq(Vector(ypowerst)*Transpose(Evaluate(W0,xt)));

    btnew:=[];
    for i:=1 to d do
      btnew[i]:=Kt!bt[i];
    end for;
    bt:=btnew;

    index:=0;

  elif P`inf then // infinite point

    eP,index,place,bmodp:=local_data(P,data);
    FFp:=Parent(bmodp[1]);
    Fpx:=BaseRing(FFp);

    bfun:=[];
    for i:=1 to d do
      bi:=FF!0;
      for j:=1 to d do
        bi:=bi+Winf[i,j]*FF.1^(j-1);
      end for;
      bfun[i]:=bi;
    end for;
    
    if eP eq 1 then // P is an infinite point that is not ramified
      
      xt:=t+x0;
      bt:=[];

      for i:=1 to d do

        if assigned data`minpolys and data`minpolys[2][1,i+1] ne 0 then
          poly:=data`minpolys[2][1,i+1]; 
        else 
          poly:=minpoly(FF!(1/Qt.1),bfun[i]);
        end if;

        C:=Coefficients(poly);
        D:=[];
        for j:=1 to #C do
          D[j]:=Evaluate(C[j],xt); 
        end for;
        fy:=Kty!D;
        derfy:=Derivative(fy);

        modpprec:=mod_p_prec(fy);

        if assigned P`bt and Precision(Parent(P`bt[i])) ge modpprec then
          approxroot:=P`bt[i];
        else
          tmodp:=1/Fpx.1-Fp!x0;
          expamodp:=mod_p_expansion(bmodp[i],place,tmodp,modpprec);
          approxroot:=approx_root(fy,b[i],modpprec,expamodp);
        end if;

        bti:=hensel_lift(fy,approxroot);
        bt[i]:=bti;

      end for;

    else // P is an infinite point that is ramified

      if assigned data`minpolys and data`minpolys[2][index+1,1] ne 0 then
        poly:=data`minpolys[2][index+1,1];
      else
        poly:=minpoly(bfun[index],FF!1/(Qt.1));
      end if;

      C:=Coefficients(poly);
      D:=[];
      for j:=1 to #C do
        D[j]:=Evaluate(C[j],t+b[index]); 
      end for;
      fy:=Kty!D;
      derfy:=Derivative(fy);

      modpprec:=mod_p_prec(fy);

      if assigned P`xt and Precision(Parent(P`xt)) ge modpprec then
        approxroot:=P`xt;
      else
        tmodp:=bmodp[index]-Fp!b[index];
        expamodp:=mod_p_expansion(FFp!1/Fpx.1,place,tmodp,modpprec);
        approxroot:=approx_root(fy,x0,modpprec,expamodp);
      end if;

      xt:=hensel_lift(fy,approxroot);

      bt:=[];
      for i:=1 to d do 
      
        if i eq index then
          bt[i]:=t+b[i];
        else
          
          if assigned data`minpolys and data`minpolys[2][index+1,i+1] ne 0 then
            poly:=data`minpolys[2][index+1,i+1];
          else
            poly:=minpoly(bfun[index],bfun[i]);
          end if;

          C:=Coefficients(poly);
          D:=[];
          for j:=1 to #C do
            D[j]:=Evaluate(C[j],t+b[index]); 
          end for;

          fy:=Kty!D;
          derfy:=Derivative(fy);

          modpprec:=mod_p_prec(fy);

          if assigned P`bt and Precision(Parent(P`bt[i])) ge modpprec then
            approxroot:=P`bt[i];
          else
            tmodp:=bmodp[index]-Fp!b[index];
            expamodp:=mod_p_expansion(bmodp[i],place,tmodp,modpprec);
            approxroot:=approx_root(fy,b[i],modpprec,expamodp);
          end if;

          bti:=hensel_lift(fy,approxroot);
          bt[i]:=bti;

        end if;
 
      end for;

    end if;

  else // finite bad point

    eP,index,place,bmodp:=local_data(P,data);
    FFp:=Parent(bmodp[1]);
    Fpx:=BaseRing(FFp);

    bfun:=[];
    for i:=1 to d do
      bi:=FF!0;
      for j:=1 to d do
        bi:=bi+W0[i,j]*FF.1^(j-1);
      end for;
      bfun[i]:=bi;
    end for;

    if eP eq 1 then // P is a finite point that is not ramified

      xt:=t+x0;
      bt:=[];
      for i:=1 to d do
        
        if assigned data`minpolys and data`minpolys[1][1,i+1] ne 0 then
          poly:=data`minpolys[1][1,i+1];
        else
          poly:=minpoly(FF!Qt.1,bfun[i]);
        end if;

        C:=Coefficients(poly);
        D:=[];
        for j:=1 to #C do
          D[j]:=Evaluate(C[j],xt); 
        end for;
        fy:=Kty!D;
        derfy:=Derivative(fy);

        modpprec:=mod_p_prec(fy);

        if assigned P`bt and Precision(Parent(P`bt[i])) ge modpprec then
          approxroot:=P`bt[i];
        else
          tmodp:=Fpx.1-Fp!x0;
          expamodp:=mod_p_expansion(bmodp[i],place,tmodp,modpprec);
          approxroot:=approx_root(fy,b[i],modpprec,expamodp);
        end if;

        bti:=hensel_lift(fy,approxroot);
        bt[i]:=bti;

      end for;

    else // P is a finite point that ramifies

      if assigned data`minpolys and data`minpolys[1][index+1,1] ne 0 then
        poly:=data`minpolys[1][index+1,1];
      else
        poly:=minpoly(bfun[index],FF!Qt.1);
      end if;

      C:=Coefficients(poly);
      D:=[];
      for j:=1 to #C do
        D[j]:=Evaluate(C[j],t+b[index]); 
      end for;
      fy:=Kty!D;
      derfy:=Derivative(fy);

      modpprec:=mod_p_prec(fy);

      if assigned P`xt and Precision(Parent(P`xt)) ge modpprec then
        approxroot:=P`xt;
      else
        tmodp:=bmodp[index]-Fp!b[index];
        expamodp:=mod_p_expansion(FFp!Fpx.1,place,tmodp,modpprec);
        approxroot:=approx_root(fy,x0,modpprec,expamodp);
      end if;

      xt:=hensel_lift(fy,approxroot);  

      bt:=[];
      for i:=1 to d do 
      
        if i eq index then
          bt[i]:=t+b[i];
        else
          
          if assigned data`minpolys and data`minpolys[1][index+1,i+1] ne 0 then
            poly:=data`minpolys[1][index+1,i+1];
          else
            poly:=minpoly(bfun[index],bfun[i]);
          end if;

          C:=Coefficients(poly);
          D:=[];
          for j:=1 to #C do
            D[j]:=Evaluate(C[j],t+b[index]);
          end for;

          fy:=Kty!D;

          derfy:=Derivative(fy);

          modpprec:=mod_p_prec(fy);

          if assigned P`bt and Precision(Parent(P`bt[i])) ge modpprec then
            approxroot:=P`bt[i];
          else
            tmodp:=bmodp[index]-Fp!b[index];
            expamodp:=mod_p_expansion(bmodp[i],place,tmodp,modpprec);
            approxroot:=approx_root(fy,b[i],modpprec,expamodp);
          end if;
          bti:=hensel_lift(fy,approxroot);
          bt[i]:=bti;

        end if;
 
      end for;

    end if;

  end if;

  return xt,bt,index;

end function;


tiny_integral_prec:=function(prec,e,maxpoleorder,maxdegree,mindegree,val,data : N := 0);

  // Determines the p-adic precision to which the tiny integrals of the 
  // differential with maximum pole order equal to maxpoleorder etc. 
  // is correct, where val is the valuation of the local coordinate at one point evaluated
  // at the other point. N is the number of digits to which the differential is known to
  // be correct.

  if IsZero(N) then N:=data`N; end if;

  p:=data`p;

  // Precision loss from terms of positive order we do consider:

  m1:=N*e-val;
  for i:=1 to maxdegree do
    m1:=Minimum(m1,N*e+i-e*Floor(Log(p,i+1)));
  end for;  

  // Precision loss from terms we omit:

  m2:=mindegree+2-e*Floor(Log(p,mindegree+2));
  for i:=mindegree+2 to Ceiling(e/Log(p)) do
    m2:=Minimum(m2,i+1-e*Floor(Log(p,i+1)));
  end for;

  // Precision loss from terms of negative order

  m3:=N*e-val;
  if maxpoleorder ge 2 then
    m3:=N*e-val-maxpoleorder*val-e*Floor(Log(p,maxpoleorder-1));
  end if;

  m:=Minimum([m1,m2,m3]);

  return m/e;

end function;


find_bad_point_in_disk:=function(P,data);

  // Find the very bad point in the residue disk of a bad point P.

  x0:=P`x; b:=P`b; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf; r:=data`r;
  d:=Degree(Q); K:=Parent(x0); Ky:=PolynomialRing(K); 

  if not is_bad(P,data) then
    error "Residue disk does not contain a bad point";
  end if;

  if P`inf then
    x0:=K!0;
  else
    rQp:=Ky!Coefficients(r);
    x0:=HenselLift(rQp,x0);
  end if;

  Qt:=RationalFunctionField(RationalField()); Qty:=PolynomialRing(Qt);

  f:=Qty!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qty.1^i*Qt.1^j;
    end for;
  end for;  
  FF:=FunctionField(f); // function field of curve

  eP,index:=local_data(P,data);

  if P`inf then
    W:=Winf;
  else
    W:=W0;
  end if;

  bfun:=[];
  for i:=1 to d do
    bi:=FF!0;
    for j:=1 to d do
      bi:=bi+W[i,j]*FF.1^(j-1);
    end for;
    bfun:=Append(bfun,bi);
  end for;

  if index eq 0 then
    if P`inf then
      xfun:=FF!(1/Qt.1);
    else
      xfun:=FF!(Qt.1);
    end if;

    for i:=1 to d do
      poly:=minpoly(xfun,bfun[i]);
      C:=Coefficients(poly);
      D:=[];
      for i:=1 to #C do
        D[i]:=Evaluate(C[i],x0); 
      end for;
      fy:=Ky!D;
      fac:=Factorisation(fy);
      done:=false;
      j:=1;
      while not done and j le #fac do
        if Degree(fac[j][1]) eq 1 and Valuation(-Coefficient(fac[j][1],0)-b[i]) gt 0 then
          done:=true;
          b[i]:=-Coefficient(fac[j][1],0);
        end if;
        j:=j+1;
      end while;
    end for;
  else
   bindex:=bfun[index];
   if P`inf then
      xfun:=FF!(1/Qt.1);
    else
      xfun:=FF!(Qt.1);
    end if;
    poly:=minpoly(xfun,bindex);
    C:=Coefficients(poly);
    D:=[];
    for i:=1 to #C do
      D[i]:=Evaluate(C[i],x0); 
    end for;
    fy:=Ky!D;
    fac:=Factorisation(fy);
    done:=false;
    j:=1;
    while not done and j le #fac do
      if Degree(fac[j][1]) eq 1 and Valuation(-Coefficient(fac[j][1],0)-b[index]) gt 0 then
        done:=true;
        b[index]:=-Coefficient(fac[j][1],0);
      end if;
      j:=j+1;
    end while;
    for i:=1 to d do
      if i ne index then
        poly:=minpoly(bindex,bfun[i]);
        C:=Coefficients(poly);
        D:=[];
        for i:=1 to #C do
          D[i]:=Evaluate(C[i],b[index]); 
        end for;
        fy:=Ky!D;
        fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
        done:=false;
        j:=1;
        while not done and j le #fac do
          if Degree(fac[j][1]) eq 1 and Valuation(-Coefficient(fac[j][1],0)-b[i]) gt 0 then
            done:=true;
            b[i]:=-Coefficient(fac[j][1],0);
          end if;
          j:=j+1;
        end while;
      end if;
    end for; 
  end if;

  Pbad:=set_bad_point(x0,b,P`inf,data);

  return Pbad;

end function;


tadicprec:=function(data,e : N := 0);

  // Compute the necessary t-adic precision to compute tiny integrals

  p:=data`p; 

  if IsZero(N) then N:=data`N; end if;

  prec:=1;
  while Floor(prec/e)+1-Floor(Log(p,prec+1)) lt N do
    prec:=prec+1;
  end while;
  prec:=Maximum([prec,100]); // 100 arbitrary, avoid problems with small precisions 
  //prec:=Maximum([prec,50]); // 100 arbitrary, avoid problems with small precisions 

  return prec;

end function;


tiny_integrals_on_basis:=function(P1,P2,data:prec:=0,P:=0);

  // Compute tiny integrals of basis elements from P1 to P2.
  // If P1 is not defined over Qp (but a totally ramified 
  // extension) then a point P defined over Qp in the same
  // residue disk as P1 has to be specified.

  x1:=P1`x; x2:=P2`x; b1:=P1`b; b2:=P2`b; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf; r:=data`r; basis:=data`basis; N:=data`N;
  d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x1); 

  if not lie_in_same_disk(P1,P2,data) then
    error "the points do not lie in the same residue disk";
  end if;

  //if ((x1 eq x2) and (b1 eq b2)) then 
  //  return RSpace(K,#basis)!0, N*Degree(K);
  //end if;

  if (Valuation(x1-x2)/Valuation(Parent(x1-x2)!p) ge N) and (Minimum([Valuation(b1[i]-b2[i])/Valuation(Parent(b1[i]-b2[i])!p):i in [1..d]]) ge N) then
    return RSpace(K,#basis)!0, N*Degree(K);
  end if; 

  if Degree(K) gt 1 then // P1 needs to be defined over Qp
    tinyPtoP2,NtinyPtoP2:=$$(P,P2,data);
    tinyPtoP1,NtinyPtoP1:=$$(P,P1,data);
    return tinyPtoP2-tinyPtoP1,Minimum(NtinyPtoP2,NtinyPtoP1);
  end if;

  if not Type(P) eq Rec then
    P:=P1;
  end if;

  if is_bad(P1,data) and not is_very_bad(P1,data) then // on a bad disk P1 needs to be very bad
    P:=find_bad_point_in_disk(P,data);
    tinyPtoP2,NtinyPtoP2:=$$(P,P2,data);
    tinyPtoP1,NtinyPtoP1:=$$(P,P1,data);
    return tinyPtoP2-tinyPtoP1,Minimum(NtinyPtoP2,NtinyPtoP1);
  end if;

  e:=Degree(Parent(x2));

  if prec eq 0 then // no t-adic precision specified
    prec:=tadicprec(data,e);
  end if;

  Kt:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

  xt,bt,index:=local_coord(P1,prec,data);

  Qt<t>:=LaurentSeriesRing(RationalField(),prec);
  xt:=Qt!xt;
  btnew:=[Qt|];
  for i:=1 to d do
    btnew[i]:=Qt!bt[i];
  end for;
  bt:=Vector(btnew);

  if P1`inf then
    xt:=1/xt;
    xt:=Qt!Kt!xt; 
    Winv:=W0*Winf^(-1);          
    bt:=bt*Transpose(Evaluate(Winv,xt));
    for i:=1 to d do
      bt[i]:=Qt!(Kt!bt[i]);
    end for; 
  end if;

  if P1`inf or not is_bad(P1,data) then 
    denom:=Qt!Kt!(1/Evaluate(r,xt));
  else
    Qp:=pAdicField(p,N);
    Qpx:=PolynomialRing(Qp);
    rQp:=Qpx!r;
    zero:=HenselLift(rQp,x1);
    sQp:=rQp div (Qpx.1-zero);
    denom:=Qt!Kt!((Qt!OKt!(xt-Coefficient(xt,0)))^(-1)*(Qt!Kt!(1/Evaluate(sQp,xt))));
  end if;

  derxt:=Qt!Kt!Derivative(xt); 
  diffs:=[];
  for i:=1 to #basis do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    diffs[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    diffs[i]:=Qt!Kt!diffs[i];
    if Coefficient(diffs[i],-1) ne 0 then
      diffs[i]:=diffs[i]-Coefficient(diffs[i],-1)*Kt.1^(-1); // temporary, deal with logs later, important for double integrals
    end if;
  end for;

  maxpoleorder:=-(Minimum([Valuation(diffs[i]): i in [1..#basis]])); 
  maxdegree:=Maximum([Degree(diffs[i]): i in [1..#basis]]);
  mindegree:=Minimum([Degree(diffs[i]): i in [1..#basis]]);

  indefints:=[];
  for i:=1 to #basis do
    indefints := Append(indefints, Integral(diffs[i]));
  end for;

  tinyP1toP2:=[];
  for i:=1 to #basis do
    if index eq 0 then // x-x(P1) is the local coordinate
      tinyP1toP2[i]:=Evaluate(indefints[i],x2-x1);
      val:=Valuation(x2-x1);
    else // b[index]-b[index](P1) is the local coordinate
      tinyP1toP2[i]:=Evaluate(indefints[i],b2[index]-b1[index]);
      val:=Valuation(b2[index]-b1[index]);
    end if;
  end for;

  NtinyP1toP2:=tiny_integral_prec(prec,e,maxpoleorder,maxdegree,mindegree,val,data);

  return Vector(tinyP1toP2),NtinyP1toP2;

end function;


tiny_integrals_on_basis_to_z:=function(P,data:prec:=0);

  // Compute tiny integrals of basis elements from P to an
  // arbitrary point in its residue disk as a power series
  // in the local parameter there. The series expansions xt
  // and bt of the coordinates on the curve in terms of this 
  // local parameter are also returned.

  x0:=P`x; b:=P`b; Q:=data`Q; p:=data`p; N:=data`N; basis:=data`basis; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x0);

  if is_bad(P,data) and not is_very_bad(P,data) then // on a bad disk P needs to be very bad
    P1:=find_bad_point_in_disk(P,data);  
  else
    P1:=P;
  end if;
  x1:=P1`x;

  IPP1,NIPP1:=tiny_integrals_on_basis(P,P1,data:prec:=prec);

  if prec eq 0 then // no t-adic precision specified
    prec:=tadicprec(data,1);
  end if;

  Kt<t>:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

  xt,bt,index:=local_coord(P1,prec,data);

  xtold:=xt;
  btold:=bt;

  Qt<t>:=LaurentSeriesRing(RationalField(),prec);
  xt:=Qt!xt;
  btnew:=[Qt|];
  for i:=1 to d do
    btnew[i]:=Qt!bt[i];
  end for;
  bt:=Vector(btnew);

  if P1`inf then
    xt:=1/xt;
    xt:=Qt!Kt!xt; 
    Winv:=W0*Winf^(-1);          
    bt:=bt*Transpose(Evaluate(Winv,xt));
    for i:=1 to d do
      bt[i]:=Qt!(Kt!bt[i]);
    end for; 
  end if;

  if P1`inf or not is_bad(P1,data) then 
    denom:=Qt!Kt!(1/Evaluate(r,xt));
  else
    Qp:=pAdicField(p,N);
    Qpx:=PolynomialRing(Qp);
    rQp:=Qpx!r;
    zero:=HenselLift(rQp,x1);
    sQp:=rQp div (Qpx.1-zero);
    denom:=Qt!Kt!((Qt!OKt!(xt-Coefficient(xt,0)))^(-1)*(Qt!Kt!(1/Evaluate(sQp,xt))));
  end if;

  derxt:=Qt!Kt!Derivative(xt); 
  diffs:=[];
  for i:=1 to #basis do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    diffs[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    diffs[i]:=Qt!Kt!diffs[i];
    if Coefficient(diffs[i],-1) ne 0 then
      diffs[i]:=diffs[i]-Coefficient(diffs[i],-1)*t^(-1); // temporary, TODO deal with logs later, important for double integrals
    end if;
  end for;

  indefints:=[];
  for i:=1 to #basis do
    indefints := Append(indefints, Integral(diffs[i]));
  end for;

  xt:=xtold;
  bt:=Vector(btold);

  return Vector(indefints)+IPP1,xt,bt,NIPP1;

end function;


pow:=function(x,k);

  if k eq 0 then
    return Parent(x)!1;
  else
    return x^k;
  end if;

end function;


evalfinf:=function(finf,P,data);

  // Evaluate vector of functions finf at P.

  x0:=P`x; b:=P`b; Q:=data`Q; W0:=data`W0; Winf:=data`Winf; N:=data`N; p:=data`p;
  d:=Degree(Q); K:=Parent(x0); 

  W:=Winf*W0^(-1); 

  valfinf:=0;

  if P`inf then
    finfP:=K!0;
    for i:=1 to d do
      finfi:=finf[i];
      C:=Coefficients(finfi);
      val:=Valuation(finfi);
      for j:=1 to #C do
        finfP:=finfP+(K!C[j])*pow(1/x0,val+j-1)*b[i];
        valfinf:=Minimum(valfinf,Valuation(K!C[j]));
      end for;
    end for;
    NfinfP:=N*Degree(K)+p*(ord_0_mat(W)+1)*Valuation(x0)+valfinf;
  else 
    finf:=finf*ChangeRing(W,BaseRing(finf));
    finfP:=K!0;
    for i:=1 to d do
      finfi:=finf[i];
      C:=Coefficients(finfi);
      val:=Valuation(finfi);
      for j:=1 to #C do
        finfP:=finfP+(K!C[j])*pow(x0,val+j-1)*b[i];
        valfinf:=Minimum(valfinf,Valuation(K!C[j]));
      end for;
    end for;
    NfinfP:=N*Degree(K)+valfinf;
  end if;

  return finfP, NfinfP/Degree(K);

end function;

evalf0:=function(f0,P,data);

  // Evaluate vector of functions f0 at P.
 
  x0:=P`x; b:=P`b; Q:=data`Q; r:=data`r; W0:=data`W0; Winf:=data`Winf; N:=data`N; Nmax:=data`Nmax; p:=data`p;
  d:=Degree(Q); lcr:=LeadingCoefficient(r); K:=Parent(x0);

  valf0:=0;

  if P`inf then 
    Winv:=W0*Winf^(-1); 
    Qt:=BaseRing(Winv);
    b:=Vector(b)*Transpose(Evaluate(Evaluate(Winv,1/Qt.1),x0)); // values of the b_i^0 at P
    
    z0:=Evaluate(r,1/x0)/lcr;
    invz0:=1/z0;
    invz0pow:=[K!1];
    for i:=1 to p*(Nmax-1) do
      invz0pow[i+1]:=invz0pow[i]*invz0;
    end for;
    
    invx0:=1/x0;
    invx0pow:=[K!1];
    for i:=1 to Degree(r)-1 do
      invx0pow[i+1]:=invx0pow[i]*invx0;
    end for;

    f0P:=K!0;
    for i:=1 to d do
      f0i:=f0[i];
      C:=Coefficients(f0i);
      val:=Valuation(f0i);
      for j:=1 to #C do
        D:=Coefficients(C[j]);
        for k:=1 to #D do
          f0P:=f0P+(K!D[k])*invx0pow[k]*invz0pow[2-j-val]*b[i];
          valf0:=Minimum(valf0,Valuation(K!D[k]));
        end for;
      end for;
    end for;
    Nf0P:=N*Degree(K)+(ord_inf_mat(Winv)+1)*Valuation(x0)+valf0;

  else

    z0:=Evaluate(r,x0)/lcr;  
    invz0:=1/z0;
    invz0pow:=[K!1];
    for i:=1 to p*(Nmax-1) do
      invz0pow[i+1]:=invz0pow[i]*invz0;
    end for;

    x0pow:=[K!1];
    for i:=1 to Degree(r)-1 do
      x0pow[i+1]:=x0pow[i]*x0;
    end for;  
 
    f0P:=K!0;
    for i:=1 to d do
      f0i:=f0[i];
      C:=Coefficients(f0i);
      val:=Valuation(f0i);
      for j:=1 to #C do
        D:=Coefficients(C[j]);
        for k:=1 to #D do
          f0P:=f0P+(K!D[k])*x0pow[k]*invz0pow[2-j-val]*b[i];
          valf0:=Minimum(valf0,Valuation(K!D[k]));
        end for;
      end for;
    end for;
    Nf0P:=N*Degree(K)-p*(Nmax-1)*Valuation(z0)+valf0; // TODO this is error of terms we did consider, take error of terms we ignored into account as well
  end if;

  return f0P,Nf0P/Degree(K);

end function;


evalfinf:=function(finf,P,data);

  // Evaluate vector of functions finf at P.

  x0:=P`x; b:=P`b; Q:=data`Q; W0:=data`W0; Winf:=data`Winf; N:=data`N; p:=data`p;
  d:=Degree(Q); K:=Parent(x0); 

  W:=Winf*W0^(-1); 

  valfinf:=0;

  if P`inf then
    finfP:=K!0;
    for i:=1 to d do
      finfi:=finf[i];
      C:=Coefficients(finfi);
      val:=Valuation(finfi);
      for j:=1 to #C do
        finfP:=finfP+(K!C[j])*pow(1/x0,val+j-1)*b[i];
        valfinf:=Minimum(valfinf,Valuation(K!C[j]));
      end for;
    end for;
    NfinfP:=N*Degree(K)+p*(ord_0_mat(W)+1)*Valuation(x0)+valfinf;
  else 
    finf:=finf*ChangeRing(W,BaseRing(finf));
    finfP:=K!0;
    for i:=1 to d do
      finfi:=finf[i];
      C:=Coefficients(finfi);
      val:=Valuation(finfi);
      for j:=1 to #C do
        finfP:=finfP+(K!C[j])*pow(x0,val+j-1)*b[i];
        valfinf:=Minimum(valfinf,Valuation(K!C[j]));
      end for;
    end for;
    NfinfP:=N*Degree(K)+valfinf;
  end if;

  return finfP, NfinfP/Degree(K);

end function;


evalfend:=function(fend,P,data);

  // Evaluate vector of functions fend at P.

  x0:=P`x; b:=P`b; Q:=data`Q; W0:=data`W0; Winf:=data`Winf; N:=data`N;
  d:=Degree(Q);
  K:=Parent(x0);

  valfend:=0;

  if P`inf then
    Winv:=W0*Winf^(-1);
    Qt:=BaseRing(Winv);
    b:=Vector(b)*Transpose(Evaluate(Evaluate(Winv,1/Qt.1),x0)); // values of the b_i^0 at P
    fendP:=K!0;
    for i:=1 to d do
      fendi:=fend[i];
      C:=Coefficients(fendi);
      for j:=1 to #C do
        fendP:=fendP+(K!C[j])*pow(1/x0,j-1)*b[i];
        valfend:=Minimum(valfend,Valuation(K!C[j]));
      end for;
    end for;
    NfendP:=N*Degree(K)+(ord_0_mat(Winf)+1)*Valuation(x0)+valfend;
  else
    fendP:=K!0;
    for i:=1 to d do
      fendi:=fend[i];
      C:=Coefficients(fendi);
      for j:=1 to #C do
        fendP:=fendP+(K!C[j])*pow(x0,j-1)*b[i];
        valfend:=Minimum(valfend,Valuation(K!C[j]));
      end for;
    end for;
    NfendP:=N*Degree(K)+valfend;
  end if;

  return fendP, NfendP/Degree(K);

end function;


round_to_Qp:=function(L)

  // Rounds a vector over a totally ramified extension of Qp to one over Qp.

  K:=CoefficientRing(L);
  deg:=Degree(K);
  e:=Precision(K);

  l:=[];
  for i:=1 to #Eltseq(L) do
    l[i]:=Eltseq(L[i])[1];  
    e:=Minimum(e,Valuation(L[i]-l[i]));
  end for;

  return Vector(l),e/deg;

end function;


coleman_integrals_on_basis:=function(P1,P2,data:e:=1)

  // Integrals of basis elements from P1 to P2. 

  F:=data`F; Q:=data`Q; basis:=data`basis; x1:=P1`x; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q); K:=Parent(x1); 

  // First make sure that if P1 or P2 is bad, then it is very bad

  if is_bad(P1,data) and not is_very_bad(P1,data) then
    S1:=find_bad_point_in_disk(P1,data);
    _,index:=local_data(S1,data);
    data:=update_minpolys(data,S1`inf,index);
    xt,bt,index:=local_coord(S1,tadicprec(data,e),data);
    S1`xt:=xt;
    S1`bt:=bt;
    S1`index:=index;
    IS1P1,NIS1P1:=tiny_integrals_on_basis(S1,P1,data:prec:=tadicprec(data,e));
    IS1P2,NIS1P2:=$$(S1,P2,data:e:=e);
    IP1P2:=IS1P2-IS1P1;
    NIP1P2:=Ceiling(Minimum([NIS1P1,NIS1P2]));
    return IP1P2,NIP1P2;
  end if;

  if is_bad(P2,data) and not is_very_bad(P2,data) then
    S2:=find_bad_point_in_disk(P2,data);
    _,index:=local_data(S2,data);
    data:=update_minpolys(data,S2`inf,index);
    xt,bt,index:=local_coord(S2,tadicprec(data,e),data);
    S2`xt:=xt;
    S2`bt:=bt;
    S2`index:=index;
    IP1S2,NIP1S2:=$$(P1,S2,data:e:=e);
    IP2S2,NIP2S2:=tiny_integrals_on_basis(P2,S2,data:prec:=tadicprec(data,e));
    IP1P2:=IP1S2-IP2S2;
    NIP1P2:=Ceiling(Minimum([NIP1S2,NIP2S2]));
    return IP1P2,NIP1P2;
  end if;

  // If P1,P2 is bad (hence very bad), use a near boundary point.

  _,index:=local_data(P1,data);
  data:=update_minpolys(data,P1`inf,index);
  _,index:=local_data(P2,data);
  data:=update_minpolys(data,P2`inf,index);

  if is_bad(P1,data) then
    xt,bt,index:=local_coord(P1,tadicprec(data,e),data);
    P1`xt:=xt;       
    P1`bt:=bt;       
    P1`index:=index; 
    Qp:=Parent(P1`x);
    Qpa<a>:=PolynomialRing(Qp);
    K<a>:=TotallyRamifiedExtension(Qp,a^e-p);
    format:=recformat<x,b,inf,xt,bt,index>;
    S1:=rec<format|>;                                                    
    S1`inf:=P1`inf;
    S1`x:=Evaluate(xt,a);
    S1`b:=[Evaluate(bt[i],a):i in [1..d]];
  else
    xt,bt,index:=local_coord(P1,tadicprec(data,1),data);
    P1`xt:=xt;       
    P1`bt:=bt;       
    P1`index:=index; 
    S1:=P1;
  end if;

  if is_bad(P2,data) then
    xt,bt,index:=local_coord(P2,tadicprec(data,e),data);
    P2`xt:=xt;       
    P2`bt:=bt;       
    P2`index:=index; 
    if not is_bad(P1,data) then
      Qp:=Parent(P2`x);
      Qpa<a>:=PolynomialRing(Qp);
      K<a>:=TotallyRamifiedExtension(Qp,a^e-p);
    end if;
    format:=recformat<x,b,inf,xt,bt,index>;
    S2:=rec<format|>;                                                    
    S2`inf:=P2`inf;
    S2`x:=Evaluate(xt,a);
    S2`b:=[Evaluate(bt[i],a):i in [1..d]];
  else
    xt,bt,index:=local_coord(P2,tadicprec(data,1),data);
    P2`xt:=xt;       
    P2`bt:=bt;       
    P2`index:=index; 
    S2:=P2;
  end if;

  // Split up the integral and compute the tiny ones.

  tinyP1toS1,NP1toS1:=tiny_integrals_on_basis(P1,S1,data);
  tinyP2toS2,NP2toS2:=tiny_integrals_on_basis(P2,S2,data);

  FS1:=frobenius_pt(S1,data);
  FS2:=frobenius_pt(S2,data);
  //JSB edit 03/31/21
  if is_bad(S1,data) and not is_very_bad(S1,data) then
    tinyP1toFS1,NP1toFS1:=tiny_integrals_on_basis(P1,FS1,data);
    tinyS1toFS1 := tinyP1toFS1 - tinyP1toS1;
    NS1toFS1:=Minimum([NP1toFS1,NP1toS1]);
  else 
    tinyS1toFS1,NS1toFS1:=tiny_integrals_on_basis(S1,FS1,data:P:=P1); 
  end if;
  //JSB edit 04/17/21
  if is_bad(S2,data) and not is_very_bad(S2,data) then
    tinyP2toFS2,NP2toFS2:=tiny_integrals_on_basis(P2,FS2,data);
    tinyS2toFS2 := tinyP2toFS2 - tinyP2toS2;
    NS2toFS2:=Minimum([NP2toFS2,NP2toS2]);
  else
      tinyS2toFS2,NS2toFS2:=tiny_integrals_on_basis(S2,FS2,data:P:=P2); 
  end if;
  NIP1P2:=Minimum([NP1toS1,NP2toS2,NS1toFS1,NS2toFS2]);  

  // Evaluate all functions.

  I:=[];
  for i:=1 to #basis do
    f0iS1,Nf0iS1:=evalf0(f0list[i],S1,data);
    f0iS2,Nf0iS2:=evalf0(f0list[i],S2,data);
    finfiS1,NfinfiS1:=evalfinf(finflist[i],S1,data);
    finfiS2,NfinfiS2:=evalfinf(finflist[i],S2,data);
    fendiS1,NfendiS1:=evalfend(fendlist[i],S1,data);
    fendiS2,NfendiS2:=evalfend(fendlist[i],S2,data);
    NIP1P2:=Minimum([NIP1P2,Nf0iS1,Nf0iS2,NfinfiS1,NfinfiS2,NfendiS1,NfendiS2]);
    I[i]:=(K!f0iS1)-(K!f0iS2)+(K!finfiS1)-(K!finfiS2)+(K!fendiS1)-(K!fendiS2)-(K!tinyS1toFS1[i])+(K!tinyS2toFS2[i]);
  end for; 

  valIP1P2:=Minimum([Valuation(I[i])/Valuation(K!p):i in [1..#basis]]);

  mat:=(F-IdentityMatrix(RationalField(),#basis));
  valdet:=Valuation(Determinant(mat),p);
  mat:=mat^-1;
  Nmat:=N-valdet-delta;
  valmat:=Minimum([Valuation(e,p):e in Eltseq(mat)]);

  NIP1P2:=Minimum([NIP1P2+valmat,Nmat+valIP1P2]);                            
  
  IS1S2:=Vector(I)*Transpose(ChangeRing(mat,K));    // Solve the linear system.
  IP1P2:=IS1S2+ChangeRing(tinyP1toS1,K)-ChangeRing(tinyP2toS2,K);
  IP1P2,Nround:=round_to_Qp(IP1P2);

  assert Nround ge NIP1P2;                          // Check that rounding error is within error bound.                          

  NIP1P2:=Ceiling(NIP1P2);

  for i:=1 to #basis do
    IP1P2[i]:=IP1P2[i]+O(Parent(IP1P2[i])!p^(NIP1P2));
  end for;

  return IP1P2,NIP1P2;
end function;


coleman_integral:=function(P1,P2,dif,data:e:=1,IP1P2:=0,NIP1P2:=0);

  // Integral of 1-form dif from P1 to P2.

  Q:=data`Q; p:=data`p; N:=data`N; Nmax:=data`Nmax; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  G0:=data`G0; Ginf:=data`Ginf; red_list_fin:=data`red_list_fin; red_list_inf:=data`red_list_inf;
  basis:=data`basis; integrals:= data`integrals; quo_map:=data`quo_map;

  coefs,f0,finf,fend:=reduce_with_fs(dif,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); 

  if NIP1P2 eq 0 then 
    IP1P2,NIP1P2:=coleman_integrals_on_basis(P1,P2,data:e:=e);
  end if;
  
  f0P1,Nf0P1:=evalf0(f0,P1,data);
  f0P2,Nf0P2:=evalf0(f0,P2,data);
  finfP1,NfinfP1:=evalfinf(finf,P1,data);
  finfP2,NfinfP2:=evalfinf(finf,P2,data);
  fendP1,NfendP1:=evalfend(fend,P1,data);
  fendP2,NfendP2:=evalfend(fend,P2,data);

  IdifP1P2:=f0P2-f0P1+finfP2-finfP1+fendP2-fendP1;
  NIdifP1P2:=Minimum([Nf0P1,Nf0P2,NfinfP1,NfinfP2,NfendP1,NfendP2]);
  
  for i:=1 to #coefs do
    IdifP1P2:=IdifP1P2+coefs[i]*IP1P2[i];
    NIdifP1P2:=Minimum(NIdifP1P2,NIP1P2+Valuation(coefs[i],p));
  end for;

  NIdifP1P2:=Ceiling(NIdifP1P2);
  IdifP1P2:=IdifP1P2+O(Parent(IdifP1P2)!p^NIdifP1P2);

  return IdifP1P2, NIdifP1P2;

end function;

function set_point_affine(P, data)
  x0, y0 := Explode(P);
  r := data`r; d := Degree(data`Q);

  if x0 in RationalField() then
    K:=pAdicField(data`p,data`N);
  else
    K:=Parent(x0);
  end if;
  x0:=K!x0; y0:=K!y0;
  
  if Valuation(x0) ge 0 then // affine disk
    if Valuation(Evaluate(r,x0)) eq 0 then // finite good point
      return set_point(P[1], P[2], data);
    else
     b := [0 : i in [1..d]];
      for i:=1 to d do
        for j:=1 to d do
           b[i] +:= Evaluate(data`W0[i,j],x0)*y0^(j-1);
        end for;
      end for;
      return set_bad_point(x0, b, false, data);
    end if;
  else 
    b := [0 : i in [1..d]];
    for i:=1 to d do
      for j:=1 to d do
         b[i] +:= Evaluate(data`Winf[i,j],x0)*y0^(j-1);
      end for;
    end for;
    return set_bad_point(1/x0, b, true, data);
  end if;
end function;


function coleman_integrals_on_basis_divisors(D, E, data)
  // assume D and E are zero cycles on X(Qp), currently not containing a point at infinity
  assert #D eq #E;
  D_pts := [set_point_affine(P, data) : P in D];
  E_pts := [set_point_affine(P, data) : P in E];

  return &+[coleman_integrals_on_basis(D_pts[i], E_pts[i], data) : i in [1..#D]];
end function;


function to_Qxzzinvd(w, data)
  Q := data`Q; p := data`p; N := data`N;
  O,Ox,S,R:=getrings(p,N);
  d := Degree(Q);
  w1 := RSpace(S,d)!0;
  for i:=1 to d do
    w1[i] := R!(Ox!Coefficients(w[i]));
  end for;
  return convert_to_Qxzzinvd(w1, Q);
end function;
