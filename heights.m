/////////////////////////////////////
// functions for computing heights //
/////////////////////////////////////


function frob_equiv_iso(G,data)

  // Given a matrix G defining Frob^-1 on a mixed extension this returns s^phi.

  p:=data`p; N:=data`N; g:=data`g; F:=data`F;

  Qp:=pAdicField(p,N);  

  FQp:=ZeroMatrix(Qp,2*g,2*g);
  for i:=1 to 2*g do
    for j:=1 to 2*g do
      FQp[i,j]:=Qp!F[i,j];
    end for;
  end for;
  
  fx:=Matrix(Qp,2*g,1,[Qp!G[i+1,1]:i in [1..2*g]]);
  gx:=Matrix(Qp,1,2*g,[Qp!G[2*g+2,i+1]:i in [1..2*g]]);
  hx:=Matrix(Qp,1,1,[Qp!G[2*g+2,1]]);
  
  I := IdentityMatrix(Qp,2*g);
  
  hxprime := 1/(1-p)*(gx*((I-FQp)^-1)*fx+hx);
  
  s_phi := IdentityMatrix(Qp,2*g+2);
  for i in [1..2*g] do
    s_phi[i+1,1] := ((I-FQp)^(-1)*fx)[i,1];
    s_phi[2*g+2,i+1] := (gx*(FQp-p*I)^-1)[1,i];
  end for;
  s_phi[2*g+2,1] := hxprime[1,1];

  return s_phi;

end function;


function parallel_transport(P1,P2,Z,eta,data:prec:=0)

  // Computes the parallel transport map of the unipotent 
  // connection Lambda defined by Z,eta from P1 to P2.

  // TODO: on a finite bad disk, make sure to take local parameters centered at the (very) bad point.

  x1:=P1`x; x2:=P2`x; b1:=P1`b; b2:=P2`b; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf; r:=data`r; basis:=data`basis; g:=data`g;
  d:=Degree(Q); lc_r:=LeadingCoefficient(r); K:=Parent(x1);

  if not lie_in_same_disk(P1,P2,data) then
    error "the points do not lie in the same residue disk";
  end if;

  xt,bt,index:=local_coord(P1,prec,data); 

  if index eq 0 then // x-x(P1) is the local coordinate
    val:=Valuation(x2-x1);
  else // b[index]-b[index](P1) is the local coordinate
    val:=Valuation(b2[index]-b1[index]);
  end if;

  Qt<t>:=LaurentSeriesRing(RationalField(),prec);
  xt:=Qt!xt;
  btnew:=[Qt|];
  for i:=1 to d do
    btnew[i]:=Qt!bt[i];
  end for;
  bt:=Vector(btnew);

  Kt:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

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

  // determine the number of points at infinity

  FF:=fun_field(data);
  infplaces:=InfinitePlaces(FF);
  infpoints:=0;
  for i:=1 to #infplaces do
    infpoints:=infpoints+Degree(infplaces[i]);
  end for;

  // compute the powerseries expansions of the basis elements of H^1(Y)

  derxt:=Qt!Kt!Derivative(xt); 
  omegax:=[];
  for i:=1 to 2*g+infpoints-1 do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    omegax[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    omegax[i]:=Qt!Kt!omegax[i];
    if Coefficient(omegax[i],-1) ne 0 then
      omegax[i]:=omegax[i]-Coefficient(omegax[i],-1)*Kt.1^(-1);
    end if;
  end for;

  // tiny single integrals

  Omegax:=[];
  for i:=1 to 2*g do
    Omegax[i]:=-Integral(omegax[i]);
  end for;

  singleintegrals:=[];
  for i:=1 to 2*g do
    if index eq 0 then // x-x(P1) is the local coordinate
      singleintegrals[i]:=Evaluate(Omegax[i],x2-x1);
    else // b[index]-b[index](P1) is the local coordinate
      singleintegrals[i]:=Evaluate(Omegax[i],b2[index]-b1[index]);
    end if;
  end for;
 
  // tiny double integral

  dgx:=0;
  for i:=1 to 2*g do
    for j:=1 to 2*g do
      dgx:=dgx+omegax[i]*(K!Z[i,j])*Omegax[j]; 
    end for;
  end for;
  for i:=1 to infpoints-1 do
    dgx:=dgx-eta[i]*omegax[2*g+i];
  end for;  
  gx:=Integral(dgx);

  if index eq 0 then // x-x(P1) is the local coordinate
    doubleintegral:=Evaluate(gx,x2-x1);
  else // b[index]-b[index](P1) is the local coordinate
    doubleintegral:=Evaluate(gx,b2[index]-b1[index]);
  end if;

  C:=IdentityMatrix(K,2*g+2);
  // entries in first column (except last one) 
  for i:=1 to 2*g do
    C[i+1,1]:=-singleintegrals[i];
  end for;
  // entries in the last row (except first one)
  for i:=1 to 2*g do
    for j:=1 to 2*g do
      C[2*g+2,i+1]:=C[2*g+2,i+1]-singleintegrals[j]*(K!Z[j,i]);
    end for;
  end for;
  // bottom left entry
  C[2*g+2,1]:=-doubleintegral;

  return C;

end function;


function parallel_transport_to_z(P,Z,eta,data:prec:=0)

  // Computes the parallel transport map of the unipotent 
  // connection Lambda defined by Z,eta from P to to an
  // arbitrary point in its residue disk as a power series
  // in the local parameter there. The series expansions xt
  // and bt of the coordinates on the curve in terms of this 
  // local parameter are also returned.

  x0:=P`x; b:=P`b; Q:=data`Q; p:=data`p; N:=data`N; basis:=data`basis; g:=data`g; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x0);

  P1:=P; // TODO: on a finite bad disk, make sure to take local parameters centered at the (very) bad point.
  x1:=P1`x;

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

  Kt:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

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

  // determine the number of points at infinity

  FF:=fun_field(data);
  infplaces:=InfinitePlaces(FF);
  infpoints:=0;
  for i:=1 to #infplaces do
    infpoints:=infpoints+Degree(infplaces[i]);
  end for;

  // compute the powerseries expansions of the basis elements of H^1(Y)

  derxt:=Qt!Kt!Derivative(xt); 
  omegax:=[];
  for i:=1 to 2*g+infpoints-1 do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    omegax[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    omegax[i]:=Qt!Kt!omegax[i];
    if Coefficient(omegax[i],-1) ne 0 then
      omegax[i]:=omegax[i]-Coefficient(omegax[i],-1)*Kt.1^(-1);
    end if;
  end for;

  // tiny single integrals

  Omegax:=[];
  for i:=1 to 2*g do
    Omegax[i]:=-Integral(omegax[i]);
  end for;

  // tiny double integral

  dgx:=0;
  for i:=1 to 2*g do
    for j:=1 to 2*g do
      dgx:=dgx+omegax[i]*(K!Z[i,j])*Omegax[j]; 
    end for;
  end for;
  for i:=1 to infpoints-1 do
    dgx:=dgx-eta[i]*omegax[2*g+i];
  end for;  
  gx:=Integral(dgx);

  C:=IdentityMatrix(Parent(gx),2*g+2);
  // entries in first column (except last one) 
  for i:=1 to 2*g do
    C[i+1,1]:=-Omegax[i];
  end for;
  // entries in the last row (except first one)
  for i:=1 to 2*g do
    for j:=1 to 2*g do
      C[2*g+2,i+1]:=C[2*g+2,i+1]-Omegax[j]*(K!Z[j,i]);
    end for;
  end for;
  // bottom left entry
  C[2*g+2,1]:=-gx;

  xt:=xtold;
  bt:=Vector(btold);

  return C,xt,bt;

end function;

function parallel_transport_from_b(P,Z,eta,data,kb:prec:=0,printlevel:=0)
  //P will always be the point bQ

  x0 := P`x; b:=P`b; Q:=data`Q; p:=data`p; N:=data`N; basis:=data`basis; g:=data`g; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  b0 := teichmueller_pt(P,data); 
  d  := Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x0);

  P1:=P; // TODO: on a finite bad disk, make sure to take local parameters centered at the (very) bad point.
  x1:=P1`x;

  print "P (bQ): ", P;

  xt,bt,index:=local_coord(P1,prec,data); 

  print "xt: ", xt;

  xtold:=xt;
  btold:=bt;

  Qt<t>:=LaurentSeriesRing(RationalField(),prec);
  xt:=Qt!xt;
  btnew:=[Qt|];
  for i:=1 to d do
    btnew[i]:=Qt!bt[i];
  end for;
  bt:=Vector(btnew);

  Kt:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

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

  // determine the number of points at infinity

  FF:=fun_field(data);
  infplaces:=InfinitePlaces(FF);
  infpoints:=0;
  for i:=1 to #infplaces do
    infpoints:=infpoints+Degree(infplaces[i]);
  end for;

  // compute the powerseries expansions of the basis elements of H^1(Y)

  derxt:=Qt!Kt!Derivative(xt); 
  omegax:=[];
  for i:=1 to 2*g+infpoints-1 do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    omegax[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    omegax[i]:=Qt!Kt!omegax[i];
    if Coefficient(omegax[i],-1) ne 0 then
      omegax[i]:=omegax[i]-Coefficient(omegax[i],-1)*Kt.1^(-1);
    end if;
  end for;

  // tiny single integrals

  Omegax:=[];
  for i:=1 to 2*g do
    Omegax[i]:=-Integral(omegax[i]);
  end for;

  // tiny double integral

  dgx:=0;
  for i:=1 to 2*g do
    for j:=1 to 2*g do
      dgx:=dgx+omegax[i]*(K!Z[i,j])*Omegax[j]; 
    end for;
  end for;
  for i:=1 to infpoints-1 do
    dgx:=dgx-eta[i]*omegax[2*g+i];
  end for;  
  gx:=Integral(dgx);

  C:=IdentityMatrix(Parent(gx),2*g+2);

  // entries in first column (except last one) 
  for i:=1 to 2*g do
    C[i+1,1]:= Omegax[i]; 
  end for;

  // entries in the last row (except first one)
  for i:=1 to 2*g do
    for j:=1 to 2*g do
      C[2*g+2,i+1]:=(C[2*g+2,i+1]-Omegax[j]*(K!Z[j,i]));
    end for;
//     C[2*g+2,i+1] := - C[2*g+2,i+1];
  end for;
  // bottom left entry
  C[2*g+2,1]:= gx; 

  xt:=xtold;
  bt:=Vector(btold);

  print "xt: ", xt;
  param:=(b0`x - P`x);  
  if printlevel gt 1 then
    print "param: ", param;
    print "Evaluating xt at param: ", Evaluate(xt,param);
    print "b0's x-coord: ", b0`x;
  end if;
  for i :=1 to 2*g+2 do
    for j:=1 to 2*g+2 do
       C[i,j]:= Evaluate(C[i,j],param);
    end for;
  end for;
  
  return C,xt,bt;

end function;


// function parallel_transport_from_b2(P,Z,eta,data,kb:prec:=0)
// 
// 	x0:=P`x; b:=P`b; Q:=data`Q; p:=data`p; N:=data`N; basis:=data`basis; g:=data`g; r:=data`r; W0:=data`W0; Winf:=data`Winf;
// 	b0:=teichmueller_pt(P,data); 
// 	d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x0);
// 	
// 	C := parallel_transport(b0,P,Z,eta,data:prec:=prec);
// 	for i := 1 to 2*g do
// 		C[2*g+2,i+1] := -C[2*g+2,i+1];
// 	end for;
// 
// 	return C;
// 
// end function;



height:=function(Phi,betafil,gammafil,splitting,data)

  // This function computes the p-adic height of a filtered phi-module given its Frobenius 
  // matrix Phi and splitting of the Hodge filtration determined by gamma_fil, beta_fil.

  p:=data`p; g:=data`g;

  S:=BaseRing(Phi);
  splitting:=ChangeRing(splitting,S);

  betafil    := Vector(S,[0 : i in [1..g]] cat Eltseq(betafil));
  gammafil   := S!gammafil;
  alpha1g    := Vector(S,g,[Phi[i+1,1]:i in [1..g]]);
  alpha      := Vector(S,2*g,[Phi[i+1,1]:i in [1..2*g]]);
  s1alphaphi := ChangeRing(alpha1g*Transpose(splitting),S);
  s2alphaphi := alpha-alpha1g*Transpose(splitting);
  gammaphi   := Phi[2*g+2,1];
  betaphi    := Vector(S,2*g,[Phi[2*g+2,i+1]:i in [1..2*g]]);
  
  return gammaphi-gammafil-DotProduct(s1alphaphi,betaphi)-DotProduct(s2alphaphi,betafil);

end function;


E1_tensor_E2:=function(Phi,betafil,basisH0star,data,Salpha)

  // TODO comment

  g:=data`g;
  changebasis:=Matrix(basisH0star)^(-1);
  changebasis:=ChangeRing(changebasis,Salpha);

  E1 := Vector(Salpha,[Phi[i,1] : i in [2..g+1]])*changebasis; 
  E2 := Vector(Salpha,[Phi[2*g+2,g+1+j] - betafil[j] : j in [1..g]])*changebasis;

  return &+[E1[i]*Salpha.1^(i-1) : i in [1..g]] * &+[E2[i]*Salpha.1^(i-1) : i in [1..g]], E1, E2;

end function;


expand_algebraic_function:=function(P,g,data,N,prec)

  // expands the algebraic function g with respect to the chosen parameter at P.
  // the parameter is the same as in parallel_transport_to_z.

  p:=data`p;
  xt,bt,index:=local_coord(P,prec,data); 

  Qt<t>:=LaurentSeriesRing(pAdicField(p,N),prec);
  xt:=Qt!xt;
  bt:=[Qt!bt[i]:i in [1..#bt]];
  return &+[Evaluate(g[i],xt)*bt[i]:i in [1..NumberOfColumns(g)]];
end function;


function height_coefficients(divisors, intersections, local_CG_heights_p, data)
  // TODO: arbitrary g

  local_CG_heights_away := [ ];
  p := data`p;
  g := data`g;
  if g ne 2 then
    error "Only genus 2 currently implemented";
  end if;
  Qp := pAdicField(p, data`N);

  for i := 1 to #intersections do
   local_CG_heights_away[i] := IsEmpty(intersections[i]) select 0
           else &+[Log(Qp!t[1])*t[2] : t in intersections[i] | t[1] ne p];
  end for;

  heights_basis := [local_CG_heights_p[i] + local_CG_heights_away[i] : i in [1..#local_CG_heights_p]];
  //long_divisors := [divisors[1], divisors[1], divisors[1], divisors[2], divisors[2], divisors[2]];
  //alphas := height_fitting_g2(long_divisors, heights_basis, data);

  n := g*(g+1) div 2;
  M := ZeroMatrix(Parent(divisors[1,1,1,1]), n, n);

  integrals := [coleman_integrals_on_basis_divisors(t[2], t[1], data) : t in divisors];
  //for i,j in [1..N] do
    //M[i,j] := 1/2*(integrals[1,1]*integrals[2,2]+integrals[2,1]*integrals[1,2]); 
  //end for;
  M[1,1] := integrals[1,1]*integrals[1,1];
  M[1,2] := 1/2*(integrals[1,1]*integrals[1,2]+integrals[1,1]*integrals[1,2]);
  M[1,3] := integrals[1,2]*integrals[1,2];
  M[2,1] := integrals[1,1]*integrals[2,1];
  M[2,2] := 1/2*(integrals[1,1]*integrals[2,2]+integrals[2,1]*integrals[1,2]);
  M[2,3] := integrals[1,2]*integrals[2,2];
  M[3,1] := integrals[2,1]*integrals[2,1];
  M[3,2] := 1/2*(integrals[2,1]*integrals[2,2]+integrals[2,1]*integrals[2,2]);
  M[3,3] := integrals[2,2]*integrals[2,2];

  assert Determinant(M) ne 0;
  heights_vector := Matrix(BaseRing(M),n, 1, heights_basis);

  alphas := Eltseq(M^-1*heights_vector);
  return [[alphas[1], alphas[2]], [0, alphas[3]]];
end function;

