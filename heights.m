/////////////////////////////////////
// functions for computing heights //
/////////////////////////////////////

// July 21: JSM/JB added precision estimates



function frob_equiv_iso(G,data,N)

  // Given a matrix G defining Frob^-1 on a mixed extension this returns s^phi.

  p:=data`p; g:=data`g; F:=data`F; //N:=data`N; 

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

  return s_phi, Min(N, minprec(s_phi));

end function;


function parallel_transport(P1,P2,Z,eta,data:prec:=0,N:=0)

  // Computes the parallel transport map of the unipotent 
  // connection Lambda defined by Z,eta from P1 to P2.

  // TODO: on a finite bad disk, make sure to take local parameters centered at the (very) bad point.

  x1:=P1`x; x2:=P2`x; b1:=P1`b; b2:=P2`b; Q:=data`Q; p:=data`p; W0:=data`W0; Winf:=data`Winf; r:=data`r; basis:=data`basis; g:=data`g;
  d:=Degree(Q); lc_r:=LeadingCoefficient(r); K:=Parent(x1);

  if IsZero(N) then N:=data`N; end if;

  C:=IdentityMatrix(K,2*g+2);
  if are_equal_records(P1, P2) then
    return C,data`N;
  end if;
    
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
    assert IsZero(Coefficient(omegax[i],-1)); // second kind
  end for;

  // tiny single integrals
  //
  // compute p-adic precision
  e:=Degree(Parent(x2)); // e=1 in our applications
  maxpoleorder:=-(Minimum([Valuation(omegax[i]): i in [1..2*g]])); 
  maxdegree:=Maximum([Degree(omegax[i]): i in [1..2*g]]);
  mindegree:=Minimum([Degree(omegax[i]): i in [1..2*g]]);
  Nsingle := tiny_integral_prec(prec,1,maxpoleorder,maxdegree,mindegree,val,data);

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

  val_eta := Min([0] cat [Valuation(c, p) : c in Eltseq(eta)]);
  maxpoleorder:=-Valuation(dgx);
  maxdegree:=Degree(dgx);
  mindegree:=maxdegree;
  Ndouble := Integers()!tiny_integral_prec(prec,1,maxpoleorder,maxdegree,mindegree,val,data : N := N+Min(val_eta, -Floor(log(p,N))));

  gx:=Integral(dgx);

  if index eq 0 then // x-x(P1) is the local coordinate
    doubleintegral:=Evaluate(gx,x2-x1);
  else // b[index]-b[index](P1) is the local coordinate
    doubleintegral:=Evaluate(gx,b2[index]-b1[index]);
  end if;

  C:=IdentityMatrix(pAdicField(p,Ndouble), 2*g+2);
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

  return C, Ndouble;

end function;


function parallel_transport_to_z(P,Z,eta,data:prec:=0,N:=0)

  // Computes the parallel transport map of the unipotent 
  // connection Lambda defined by Z,eta from P to to an
  // arbitrary point in its residue disk as a power series
  // in the local parameter there. The series expansions xt
  // and bt of the coordinates on the curve in terms of this 
  // local parameter are also returned.

  x0:=P`x; b:=P`b; Q:=data`Q; p:=data`p; basis:=data`basis; g:=data`g; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x0);
  if IsZero(N) then N:=data`N; end if;

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
  // TODO: These get recomputed a lot. Maybe store them and update if we need them to
  // larger precision?

  derxt:=Qt!Kt!Derivative(xt); 
  omegax:=[];
  for i:=1 to 2*g+infpoints-1 do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    omegax[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    omegax[i]:=Qt!Kt!omegax[i];
    assert IsZero(Coefficient(omegax[i],-1)); // second kind
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


height:=function(Phi,betafil,gammafil,splitting,data)

  // This function computes the local p-adic height at p of a 
  // filtered phi-module given its Frobenius 
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


E1_tensor_E2:=function(Phi,betafil,changebasis,data,Salpha)

  changebasis:=ChangeRing(changebasis,Salpha);
  g:=data`g;
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

  n := g*(g+1) div 2;
  M := ZeroMatrix(Parent(divisors[1,1,1,1]), n, n);

  integrals := [coleman_integrals_on_basis_divisors(t[2], t[1], data) : t in divisors];
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



function new_height_coefficients(divisors, intersections, factors, local_CG_heights_p, data)
  // TODO: arbitrary g
  // Same as height_coefficients, but allow more general divisors.


  g := data`g;
  if g ne 2 then
    error "Only genus 2 currently implemented";
  end if;

  p := data`p;
  Qp := pAdicField(p, data`N);

  local_CG_heights_away := [ ];
  for i := 1 to #intersections do
   local_CG_heights_away[i] := IsEmpty(intersections[i]) select 0
           else &+[Log(Qp!t[1])*t[2] : t in intersections[i] | t[1] ne p];
  end for;

  factors1, factors2 := Explode(factors);
  heights_basis := [local_CG_heights_p[i] - local_CG_heights_away[i] : i in [1..#local_CG_heights_p]];
  h1 := heights_basis[1]/(factors1[1,1]*factors2[1,1]);
  h2 := heights_basis[2]/(factors1[1,2]*factors2[1,2]);
  h3 := heights_basis[3]/(factors1[2,2]*factors2[2,2]);
  regulator := h1*h3-h2^2;

  n := g*(g+1) div 2;
  M := ZeroMatrix(Parent(divisors[1,1,1,1]), n, n);

  
  integrals := [coleman_integrals_on_basis_divisors(t[2], t[1], data) : t in divisors];
  integrals[1,1] /:= factors1[1,1];
  integrals[1,2] /:= factors1[1,1];
  integrals[2,1] /:= factors2[2,2];
  integrals[2,2] /:= factors2[2,2];

  M[1,1] := integrals[1,1]*integrals[1,1];
  M[1,2] := 1/2*(integrals[1,1]*integrals[1,2]+integrals[1,1]*integrals[1,2]);
  M[1,3] := integrals[1,2]*integrals[1,2];
  M[2,1] := integrals[1,1]*integrals[2,1];
  M[2,2] := 1/2*(integrals[1,1]*integrals[2,2]+integrals[2,1]*integrals[1,2]);
  M[2,3] := integrals[1,2]*integrals[2,2];
  M[3,1] := integrals[2,1]*integrals[2,1];
  M[3,2] := 1/2*(integrals[2,1]*integrals[2,2]+integrals[2,1]*integrals[2,2]);
  M[3,3] := integrals[2,2]*integrals[2,2];

  assert Determinant(M) ne 0;  // Points should be independent
  heights_vector := Matrix(BaseRing(M),n, 1, [h1,h2,h3]);

  alphas := Eltseq(M^-1*heights_vector);
  return [[alphas[1], alphas[2]], [0, alphas[3]]], regulator;
end function;

