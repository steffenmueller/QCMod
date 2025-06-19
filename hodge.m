//////////////////////////////////////////////
// Functions for computing Hodge structures //
//////////////////////////////////////////////

function hodge_data_generic(data, Z, bpt : prec:=5)
  //{Compute the 1-form eta, as a vector of coefficients w.r.t. basis[i] for i=2g+1,...,2g+k-1 where k is the number of points lying over x=infinity, and the vector of constants beta_fil and the function gamma_fil. This only works when the Galois action on the places at infinity is maximal.}

  Q := data`Q;
  g := data`g;
  r := data`r;
  W0 := data`W0;
  basis := data`basis;
  d := Degree(Q);
  K := BaseRing(BaseRing(Q));

  // find the points at infinity:

  Kx := RationalFunctionField(K);
  Kxy := PolynomialRing(Kx);

  FF := function_field(Q); // function field of curve over K
  infplaces:=InfinitePlaces(FF);
  assert #infplaces eq 1; // TODO: generalize. 

  split := K;
  finf := CharacteristicPolynomial(ResidueClassField(infplaces[1]).1);
  split := SplittingField(finf);
  finfsplit := ChangeRing(finf, split); 
  assert SymmetricGroup(Degree(finf)) eq GaloisGroup(finf); // TODO:
                                                            // generalize

  rts_tuples := Roots(finfsplit);
  rts := [t[1] : t in rts_tuples];
  subfields := [* *]; 
  infplacesext := [* *];
  Kinfxs := [];
  Kinfs := [];
  FFKinfs :=[];
  for rt in rts do
    subfield, embedding := sub<split | rt>;
    // K(rt), K(rt) c-> split
    Append(~subfields, <subfield, embedding>);
    Kinf := subfield;
    Kinfx := RationalFunctionField(Kinf);
    Kinfxy := PolynomialRing(Kinfx);
    FFKinf := FunctionField(Kinfxy!Q);
    infplacesKinf := InfinitePlaces(FFKinf); // places at infinity 
    deg1_infplaces := [P : P in infplacesKinf | Degree(P) eq 1];
    assert #deg1_infplaces eq 1;
    Append(~Kinfxs, Kinfx);
    Append(~Kinfs, Kinf);
    Append(~FFKinfs, FFKinf);
    Append(~infplacesext, deg1_infplaces[1]); 
  end for;

  // compute the expansions omega_x, Omega_x, b^0_x for all points x at
  // infinity, working over the different K(x)

  omegax:=[**]; // expansions of omega
  Omegax:=[**]; // expansions of Omega
  b0funx:=[**]; // expansions of b^0
  xfunx:=[**];  // expansions of x
  omegaZOmega:=[* *];  // expansions of omegaZOmega

  for i:=1 to #infplacesext do

    P:=infplacesext[i];
    Kinfx := Kinfxs[i];
    Kinf := Kinfs[i];
    FFKinf := FFKinfs[i];
    xfunx[i]:=Expand(FFKinf!Kinfx.1,P : RelPrec:=prec+3); 
    dxdt:=Derivative(xfunx[i]);
    
    rx := ChangeRing(r, Kinf);
    //Evaluate(r,Kinfx.1); Parent(Evaluate(rx,Kinfx.1));
    zinv:=Expand(LeadingCoefficient(rx)/(FFKinf!Evaluate(rx,Kinfx.1)),P : RelPrec:=prec+3);

    b0funKinf:=[]; // functions b^0 (finite integral basis)
    W0x := ChangeRing(W0, Kinfx);
    for k:=1 to d do
      b0k:=FFKinf!0;
      for j:=1 to d do
        b0k +:= Evaluate(W0x[k,j],Kinfx.1)*FFKinf.1^(j-1);
      end for;
      b0funKinf[k]:=b0k;
    end for;

    L:=[];
    basisx := [];
    for k:=1 to #basis do
      Append(~basisx, [ChangeRing(w, Kinf) : w in Eltseq(basis[k])]);
    end for;

    for k:=1 to (2*g+#infplacesext-1) do
      fun:=FFKinf!0;
      for j:=1 to d do
        fun +:= Evaluate(basisx[k][j],Kinfx.1)*b0funKinf[j];
      end for;
      L[k]:=fun;
    end for;
    
    omegaP:=[];
    for j:=1 to 2*g+#infplacesext-1 do
      omegaP[j]:=Expand(L[j],P : RelPrec:=prec+3)*dxdt*zinv;
    end for;
    Append(~omegax,omegaP);
    
    OmegaP:=[];
    for j:=1 to 2*g do
      OmegaP[j]:=Integral(omegaP[j]); 
    end for;
    Append(~Omegax,OmegaP);

    b0funP:=[];
    for j:=1 to d do
      b0funP[j]:=Expand(b0funKinf[j],P : RelPrec:=prec+3);
    end for;
    Append(~b0funx,b0funP);

    omegaZOmegaP:=Kinf!0;
    for j:=1 to 2*g do
      for k:=1 to 2*g do
//Parent(omegax[i][j]); Parent(Z[j,k]); Parent(Kinf!(Z[j,k])); Parent(Omegax[i][k]);
        omegaZOmegaP +:= omegax[i][j]*Kinf!(Z[j,k])*Omegax[i][k];
      end for;
    end for;
    Append(~omegaZOmega, omegaZOmegaP);
  end for;

  // set up the linear system eta*A=v satisfied by eta
  
  v:=[];
  A:=ZeroMatrix(split,#infplacesext-1,#infplacesext);
  for i:=1 to #infplacesext do
    embedding := subfields[i,2];
    v[i]:=-embedding(Coefficient(omegaZOmega[i],-1)); // residue of eta at i-th point of infinity 
    for j:=1 to #infplacesext-1 do
      A[j,i]:=embedding(Coefficient(omegax[i][2*g+j],-1)); // residue of omega_{2g+j} at i-th point at infinity
    end for;
  end for;
  //

  eta := Solution(A,Vector(v)); // solve for eta
  eta := ChangeRing(eta,K);

  gx:=[**]; // functions g_x
  for i:=1 to #infplacesext do
    Kinf := Kinfs[i];
    dgxi:=omegaZOmega[i]; 
    for j:=1 to (#infplacesext-1) do
      dgxi +:= Kinf!(eta[j])*omegax[i][2*g+j]; 
    end for;
    gx[i]:=Integral(dgxi);

    for j:=1 to 2*g do
      for k:=g+1 to 2*g do
        gx[i] +:= Omegax[i][j]*Kinf!(Z[j,k])*Omegax[i][k]; 
      end for;
    end for;
  end for;


  poleorder:=0;
  for i:=1 to #infplacesext do
    for j:=1 to 2*g do
      poleorder:=Minimum(poleorder,Valuation(Omegax[i][j]));
    end for;
  end for;
  poleorder_Omegax := poleorder;

  for i:=1 to #infplacesext do
    val:=Valuation(gx[i]);
    poleorder:=Minimum(poleorder,val);
  end for;

  done:=false;
  degx:=0;
  while not done do // try larger and larger degree in x
    
    for i:=1 to #infplacesext do
      for j:=1 to d do
        poleorder:=Minimum(poleorder,Valuation(b0funx[i][j])+degx*Valuation(xfunx[i]));
      end for;
    end for;

    v:=[]; // coefficients of principal parts of all gx 
    cnt:=0;
    for i:=1 to #infplacesext do
      embedding := subfields[i,2];
      for j:=poleorder to -1 do
        cnt +:= 1;
        v[cnt]:=embedding(Coefficient(gx[i],j));
      end for;
    end for;

    rows:=[];

    for i:=1 to g do
      row:=[];
      cnt:=0;
      for j:=1 to #infplacesext do
        embedding := subfields[j,2];
        for k:=poleorder to -1 do
          cnt +:= 1;
          row[cnt]:=embedding(Coefficient(Omegax[j][i+g],k)); // coefficients of principal part of Omegax_{i+g} at jth point at infinity
        end for; 
      end for;
      Append(~rows,row);
    end for;

    for i:=1 to d do
      for j:=0 to degx do
        row:=[];
        cnt:=0;
        for k:=1 to #infplacesext do
          embedding := subfields[k,2];
          for l:=poleorder to -1 do
            cnt +:= 1;
            row[cnt]:=embedding(Coefficient(b0funx[k][i]*xfunx[k]^j,l)); // coefficients of principal part of x^j*b^0_i at kth point at infinity
          end for;
        end for;
        Append(~rows,row);  
      end for;
    end for;   
    suc,sol := IsConsistent(Matrix(rows),Vector(v));
    if suc then
      done:=true;
    else // if no success, increase the degree in x
      degx +:= 1;
    end if;
  
  end while;

  // read off beta from solution

  beta:=[];
  for i:=1 to g do
    beta[i] := K!sol[i];
  end for;

  // read off gamma from solution
  Kt := PolynomialRing(K);
  gamma:=[];
  cnt:=g;
  for i:=1 to d do
    poly:=Kt!0;
    for j:=0 to degx do
      cnt +:= 1;
      poly +:= (K!sol[cnt])*Kt.1^j;
    end for;
    Append(~gamma, poly);
  end for;

  b0fun:=[]; // functions b^0 (finite integral basis)
  for i:=1 to d do
    b0i:=FF!0;
    for j:=1 to d do
      b0i +:= Evaluate(W0[i,j],Kx.1)*FF.1^(j-1);
    end for;
    b0fun[i]:=b0i;
  end for;

  // substract constant such that gamma(bpt)=0

  gamma_FF:=FF!0;
  for i:=1 to d do
    gamma_FF +:= Evaluate(gamma[i],Kx.1)*b0fun[i];
  end for;
  gamma[1] -:= Evaluate(gamma_FF,bpt); 
  return Vector(eta),Vector(beta),Vector(gamma),Integers()!poleorder_Omegax;

end function;


hodge_data:=function(data, Z, bpt: prec:=5)

  // Compute the 1-form eta, as a vector of coefficients
  // w.r.t. basis[i] for i=2g+1,...,2g+k-1 where k is the 
  // number of points lying over x=infinity.
  // prec is the relative precision to be used for the expansions

  try 
    // Check if the Galois action 
    // When the Galois action on the places at infinity is maximal, can
    // work over the ground field. If this isn't satisfied,
    // hodge_data_maximal throws an error
    eta, beta, gamma, poleorder := hodge_data_generic(data, Z, bpt : prec:=prec);
    return eta, beta, gamma, poleorder;
  catch e;  

    // work over the splitting field

    Q:=data`Q; g:=data`g; r:=data`r; W0:=data`W0; basis:=data`basis;

    d:=Degree(Q);

    // find the points at infinity:

    Qx:=RationalFunctionField(RationalField()); Qxy:=PolynomialRing(Qx);

    FF:=fun_field(data); // function field of curve over the rationals
    infplaces:=InfinitePlaces(FF);
    infplacesKinf := infplaces;

    Kinf:=RationalField();
    repeat 
      infdeg := &+[Degree(P) : P in infplacesKinf];
      for i:=1 to #infplacesKinf do
        if not IsOne(Degree(infplacesKinf[i])) then
        Kinf:=Compositum(Kinf,(NormalClosure(ResidueClassField(infplacesKinf[i])))); // field generated by points at infinity
        end if;
      end for;

      Kinfx:=RationalFunctionField(Kinf); Kinfxy:=PolynomialRing(Kinfx);

      finf:=Kinfxy!0;
      for i:=0 to d do
        for j:=0 to Degree(Coefficient(Q,i)) do
          finf:=finf+Coefficient(Coefficient(Q,i),j)*Kinfxy.1^i*Kinfx.1^j;
        end for;
      end for;  
      FFKinf:=FunctionField(finf); // function field of curve over Kinf


      infplacesKinf:=InfinitePlaces(FFKinf); // places at infinity all of degree 1, will be denoted by P
    until &and[IsOne(Degree(P)) : P in infplacesKinf];
    infdeg := &+[Degree(P) : P in infplacesKinf];
    
    b0funKinf:=[]; // functions b^0 (finite integral basis)
    for i:=1 to d do
      b0i:=FFKinf!0;
      for j:=1 to d do
        b0i:=b0i+Evaluate(W0[i,j],Kinfx.1)*FFKinf.1^(j-1);
      end for;
      b0funKinf[i]:=b0i;
    end for;

    L:=[];
    for i:=1 to (2*g+#infplacesKinf-1) do
      fun:=FFKinf!0;
      for j:=1 to d do
        fun:=fun+Evaluate(basis[i][j],Kinfx.1)*b0funKinf[j];
      end for;
      L[i]:=fun;
    end for;

    // compute the expansions omega_x, Omega_x, b^0_x

    omegax:=[]; // expansions of omega
    Omegax:=[]; // expansions of Omega
    b0funx:=[]; // expansions of b^0
    xfunx:=[];  // expansions of x

    for i:=1 to #infplacesKinf do

      P:=infplacesKinf[i];
      xfunx[i]:=Expand(FFKinf!Kinfx.1,P : RelPrec:=prec+3); 
      dxdt:=Derivative(xfunx[i]);
      
      zinv:=Expand(LeadingCoefficient(r)/(FFKinf!Evaluate(r,Kinfx.1)),P : RelPrec:=prec+3);
      
      omegaP:=[];
      for j:=1 to 2*g+#infplacesKinf-1 do
        omegaP[j]:=Expand(L[j],P : RelPrec:=prec+3)*dxdt*zinv;
      end for;
      omegax:=Append(omegax,omegaP);
      
      OmegaP:=[];
      for j:=1 to 2*g do
        OmegaP[j]:=Integral(omegaP[j]); 
      end for;
      Omegax:=Append(Omegax,OmegaP);

      b0funP:=[];
      for j:=1 to d do
        b0funP[j]:=Expand(b0funKinf[j],P : RelPrec:=prec+3);
      end for;
      b0funx:=Append(b0funx,b0funP);

    end for;

    // compute expansions of Omega*Z*omega at all points at infinity

    omegaZOmega:=[];
    for i:=1 to #infplacesKinf do
      omegaZOmegaP:=0;
      for j:=1 to 2*g do
        for k:=1 to 2*g do
          omegaZOmegaP:=omegaZOmegaP+omegax[i][j]*Z[j,k]*Omegax[i][k];
        end for;
      end for;
      omegaZOmega:=Append(omegaZOmega,omegaZOmegaP);
    end for;

    // set up the linear system eta*A=v satisfied by eta
    
    v:=[];
    A:=ZeroMatrix(Kinf,#infplacesKinf-1,#infplacesKinf);
    for i:=1 to #infplacesKinf do

      v[i]:=-Coefficient(omegaZOmega[i],-1); // residue of eta at i-th point of infinity 
      for j:=1 to #infplacesKinf-1 do
        A[j,i]:=Coefficient(omegax[i][2*g+j],-1); // residue of omega_{2g+j} at i-th point at infinity
      end for;
    end for;
    //

    eta:=Solution(A,Vector(v)); // solve for eta
    eta:=ChangeRing(eta,RationalField());

    gx:=[]; // functions g_x
    for i:=1 to #infplacesKinf do
      dgxi:=omegaZOmega[i]; 
      for j:=1 to (#infplacesKinf-1) do
        dgxi:=dgxi+eta[j]*omegax[i][2*g+j]; 
      end for;
      gx[i]:=Integral(dgxi);
    end for;

    OmegaZs2Omega:=[];
    for i:=1 to #infplacesKinf do
      OmegaZs2OmegaP:=0;
      for j:=1 to 2*g do
        for k:=g+1 to 2*g do
          OmegaZs2OmegaP:=OmegaZs2OmegaP+Omegax[i][j]*Z[j,k]*Omegax[i][k]; 
        end for;
      end for;
      OmegaZs2Omega[i]:=OmegaZs2OmegaP;
    end for;

    for i:=1 to #infplacesKinf do
      gx[i]:=gx[i]+OmegaZs2Omega[i];
    end for;

    poleorder:=0;
    for i:=1 to #infplacesKinf do
      for j:=1 to 2*g do
        poleorder:=Minimum(poleorder,Valuation(Omegax[i][j]));
      end for;
    end for;
    poleorder_Omegax := poleorder;

    for i:=1 to #infplacesKinf do
      val:=Valuation(gx[i]);
      poleorder:=Minimum(poleorder,val);
    end for;

    done:=false;
    degx:=0;
    while not done do // try larger and larger degree in x
      
      for i:=1 to #infplacesKinf do
        for j:=1 to d do
          poleorder:=Minimum(poleorder,Valuation(b0funx[i][j])+degx*Valuation(xfunx[i]));
        end for;
      end for;

      v:=[]; // coefficients of principal parts of all gx 
      cnt:=0;
      for i:=1 to #infplacesKinf do
        for j:=poleorder to -1 do
          cnt:=cnt+1;
          v[cnt]:=Coefficient(gx[i],j);
        end for;
      end for;
  //"#v", #Eltseq(v);

      rows:=[];

      for i:=1 to g do
        row:=[];
        cnt:=0;
        for j:=1 to #infplacesKinf do
          for k:=poleorder to -1 do
            cnt:=cnt+1;
            row[cnt]:=Coefficient(Omegax[j][i+g],k); // coefficients of principal part of Omegax_{i+g} at jth point at infinity
          end for; 
        end for;
        rows:=Append(rows,row);
      end for;

      for i:=1 to d do
        for j:=0 to degx do
          row:=[];
          cnt:=0;
          for k:=1 to #infplacesKinf do
            for l:=poleorder to -1 do
              cnt:=cnt+1;
              row[cnt]:=Coefficient(b0funx[k][i]*xfunx[k]^j,l); // coefficients of principal part of x^j*b^0_i at kth point at infinity
            end for;
          end for;
          rows:=Append(rows,row);  
        end for;
      end for;   
        
      suc,sol:=IsConsistent(Matrix(rows),Vector(v));
      if suc then
        done:=true;
      else // if no success, increase the degree in x
        degx:=degx+1;
      end if;
    
    end while;

    // read off beta from solution

    beta:=[];
    for i:=1 to g do
      beta[i]:=RationalField()!sol[i];
    end for;

    // read off gamma from solution

    Qt:=PolynomialRing(RationalField());
    gamma:=[];
    cnt:=g;
    for i:=1 to d do
      poly:=Qt!0;
      for j:=0 to degx do
        cnt:=cnt+1;
        poly:=poly+(RationalField()!sol[cnt])*Qt.1^j;
      end for;
      gamma:=Append(gamma,poly);
    end for;

    b0fun:=[]; // functions b^0 (finite integral basis)
    for i:=1 to d do
      b0i:=FF!0;
      for j:=1 to d do
        b0i:=b0i+Evaluate(W0[i,j],Qx.1)*FF.1^(j-1);
      end for;
      b0fun[i]:=b0i;
    end for;

    // substract constant such that gamma(bpt)=0

    gamma_FF:=FF!0;
    for i:=1 to d do
      gamma_FF:=gamma_FF+Evaluate(gamma[i],Qx.1)*b0fun[i];
    end for;
    gamma[1]:=gamma[1]-Evaluate(gamma_FF,bpt); 

    return Vector(eta),Vector(beta),Vector(gamma),Integers()!poleorder_Omegax;
  end try;

end function;


