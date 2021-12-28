// Find a good second affine patch for smooth plane quartics so that
// - every residue disk is good (i.e. is affine and the Frobenius lift is defined
//   there) on at least one affine patch
// - every affine patch contains enough rational points to fit the height pairing.

function curve(Q)
  // given a bivariate polynomial in K[x][y], construct the curve Q = 0
  K := BaseRing(BaseRing(Q));
  PK3<X,Y,Z>:=PolynomialRing(K,3);                         
  Q_dehom:=PK3!0;
  d := Degree(Q);
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      Q_dehom +:= Coefficient(Coefficient(Q,i),j)*Y^i*X^j;
    end for;
  end for;
  Q_hom := Homogenization(Q_dehom, Z);                                                                
  P2<X1,Y1,Z1> := ProjectiveSpace(K, 2);
  C_Q := Curve(P2,Q_hom);
  return C_Q, Q_dehom;
end function;

function small_rat_pts(Q)
  C := curve(Q);
  C_rat_pts := Points(C:Bound:=100);
  rat_pts := [];
  for P in C_rat_pts do
    L := Eltseq(P);
    d := LCM([Denominator(c): c in L]);
    Append(~rat_pts, [d*c : c in L]);
  end for;
  return rat_pts;
end function;

function second_affine_patch_modp(Q, p, A, rat_pts : printlevel := 0)
    
  // Find a good second affine patch mod p.
  // We want bad points and (enough) rational points to go to good points 
  //
  pl := printlevel;
  Fp := GF(p);
  a,b,c,d := Explode(ChangeUniverse(A,Fp)); 
  PFp<x,y> := PolynomialRing(Fp, 2);
  PFpx<x> := PolynomialRing(Fp);
  PFpxy<y> := PolynomialRing(PFpx);

  PFp3<X,Y,Z>:=PolynomialRing(Fp,3);                         
  Q_dehom:=PFp3!0;
  deg := Degree(Q);
  for i:=0 to deg do
    for j:=0 to Degree(Coefficient(Q,i)) do
      Q_dehom +:= Fp!Coefficient(Coefficient(Q,i),j)*Y^i*X^j;
    end for;
  end for;

  Q_modp := PFpxy!0;
  for i:=0 to Degree(Q_dehom, Y) do
    for j:=0 to Degree(Q_dehom, Y)  do
      Q_modp +:= Fp!Coefficient(Coefficient(Q_dehom, Y,i), X, j)*x^j*y^i;
    end for;
  end for;
  Delta_modp := Discriminant(Q_modp);
  r_modp := Numerator(Delta_modp/GCD(Delta_modp,Derivative(Delta_modp)));

  branch_pts := [t[1] : t in Roots(r_modp)];
  branch_lifted_fact := [Factorisation(UnivariatePolynomial(Evaluate(Q_dehom, [b,Y,1]))) : b in branch_pts];
  Q_modp_hom := Homogenization(Q_dehom, Z);                                                                
  P2<X1,Y1,Z1> := ProjectiveSpace(Fp, 2);
  C_Q := Curve(P2,Q_modp_hom);
  C_Q_pts := Points(C_Q);
  rat_pts_modp := [C_Q!ChangeUniverse(P, Fp) : P in rat_pts];
  inf_pts := [P: P in C_Q_pts | P[3] eq 0 ];
  //ram_pts := [P : P in C_Q_pts | P[3] ne 0 and P[1] in branch_pts];
  ram_pts := [];
  for i in [1..#branch_pts] do
    ram_pts cat:= [C_Q![branch_pts[i], -Evaluate(t[1],0),1]  : t in branch_lifted_fact[i]];  
  end for; 
  bad_pts := ram_pts cat inf_pts;
  //"ram_pts", ram_pts;
  // TODO: Make sure (0:1:0) isn't on the curve

  Q_modp_trans_hom := Evaluate(Q_modp_hom, [a*X+Z+b*Y, Y, c*Z+X+d*Y]);
  C_Q_trans1 := Curve(P2,Q_modp_trans_hom);
  pi1 := map<C_Q_trans1 -> C_Q | [a*X1+Z1+b*Y1, Y1, c*Z1+X1+d*Y1]>;
  lc := Fp!Coefficient(Q_modp_trans_hom, Y, 4); 
  assert lc ne 0;
  Q_modp_trans_hom := lc^3*Evaluate(Q_modp_trans_hom,[X,Y/lc,Z]);
  C_Q_trans := Curve(P2,Q_modp_trans_hom);
  pi2 := map<C_Q_trans -> C_Q_trans1 | [X1, Y1/lc, Z1]>;
  pi := pi2*pi1;
  phi := Inverse(pi);

  transformed_bad_pts := [phi(P) : P in bad_pts];
  transformed_rat_pts_modp := [phi(P) : P in rat_pts_modp];

  Q_modp_trans_dehom := Evaluate(Q_modp_trans_hom, [X,Y,1]);

  Q_modp_trans := PFpxy!0;
  for i:=0 to Degree(Q_modp_trans_dehom, Y) do
    for j:=0 to Degree(Q_modp_trans_dehom, Y)  do
      Q_modp_trans +:= Fp!Coefficient(Coefficient(Q_modp_trans_dehom, Y,i), X, j)*x^j*y^i;
    end for;
  end for;
  if pl gt 2 then "transformed Q mod p"; Q_modp_trans; end if;
  
  Delta_modp_trans := Discriminant(Q_modp_trans);
  r_modp_trans := Numerator(Delta_modp_trans/GCD(Delta_modp_trans,Derivative(Delta_modp_trans)));
  branch_pts_trans := [t[1] : t in Roots(r_modp_trans)];
  //"branch_pts_trans", branch_pts_trans;
  branch_lifted_fact_trans := [Factorisation(UnivariatePolynomial(Evaluate(Q_modp_trans_hom, [b,Y,1]))) : b in branch_pts_trans];
  ram_pts_trans := [];
  for i in [1..#branch_pts_trans] do
    //ram_pts_trans cat:= [C_Q_trans![branch_pts_trans[i], -Evaluate(t[1],0),1]  : t in branch_lifted_fact_trans[i] | t[2] gt 1];
    ram_pts_trans cat:= [C_Q_trans![branch_pts_trans[i], -Evaluate(t[1],0),1]  : t in branch_lifted_fact_trans[i]];
  end for; 
  if pl gt 3 then "bad points get mapped to"; transformed_bad_pts; end if;
  if pl gt 3 then "rational points get mapped to"; transformed_rat_pts_modp; end if;
  C_Q_pts_trans := Points(C_Q_trans);
  inf_pts_trans := [P: P in C_Q_pts_trans | P[3] eq 0 ];
  bad_pts_trans := ram_pts_trans cat inf_pts_trans;
  number_of_good_rat_pts_trans := #[P : P in transformed_rat_pts_modp | P notin bad_pts_trans]; 
  assert number_of_good_rat_pts_trans ge 3;
  if pl gt 2 then "bad points of transformed curve"; bad_pts_trans; end if;
  bad := [P : P in transformed_bad_pts | P in bad_pts_trans];
  //"bad", bad;
  //bad cat:= [P : P in transformed_inf_pts | P[3] eq 0];
  done := IsEmpty(bad);
  //"done", done;

  return done, A;
end function;

function second_affine_patch(Q, p : printlevel := 0, bd:=p-1, max_inf_deg := 0)
  pl := printlevel;
  y := Parent(Q).1;
  x := BaseRing(Parent(Q)).1;
  K := BaseRing(BaseRing(Q));
  if bd gt p-1 then bd := p-1; end if;  // bd > p-1 makes no sense.

  function small_lift(ap, K)
    a := Integers()!ap;
    if a gt p/2 then
      a := a-p;
    end if;
    return Rationals()!a;
  end function;

  min_ht_Q_trans := [];
  min_height := 10^10;

  PK3<X,Y,Z>:=PolynomialRing(K,3);                         
  rat_pts := small_rat_pts(Q);
  Q_dehom:=PK3!0;
  d := Degree(Q);
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      Q_dehom +:= Coefficient(Coefficient(Q,i),j)*Y^i*X^j;
    end for;
  end for;
  Q_hom := Homogenization(Q_dehom, Z);                                                                

  Qs_trans := [];
  heights := [];
  for c0,a0,d0,b0 in [0..bd] do 
    try 
      bool, Ap := second_affine_patch_modp(Q, p, [a0,b0,c0,d0], rat_pts : printlevel := pl);
      if not bool then continue; end if;
    catch e
      continue;
    end try;
    // If we're here, we've found a good second affine patch mod p.
    // Now lift.
    A := [small_lift(a,K) : a in Ap];
    a,b,c,d := Explode(A);
    Q_trans_hom_non_monic := Evaluate(Q_hom, [a*X+Z+b*Y, Y, c*Z+X+d*Y]);
    lc := K!Coefficient(Q_trans_hom_non_monic, Y, 4);  // A Tuitman model requires Q monic in y
    if lc eq 0 then continue; end if;
    Q_trans_hom := lc^3*Evaluate(Q_trans_hom_non_monic,[X,Y/lc,Z]);
    Q_trans_dehom := Evaluate(Q_trans_hom, [X,Y,1]);
    Q_trans := Parent(Q)!0;
    for i:=0 to Degree(Q_trans_dehom, Y) do
      for j:=0 to Degree(Q_trans_dehom, Y)  do
        Q_trans +:= K!Coefficient(Coefficient(Q_trans_dehom, Y,i), X, j)*x^j*y^i;
      end for;
    end for;
    height := Max([Abs(c) : c in Coefficients(Q_trans_dehom)]);
    Append(~heights, height);
    Append(~Qs_trans, Q_trans);
    if height lt min_height then
      discard := false;
      if max_inf_deg gt 0 then // want small degree places at infinity
        FF:=function_field(Q_trans); // function field of curve over the rationals
        infplaces:=InfinitePlaces(FF);
        infplacesKinf := infplaces;
        Kinf:=RationalField();
        if #infplaces gt 1 then // TODO: Keep this?
          repeat 
            for i:=1 to #infplacesKinf do
              if not IsOne(Degree(infplacesKinf[i])) then
                Kinf:=Compositum(Kinf,(NormalClosure(ResidueClassField(infplacesKinf[i])))); // field generated by points at infinity
              end if;
            end for;
            Kinfx:=RationalFunctionField(Kinf); Kinfxy:=PolynomialRing(Kinfx);
            finf:=Kinfxy!0;
            for i:=0 to Degree(Q_trans) do
              for j:=0 to Degree(Coefficient(Q_trans,i)) do
                finf:=finf+Coefficient(Coefficient(Q_trans,i),j)*Kinfxy.1^i*Kinfx.1^j;
              end for;
            end for;  
            FFKinf:=FunctionField(finf); // function field of curve over Kinf
            infplacesKinf:=InfinitePlaces(FFKinf); // places at infinity all of degree 1, will be denoted by P
          until &and[IsOne(Degree(P)) : P in infplacesKinf];

          if AbsoluteDegree(Kinf) gt max_inf_deg then
            "Degree", AbsoluteDegree(Kinf);
            discard := true;
          end if;
        else 
          discard := true;
        end if;
      end if; // max_inf_deg gt 0
      
      if not discard then
        if pl gt 1 then "\nSmallest transformation found has max coeff size ", height; ;end if;
        min_height := height;
        min_ht_Q_trans := Q_trans;
        min_A := A;
      end if;
    end if; // height lt min_height

  end for; 

  if not assigned min_A then
    error "No good second affine patch found. Try a larger prime.";
  end if;
    
  return min_ht_Q_trans, min_A;

end function;
