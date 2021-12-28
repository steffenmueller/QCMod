/* Compute the local p-adic height at p between two divisors D and E with disjoint support.
The algorithm is described in Balakrishnan-Besser, IMRN 2012.
Most of the code is a copy of Sage-Code due to Jennifer Balakrishnan.
Current restrictions:
- The curve is hyperelliptic of odd degree and defined over Q_p
- The divisors are of the form D = (P) - (Q), E = (R) - (S), all points are defined
  over Q_p
- Some cases of P,Q,R,S lying in common residue disks are not implemented
- The splitting of the Hodge filtration is the unit root splitting. 
- p is a prime of good reduction.
*/

/* 
 * JSM, August 21: Simplified sum_of_local_symbols to get rid of coleman_integral for
 * easier precision analysis.
 * 
*/


/*
TODO:
  - Create data structure "Coleman divisor" or something like that: collection of points with multiplicities, but can
    add/store attributes, such as residue differential, local interpolation.
  - Allow more general splittings, but check for isotropicity. For instance, if the given basis of H^1_dR is symplectic, the corresponding complementary subspace is isotropic and is just represented the identity matrix.
  - Missing cases in omega_integral
  - frob_diff_nw
*/

Qx<x>:=PolynomialRing(RationalField());
Qxy<y>:=PolynomialRing(Qx);


function weierstrass_local_coord(P, prec, data, f)
  // Local coordinates at Weierstrass point. Unlike local_coord, this also
  // works for points defined over arbitrary finite extensions of Qp.

  x0:=P`x; K:=Parent(x0); Kt<t>:=PowerSeriesRing(K,prec+2*Prime(K)); 
  
  f_prime := Derivative(f);
  xt := x0 + t^2/Evaluate(f_prime, x0);
  for i in [1..Floor(1+Log(2, prec+2))] do
    xt -:= (Evaluate(f,xt)-t^2)/Evaluate(f_prime,xt);
  end for;
  // xt is only correct up to O(t^(prec+2)),
  // We work in a ring with larger precision, since the precision is fixed
  // and we divide by y^2p in recip_froby.

  return xt, t;
end function;


function hyperell_local_coord(P, prec, data)
  // Local coordinates at affine point. 
  // Unlike local_coord, this also
  // works for points defined over arbitrary finite extensions of Qp.
  assert not P`inf; // not implemented for pts at inf
  if is_bad(P, data) then // affine Weierstrass point
    if IsTotallyRamified(Parent(P`x)) then
      xt := local_coord(P, prec, data);
      return xt, Parent(xt).1;
    else 
      f := -ConstantCoefficient(data`Q); // Hyperell poly
      fp := ChangeRing(f, Parent(P`x));
      return weierstrass_local_coord(P, prec, data, fp);
    end if;

  else  // affine non-Weierstrass point
    xt, yt := local_coord(P, prec, data);
    return xt, yt[2];
  end if;
end function;


function local_analytic_interpolation(P, Q, prec, data)
  // Compute interpolation between P and Q to prec digits
        
  K<t> := PowerSeriesRing(Parent(P`x), prec);
  f := -ConstantCoefficient(data`Q); // Hyperell poly
  if not lie_in_same_disk(P,Q, data) then 
    error "points are not in the same disk";
  end if;
  if P`inf then
    xt,yt := hyperell_local_coord(P, prec, data);
    g := data`g;
    return x*t^(2*g+1),y*t^(2*g+1),t^(2*g+1);
  elif not is_bad(P, data) then  // good affine disk
    xt := P`x+t*(Q`x-P`x);
    yt := Sqrt(Evaluate(f, xt));
    if Coefficient(yt, 0) eq P`b[2] then
      return xt, yt, K!1;
    else
      assert Coefficient(yt, 0) eq -P`b[2];  // if this fails, it's probably due to precision
      return xt, -yt, K!1;
    end if;
  else // Weierstrass disk
    S := find_bad_point_in_disk(P);
    xt := hyperell_local_coord(S, data, 2*prec);
    a := P[1];
    b := Q[1] - P[1];
    yt := P`b[2] + (Q`b[2]-P`b[2])*t;
    return Evaluate(xt, y), yt, K!1;
  end if;
end function;


function local_analytic_interpolation_cyclotomic(P,Q,prec,data)
  /*
        Given P and x(Q), with P,Q non-Weiertrass and
        in the same residue disc and P defined over Qp,
        this computes the local analytic interpolation
        between P,Q to prec digits.
  */
  
  xQ := Q`x;
  K := Parent(xQ); 
  Kt<t> := PowerSeriesRing(K,prec); 
  xtP,ytP := hyperell_local_coord(P,prec,data);      
  arg := (xQ-K!P`x)*t;
  X := Evaluate(Kt!xtP, arg);
  Y := Evaluate(Kt!ytP, arg);
  return X,Y;
end function;


function unit_root_subspace(data)
  // Compute a basis for the unit root subspace
  // Uses Prop 6.1 of BB12
  //
  if not data`ordinary then
    error "Can't compute the unit root subspace: Jacobian is not ordinary";
  end if;
  F := Transpose(data`F); // matrix of Frob on H^1. Transposed, as in sage
  N := data`N; g := data`g; p := data`p;
  // Y = Frob^N applied to omega_g,..., omega_{2g-1}
  // where (omega_i) is the given basis of H^1
  Y := reduce_mod_pN_Q_mat(Submatrix(F^N, 1, g+1, 2*g, g), p, N);
  I := IdentityMatrix(RationalField(), g);
  Z := ZeroMatrix(RationalField(), g,g); 
  W := HorizontalJoin(VerticalJoin(I,Z),Y);
  data`subspace := W;
  return W, data;
end function;


function sum_of_local_symbols(D, data)
/*
  For $w$ a differential with residue divisor D and $w_0,...,
    w_{2g-1}$ the basis of de Rham cohomology, computes
    $\{\sum_P <w,w_i>_P\}_{i=0,...,2g-1}$, where the sum is taken over all
    points $P$ in the divisor as well as all weierstrass points.
*/
  g := data`g; basis := data`basis;
  IP1P2, NIP1P2 := coleman_integrals_on_basis(D[2,1],D[1,1],data);  // from D[2,1] to D[1,1]
  // basis x^i*dx/(2y)
  assert &and[basis[i,1] eq 0 and basis[i,2] eq x^(i-1) : i in [1..2*g]];
  assert data`s eq 2*y;  
  symbols := [IP1P2[i] : i in [1..2*g]];
  return symbols;
end function;


function differential_log(D, data : subspace := 0)
  /*
        Compute the log of a differential with given residue divisor.

        This is Psi(w), where Res(w) = D
  */
  // magma = 1/2*sage
  v := Matrix(2*data`g, 1, sum_of_local_symbols(D, data));
  Qp := BaseRing(v);
  if IsZero(v) then return v; end if;
  // W = complementary subspace in H^1, isotropic wrt cup product
  if not assigned(data`subspace) and data`ordinary then
    W, data := unit_root_subspace(data);
  else 
    W := data`subspace;
  end if;
  WQp := ChangeRing(W, Qp);
  cpmQp := ChangeRing(data`cpm, Qp);
  return Eltseq(WQp^(-1)*cpmQp^(-1)*v), data; 
end function;


function psi_alpha(D, data)
  /*
      Computes Psi(alpha)= Psi(phi^*w-p*w) as phi^*(Psi(w))-p*Psi(w)
      Incorporates frob_psi_diff in sage
      magma = 1/2*sage
  */
  psiw, data := differential_log(D, data);
  psiw := Matrix(2*data`g, 1, psiw);
  W := data`subspace;
  WQp := ChangeRing(W, BaseRing(psiw));
  M := Transpose(data`F); 
  return M*WQp*psiw - data`p*WQp*psiw;
end function;


function psiA_cup_psiB(D, E, data)
  /*
    Returns the cup product of psiA and psiB
    magma = sage
  */
  psiB, data := differential_log(E, data); 
  if IsZero(psiB) then
    return 0;
  end if;
  psiA := psi_alpha(D, data);
  Qp := BaseRing(psiA);
  WQp := ChangeRing(data`subspace, Qp);
  cpmQp := ChangeRing(data`cpm, Qp);
  psiB := WQp*Matrix(2*data`g,1,psiB);
  return (Vector(psiA)*cpmQp*psiB)[1]; 
end function;


function find_pth_root_points(P, data)
  /*
        Given a Tuitman point record P=(a,b), finds points P'=(a',b') over Qp(a^(1/p) such that
        a'^p = a, one for each factor of x^p - a. Also returns multiplicity.

  */
  p := data`p; Q := data`Q;
  f := -ConstantCoefficient(Q); // Hyperell poly
  xP := P`x;
  K := Parent(P`x);
  PK<X> := PolynomialRing(K);
  h := X^p - xP;
  if IsZero(Evaluate(h,xP)) then
    h := h div (X-xP);
  end if;
  fact_h := Factorisation(h);
  has_root, a := HasRoot(h);   // Is xP a pth power?
  pth_roots := [];
  for factor in fact_h do
    // The following avoids the need to split the extension into inertial + Eisenstein
    L<w> := RamifiedRepresentation(LocalField(K, factor[1])); 
    factor_L := ChangeRing(factor[1], L);
    has_root, a := HasRoot(factor_L);   
    if not has_root then
      error "xP has no pth root over extension"; 
    end if;
    if Precision(a) lt Precision(L) and not IsWeaklyZero(a) then  // precision loss
      ChangePrecision(~L, Precision(a)); 
      a := L!a; 
    end if;
    b_squared := Evaluate(ChangeRing(f,L), a);  // b^2 = f(a)
    is_square, b := IsSquare(b_squared);
    if is_square then 
      if Precision(b) lt Precision(L) and not IsWeaklyZero(b) then 
        ChangePrecision(~L, Precision(b)); 
      end if;
      Append(~pth_roots, <set_point(L!a, L!b, data), factor[2], [*0,0*]>);
    else 
      s := Polynomial(L, [-b_squared, 0, 1]); // find a square root of f(a)
      L<u> := RamifiedRepresentation(LocalField(L, s));
      has_root_bsq, b := HasRoot(ChangeRing(s, L));
      assert has_root_bsq;
      if Precision(b) lt Precision(L) and not IsWeaklyZero(b) then 
        ChangePrecision(~L, Precision(b)); // 
      end if;
      Append(~pth_roots, <set_point(L!a, L!b, data), factor[2], [*0,0*]>);
    end if;
  end for;
  return pth_roots;
end function;


function binomial_rat(n, k)
  num := &*[n-i : i in [0..k-1]];
  return num/Factorial(k);
end function;


function recip_froby(x, y, data : prec := 20, weierstrass := false)
  /*
        Given local expansions x(t) and y(t), computes the reciprocal of the Frobenius of y
        sage = magma
  */
  p := data`p; Q := data`Q;
  f := -ConstantCoefficient(Q); // Hyperell poly
  evalfx := weierstrass select y^2 else Evaluate(f,x);  // Telling magma that f(x) = y^2 (when y is a uniformizer)
  evalfxp := evalfx^p;
  sum := 0;
  quot :=  Evaluate(f,x^p)/evalfxp -1;
  quoti := quot;
  for i := 1 to prec do
    sum +:= binomial_rat(-1/2, i)*quoti;
    if i lt prec then quoti *:= quot; end if;
  end for;
  return (FieldOfFractions(Parent(y))!y)^(-p)*(1+sum);
end function;


function frob_diff_nw(D, x, y, data : prec := 20)
  // TODO!
  return 0;
end function;


function frob_diff_wstrass(D, x, y, data : prec := 20)
  /*
        Returns the action of Frobenius on the differential w associated
        to the divisor (P)-(Q) wrt local coordinates of a Weierstrass point

        This is phi^*w

*/
  p := data`p;
  P := D[1,1]; Q := D[2,1];
  K := BaseRing(Parent(x));
  a := K!(P`x); b := K!(P`b[2]);   
  c := K!(Q`x); d := K!(Q`b[2]);  
  if b*d eq 0 then
      error "D must have non-Weierstrass support.";
  end if;
  xpm1 := x^(p-1);
  xp := xpm1*x;
  recip := recip_froby(x,y,data : weierstrass, prec := prec);
  dif := p*xpm1/(2*(xp-a)*(xp-c))*(a-c+((b-d)*xp+a*d-b*c)*
                  recip)*Derivative(x);
  return dif;
end function;


function diff_D(D, xt, yt, data) // : tiny := false, alpha := false)
  /*
        Writing differential with residue divisor D = (P1) - (P2) 
        in terms of local coordinates or interpolation xt, yt.
        P1 and P2 are assumed in good and finite  disks.
        This is diff in the sage code

        We assume that (xt(0),yt(0)) is not in the same disk as P1 or P2,
  */


  function is_neg_disc(P, R)

    K := Parent(P`x);
    p := Prime(K);
    if (Integers()!P`x mod p eq Integers()!R[2] mod p)
              and (Integers()!P`b[2] mod p eq -Integers()!R[2] mod p) then
      return true;
    else
      return false; 
    end if;
  end function;
    
  function diff_quot(f, x, a)
    // difference quotient (f(x) - f(a))/(x-a)
    return &+[Coefficient(f,n) * &+[a^i*x^(n-1-i) : i in [0..n-1]] : n in [1..Degree(f)]];
  end function;

  function is_good(P, R)
    if P`x cmpeq R[1] and P`b[2] cmpeq -R[2] then
      return true;
    elif not is_neg_disc(P,R) then
      return true;
    else
      return false;
    end if;
  end function;
      
  P1 := D[1,1];
  P2 := D[2,1];
  a := P1`x; b := P1`b[2];
  c := P2`x; d := P2`b[2];
  g := data`g; p := data`p; Q := data`Q;
  f := -ConstantCoefficient(Q); // Hyperell poly
  Z := [Coefficient(z, 0) : z in [xt,yt]];
  t := Parent(xt).1;

  a,b,c,d := Explode([Parent(xt)!e : e in [a,b,c,d]]);
  if (a cmpeq c and b cmpeq -d and is_good(P1, Z) and is_good(P2, Z) ) then
    return b*Derivative(xt)/(yt*(xt-a));
  elif P1`inf then
    return -Derivative(xt)/(2*yt)*(yt+d)/(xt-c);
  elif P2`inf then
    return -Derivative(xt)/(2*yt)*(yt+b)/(xt-a);
  elif a cmpeq Z[1] then
    denom := Coefficient(xt-a,1);
    forP1 := (yt+b)/(denom*t);
  elif is_good(P1, Z) then
    forP1 := (yt+b)/(xt-a);
    if not &and[Precision(c) gt 0 or Valuation(c) ge Precision(Parent(c))  
                                           : c in Coefficients(forP1)] then
      // Some coefficients only known to non-positive precision. Rewrite forP1.  
      hP1 := diff_quot(f, xt, a);
      forP1 := hP1/(yt-b);
    end if;
  else
    hP1 := diff_quot(f, xt, a);
    forP1 := hP1/(yt-b);
  end if;
  if c cmpeq Z[1] then
    denom := Coefficient(xt-c,1);
    forP2 := (yt+d)/(denom*t);
  elif is_good(P2, Z) then
    forP2 := (yt+d)/(xt-c);
    if not &and[Precision(c) gt 0 or Valuation(c) ge Precision(Parent(c))  : c in Coefficients(forP2)] then
      // Some coefficients only known to non-positive precision. Rewrite forP2.  
      hP2 := diff_quot(f, xt, c);
      forP2 := hP2/(yt-d);
    end if;
  else
    hP2 := diff_quot(f, xt, c);
    forP2 := hP2/(yt-d);
  end if;

  assert &and[Precision(c) gt 0 or Valuation(c) gt 0 : c in Coefficients(forP1)]; 
  assert &and[Precision(c) gt 0 or Valuation(c) gt 0 : c in Coefficients(forP2)]; 
  res := Derivative(xt)/(2*yt)*(forP1-forP2);
  assert &and[Precision(c) gt 0 or Valuation(c) gt 0 : c in Coefficients(res)]; 
  // Check if we have a pole
  if not &and[IsWeaklyZero(Coefficient(res, i)) : i in [Valuation(res)..-1]] then
    error "pole in diff_D";
  end if;
  return res;

end function;


function local_coords_weierstrass_points(data, N, prec_loc_coord)
  /*
   * For each irreducible factor of f, compute local coordinates at (r,0), where r is a
   * root of this factor. 
   * N is the p-adic precision, prec_loc_coord is the target t-adic precision of the local
   * coordinates.
   */
  p := data`p; Q := data`Q; g := data`g;
  f := -ConstantCoefficient(Q); // Hyperell poly
  Qp := pAdicField(p, N);
  fp := ChangeRing(f, Qp);
  factors := Factorisation(fp);
  local_coords := [* *];
  for factor in factors do
    // The following workaround avoids the need to split the extension into inertial + Eisenstein
    K<a> := RamifiedRepresentation(LocalField(Qp, factor[1]));
    rts := Roots(ChangeRing(factor[1], K));
    assert #rts gt 0;
    P := set_point(rts[1,1], 0, data);
    xt, yt := weierstrass_local_coord(P,prec_loc_coord, data, fp); 
    Append(~local_coords, [xt,yt]);
  end for;
  return local_coords;
end function;


function res_alpha_int_beta_weierstrass(D1, D2, data, N, local_coords : alphas := [**])

  /*
        Returns sum(res(alpha*integral(beta))), where alpha and beta are
        in the notation of Balakrishnan-Besser,
        ``Coleman-Gross height pairings and the p-adic sigma function,'' IMRN 2012
        (need to sum over all of the right residue discs)
        local_coords is a list of local coordinates at Weierstrass points, one for each Galois
        orbit over Qp.
        alphas contains the expansions of the corresponding alpha, if already known
*/

  p := data`p; Q := data`Q; g := data`g;
  residues := [ ];
  new_alphas := [* *];
  for i in [1..#local_coords] do
    xt, yt := Explode(local_coords[i]);
    if IsZero(#alphas) then // Compute alpha
      frob_D1 := frob_diff_wstrass(D1, xt, yt, data : prec := N-1);
      diff1 := diff_D(D1, xt, yt, data);
      alpha := frob_D1 - p*diff1;
      Append(~new_alphas, alpha);
    else 
      alpha := alphas[i];
    end if;
    beta := diff_D(D2, xt, yt, data);
    res := Trace(Coefficient(alpha*Integral(beta), -1));
    Append(~residues, res);
  end for;

  if IsZero(#alphas) then alphas := new_alphas; end if;
  return &+residues, alphas;
end function;


function res_alpha_int_beta_non_weierstrass(D1, D2, data, cycl_data : N := 0, printlevel := 0);

  /*
        Returns sum(res(alpha*(int(beta) + c))) where c is the right constant of integration
        and the sum is over non-Weierstrass poles of alpha

        D1 = (P) - (Q), D2 = (R) - (S)
        This is res_alpha_int_beta in sage

        cycl_data contains 
          * points P' s.t. x(P')^p = x(P), one for each factor of x^p-x(P)
          * the multiplicity of the factor 
          * local analytic interpolation between P and P' 
        and the same for Q.

        currently assumes 
        - P and Q are in distinct disks
        - Q and R are in distinct disks (done in sage)
        - Q and S are in distinct disks
  */
  p := data`p; Q := data`Q; g := data`g;
  if IsZero(N) then N := data`N; end if;;
  pl := printlevel;        
  f := -ConstantCoefficient(Q); // Hyperell poly
  Qp := pAdicField(p, N);
  Nmin := N;
  P := D1[1,1]; Q := D1[2,1]; R := D2[1,1]; S := D2[2,1]; 
  pth_rts_P, pth_rts_Q := Explode(cycl_data);
  integrals := [Qp!0, Qp!0];
  xtP := 0; xtQ := 0;
  xP := P`x; xQ := Q`x; xR := R`x; xS := S`x;
  yP := P`b[2]; yQ := Q`b[2]; yR := R`b[2]; yS := S`b[2]; 
  for triple in pth_rts_P do
    if xP ne 0 then // harder case
      xtPPp, ytPPp := Explode(triple[3]);
      d := AbsoluteDegree(Parent(triple[1]`x));
      tprecx, pprecx := Explode(Precision(xtPPp));
      tprecy, pprecy := Explode(Precision(ytPPp));
      tprec := Min(tprecx, tprecy);
      pprec := Min(pprecx, pprecy);
      if lie_in_same_disk(P, R, data) and xR eq xS then
        betaP := Derivative(xtPPp) * (Evaluate(f,xR) - Evaluate(f,xtPPp)) /(xtPPp - xR) * 1/(yR+ytPPp)/ytPPp; // Check this if results are wrong
        int_betaP_part := Integral(betaP);
        log1 := Log(triple[1]`x - xR);
        log2 := Log(xP - xR);
        I1 := Evaluate(int_betaP_part, 1) + (log1 -log2);
      else 
        // Expand differential with residue divisor D2 in terms of xtPPp, ytPPp
        betaP := diff_D(D2, xtPPp, ytPPp, data); 
        int_betaP := Integral(betaP);
        KQp := Parent(triple[1]`x);
        int_betaP_KQp := ChangeRing(Parent(int_betaP), KQp)!int_betaP;
        I1 := Evaluate(int_betaP_KQp, 1) - Evaluate(int_betaP_KQp, 0);
      end if;

      NI1ext := Min([d*Precision(triple[1]`x), d*Precision(triple[1]`b[2]),
                 pprec, Floor(tprec+1) - log(p, tprec+1)]); 
      integrals[1] +:= Trace(I1)*triple[2];
      Nmin := Min(Nmin, Floor(NI1ext/d));
    end if; // xP ne 0
  end for;

  for triple in pth_rts_Q do
    pth_rt_Q := triple[1];
    if lie_in_same_disk(P, Q, data) then
      error "Haven't done this case yet";  // TODO: Finish.

    //elif xP eq xQ and yP eq -yQ then
    //  return 2*integrals[1];

    end if;  //lie_in_same_disk(P, Q, data) 
    if xQ ne 0 then
      xtQQp, ytQQp := Explode(triple[3]);  // local analytic interpolation from Q to pth_rt_Q
      d := AbsoluteDegree(Parent(triple[1]`x));
      tprecx, pprecx := Explode(Precision(xtQQp));
      tprecy, pprecy := Explode(Precision(ytQQp));
      tprec := Min(tprecx, tprecy);
      pprec := Min(pprecx, pprecy);
      if lie_in_same_disk(Q, S, data) then
        error "Haven't done this case yet";
      elif lie_in_same_disk(Q, R, data) then
        error "Haven't done this case yet";
      else  // Q doesn't lie in disk of R or S
        betaQ := diff_D(D2, xtQQp, ytQQp, data);
        int_betaQ := Integral(betaQ);
        KQp := Parent(triple[1]`x);
        int_betaQ_KQp := ChangeRing(Parent(int_betaQ), KQp)!int_betaQ;
        I2 := Evaluate(int_betaQ_KQp, 1) - Evaluate(int_betaQ_KQp, 0);
        NI2ext := Min([d*Precision(triple[1]`x), d*Precision(triple[1]`b[2]),
                 pprec, Floor(tprec+1) - log(p, tprec+1)]); 
        integrals[2] +:= Trace(I2)*triple[2];
        Nmin := Min(Nmin, Floor(NI2ext/d));
      end if; // lie_in_same_disk(Q, S, data) 
    end if; // xQ ne 0
  end for;  // triple in pth_rts_Q 
  if pl gt 1 then "I1 = ",integrals[1]; end if;
  if pl gt 1 then "I2 = ",integrals[2]; end if;
  return integrals[1] - integrals[2], Nmin;
end function;
 

function omega_integral(D1, D2, data : N := 0, wlcs := [**], alphas := [**], cycl_data := [**], printlevel := 0)
  /*
        Coleman integral of omega, in the notation of Balakrishnan-Besser,
        ``Coleman-Gross height pairings and the p-adic sigma function,'' IMRN 2012
  */

  Q := data`Q; p := data`p; g := data`g;
  if IsZero(N) then N := data`N; end if;
  f := -ConstantCoefficient(data`Q); // Hyperell poly
  P := D1[1,1]; Q := D1[2,1]; R := D2[1,1]; S := D2[2,1]; 
  pl := printlevel;

  if lie_in_same_disk(R, S, data) then
    if pl gt 1 then printf "Points in %o lie in same disk -- problem here?\n", D2; end if;
    xtSR, ytSR := local_analytic_interpolation(S,R,5*N+10,data);
    diffS := diff_D(D1, xtSR, ytSR, data);
    int_diffS := Integral(diffS);
    if pl gt 1 then printf "omega_integral = %o\n\n", Evaluate(int_diffS, 1); end if;
    return Evaluate(int_diffS, 1), wlcs, alphas, cycl_data;
  end if; 

  FR := frobenius_pt(R, data);
  // 
  if pl gt 2 then printf "Compute integral from R to FR.\n"; end if;
  R_to_FR := 0;  
  NRFR := N;
  if R`x ne FR`x or R`b ne FR`b then
    tadicprecR := 2*N+10;
    tadicprecR := 2*N;
    xtRFR, ytRFR := local_analytic_interpolation(R,FR, tadicprecR, data);

    if not &or[lie_in_same_disk(R,pt,data) : pt in [P,Q]] then
      // this is the case of beta having residue divisor "Q - wQ" (paper)
      diffRFR := diff_D(D1, xtRFR, ytRFR, data);
      int_diffRFR := (Integral(diffRFR));
      R_to_FR := Evaluate(int_diffRFR, 1);
    elif P`x eq Q`x and P`b[2] eq -Q`b[2] then
      // changing P to R, P' to FR, Q to P (in BB12)
      diffpart1 := (Evaluate(f, P`x) - Evaluate(f, xtRFR))*Derivative(xtRFR) / (ytRFR*(xtRFR-P`x)*(P`b[2] + ytRFR));
      intpart := Integral(diffpart1);
      intpart1 := Evaluate(intpart, 1);
      R_to_FR := intpart1 + Log(FR`x - P`x) - Log(R`x - P`x);

    elif lie_in_same_disk(R,P,data) then
      diffpart1 := (Evaluate(f, P`x) - Evaluate(f, xtRFR))*Derivative(xtRFR) / (2*ytRFR*(xtRFR - P`x)*(P`b[2] + ytRFR));
      intpart := (Integral(diffpart1));
      intpart1 := Evaluate(intpart, FR`x-R`x);
      diffpart2 := Derivative(xtRFR)/(2*ytRFR)*(ytRFR + Q`b[2])/(xtRFR-Q`x);
      intpart := (Integral(diffpart2));
      intpart2 := Evaluate(intpart, FR`x-R`x);
      R_to_FR := intpart1 + Log(FR`x - P`x) - Log(R`x - P`x) - intpart2;

    else // lie_in_same_disk(R,Q)
      diffpart1 := (Evaluate(f, Q`x) - Evaluate(f, xtRFR))*Derivative(xtRFR) / (2*ytRFR*(xtRFR - Q`x)*(Q`b[2] + ytRFR));
      intpart := Integral(diffpart1);
      intpart1 := Evaluate(intpart, FR`x-R`x);
      diffpart2 := Derivative(xtRFR)/(2*ytRFR)*(ytRFR + P`b[2])/(xtRFR-P`x);
      intpart := Integral(diffpart2);
      intpart2 := Evaluate(intpart, FR`x-R`x);
      R_to_FR := intpart2 - (intpart1 - Log(FR`x - Q`x) - Log(R`x - Q`x));
    end if;  // not &or[lie_in_same_disk(R,pt,data) : pt in [P,Q]] 
    NRFR := Min(N, tadicprecR);
  end if;  // R`x ne FR`x or R`b ne FR`b 
  if pl gt 1 then printf "Integral from R to FR is %o.\n", R_to_FR; end if;

  if pl gt 2 then printf "Compute integral from FS to S.\n"; end if;
  FS := frobenius_pt(S, data);
  FS_to_S := 0;  
  NFSS := N;
  if S`x ne FS`x or S`b ne FS`b then
    tadicprecS := 2*N+10;
    tadicprecS := 2*N;
    if not &or[lie_in_same_disk(S,pt,data) : pt in [P,Q]] then
      xtFSS, ytFSS := local_analytic_interpolation(FS,S, tadicprecS, data);
      diffFSS := diff_D(D1, xtFSS, ytFSS, data);
      int_diffFSS := (Integral(diffFSS));
      FS_to_S := Evaluate(int_diffFSS, 1);
      NFSS := Min(N, tadicprecS);

    elif P`x eq Q`x and P`b[2] eq -Q`b[2] and S`x eq R`x and S`b[2] eq -R`b[2] then
      FS_to_S := R_to_FR;
      NFSS := NRFR;
    else
      error "This case is not implemented yet";
    end if;
  end if; // S`x ne FS`x or S`b ne FS`b then
  if pl gt 1 then printf "Integral from FS to S is %o.\n", FS_to_S; end if;
 


  if pl gt 2 then printf "\nCompute sum of residues of alpha*int(beta) at non-Weierstrass points.\n"; end if;
  // First try with low precision, increase if insufficient
  added_prec := 0;
  if #cycl_data eq 0 then 
    pth_rts_P := find_pth_root_points(P, data);
    pth_rts_Q := find_pth_root_points(Q, data);
  else 
    pth_rts_P, pth_rts_Q := Explode(cycl_data);
  end if;
  repeat 
    try 
      if pth_rts_P[1,3] eq [*0,0*] and P`x ne 0 then
        for i in [1.. #pth_rts_P] do
          //Find interpolation between P and pth_rts_P[i,1] and add to pth_rts_P
          if pl gt 3 then printf "Find interpolation between %o and %o.\n", P, pth_rts_P[i,1]; end if;
          d := AbsoluteDegree(Parent(pth_rts_P[i,1]`x));
          xtPPp, ytPPp := local_analytic_interpolation_cyclotomic(P, pth_rts_P[i,1], d*N + added_prec, data);
          pth_rts_P[i,3] := [*xtPPp, ytPPp*];
        end for;
      end if;
      if pth_rts_Q[1,3] eq [*0,0*] and Q`x ne 0 then
        for i in [1.. #pth_rts_Q] do
          //Find interpolation between Q and pth_rts_Q[i,1] and add to pth_rts_Q
          if pl gt 3 then printf "Find interpolation between %o and %o.\n", Q, pth_rts_Q[i,1]; end if;
          d := AbsoluteDegree(Parent(pth_rts_Q[i,1]`x));
          xtQQp, ytQQp := local_analytic_interpolation_cyclotomic(Q, pth_rts_Q[i,1], d*N + added_prec, data);
          pth_rts_Q[i,3] := [*xtQQp, ytQQp*];
        end for;
      end if;
      cycl_data := [pth_rts_P, pth_rts_Q];
      res_alpha_int_beta_nw, Nresnw := res_alpha_int_beta_non_weierstrass(D1, D2, data, cycl_data : printlevel := pl);
    catch e
      if pl gt 1 then e; end if;
      added_prec +:= p;
      if pl gt 1 then "insufficient_precision", d*N+added_prec-p; "Try precision", d*N+added_prec; end if;
    end try;
  until assigned res_alpha_int_beta_nw;
  if pl gt 1 then printf "sum of residues of alpha*int(beta) at non-Weierstrass points = %o.\n", res_alpha_int_beta_nw; end if;
  Nomega := Min([N, Nresnw, NRFR, NFSS]);

  if pl gt 1 then "sum of residues of alpha*int(beta) at non-Weierstrass points = %o.\n", res_alpha_int_beta_nw; end if;
  // 
  // Now residues at Weierstrass points
  // First try with low precision, increase if insufficient
  target_padic_prec := Nomega;
  weierstrass_prec := 2*p*target_padic_prec-p-1; // BB12, Prop 6.5
  insuff_prec := false;
  repeat 
    try 
      if #wlcs eq 0 or insuff_prec then
        if pl gt 2 then "Computing local coordinates at Weierstrass points"; end if;
        wlcs := local_coords_weierstrass_points(data, target_padic_prec, weierstrass_prec);
        // Only need Nomega digits.
      end if;
      res_alpha_int_beta, alphas := res_alpha_int_beta_weierstrass(D1, D2, data, 
                                     target_padic_prec, wlcs : alphas := alphas);
    catch e
      if pl gt 1 then e; end if;
      insuff_prec := true;
      weierstrass_prec +:= p;
      if pl gt 2 then "insufficient_precision", weierstrass_prec-p; "Try precision", weierstrass_prec; end if;
    end try;
  until assigned res_alpha_int_beta;
  if pl gt 1 then printf "sum of residues of alpha*int(beta) at Weierstrass points = %o.\n", res_alpha_int_beta; end if;

  res_alpha_int_beta +:= res_alpha_int_beta_nw;
  cups := psiA_cup_psiB(D1, D2, data);
  if pl gt 1 then printf "psi(A) cup psi(B) = %o.\n", cups; end if;
  omega := 1/(1-data`p)*(cups+res_alpha_int_beta-FS_to_S-R_to_FR);
  if pl gt 1 then printf "omega_integral = %o\n\n", omega; end if;
  return omega, wlcs, alphas, cycl_data, Nomega;
end function;


function local_height_divisors_p(D1, D2, data : N := 0, D1_data := 0, printlevel := 0)
/*  
 * Compute the local p-adic height pairing at p between two divisors D and E with disjoint support
 * on an odd degree hyperelliptic curves over Qp.
 * The theory is described in Coleman-Gross, 89
 * The algorithm is described in Balakrishnan-Besser, IMRN 2012.
 * Heavily based on a sage implementation due to Jennifer Balakrishnan.
 * We assume that D1 and D2 are sequences of pairs [P,Q] of point records as in Jan Tuitmans
 * Coleman integration code. The height pairing between D1 and D2 is then the sum of the
 * pairings between the various divisors P-Q.
 * We currently need an ordinary prime and the unit root splitting, the idele
 * class character is the canonical cylcotomic character coming from the Iwasawa log.
 * 
 * This returns the height and some auxiliary data that can be recycled to compute 
 * height pairings between D1 and other divisors.
 */


  Q := data`Q;
  assert Degree(Q) eq 2 and IsZero(Coefficient(Q, 1)); // want equation y^2=f(x) 
  f := -ConstantCoefficient(Q); // Hyperell poly
  if not IsOdd(Degree(f)) then
    error "Currently only implemented for odd degree models";
  end if;
  if not IsMonic(f) then
    error "Currently only implemented for monic models";
  end if;
  pl := printlevel;
  if IsZero(N) then  N := data`N; end if;
  p := data`p;
  basis := data`basis; g := data`g;
  if not data`ordinary then
    error "Currently only implemented for ordinary reduction.";
  end if;
  subspace := unit_root_subspace(data); 
  data`subspace := subspace;
  cpm := data`cpm;
  ht := 0; Nht := N;
  if D1_data cmpeq 0 then
    all_wlcs := [**];
    all_alphas := [**];
    all_cycl_data := [**];
  else 
    all_wlcs, all_alphas, all_cycl_data := Explode(D1_data);
  end if;
  for i in [1..#D1] do
    D := D1[i];
    // Precomputations for integrals of eta and omega below
    // These only depend on D, so we only do them once.
    diff_log_div1 := differential_log(D, data);
    diff_log_hol_div1 :=  Vector([diff_log_div1[i] : i in [1..g]] cat [0 : i in [1..g]]);
    wlcs := IsDefined(all_wlcs,i) select all_wlcs[i] else [**];
    alphas := IsDefined(all_alphas,i) select all_alphas[i] else [**];
    cycl_data := IsDefined(all_cycl_data,i) select all_cycl_data[i] else [**];
    for E in D2 do
      if pl gt 2 then 
        printf "\nComputing local Coleman-Gross height at %o between divisors\n %o\n and\n %o\n", p, D, E;
      end if;
      eta := 0; 
      // Compute the integral of the holomorphic differential eta as 
      // in Algorithm 5.9 of BB12
      if D[1,2] ne 0 or E[1,2] eq 0 then
        col_int_E, Neta := coleman_integrals_on_basis(E[2,1], E[1,1], data);
        eta := &+[diff_log_hol_div1[i] * col_int_E[i] : i in [1..g]];
      end if;
      if pl gt 0 then print "\n eta = ", eta; end if;
      omega, wlcs, alphas, cycl_data, Nomega := omega_integral(D,E,data: N := N, wlcs := wlcs, 
                            alphas := alphas, cycl_data := cycl_data, printlevel := pl);
      if pl gt 0 then print "\n omega = ", omega; end if;

      ht +:= (omega - eta);
      Nht := Min([Nht, Nomega, Neta]);
      ChangePrecision(~ht, Min(Precision(ht), Nht));
      // So ht is correct to Nht digits
    end for;
    
    // Update data for omega_integral, so that we don't have to recompute.
    all_wlcs[i] := wlcs;
    all_alphas[i] := alphas;
    all_cycl_data[i] := cycl_data;
  end for;

  return ht, <all_wlcs, all_alphas, all_cycl_data>, Nht;
end function;



