// Improved height constant for genus 2
//
// See J.S. Müller, M. Stoll: Canonical heights on genus two Jacobians

/*********************************************************************
 ATTENTION:
 TorsionSubgroup in Geometry/CrvG2/torsion.m should use
 HeightConstant[New](J : Fast) for efficiency reasons
**********************************************************************/


declare attributes JacHyp: HeightConstNew;


function move_points(C, pts)
// C is a curve over a non-arch. local field
// pts is a set of at most 2 points on the reduction of C
// return an isomorphic curve D such that pts[1] maps to (0:0:1) and
// pts[2] (if it exists) maps to (1:0:0) in the reduction of D

  assert #pts lt 3;
  if IsEmpty(pts) then return C; end if;
  R := BaseRing(C);
  PR := PolynomialRing(R);
  if #pts eq 1 then
    // test if pts[1] is affine or not
    if pts[1, 3] eq 0 then
      a := 1; b := 0; c := R!(pts[1, 3]); d := -R!(pts[1, 1]);
      u := -R!(pts[1, 2]/pts[1, 1]^3)*PR.1^3;
    else
      a := R!(pts[1, 3]); b := -R!(pts[1, 1]); c := 0; d := 1;
      u := PR!(-pts[1, 2]/pts[1, 3]^3);
    end if;
  else
    P1 := pts[1]; P2 := pts[2];
    if P1[3]*P2[3] ne 0 then // 2 affine points
      a := R!(P1[3]); b := -R!(P1[1]); c := R!(P2[3]); d := -R!(P2[1]);
      x1 := R!(P1[1]/P1[3]); y1 := R!(P1[2]/P1[3]^3);
      x2 := R!(P2[1]/P2[3]); y2 := R!(P2[2]/P2[3]^3);
      slope := (y2 - y1)/(x2 - x1);
      u := -slope*(PR.1 - x1) - y1;
    elif P2[3] eq 0 then // P1 affine, P2 at infty
      a := R!(P1[3]); b := -R!(P1[1]); c := R!(P2[3]); d := -R!(P2[1]);
      x1 := R!(P1[1]/P1[3]);
      y1 := R!(P1[2]/P1[3]^3);
      y2 := R!(P2[2]/P2[1]^3);
      u := -y2*(PR.1^3 - x1^3) - y1;
    elif P1[3] eq 0 then // P2 affine, P1 at infty
      a := R!(P2[3]); b := -R!(P2[1]); c := R!(P1[3]); d := -R!(P1[1]);
      x2 := R!(P2[1]/P2[3]);
      y2 := R!(P2[2]/P2[3]^3);
      y1 := R!(P1[2]/P1[1]^3);
      u := -y1*(PR.1^3-x2^3) - y2;
    else // both P1 and P2 at infty
      a := R!(P1[3]); b := -R!(P1[1]); c := R!(P2[3]); d := -R!(P2[1]);
      y := R!(P1[2]/P1[1]^3);
      f, h := HyperellipticPolynomials(C);
      h0 := Coefficient(h, 3);
      h1 := Coefficient(h, 2);
      f1 := Coefficient(f, 5);
      u :=  -y*PR.1^3 - (f1-h1*y)/(h0+2*y)*PR.1^2;
    end if; // P1[3]*P2[3] ne 0
  end if; // #pts eq 1
  return Transformation(C, [a,b,c,d], 1, u);
end function;

function alpha_p(cp, Kod);
  // due to John Cremona
  // computes an optimal upper bound for the local height constant on an elliptic curve
  // with Tamagawa number cp and Kodaira symbol Kod
  if cp eq 1 then return 0; end if;
  case Kod:
    when KodairaSymbol("I0"):   return 0;
    when KodairaSymbol("II"):   return 0;
    when KodairaSymbol("III"):  return 1/2;
    when KodairaSymbol("IV"):   return 2/3;
    when KodairaSymbol("I0*"):  return 1;
    when KodairaSymbol("II*"):  return 0;
    when KodairaSymbol("III*"): return 3/2;
    when KodairaSymbol("IV*"):  return 4/3;
  else
    n:=0;
    while true do
      n+:=1;
      if Kod eq KodairaSymbol("I" cat IntegerToString(n)) then // type In
         return (IsEven(n) select n/4 else (n^2-1)/(4*n));
      else
        if Kod eq KodairaSymbol("I" cat IntegerToString(n) cat "*") then  // type I*n
          return (cp eq 2 select 1 else (n+4)/4);
        end if;
      end if;
    end while;
  end case;
end function;

function liftquf(f, rt, prec)
  deg := Degree(f);
  F := Parent(rt);
  p := #F;
  PF := PolynomialRing(F);
  R := pAdicRing(p, prec);
  PR := PolynomialRing(R);
  fp := PF!f;
  q := (PF.1-rt)^2;
  g := ExactQuotient(fp, q);
  assert Evaluate(g, rt) ne 0;
  q0 := PR!q;
  g0 := PR!g;
  fR := PR!f;
  cofvec := func<pol | [Coefficient(pol,i) : i in [0..deg]]>;
  for j := 1 to prec-1 do
    // linear Hensel lift
    df := PF![c/p^j : c in Coefficients(fR - q0*g0)];
    vec := Vector(cofvec(df));
    mat := Matrix([cofvec(g), cofvec(PF.1*g)]
                    cat [cofvec(PF.1^j*q) : j in [0..deg-2]]);
    sol, ker := Solution(mat, vec);
    assert Dimension(ker) eq 0;
    q0 +:= p^j*PR![sol[1],sol[2]];
    g0 +:= p^j*PR!Eltseq(sol)[3..deg+1];
  end for;
  return q0;
end function;

function check_minimizable_at_2(f)
  // check if f (polynomial with integer coefficients) is a square mod 4
  cofs := ChangeUniverse([Coefficient(f,i) : i in [0..6]], Integers());
  if exists{i : i in [1,3,5] | IsOdd(cofs[i+1])} then
    // not even a square mod 2
    return false, _;
  end if;
  h := &+[Parent(f)| Parent(f).1^i : i in [0..3] | IsOdd(cofs[2*i+1])];
  f1 := PolynomialRing(Integers())!(f - h^2);
  return forall{c : c in Coefficients(f1) | c mod 4 eq 0}, h;
end function;

partitions := [ <[6,5,4],[3,2,1]>, <[6,5,3],[4,2,1]>, <[6,4,3],[5,2,1]>,
                <[6,2,1],[5,4,3]>, <[6,5,2],[4,3,1]>, <[6,4,2],[5,3,1]>,
                <[6,3,1],[5,4,2]>, <[6,3,2],[5,4,1]>, <[6,4,1],[5,3,2]>,
                <[6,5,1],[4,3,2]> ];

function HCinfinity(f : Steps := 10, Scale := 1)
  // Find a bound for the local height constant at infinity using the approach in
  // M. Stoll: On the height constant for curves of genus two, Acta Arith. 90, 183-201 (1999)
  // as improved by
  // J.S. Müller, M. Stoll: Canonical heights on genus two Jacobians, preprint (2016).
  //
  // f: the polynomial on the right hand side of the curve equation
  //    (which must be in "simpl" form, i.e., without a term h(x) y)
  // Steps: the number of refinement steps used for computing the bound on \mu
  // Scale: the factor by which the fourth Kummer coordinate is scaled
  //
  // returns three values:
  // + a bound on the local height difference at infinity
  // + the bound on \epsilon coming from [Stoll 1999]
  // + the roots of f
  roots := [ r[1] : r in Roots(f, ComplexField()) ];
  lcf := LeadingCoefficient(f);
  amat := ZeroMatrix(RealField(), 4, 10);    // matrix of |a_{i,{S,S'}}|
  bmat := ZeroMatrix(ComplexField(), 10, 4); // matrix of b_{{S,S'},j}
  // fill matrices with coefficients; see Formulas 10.2 and 10.3 in [Stoll 1999]
  // bmat[i,4] is multiplied by Scale (is originially = 1)
  // and amat[4,i] is divided by Scale^2
  for i := 1 to 10 do
    pi := partitions[i];
    p1 := pi[1]; p2 := pi[2];
    if Degree(f) eq 6 then
      u1 := roots[p1[1]] + roots[p1[2]];
      v1 := roots[p1[1]]*roots[p1[2]];
      s := [u1 + roots[p1[3]], u1*roots[p1[3]] + v1, v1*roots[p1[3]]];
      s0 := 1;
      res := &*[ roots[j1]-roots[j2] : j1 in p1, j2 in p2 ] * lcf^3;
    else
      s := [1, roots[p1[2]]+roots[p1[3]], roots[p1[2]]*roots[p1[3]]];
      s0 := 0;
      res := &*[ roots[j1]-roots[j2] : j1 in p1[[2,3]], j2 in p2 ] * lcf^3;
    end if;
    u2 := roots[p2[1]] + roots[p2[2]];
    v2 := roots[p2[1]]*roots[p2[2]];
    t := [u2 + roots[p2[3]], u2*roots[p2[3]] + v2, v2*roots[p2[3]]];
    bmat[i,1] := lcf*(s[3]*t[1] + s[1]*t[3]);
    bmat[i,2] := -lcf*(s[3] + s0*t[3]);
    bmat[i,3] := lcf*(s[2] + s0*t[2]);
    bmat[i,4] := Scale;
    rr := Modulus(lcf/(4*res));
    amat[1,i] := rr*Modulus(s[1]-s0*t[1]);
    amat[2,i] := rr*Modulus(s[3]-s0*t[3] + s[2]*t[1]-s[1]*t[2]);
    amat[3,i] := rr*Modulus(s[3]*t[2]-s[2]*t[3]);
    amat[4,i] := lcf^2*rr*Modulus(s[1]*s[3]^2*t[2] - s0^2*s[2]*t[1]*t[3]^2
                                  + s[1]*s[2]*t[1]*t[2]*(s[3] - s0*t[3])
                                  - s[3]*t[3]*(s[1]*s[2] - s0^2*t[1]*t[2])
                                  - s[1]*t[1]*(s[2]^2*t[3] - s0*s[3]*t[2]^2)
                                  - s[1]^2*s[3]*t[2]^2 + s0*s[2]^2*t[1]^2*t[3]
                                  + 4*s[1]*s[3]*t[1]*t[3]*(s[1] - s0*t[1])
                                  + s[2]*t[2]*(s[1]^2*t[3] - s0*s[3]*t[1]^2)
                                  - s0*(s[3]^2*t[1]*t[2] - t[3]^2*s[1]*s[2])
                                  + s0*(4*s[3]*t[3]*(s[3] - s0*t[3])
                                        + 4*s[2]*t[2]*(s[3]*t[2] - s[2]*t[3])
                                        - 3*s[3]*t[3]*(s[2]*t[1] - s[1]*t[2])))/Scale^2;
  end for;
  eseq := [[1,e2,e3,e4] : e2, e3, e4 in [1,-1]];
  function step(ds)
    // This is the function f from [Müller-Stoll]
    bvec := Vector([Sqrt(Max([Modulus(&+[bmat[i,j]*es[j]*ds[j] : j in [1..4]]) : es in eseq]))
                     : i in [1..#partitions]]);
    return [Sqrt((amat[k], bvec)) : k in [1..4]];
  end function;
  bn := step([RealField()| 1, 1, 1, 1]);
  bnabs := Max([Abs(b) : b in bn]);
  gamma := 4*Log(bnabs);
  sum := gamma;
  bn := [b/bnabs : b in bn];
  for n := 2 to Steps do
    bn := step(bn);
    bnabs := Max([Abs(b) : b in bn]);
    sum +:= 4^n*Log(bnabs);
    bn := [b/bnabs : b in bn];
  end for;
  return sum/(4^Steps-1), gamma, roots;
end function;

intrinsic HeightConstantNew(J::JacHyp : Factor := true, Steps := 10,
                                        Modified := false, Fast := false)
  -> FldReElt, FldReElt
{If J is the Jacobian of a gneus 2 curve defined over the rationals,
 of the form  y^2 = f(x)  with integral coefficients, this computes
 a real number c such that  h_K(P) le h(P) + c  for all P in J(Q),
 where h_K is the naive logarithmic height obtained from the Kummer surface
 and h is the canonical height on J.
 The second value returned is a bound for |mu_infinity|.
 If Factor is set, then the discriminant will be factored, and its prime divisors
 will be considered individually. This usually results in an improvement
 of the bound.
 If Fast is set, the cheap bound from [Stoll 1999] is used (and Factor is ignored).
 If Modified is set, the modified naive height is used as in [Müller-Stoll 2016].}
    // Based on
    // J.S. Müller, M. Stoll: Canonical heights on genus two Jacobians, preprint (2016).
    C := Curve(J);
    // check the assumptions on J
    require Genus(C) eq 2 and CoefficientRing(C) cmpeq Rationals():
            "HeightConstant is only implemented",
            "for Jacobians of genus 2 curves over the rationals.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0 and &and[ Denominator(c) eq 1 : c in Coefficients(f)]:
            "HeightConstant needs a curve of the form  y^2 = f(x), ",
            "where f has integral coefficients.";
    // only cache results when Factor is set; use quadruple
    // [*height-const, mubound, height-const', mubound'*]
    // where the second pair of values is for the Modified version.
    // Use 'false' as a placeholder for missing values
    if assigned J`HeightConstNew then
      if Modified and J`HeightConstNew[3] cmpne false then
        return J`HeightConstNew[3], J`HeightConstNew[4];
      elif not Modified and J`HeightConstNew[1] cmpne false then
        return J`HeightConstNew[1], J`HeightConstNew[2];
      end if;
    end if;
    lcf := Abs(LeadingCoefficient(f));
    K := KummerSurface(J);
    c := GCD(ChangeUniverse(Eltseq(f), Integers()));
    // primitive version of f if Modified:
    // we are effectively using the Kummer surface of y^2 = fm(x)
    fm := Modified select f/c else f;
    // scaling of the naive height at infinity
    // is given by ||f||_infty if Modified is set, 1 else.
    scale := Modified select Max([Abs(c) : c in Coefficients(fm)]) else 1;
    // compute local contribution at infinity to height difference bound
    beta_inf, hc_inf, roots := HCinfinity(fm : Steps := Steps, Scale := scale);
    // --> beta_inf is the bound, hc_inf is a bound on epsilon_infty,
    //     roots are the roots of f
    vprintf JacHypHeight, 1: " Bounds for epsilon and mu at infinity:\n";
    vprintf JacHypHeight, 1: "   %o and %o\n", hc_inf, beta_inf;
    // Determine upper bound for |log(|delta(P)|/|P|^4)| at infinity
    hc_inf_both := Max(hc_inf,
                       Log(Max([Abs(t) :
                                t in &cat[Coefficients(d) :
                                          d in KummerSurface(J)`Delta]])));
    // Now find a bound for the finite part
    disc := Integers()!Abs(Discriminant(C)/256); // this is |disc(F)|
    disc1 := ExactQuotient(16*disc, Modified select c^10 else c^6);
    // first bound
    hc_finite := Log(disc1)/3;
    vprintf JacHypHeight, 1: " Bound for finite part of height constant:\n";
    vprintf JacHypHeight, 1: "   %o\n", hc_finite;

    if Fast then
      // return the easy bound
      return hc_finite + beta_inf, hc_inf_both;

    elif not Factor then
      // Use bound via R(S, S').
      // For a subset S of {1,2,3,4,5,6}, let F_S be the corresponding
      //  divisor of F (= homogenization of f of degree 6).
      // Find the product over all (X - Disc(F_S) Disc(F_S')) where
      //  {S, S'} is a partition of {1,...,6} into two three-sets.
      //  This is a polynomial with integral coefficients.
      vprintf JacHypHeight, 1: "  Look at R(S,S')^2...\n";
      // First use the absolute values in order to estimate the
      //  precision needed.
      lcfm := Modified select (lcf/c)^4 else lcf^4;
      if Degree(f) eq 6 then
        ds := [ Modulus(lcfm*dis(part[1])*dis(part[2])) : part in partitions ]
              where dis := func< p | (roots[p[1]]-roots[p[2]])^2
                                      * (roots[p[1]]-roots[p[3]])^2
                                      * (roots[p[2]]-roots[p[3]])^2 >;
      else // deg(f) = 5
        ds := [ Modulus(lcfm*(roots[part[1][2]]-roots[part[1][3]])^2
                              *dis(part[2]))
                  : part in partitions ]
              where dis := func< p | (roots[p[1]]-roots[p[2]])^2
                                      * (roots[p[1]]-roots[p[3]])^2
                                      * (roots[p[2]]-roots[p[3]])^2 >;
      end if; // Degree(f) eq 6
      cs := Eltseq(&*[ PR.1 - d : d in ds ]) where PR is
                                        PolynomialRing(RealField());
      prec := Ceiling(Log(Max(cs))) + 6;
      vprintf JacHypHeight, 2: "   Estimated precision: %o decimal digits.\n",
              prec;
      // Recompute the roots to the new precision
      roots := [ r[1] : r in Roots(f, ComplexField(prec)) ];
      // Now compute the polynomial we want
      PC := PolynomialRing(ComplexField(prec));
      if Degree(f) eq 6 then
        dp := &*[ PC.1 - lcfm*dis(part[1])*dis(part[2]) : part in partitions ]
              where dis := func< p | (roots[p[1]]-roots[p[2]])^2
                                      * (roots[p[1]]-roots[p[3]])^2
                                      * (roots[p[2]]-roots[p[3]])^2 >;
      else // deg(f) = 5
        dp := &*[ PC.1 - lcfm*(roots[part[1][2]]-roots[part[1][3]])^2
                              *dis(part[2])
                  : part in partitions ]
              where dis := func< p | (roots[p[1]]-roots[p[2]])^2
                                      * (roots[p[1]]-roots[p[3]])^2
                                      * (roots[p[2]]-roots[p[3]])^2 >;
      end if; // Degree(f) eq 6
      ds := Eltseq(dp);
      cs := [ Round(Real(c)) : c in ds ];
      require Max([Modulus(cs[i] - ds[i]) : i in [1..11]]) le 0.1 :
              "Insufficient precision in computation of resolvent polynomial.";
      // Check that suitable powers of disc divide the lower coeffs
      discm := Modified select ExactQuotient(disc, c^10) else disc;
      require (cs[1] eq discm^4) and (cs[2] mod discm^3 eq 0)
                and (cs[3] mod discm^2 eq 0) and (cs[4] mod discm eq 0) :
              "Insufficient precision in computation of resolvent polynomial.";
      // Now split off the primes that will contribute to improving the bound
      g := GCD(cs[[5..10]]);
      vprintf JacHypHeight, 2: "   `Small primes factor' = %o\n", g;
      if g eq 1 then
        vprintf JacHypHeight, 2: "   no improvement\n";
      else
        pl := [ a[1] : a in Factorization(g) ];
        vprintf JacHypHeight, 2: "   is divisible by primes ";
        if GetVerbose("JacHypHeight") ge 2 then
          for i := 1 to #pl do
            if i lt #pl
              then printf "%o, ", pl[i];
              else printf "%o\n", pl[i];
            end if;
          end for;
        end if; // GetVerbose("JacHypHeight") ge 2
        improve := 1;
        for p in pl do
          im_p := Min([Ceiling(Valuation(cs[i], p)/(11-i)) : i in [1..10]
                                                            | cs[i] ne 0]);
          vprintf JacHypHeight, 2: "   improvement by  %o log %o\n", im_p, p;
          improve *:= p^im_p;
        end for;
        disc1 := ExactQuotient(disc1, improve);
        hc_finite -:= Log(improve)/3;
        vprintf JacHypHeight, 2: " New finite part is %o\n", hc_finite;
      end if; // g eq 1
      vprintf JacHypHeight, 1: " Result (beta_inf + beta_finite) is\n  %o\n\n",
              hc_finite + beta_inf;
      return hc_finite + beta_inf, hc_inf_both;

    else // Factor is set
      vprintf JacHypHeight, 2: " Factoring the finite bound...\n";
      fact := Factorization(disc1);
      vprintf JacHypHeight, 2: "  Factorization: %o\n", fact;
      // Use techniques from Mueller-Stoll
      hc_finite := 0.0;
      // compute Igusa invariants of C or the primitive version of C
      J2, J4, J6, J8, J10 := Explode(JInvariants(fm, Parent(f)!0));
      // need I4 and I12 from Liu's '93 paper Courbes stables de genre 2 et leur schema de modules
      I4 := J2^2 - 2^3*3*J4;
      I12 := -2^3*J4^3 + 3^2*J2*J4*J6 - 3^3*J6^2 - J2^2*J8;
      jinvs := [J2, J4, J6, J8, J10, I4, I12];
      C_min := Modified select HyperellipticCurve(fm) else C;
      discm := Modified select ExactQuotient(disc, c^10) else disc;
      // check if minimization at 2 is possible by introducing mixed terms
      flag2, h := check_minimizable_at_2(fm);
      if flag2 then
        // yes: scale Igusa invariants as when doing the minimization
        for i := 1 to #jinvs do
          jinvs[i] /:= 16^([1,2,3,4,5,2,6][i]);
        end for;
        C_min := HyperellipticCurve((fm - h^2)/4, h);
      end if;
      vprintf JacHypHeight, 3: "  Igusa invariants are %o\n", jinvs;

      for fp in fact do
        p := fp[1]; v := fp[2]; vd := Valuation(discm, p);
        vprintf JacHypHeight, 2: "  p = %o: v_%o(disc) = %o.\n", p, p, vd;
        if not Modified or IsEven(Valuation(c, p)) then
          // deal with simple cases from [Stoll 2002, Prop. 5.2]
          if vd eq 1 then
            vprintf JacHypHeight, 2: "   v_%o = 1 --> can remove %o.\n", p, p;
            disc1 := ExactQuotient(disc1, p^v);
            v := 0;
          elif IsOdd(p) and vd le 4 then
            fred := PolynomialRing(GF(p))!ChangeUniverse(Eltseq(fm), Integers());
            factred := [ a[2] : a in Factorization(fred) ];
            if Degree(f) lt 6 then factred cat:= [6 - Degree(f)]; end if;
            vprintf JacHypHeight, 2:
                    "   Exponents in factorization of f mod %o:\n   %o\n",
                    p, factred;
            // now factred is the sequence of exponents in the factorisation
            // of the homogenized f
            if Max(factred) eq vd + 1 then
              vprintf JacHypHeight, 2:
                    "   Model is regular at %o, f mod %o has at least 2 roots,\n",
                    p, p;
              vprintf JacHypHeight, 2 :
                      "     with only one of them multiple --> can remove %o.\n",
                      p;
              disc1 := ExactQuotient(disc1, p^v);
              v := 0;
            end if; // Max(factred) eq vd + 1
          end if; // vd eq 1
        end if; // not Modified or IsEven(Valuation(c, p))

        if v gt 0 then
          // Check which reduction type we're in.
          // We can get nontrivial improvements if we have nodal or cuspidal reduction.
          // This can be checked easily using Igusa invariants.
          // To do:  non-reduced reduction
          jinvs_mod_p := ChangeUniverse(jinvs, GF(p));
          vd := Valuation(jinvs[5], p); // v(Delta(C))
          vprintf JacHypHeight, 2:
                "   Igusa invariants mod %o are %o\n", p, jinvs_mod_p;
          beta := vd / 4; // crude upper bound

          if not IsZero(jinvs_mod_p[5]) then // smooth reduction, should not occur
            vprintf JacHypHeight, 2: "   Reduction type [I_{0-0-0}]\n";
            beta := 0;

          elif not IsZero(jinvs_mod_p[7]) then // one node. Use Cor. 9.7
            vprintf JacHypHeight, 2: "   Reduction type [I_{%o-0-0}]\n", vd;
            if not Modified or IsEven(Valuation(c, p)) then
              // Modified and scaling by odd power of p
              //  --> use \bar{beta} = vd/4, so nothing to do
              Cp := ChangeRing(C_min, GF(p, 2)); // reduction of C_min over F_p
              P := SingularPoints(Cp)[1]; // have only one sing pt
              split := not IsIrreducible(TangentCone(Cp, P)); // check if node is split
              beta := split or IsEven(vd) select 1/2/vd*Floor(vd^2/2) else 0;
            end if; // not Modified or IsEven(Valuation(c, p))

          elif not IsZero(jinvs_mod_p[6])
                 and not (IsZero(jinvs_mod_p[2])
                 and IsZero(jinvs_mod_p[3])) then  // two nodes. Use Cor. 9.9
            m1 := Integers()!Min([vd/2, Valuation(jinvs[7], p)]);
            m2 := vd - m1;
            vprintf JacHypHeight, 2: "   Reduction type [I_{%o-%o-0}]\n", m1, m2;
            if not Modified or IsEven(Valuation(c, p)) then
              // Modified and scaling by odd power of p
              //  --> use \bar{beta} = vd/4, so nothing to do
              Cp := ChangeRing(C_min, GF(p, 6));  // reduction of C_min over F_p^6
              sing_pts := SingularPoints(Cp);
              assert #sing_pts eq 2;
              // check if nodes are split
              split := [not IsIrreducible(TangentCone(Cp, P)) : P in sing_pts];
              even := [IsEven(m) : m in [m1, m2]];
              if not &or even and not &or split then // both nodes non-split and odd
                beta := 0;
              elif p eq 2 and (not &or split and not &or even) then // one node is non-split and odd
                // upper bound may not be optimal.
                beta := 1/2/m*Floor(m^2/2) where m is Maximum(m1, m2);
              elif p ne 2 and (not &and split or not &and even) then
                // at least one node is non-split or odd
                // Need to match the mis with the splitting information, i.e.
                // need to find out which mi corresponds to which node
                //
                // To do: p=2
                D, sigma := SimplifiedModel(C_min); // v(sigma) = 0!
                g := HyperellipticPolynomials(D);
                rts := [t[1] : t in Roots(ChangeRing(g, GF(p))) | t[2] eq 2];
                Dp := ChangeRing(D, GF(p, 6));
                if IsEmpty(rts) then // nodes are conjugate
                  assert IsEven(vd);
                  mis := [vd div 2, vd div 2]; // can take split as above
                else
                  mis := [Valuation(Discriminant(liftquf(g, rts[1], vd+1)))];
                  Append(~mis, vd-mis[1]);
                  split := [not IsIrreducible(TangentCone(Dp, P)) :
                                            P in [Dp![r, 0] : r in rts]]; //affine nodes split?
                  if #split eq 1 then // have a node at infinity
                    P := [Q : Q in SingularPoints(Dp) | Q[3] eq 0][1]; // P is that node
                    Append(~split, not IsIrreducible(TangentCone(Dp, P))); // P split?
                  end if;
                end if; // IsEmpty(rts)
                assert #split eq 2;
                if not split[1] and IsOdd(mis[1]) then  // first node non-split and odd
                  beta := 1/2/mis[2]*Floor(mis[2]^2/2);
                elif not split[2] and IsOdd(mis[2]) then  // second node non-split and odd
                  beta := 1/2/mis[1]*Floor(mis[1]^2/2);
                else // both nodes split or even
                  beta := 1/2/m1*Floor(m1^2/2) + 1/2/m2*Floor(m2^2/2);
                end if;
              else // both nodes split or even or we have p=2 and ...
                beta := 1/2/m1*Floor(m1^2/2) + 1/2/m2*Floor(m2^2/2);
              end if;
            end if; // not Modified or IsEven(Valuation(c, p))

          elif not IsZero(jinvs_mod_p[6]) then // 3 nodes. Use Cor. 9.10
            Cp := ChangeRing(C_min, GF(p));  // reduction of C_min over F_p
            n := Valuation(jinvs[7], p);
            m := Valuation(jinvs[2], p);
            m3 := Integers()!Min([vd/3, n/2, m]);
            m2 := Integers()!Min([n - m3, (vd - m3)/2]);
            m1 := vd - m3 - m2;
            assert m3 le m1 and m3 le m2;
            vprintf JacHypHeight, 2: "   Reduction type [I_{%o-%o-%o}]\n", m1, m2, m3;
            if not Modified or IsEven(Valuation(c, p)) then
              M := m1*m2 + m1*m3 + m2*m3;
              split := not IsIrreducible(Cp); // C is split if cpts are defined over F_p
              sing_pts := SingularPoints(Cp);
              if split and #sing_pts eq 3 then // all nodes defined over F_p and C split
                beta := 1/2/M*(m2*Floor(m1^2/2) + m3*Floor((m1+m2)^2/2) + m1*Floor(m2^2/2));
              elif #sing_pts eq 3 then // all nodes defined over F_p and C non-split
                even_mi := [m : m in [m1, m2, m3] | IsEven(m)];
                max_even_mi := Maximum([0] cat even_mi);
                beta := (max_even_mi + Maximum([0] cat [m : m in even_mi | m lt max_even_mi]))/4;
              elif #sing_pts eq 1 then // one node def'd over F_p, two in F_p^2 and conjugate / F_p
                if m1 ne m2 then // have m1 = m2 or m2 = m3. want m3 to correspond to the rational node
                  m3 := m1;
                  m1 := m2;
                end if;
                // now have m1 = m2
                if split then
                  beta := m1/M * Max(Floor(m1^2/2) + m1*m3, Floor(m3^2/2) + m1 * Floor(m3/2));
                elif IsEven(m1) then
                  beta := m1 / 2;
                else
                  beta := 0;
                end if; // split
              else // all nodes in F_p^3 and conjugate / F_p
                beta := split select vd / 9 else 0;
              end if; // split and #sing_pts eq 3
            else
              // Modified and scaling by odd power of p --> use \bar{beta} = (m1+m2)/4
              beta := (m1 + m2)/4;
            end if; // not Modified or IsEven(Valuation(c, p))

          elif not &and[IsZero(j) : j in jinvs_mod_p] then // cusp in reduction. Use Thm 10.13.
            // The reduction type is [K_1-K_2-l]. need to find K_1, K_2 and l.
            // We want to change the model s.t. the singularities are at (0,0) and infty
            if p ne 2 then // To do: p=2
              precp := 2*(vd + 2);
              flag := false; // flag will be set if computation with given precision was successful
              repeat
                vprintf JacHypHeight, 3: "    current %o-adic precision is %o\n", p, precp;

                sing_pts := SingularPoints(ChangeRing(C_min, GF(p)));
                // choice of p-adic field depends on field of def'n of singularities.
                if IsEmpty(sing_pts) then // two cusps def'd over F_p^2 and conjugate / F_p
                  sing_pts := SingularPoints(ChangeRing(C_min, GF(p, 2)));
                  Kp := UnramifiedExtension(pAdicField(p, precp), 2);
                else // cusp(s) defined over F_p
                  Kp := pAdicField(p, precp);
                end if;
                D := move_points(ChangeRing(C_min, Kp), sing_pts); // move singularities to 0 and infty
                PKp := PolynomialRing(Kp);
                fD, hD := HyperellipticPolynomials(D);
                try
                  // factor 4fD+hD^2 to find elliptic curves E_1 and E_2 such that
                  // E_i has Kodaira type K_i.
                  fact := Factorisation(4*fD+hD^2);
                  flag := true;
                catch e
                  precp *:= 2; // double p-adic precision after each unsuccessful attempt
                end try;
              until flag;
              kp, pi := ResidueClassField(Integers(Kp));
              Pkp := PolynomialRing(kp);
              reduce_poly := func<g | Pkp!Polynomial(kp, [pi(c) : c in Coefficients(g)])>;
              make_primitive := func<h | ShiftValuation(h, -Min([Valuation(a)
                                                                  : a in Coefficients(h)]))>;
              if Degree(reduce_poly(4*fD + hD^2)) eq 3 then // cusp at infty
                fact1 := [ t :t in fact | Degree(reduce_poly(make_primitive(t[1]))) gt 0];
              else // cusp at origin
                fact1 := [t : t in fact
                            | IsZero(ConstantCoefficient(reduce_poly(make_primitive(t[1]))))];
              end if;
              r := &*[make_primitive(t[1]) : t in fact1]; // r encodes information at origin
              r0, r1, r2, r3 := Explode(Coefficients(r));
              s := &*[make_primitive(t[1]) : t in fact | t notin fact1];
                 // s encodes information at infty
              s3, s2, s1, s0 := Explode(Coefficients(s) cat [0,0,0,0]);
              E1 := EllipticCurve([0, r2, 0, r1*r3, r0*r3^2]); // contains info at origin
              E2 := EllipticCurve([0, s2, 0, s1*s3, s0*s3^2]); // contains info at infty
              L1 := LocalInformation(E1); // run Tate's algorithm on E1
              L2 := LocalInformation(E2); // run Tate's algorithm on E2
              /*
                f0, f1, f2, f3, f4, f5, f6 := Explode([Coefficient(fD, i) : i in [0..6]]);
                h0, h1, h2, h3 := Explode([Coefficient(hD, i) : i in [0..3]]);
                E1 := EllipticCurve([h1, f2, h0*f3, f1*f3, f0*f3^2]); // encodes information at (0,0)
                E2 := EllipticCurve([h2, f4, h3*f3, f5*f3, f6*f3^2]); // encodes information at infty
              */
              // Now find K_1, K_2 and l. The first two are contained in L1 and L2
              // we know that vd = v(Delta_min(E1) + v(Delta_min(E2)) + 12 l
              assert IsDivisibleBy(vd - L1[2] - L2[2], 12);
              l := (vd - L1[2] - L2[2]) div 12;
              vprintf JacHypHeight, 2: "   Reduction type [%o-%o-%o]\n", L1[5], L2[5], l;
              if not Modified or IsEven(Valuation(c, p)) then
                beta := alpha_p(L1[4], L1[5]) + alpha_p(L2[4], L2[5]) + 2*l;
              else
                // Modified and scaling by odd power of p --> (L1[2]+L2[2])/4 + 2l
                beta := (L1[2]+ L2[2])/4 + 2*l;
              end if;
            end if; // p ne 2
          end if; //not IsZero(jinvs_mod_p[5])

          vprintf JacHypHeight, 1: "  beta_%o is %o\n", p, beta;
          vprintf JacHypHeight, 1: "  gamma_%o/3 is %o\n", p, Valuation(disc1, p)/3;
          // Sometimes gamma/3 is better than our beta:
          beta := Min(beta, Valuation(disc1, p)/3);
          hc_finite +:= beta*Log(p);
        end if; // v gt 0
      end for; // fp in fact
    end if; // Fast / not Factor / Factor
    // if we have miminized at 2, take note of the scaling of the delta polynomials by 1/64
    if flag2 then hc_finite +:= Log(4); end if;

    vprintf JacHypHeight, 1: " Result (beta_inf + beta_finite) is\n  %o\n\n",
            hc_finite + beta_inf;
    if not assigned J`HeightConstNew then
      J`HeightConstNew := [*false, false, false, false*];
    end if;
    if Modified then
      J`HeightConstNew[3] := hc_finite + beta_inf;
      J`HeightConstNew[4] := hc_inf_both/3;
    else
      J`HeightConstNew[1] := hc_finite + beta_inf;
      J`HeightConstNew[2] := hc_inf_both/3;
    end if;
    return hc_finite + beta_inf, hc_inf_both/3;
end intrinsic;
