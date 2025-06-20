// Initialize the qc/mws computation for genus 2 curves having RM and rank 2.
// This requires magma version >= 2.25 for MordellWeilGroupGenus2.
//
// If your version of magma is older, use a subgroup of finite index, or find the code on
// Stoll's webpage.

load "mws_qc.m";  // Mordell-Weil sieve implementation


PR<x> := PolynomialRing(RationalField());

function MakeIsZero(R)
  if (Type(R) eq RngSerLaur) then
    if ((R!1) - (R!1) eq 0) then
      return func< z | z eq 0 or RelativePrecision(z) eq 0 >;
    else
      return func< z | z eq 0 or Valuation(z) ge prec > where prec := AbsolutePrecision(R!1);
    end if;
  elif Type(R) eq FldPad then
    return func< z | IsWeaklyZero(z)>;
  else
    return func< z | z eq R!0 >;
  end if;
end function;

function number_of_non_unit_roots(f)
// f is a p-adic polynomial in 1 variable with integral coeffs
// Find the number of non-unit roots of f, including roots over 
// extension fields.
    count := 0; // count contains the number of non-unit roots
    fact := Factorisation(f);
    for t in fact do
        if Valuation(ConstantCoefficient(t[1])) gt 0 then 
            // else disregard t
            if Degree(t[1]) eq 1 then 
                // linear factor with non-unit root
                count +:= t[2];
            else
                n := Degree(t[1]);
                A := AllExtensions(BaseRing(f), n);
                done := false;
                i := 1;
                while not done do
                    assert i le #A;
                    K := A[i];
                    fK := ChangeRing(t[1], K);
                    if not IsIrreducible(fK) then
                        //fK splits, recurse
                        count +:= t[2]*number_of_non_unit_roots(fK);
                        done := true;
                    end if;
                    i +:=1;
                end while;
            end if;
        end if;
    end for;
    return count;
end function;

function is_ordinary(Q, p, g, N)
// Check if the curve is ordinary at p
  //if assigned(data`ordinary) then return data`ordinary; end if;
  //Q:=data`Q; p:=data`p; d:=Degree(Q); g := data`g;
  d := Degree(Q);
  Fp:=FiniteField(p); Fpx:=RationalFunctionField(Fp); Fpxy:=PolynomialRing(Fpx);
  f:=Fpxy!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+(Fp!Coefficient(Coefficient(Q,i),j))*Fpxy.1^i*Fpx.1^j;
    end for;
  end for;
  FFp:=FunctionField(f); // function field of curve mod p

  pol := ReciprocalPolynomial(Numerator(ZetaFunction(FFp)));
// pol is the characteristic poly of Frobenius
  K := pAdicField(p, N);
// now lift pol to K
  pol_lifted := ChangeRing(pol, K);
// curve is ordinary iff half of the roots of the char poly of Frobenius
// are units.
  return number_of_non_unit_roots(pol_lifted) eq g;
end function;



function is_good_ordinary(C, p)
// C is a hyperelliptic curve over the rationals, p is a prime
// Check if C is good and  ordinary at p
// TO DO: same as the abpove, merge!
    g := Genus(C);
    if Valuation(Discriminant(C), p) ne 0 then
        // C has bad reduction at p
        return false;
    end if;
    Cp := ChangeRing(C, GF(p));
    pol := ReciprocalPolynomial(Numerator(ZetaFunction(Cp)));
// pol is the characteristic poly of Frobenius
    K := pAdicField(p, 50);
// now lift pol to K
    pol_lifted := ChangeRing(pol, K);
// C is ordinary iff half of the roots of the char poly of Frobenius
// are units.
    return number_of_non_unit_roots(pol_lifted) eq g;
end function;
    


function has_odd_degree_model_at_p(C, p : N := 20)
  // Find an odd degree model over Qp if one exists.
  Qp := pAdicField(p, N);
  Cp := ChangeRing(C, Qp);
  g := Genus(Cp);
  error if g ne 2, "Currently only implemented for genus 2";
  n := 2*g+2;
  fp := HyperellipticPolynomials(Cp);
  if IsOdd(Degree(fp)) then 
    _, phi := Transformation(Cp, [1,0,0,1]);
    return true, Cp, phi;
  end if;

  b, rt := HasRoot(fp);
  if not b then return false, _, _; end if;

  is_zero := MakeIsZero(BaseRing(fp));
  x1 := rt*Parent(fp).1 +1;
  z1 := Parent(fp).1;
  odd_fp := &+[Coefficient(fp,i)*x1^i*z1^(n-i) : i in [0..n] | not is_zero(Coefficient(fp, i))];
  assert is_zero(Coefficient(odd_fp, n));
  
  odd_fp := Polynomial(Qp, [Coefficient(odd_fp, i) : i in [0..n-1]]);
  Ep := HyperellipticCurve(odd_fp);
  lc := LeadingCoefficient(odd_fp);
  Fp := Transformation(Ep, [lc, 0,0,1], lc^2); // monic model
  
  // construct map from Cp to Ep. 
  // We prefer MapIsoSch, but due to precision issues this might not be possible.
  bool := IsIsomorphic(Cp, Fp);
  if bool then _, phi :=IsIsomorphic(Cp, Fp); end if;
  if not bool then
    bool2, psi := IsIsomorphic(Fp, Cp);
    if not bool2 then 
      P2C<XC,YC,ZC> := Ambient(Cp);   
      P2F<XF,YF,ZF> := Ambient(Fp);   
      phi :=  map<P2C -> P2F | [lc*ZF, lc^2*YF, XF-rt*ZF]>; 
    else 
      phi := Inverse(psi);
    end if;
  end if;
  return true, Fp, phi; 
end function;


function splits_over_Qp(f, Qp)
  fact := Factorisation(ChangeRing(f, Qp));
  if #fact eq 0 then return false; end if;
  return &+[t[2] : t in fact] eq Degree(f);
end function;

function is_pointwise_Qp_rational(P, Qp, Cp)
  // for now assume all pts in L are affine.
  // potential problem for g=3, deg=8
  if not splits_over_Qp(P[1], Qp) then
    return false, _;
  end if;
  ap := ChangeRing(P[1], Qp);
  roots := Roots(ap);
  P_list := [];
  for t in roots do
    xx := t[1];
    yy := Evaluate(Parent(ap) ! (P[2]), xx);
    P_list cat:= [[xx, yy] : i in [1..t[2]]];
  end for;
  return true, P_list;
end function;


function odd_degree_model_points(D, phi)
  // D is a sequence of p-adic points on a hyperelliptic curve C
  // phi is an isomorphism from C to another hyperelliptic curve.
  // return the images of the points in D 
  P2 :=  Domain(phi);
  p := Prime(BaseRing(P2));
  lp := [];
  for P in D do
    Q := phi(P2!Eltseq(P));
    Append(~lp,Q);
  end for;
  return lp;
end function;


function get_lambda(L, C, phi, lb, x_coords, Qp : odd_degree := true)
  // see the doc for height_init_g2
  lambda := lb;
  f := HyperellipticPolynomials(C);
  p := Prime(Qp);
  P1s := Universe(x_coords);
  while &*[Evaluate(P[1],lambda) : P in L] eq 0 or (not IsSquare(Qp ! Evaluate(f, lambda))) or IsZero(Evaluate(f, lambda)) or P1s![lambda mod p, 1] in x_coords do
    lambda +:= 1;
    error if lambda gt 50, "Can't find a suitable lambda";
  end while;
  b, yy := IsSquare(Qp ! Evaluate(f, lambda));
  assert b;
  Cp := HyperellipticCurve(ChangeRing(f, Qp));

  Q1 := Cp ! [lambda, yy];
  Q2 := Cp ! [lambda, -yy];
  if odd_degree then 
    pts := odd_degree_model_points([Q1,Q2], phi);
    P1, P2  := Explode(pts);
    // Check for Weierstrass point...
    assert not IsWeaklyZero(P1[2]) and not IsWeaklyZero(P2[2]);
  end if;

  Q1_seq := [Eltseq(Q1)[1]/Eltseq(Q1)[3], Eltseq(Q1)[2]/Eltseq(Q1)[3]^3];
  Q2_seq := [Eltseq(Q2)[1]/Eltseq(Q2)[3], Eltseq(Q2)[2]/Eltseq(Q2)[3]^3];
  return lambda, [Q1_seq, Q2_seq], pts;
end function;


function local_int(C, P, Q, lambda, mu)
  // compute all intersections between divisors representing P and Q
  // See 2014 Math Comp paper by JS Müller
  J := Jacobian(C);
  if P eq Q then 
    lid := LocalIntersectionData(J ! [P[1], P[2]], - J ! [Q[1], Q[2]]: lambda := lambda, mu := mu);
    return [<l[1], -l[2], l[3]> : l in lid];
  else
    return LocalIntersectionData(J ! [P[1], P[2]], J ! [Q[1], Q[2]]: lambda := lambda, mu := mu);
  end if;
end function;


function print_local_int(C, P, Q, lambda, mu)
  ints := local_int(C, P, Q, lambda, mu); 
  // TODO: need to make sure lambda and mu aren't changed. This shouldn't happen, but better check
  assert &and[IsOne(t[3]) : t in ints];
  return [[t[1], t[2]] : t in ints | t[2] ne 0];
end function;


function rationalize(D)
  rat_div := [ChangeUniverse(Eltseq(P), Rationals()) : P in D];
  return [[P[1], P[2]] : P in rat_div];
end function;


function find_qc_primes(X : qc_primes_bound := 100, mws_primes_bound := 1000, ordinary := true, 
               printlevel := 0, number_of_bad_disks := 0, mws_quot_bd := 10, inf_modp_allowed := true , known_rat_pts := [])
  // X is a genus 2 curve over the rationals
  // Find good primes for quadratic Chabauty / Mordell-Weil sieve combination
  //
  // * ordinary: if true, only allow ordinary primes for qc 
  // * number_of_bad_disks: only look at primes for qc such that we have this number of
  //   Weierstrass pts mod p. In practice this is 0 or 1 (1 if we need an odd degree model
  //   mod p, to compute local heights at p for divisors) 
  // * mws_quot_bd controls the allowed quality of the mws-primes, i.e. the probability
  //   that we'll get nontrivial information from them
  // * if inf_modp_allowed is true, then we allow qc primes p such that there are
  //   p-adically rational points at infinity.
  //
  assert Genus(X) eq 2;
  f,h := HyperellipticPolynomials(X);
  assert IsZero(h);
  disc := Integers()!Discriminant(f);
  J := Jacobian(X);
  
  // Find good primes for the MWSieve
  if ordinary then 
    gops := [p : p in PrimesInInterval(3, qc_primes_bound) | is_good_ordinary(X, p)];
  else
    gops := [p : p in PrimesInInterval(3, qc_primes_bound)];
  end if;
  qc_primes := [p : p in gops | #Roots(ChangeRing(f, pAdicField(p))) eq number_of_bad_disks];
  if not inf_modp_allowed then  // want no rational points in disks at infinity
    qc_primes := [p : p in qc_primes | &and[Numerator(P[3]) mod p ne 0 : P in known_rat_pts]]; 
  end if;
  assert #qc_primes gt 0;
  good_primes := [v : v in PrimesInInterval(3, mws_primes_bound) | not IsDivisibleBy(disc, v)]; 
  number_of_primes := #good_primes;
  time groups := [AbelianGroup(BaseChange(J, GF(good_primes[i]))) : i in [1..number_of_primes]];
  prime_quality := [];
  // TODO: Sort in a more meaningful way. 
  for p in qc_primes do
    if printlevel gt 0 then "p", p; end if;
    _, quots := sieving_primes(p^10,  good_primes, groups, mws_quot_bd : printlevel := printlevel);
    if IsEmpty(quots) then 
      Append(~prime_quality, []);
    else 
      Append(~prime_quality, quots); // 
    end if;
  end for;
  //ParallelSort(~prime_quality, ~qc_primes);
  //prime_exponents := [Max([Valuation(Exponent(G), p) : G in groups]) : p in qc_primes];
    
  return qc_primes, groups, good_primes, prime_quality;
end function;


function generators_g2(J)
  // Compute generators of the Mordell-Weil group of a genus 2 Jacobian
  // Uses Stoll's MordellWeilGroupGenus2
  A, psi, finite_index, proved := MordellWeilGroupGenus2(J);
  assert proved and finite_index; // otherwise, more work...
  torsion_orders := [Order(A.i) : i in  [1..#Generators(A)] | Order(A.i) gt 0]; 
  torsion_bas := [psi(A.i) : i in [1..#torsion_orders]];
  free_gens := [psi(A.i) : i in [#torsion_bas+1..#Generators(A)]]; 
  assert #free_gens eq 2; // Need rank = 2
  return torsion_bas, torsion_orders, free_gens;
end function;


function height_init_g2(X, p, free_gens : N := 20, multiple_bound := 50, make_odd_degree := true, printlevel := 0)

  // Find generators that have good properties at p and compute local Coleman-Gross heights away from p
  // X is a hyperelliptic curve, currently restricted to genus 2
  // p is a good prime, currently assumed ordinary
  // free_gens is a sequence of 2 independent points 
  // if make_odd_degree is true, then we return the p-adic data on an odd degree model.
  // The generators are represented by divisors of the form 
  //  D-div0(x-lambda) and  E-div0(x-mu)
  // for effective D and E and suitable constants lambda and mu so that we can compute local heights between
  // them.
  // Because of the current implementation of the local heights at p on divisors,
  // this means we want
  // * the supports to be away from Weierstrass disks 
  // * the base changes of the generators to Qp to have pointwise rational support
  // * these points to live in distinct residue disks for different generators
  //
  Xs := ChangeRing(X, GF(p));
  P1s := ProjectiveSpace(GF(p),1);
  Qp := pAdicField(p, N);
  Xp := ChangeRing(X, Qp);
  fp := HyperellipticPolynomials(Xp);

  if make_odd_degree then 
    bool, Ep, phi := has_odd_degree_model_at_p(X, p : N:=N);
    assert bool;
    branch_pt := Roots(HyperellipticPolynomials(Xs))[1,1];
    reduced_x_coords := [P1s![branch_pt,1]];
  else 
    Ep := Xp;
    phi := Transformation(Xp, [1,0,0,1]);  
    reduced_x_coords := [];
    reduced_x_coords := [P1s![1,0]];
  end if;
  g := Genus(X);
  splitting_generators := [];
  splitting_indices := [];
  generators_support := [];

  function reduced_x_coord(pt)
    if Valuation(pt[1]) lt 0 then
      return P1s![1,0];
    end if;
    return P1s![(Xs!pt)[1], (Xs!pt)[3]]; 
  end function;

  k := 1;
  done := false;
  repeat
    for i := 0 to k do
      j := k-i;
      P := i*free_gens[1] + j*free_gens[2];
      if -P notin splitting_generators and  (Degree(P[1]) eq 2) then 
        // currently need even degree Mumford polys in the intersection computation. TODO
        b, Pp := is_pointwise_Qp_rational(P, Qp, Xp);
        if b then // don't want Weierstrass disk 
          x_coords := [reduced_x_coord(pt) : pt in Pp]; 
          if &and[x notin reduced_x_coords : x in x_coords] then // Want points to live in distinct residue disks
            Append(~splitting_generators, P);
            Append(~splitting_indices, [i,j]);
            Append(~generators_support, Pp);
            // For the heights computation, we need points in distinct residue disks.
            reduced_x_coords cat:= x_coords; 
            if Regulator(splitting_generators) lt 10^-5 then 
              Prune(~splitting_generators); 
              Prune(~generators_support); 
              Prune(~splitting_indices);
            end if;
          end if;
        end if;
      end if;
      if #splitting_generators eq g then done := true; break; end if;
    end for;
    k +:= 1;
    error if k gt multiple_bound, "No good generators found for this prime";
  until done;

  L := splitting_generators;
  lambda, lambda_support, odd_lambda_support  := get_lambda(splitting_generators, X, phi, 1, 
                                  reduced_x_coords, Qp : odd_degree := make_odd_degree);
  mu, mu_support, odd_mu_support  := get_lambda(splitting_generators, X, phi, lambda + 1,
                        Append(reduced_x_coords, P1s![lambda mod p,1]), Qp : odd_degree := make_odd_degree);
  odd_generators_support := [];
  for pts in generators_support do
    pts_on_odd_model := odd_degree_model_points(pts, phi);
    Append(~odd_generators_support, pts_on_odd_model);
  end for;

  // Compute intersections for local heights away from p.
  P, Q := Explode(splitting_generators);
  intersections := [print_local_int(X, P, -P, lambda, mu),
      [[t[1], -t[2]] :  t in print_local_int(X, P, Q, lambda, mu)], 
      print_local_int(X, -Q, Q, lambda, mu)];
  if g eq 2 then 
    // Check that intersections are correct by comparing two different ways to
    // compute the canonical height pairing
    assert HeightPairing(P,-P:UseArakelov:=true,lambda:=lambda,mu:=mu) - HeightPairing(P,-P) lt 10^-5;
    assert HeightPairing(P,Q:UseArakelov:=true,lambda:=lambda,mu:=mu) - HeightPairing(P,Q) lt 10^-5;
    assert HeightPairing(-Q,Q:UseArakelov:=true,lambda:=lambda,mu:=mu) - HeightPairing(-Q,Q) lt 10^-5;
  end if;

  divisors := [* [* generators_support[1], lambda_support  *], [* generators_support[2] , mu_support *] *];
  odd_divisors := [* [* odd_generators_support[1], odd_lambda_support  *], [* odd_generators_support[2] , odd_mu_support *] *];
  return splitting_generators, divisors, intersections, splitting_indices, odd_divisors, HyperellipticPolynomials(Ep);
end function;


