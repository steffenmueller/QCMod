// Code for the Mordell-Weil sieve
// Mostly copied from an earlier version of magma's Mordell-Weil sieve, due to Michael Stoll.
// Some tweaks added for use with quadratic Chabauty, but not optimised.



function MakeLookup1(G, m)
  return pmap<Codomain(m) -> G| [<m(g), g> : g in G]>;
end function;

function MakeDLp1(G, m, p)
  // G a p-group
  if #G le 25 then
    return MakeLookup1(G, m);
  end if;
  invs := Invariants(G);
  // printf "MakeDLp: Invariants(G) = %o\n", invs;
  pp := ExactQuotient(invs[#invs], p);
  if pp eq 1 then
    return MakeLookup1(G, m);
  end if;
  // printf "MakeDLp: pp = %o\n", pp;
  h := hom<G -> G | [pp*G.i : i in [1..#invs]]>;
  G1 := Image(h);
  // printf "MakeDLp: Invariants(Image(h)) = %o\n", Invariants(G1);
  m1 := map<G1 -> Codomain(m) | x:->m(x)>;
  f1 := MakeLookup1(G1, m1);
  G2 := Kernel(h);
  // printf "MakeDLp: Invariants(Kernel(h)) = %o\n", Invariants(G2);
  m2 := map<G2 -> Codomain(m) | x:->m(x)>;
  f2 := MakeDLp1(G2, m2, p);
  return pmap<Codomain(m) -> G |
               x :-> f2(x - m(a)) + a where a := f1(pp*x) @@ h>;
end function;

function MakeDL(G, m) 
// Given bijection  m : G -> X, where X has group structure, compute the
//  inverse of m. Assumes that #G is smooth.
  n := #Invariants(G);
  f := Factorization(#G);
  cofs := [&*[Integers()|f[i,1]^f[i,2] : i in [1..#f] | i ne j] : j in [1..#f]];
  _, refs := XGCD(cofs);
  assert &+[Integers()|refs[i]*cofs[i] : i in [1..#f]] eq 1;
  DLs := [**];
  for i := 1 to #f do
    p := f[i,1];
    hp := hom<G -> G | [cofs[i]*G.j : j in [1..n]]>;
    Gp := Image(hp);
    mp := map<Gp -> Codomain(m) | x:->m(x)>;
    DLp := MakeDLp1(Gp, mp, p);
    Append(~DLs, DLp);
  end for;
  return pmap<Codomain(m) -> G
               | x :-> &+[G|refs[i]*G!(DLs[i](cofs[i]*x)) : i in [1..#f]]>;
end function;


function prerun_mwsieve_g2r2(J, bas, base_pt, modulus, p, modp_points : printlevel := 0)
// Compute all classes in J(Q)/modulus*J(Q) whose image mod p
// contains the image of an Fp-point on the curve
// J is assumed to have rank=genus=2
// TODO: generalize to several primes and higher genus
  
  C := Curve(J);
  Cp := BaseChange(C, Bang(Rationals(), GF(p)));
  Jp := BaseChange(J, GF(p));
  G, m := AbelianGroup(Jp);
  if printlevel gt 0 then        printf " GroupInfo: p = %o...\n", p; end if;
  I := Invariants(G);
  //if printlevel gt 0 then        printf "   #C(F_p) = %o, Invariants(G) = %o\n", #pts, I; end if;
  fI := Factorization(I[#I]);
  if printlevel gt 0 then        printf  "   Exponent = %o\n", fI; end if;
  if printlevel gt 0 then        printf  "   Group Structure = %o\n", G; end if;

  inj := func<pt | Cp!pt - Cp!base_pt>;
  if printlevel gt 1 then        "make DL"; end if;
  DL := MakeDL(G, m); 
  
  if printlevel gt 1 then        "starting DL of generators"; end if;
  imbas := [DL(Jp!b) : b in bas]; // ... @@ m
  if printlevel gt 1 then        "finished DL of generators"; end if;
  orders := [Order(g) : g in imbas];
  lcm_orders := LCM(orders);

  if printlevel gt 0 then        "starting DL of points on curve over F_p"; end if;
  imC := {DL(inj(Cp!Eltseq(pt_seq))) : pt_seq in modp_points};
  if printlevel gt 0 then        "finished DL"; end if;

  Gsub := sub<G | imbas>;
  imbas := ChangeUniverse(imbas, Gsub);
  e1 := GCD(modulus, lcm_orders);
  if e1 lt lcm_orders then
    // throw away the part that we don't need
    Gq, qmap := quo<Gsub | [e1*g : g in Generators(Gsub)]>;
    imbas := [qmap(b) : b in imbas];
    imC := {qmap(c) : c in imC};
  end if; // e1 lt LCM(orders)
  G := Parent(imbas[1]);
  Cv_p := [P : P in SetToSequence(imC)];
  coeffs := [];
  for i,j in [1..modulus] do 
    if i*imbas[1]+j*imbas[2] in Cv_p then
      Append(~coeffs, [i,j]);
    end if;
  end for;
  printf "  %o cosets eliminated at v = %o\n", modulus^2 - #coeffs, p;
  return coeffs;

end function;


function MWSieve(J, sieving_primes, modulus, bas, base_pt, fake_coeffs : GIlb := 2, SmoothBound := 10000, satknown := {Integers()|}, excluded := {Integers()|}, satunknown := {Integers() | }, known_rat_coeffs := {}, bool_list := [true : i in [1..#fake_coeffs]], unsat := {Integers()|}, special_p_points := [], printlevel := 0) 

  bp := Seqset(BadPrimes(J)) join {p : p in excluded};
  lb := Max(3, IsEven(GIlb) select GIlb+1 else GIlb);
  C := Curve(J);
  assert #unsat lt 2;
  for p in sieving_primes do
    if IsPrime(p) and p notin bp then
      Jp := BaseChange(J, GF(p));
      oG := #Jp;
      if Max(PrimeDivisors(oG)) lt SmoothBound then
        Cp := BaseChange(C, Bang(Rationals(), GF(p)));
        pts := Points(Cp);
        G, m := AbelianGroup(Jp);
        if printlevel gt 0 then        printf " GroupInfo: p = %o...\n", p; end if;
        I := Invariants(G);
        if printlevel gt 0 then        printf "   #C(F_p) = %o, Invariants(G) = %o\n", #pts, I; end if;
        fI := Factorization(I[#I]);
        if printlevel gt 0 then        printf  "   Exponent = %o\n", fI; end if;
        if printlevel gt 0 then        printf  "   Group Structure = %o\n", G; end if;

        scalar := #unsat eq 0 select 1 else unsat[1]^Valuation(I[#I], unsat[1]);
        if printlevel gt 1 then        printf  "   Look at %o-multiples \n", scalar; end if;

        inj := func<pt | Cp!pt - Cp!base_pt>;
        if printlevel gt 1 then        "make DL"; end if;
        DL := MakeDL(G, m); 
        
        if printlevel gt 1 then        "starting DL of generators"; end if;
        imbas := [DL(Jp!b) : b in bas]; // ... @@ m
        if printlevel gt 1 then        "finished DL of generators"; end if;
        orders := [Order(g) : g in imbas];
        lcm_orders := LCM(orders);

        // We assume saturation has been checked at primes dividing the torsion order.
        // Find new primes at which saturation is known
        // (all primes q such that image of ptJ (= bas[1]) is not in q*J(F_p)).
        satknown join:= {a[1] : a in fI | imbas[1] notin a[1]*G};
        // Find primes where saturation needs to be checked
        // (all prime divisors of #J(F_p) for which saturation is not yet known).
        satunknown join:= {a[1] : a in fI};
        satunknown diff:= satknown;

        if printlevel gt 0 then        "starting DL of points on curve over F_p"; end if;
        if p notin [t[1] : t in special_p_points] then
          imC := {DL(inj(pt)) : pt in pts};
        else 
          indp := Index([t[1] : t in special_p_points], p);
          imC := {DL(inj(Cp!Eltseq(pt_seq))) : pt_seq in special_p_points[indp,2]};
        end if;
        if printlevel gt 0 then        "finished DL"; end if;
        imC := {scalar*pt : pt in imC};
        Gsub := sub<G | imbas>;
        imC := {Gsub | pt : pt in imC | pt in Gsub};

        imbas := ChangeUniverse(imbas, Gsub);
        e1 := GCD(modulus, lcm_orders);
        if e1 lt lcm_orders then
          // throw away the part that we don't need
          Gq, qmap := quo<Gsub | [e1*g : g in Generators(Gsub)]>;
          imbas := [qmap(b) : b in imbas];
          imC := {qmap(c) : c in imC};
        end if; // e1 lt LCM(orders)
        G := Parent(imbas[1]);
        M := GCD(modulus, Exponent(G));
        assert IsOne(Exponent(G) div M);
        Cv_p := [P : P in SetToSequence(imC)];
        assert &and[ &+[imbas[i]*t[i] : i in [1..#imbas]]  in Cv_p : t in known_rat_coeffs];
        old_left := #[b : b in bool_list | b];
        for i in [1..#bool_list] do
          if bool_list[i] then
            bool_list[i] := &+[imbas[j]*(fake_coeffs[i][j] mod M) : j in [1..#imbas]] in Cv_p;
          end if;
        end for;
        left := #[b : b in bool_list | b];
        if left lt old_left then printf "  %o cosets eliminated at v = %o\n", old_left - left, p; end if;;
        printf "        %o cosets remaining after v=%o\n", left, p;
        if not &or bool_list then
           return true, bool_list, satknown, satunknown, _;
        end if; 
 
      end if; // Max(PrimeDivisors(oG)) lt SmoothBound
    end if; // IsPrime(p) and p notin bp
  end for; // p
  return false, bool_list, satknown, satunknown, 
    [fake_coeffs[i] : i in [1..    #fake_coeffs] | bool_list[i]];
end function;


function coeffs_CRT(coeffs, primes, exponents)
  // TODO: Rewrite this and make it work in general. 
    assert #primes eq #exponents;
    assert #coeffs eq #primes;
    order_of_T := #coeffs[1];
    assert &and [#a eq order_of_T : a in coeffs];
    coeffs_mod_M := [];
    moduli := [primes[i]^exponents[i] : i in [1..#primes]];

    error if #primes gt 5, 
        "The case of %n primes is not implemented yet!", #primes;
    if #primes eq 1 then
        coeffs_mod_M := &cat coeffs[1]; 
    elif #primes eq 2 then 
        rank := #coeffs[1, 1, 1]; 
        for j := 1 to order_of_T do
            for i := 1 to #coeffs[1, j] do
                for k := 1 to #coeffs[2, j] do
                    Append(~coeffs_mod_M, [CRT([coeffs[1, j, i, l], coeffs[2, j, k, l]], 
                                moduli) : l in [1..rank]]);
                end for;
            end for;
        end for;
    elif #primes eq 3 then 
        rank := #coeffs[1, 1, 1]; 
        for j := 1 to order_of_T do
            for i := 1 to #coeffs[1, j] do
                for k := 1 to #coeffs[2, j] do
                    for m := 1 to #coeffs[3, j] do
                        Append(~coeffs_mod_M, [CRT([coeffs[1, j, i, l], coeffs[2, j, k, l], 
                                    coeffs[3, j, m, l]], moduli) : l in [1..rank]]);
                    end for;
                end for;
            end for;
        end for;
    elif #primes eq 4 then 
        rank := #coeffs[1, 1, 1]; 
        for j := 1 to order_of_T do
            for i := 1 to #coeffs[1, j] do
                for k := 1 to #coeffs[2, j] do
                    for m := 1 to #coeffs[3, j] do
                      for n := 1 to #coeffs[4, j] do
                          Append(~coeffs_mod_M, [CRT([coeffs[1, j, i, l], coeffs[2, j, k, l], 
                                      coeffs[3, j, m, l], coeffs[4, j, n, l]], moduli) : l in [1..rank]]);
                      end for;
                    end for;
                end for;
            end for;
        end for;
    elif #primes eq 5 then 
        rank := #coeffs[1, 1, 1]; 
        for j := 1 to order_of_T do
            for i := 1 to #coeffs[1, j] do
                for k := 1 to #coeffs[2, j] do
                    for m := 1 to #coeffs[3, j] do
                      for n := 1 to #coeffs[4, j] do
                        for o := 1 to #coeffs[4, j] do
                          Append(~coeffs_mod_M, [CRT([coeffs[1, j, i, l], coeffs[2, j, k, l], 
                                      coeffs[3, j, m, l], coeffs[4, j, n, l], coeffs[5, j, o, l]], moduli) : l in [1..rank]]);
                        end for;
                      end for;
                    end for;
                end for;
            end for;
        end for;
    end if;
    return coeffs_mod_M;
end function;

function all_coeffs(N, g)
    // return all lists a = [a_1,...,a_g], where a_i = 0,...,N-1
    coeffs := [[j] : j in [0..N-1]];
    for i := 1 to g-1 do
        old_coeffs := coeffs;
        coeffs := [];
        for a in old_coeffs do
            for j := 0 to N-1 do
                Append(~coeffs, a cat [j]);
            end for;
        end for;
    end for;
    return coeffs;
end function;



function combine_fake_good(fake_coeffs_mod_M, M, N)
    // fake_as_mod_M contains all solutions mod M.
    // N is a prime power for which we have no information where 
    // the rational points could lie.
    as := [];
    rank := #fake_coeffs_mod_M[1];
    as_mod_N := all_coeffs(N, rank);
    for i in [1..#fake_coeffs_mod_M] do
        for j in [1..#as_mod_N] do
            Append(~as, [CRT([fake_coeffs_mod_M[i,l], as_mod_N[j,l]], 
                        [M, N]) : l in [1..rank]]);
        end for;
    end for;
    return as;
end function;



function sieving_primes(M, primes, groups, bound : printlevel := 0)
    // Given a modulus M, a list of primes, a list of abelian groups, one for each
    // prime in primes, and a bound on the quality of the expected information per prime,
    // compute a list of promising primes for the  Mordell-Weil sieve.
    s_primes := [];
    quots := [];
    for i := 1 to #primes do
        v := primes[i];
        A := groups[i];
        if GCD(M, #A) ne 1 then
          MA := sub<A | [M*g : g in Generators(A)]>;
          QA := A/MA;
          if v+1 lt #QA*bound then
             if printlevel gt 0 then <v, FactoredOrder(A), (v+1.)/#QA>; end if;
            Append(~s_primes, v);
            Append(~quots, (v+1.)/#QA);
          end if;
        end if;
    end for;
    // now sort according to quotient
    //ParallelSort(~quotients, ~s_primes);
    return s_primes, quots;
end function;


function is_saturated_at_p(bas, torsion_bas, p, AuxPrimes)
    // Check whether the subgroup of the MW group generated by bas and torsion_bas is saturated at p
    assert IsPrime(p);
    J := Universe(bas);
    assert BaseField(J) cmpeq Rationals();
    // find a number (rank + AuxPrimes) of good primes q s.t. p|#J(F_q)
    C := Curve(J);
    assert IsHyperelliptic(C);
    f, h := HyperellipticPolynomials(C);
    assert h eq 0;
    assert IsIntegral(C);

    torsion_orders := [Order(P) : P in torsion_bas]; 
    rank := #bas + #[i : i in torsion_orders | IsDivisibleBy(i, p)];
    num := rank + AuxPrimes;
    disc := Integers()!Discriminant(Curve(J));
    q := 2;
    MW := AbelianGroup(torsion_orders cat [0 : b in bas]);
    genMW := torsion_bas cat bas;
    printf "Generators of known subgroup (torsion first):\n%o\n", genMW;
    mMW := map<MW -> J | x :-> &+[J | s[i]*genMW[i] : i in [1..#genMW]]
                        where s := Eltseq(x)>;
    MWp, qmap := quo<MW | [p*g : g in Generators(MW)]>;
    curr := MWp;
    // curr is the subgroup of MW/p*MW of potentially p-divisible elements
    count := 0;
    while count lt num do
    repeat
        q := NextPrime(q);
        while IsDivisibleBy(disc, q) do q := NextPrime(q); end while;
        Jq := BaseChange(J, Bang(Rationals(), GF(q)));
        h := #Jq;
    //    "q=",q;
    until IsDivisibleBy(h, p);
    printf "Found relevant prime q = %o\n", q;
    Gq, mGq := AbelianGroup(Jq);
    Gqp, Gqmap := quo<Gq | [p*g : g in Generators(Gq)]>;
    m := hom<curr -> Gqp
             | [Gqmap((Jq!mMW((MWp!g) @@ qmap)) @@ mGq)
                 : g in OrderedGenerators(curr)]>;
    curr := Kernel(m);
    printf "Dimension of remaining space is %o\n", Valuation(#curr, p);
    if #curr eq 1 then
        // no potential p-divisible elements left
        return true;
    end if;
    count +:= 1;
    end while;
    "increase AuxPrimes!";
    return false;
end function;


