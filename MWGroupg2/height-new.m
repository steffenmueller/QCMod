// Implement the factorization-free canonical height algorithm
// for genus 2 Jacobians from
// J.S. Müller and M. Stoll: Canonical heights on genus two Jacobians
//
// Michael Stoll, started 2014-11-29

declare verbose ReducedBasis, 3;
declare verbose JacHypSaturation, 3;

declare attributes CrvHyp:
  DiscriminantPartialFactorization,
// C`DiscriminantPartialFactorization = [<q_1, e_1, flag_1>, ...] such that
// * |disc(C)| = prod_i q_i^{e_i}
// * the q_i are coprime in pairs and are integers > 1
// * flag_i is true if it is known that q_i is prime, false otherwise
  HCinf,
// C`HCinf = <eta, dprec>
// where eta is a bound on |eps| and dprec is the additional number of decimal
// digits of precision that was sufficient so far
  TrialDivisionBound,
// C`TrialDivisionBound = B
// where B is the largest bound used so far for trial division in the code below
  Dseq;
// C`Dseq = [d1, d2, d3, d4]
// where dj is the vector of coefficients (in Z) of the jth duplication polynomial
// (with respect to the ordering given by MonomialsOfDegree(_, 4))

function split(a, b)
  // a and b are positive integers
  // returns
  // * a sequence [c_1, c_2, ..., c_k]
  // * a sequence [e_1, e_2, ..., e_k]
  // * a sequence [f_1, f_2, ..., f_k]
  // such that
  // * the c_i are integers > 1, coprime in pairs
  // * a = c_1^{e_1}*...*c_k^{e_k}
  // * b = c_1^{f_1}*...*c_k^{f_k}
  // compare Buchmann and Lenstra: Approximating rings of integers in number fields,
  // J. Th'eor. Nombers Bordeaux 6 (1994), no. 2, 221-260; Proposition 6.5
  if a eq 1 then
    if b eq 1 then
      return [Integers()|], [Integers()|], [Integers()|];
    else
      return [b], [0], [1];
    end if;
  elif b eq 1 then
    return [a], [1], [0];
  end if;
  seq := [a, b];
  as := [1, 0];
  bs := [0, 1];
  repeat
    flag := true;
    i := 1;
    while i lt #seq do
      g := GCD(seq[i], seq[i+1]);
      if g gt 1 then
        seq[i] := ExactQuotient(seq[i], g);
        seq[i+1] := ExactQuotient(seq[i+1], g);
        Insert(~seq, i+1, g);
        Insert(~as, i+1, as[i] + as[i+1]);
        Insert(~bs, i+1, bs[i] + bs[i+1]);
        if seq[i+2] eq 1 then
          Remove(~seq, i+2);
          Remove(~as, i+2);
          Remove(~bs, i+2);
        end if;
        if seq[i] eq 1 then
          Remove(~seq, i);
          Remove(~as, i);
          Remove(~bs, i);
        end if;
        flag := false;
      else
        i +:= 1;
      end if;
    end while;
  until flag;
  return seq, as, bs;
end function;

function SimplestFraction(a, b)
  // returns the simplest fraction between a and b (which are positive rational numbers)
  if Ceiling(a) le b then
    return Ceiling(a);
  else
    s := Floor(a);
    return s + 1/SimplestFraction(1/(b-s), 1/(a-s));
  end if;
end function;

// Use dot product of coefficient vector with vector of monomials,
// with the latter computed efficiently, to speed up evaluation of the duplication map.

// [x1^2, x1*x2, x1*x3, x1*x4, x2^2, x2*x3, x2*x4, x3^2, x3*x4, x4^2]
//    1     2      3      4      5     6      7      8     9      10
combi := [<1,1>, <1,2>,   <1,3>,   <1,4>,   <2,2>,     <2,3>,     <2,4>,      <3,3>,
       // x1^4,  x1^3*x2, x1^3*x3, x1^3*x4, x1^2*x2^2, x1^2*x2*x3, x1^2*x2*x4, x1^2*x3^2
          <3,4>,      <4,4>,     <2,5>,   <3,5>,      <4,5>,      <2,8>,      <2,9>,       <2,10>,
       // x1^2*x3*x4, x1^2*x4^2, x1*x2^3, x1*x2^2*x3, x1*x2^2*x4, x1*x2*x3^2, x1*x2*x3*x4, x1*x2*x4^2
          <3,8>,   <3,9>,      <3,10>,     <4,10>,  <5,5>, <5,6>,   <5,7>,   <5,8>,     <5,9>,
       // x1*x3^3, x1*x3^2*x4, x1*x3*x4^2, x1*x4^3, x2^4,  x2^3*x3, x2^3*x4, x2^2*x3^2,  x2^2*x3*x4
          <5,10>,    <6,8>,   <6,9>,      <6,10>,     <7,10>,  <8,8>, <8,9>,   <8,10>,    <9,10>,  <10,10>];
       // x2^2*x4^2, x2*x3^3, x2*x3^2*x4, x2*x3*x4^2, x2*x4^3, x3^4,  x3^3*x4, x3^2*x4^2, x3*x4^3, x4^4

function evdelta(dseq, seq)
  // dseq = [v1, v2, v3, v4], coefficient vectors of duplication polynomials
  // seq = [a1, a2, a3, a4]
  // returns the sequence of division polynomials evaluated at (a1,a2,a3,a4)
  a1, a2, a3, a4 := Explode(seq);
  // first the quadratic ones
  mons2 := [a1^2, a1*a2, a1*a3, a1*a4, a2^2, a2*a3, a2*a4, a3^2, a3*a4, a4^2];
  // now combine to get the monomials of degree 4
  mons4 := Vector([mons2[c[1]]*mons2[c[2]] : c in combi]);
  return [(ChangeRing(d, Universe(seq)), mons4) : d in dseq];
end function;

function HCinfinity(f, deltas)
  partitions := [ <[6,5,4],[3,2,1]>, <[6,5,3],[4,2,1]>, <[6,4,3],[5,2,1]>,
                  <[6,2,1],[5,4,3]>, <[6,5,2],[4,3,1]>, <[6,4,2],[5,3,1]>,
                  <[6,3,1],[5,4,2]>, <[6,3,2],[5,4,1]>, <[6,4,1],[5,3,2]>,
                  <[6,5,1],[4,3,2]> ];
  roots := [ r[1] : r in Roots(f, ComplexField()) ];
  lcf := Abs(LeadingCoefficient(f));
  // Find a bound for the local height constant at infinity using the approach in
  // M. Stoll: On the height constant for curves of genus two, Acta Arith. 90, 183-201 (1999).
  a1 := 0; a2 := 0; a3 := 0; a4 := 0;
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
    b := Sqrt(lcf*(Modulus(s[3]*t[1] + s[1]*t[3])
                    + Modulus(s[3] + s0*t[3])
                    + Modulus(s[2] + s0*t[2]))
                + 1);
    rr := Modulus(b/(4*res));
    a1 +:= rr*Modulus(s[1]-s0*t[1]);
    a2 +:= rr*Modulus(s[3]-s0*t[3] + s[2]*t[1]-s[1]*t[2]);
    a3 +:= rr*Modulus(s[3]*t[2]-s[2]*t[3]);
    a4 +:= rr*Modulus(s[1]*s[3]^2*t[2] - s0^2*s[2]*t[1]*t[3]^2
                        + s[1]*s[2]*t[1]*t[2]*(s[3] - s0*t[3])
                        - s[3]*t[3]*(s[1]*s[2] - s0^2*t[1]*t[2])
                        - s[1]*t[1]*(s[2]^2*t[3] - s0*s[3]*t[2]^2)
                        - s[1]^2*s[3]*t[2]^2 + s0*s[2]^2*t[1]^2*t[3]
                        + 4*s[1]*s[3]*t[1]*t[3]*(s[1] - s0*t[1])
                        + s[2]*t[2]*(s[1]^2*t[3] - s0*s[3]*t[1]^2)
                        - s0*(s[3]^2*t[1]*t[2] - t[3]^2*s[1]*s[2])
                        + s0*(4*s[3]*t[3]*(s[3] - s0*t[3])
                              + 4*s[2]*t[2]*(s[3]*t[2] - s[2]*t[3])
                              - 3*s[3]*t[3]*(s[2]*t[1] - s[1]*t[2])));
  end for;
  a1 *:= lcf; a2 *:= lcf; a3 *:= lcf; a4 *:= lcf^3;
  upper := 2*Log(Max([a1,a2,a3,a4]));
  // bound for -eps
  lower := Log(Max([&+[Abs(c) : c in Eltseq(d)] : d in deltas]));
  // eta is a bound on |eps|
  eta := Max(upper, lower);
  return eta;
end function;

// save intrinsic Precision so that we can refer to it in a context
// where Precision is a local variable
MyPrec := Precision;

intrinsic HeightNew(pt::SrfKumPt : Precision := MyPrec(RealField()), TrialDivisionBound := 1000, PrimePowerCheckBound := 10^200) -> FldReElt
{ Compute the canonical height of the rational point pt on the Kummer surface
  of a curve of genus 2 over the rationals. The curve must be given by an integral model
  of the form y^2 = f(x).
  The result is computed to Precision decimal digits after the point. Precision defaults
  to the precision of the default real field.
  TrialDivisionBound (default 1000) is used as a bound for a partial factorization of the
  discriminant of the curve. }
  // some verbose printing
  vprintf JacHypHeight, 1: "HeightNew of pt = %o\n", pt;
  vprintf JacHypHeight, 2: "  Precision = %o, TrialDivisionBound = %o\n", Precision, TrialDivisionBound;
  // check input
  TrialDivisionBound := Max(1, TrialDivisionBound);
  C := Curve(Jacobian(Parent(pt)));
  require BaseField(C) cmpeq Rationals():
          "HeightNew is only implemented for points over the rationals";
  require IsIntegral(C): "The curve must be given by an integral model";
  disc := Integers()!Discriminant(C);
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve must have an equation of the form y^2 = f(x)";
  if h eq 0 then // not really necessary now, but left here for future extensions
    disc := ExactQuotient(disc, 2^4);
  end if;
  vprintf JacHypHeight, 2: "disc = %o\n", disc;
  // check/initialize partial factorization of disc
  if not assigned C`DiscriminantPartialFactorization then
    // initialize the attributes
    C`DiscriminantPartialFactorization := [<Abs(disc), 1, false>];
    C`TrialDivisionBound := 1;
  end if;
  // do trial division
  DPF := C`DiscriminantPartialFactorization;
  if C`TrialDivisionBound lt TrialDivisionBound then
    newDPF := [Universe(DPF)| ];
    for entry in DPF do
      if entry[3] then
        Append(~newDPF, entry); // q_i already known to be prime
      else
        fact, rem := TrialDivision(entry[1], TrialDivisionBound);
        for pair in fact do
          Append(~newDPF, <pair[1], entry[2]*pair[2], true>);
        end for;
        for r in rem do
          Append(~newDPF, <rem, entry[2], false>);
        end for;
      end if;
    end for;
    C`DiscriminantPartialFactorization := newDPF;
    C`TrialDivisionBound := TrialDivisionBound;
    DPF := newDPF;
  end if;
  vprintf JacHypHeight, 2: "DPF = %o\n", DPF;
  // retrieve/initialize duplication polynomials as a sequence of coefficient vectors
  // (for better speed when evaluating, see function evdelta above)
  if not assigned C`Dseq then
    PZ4 := PolynomialRing(Integers(), 4);
    deltas := ChangeUniverse(Parent(pt)`Delta, PZ4);
    mons4 := MonomialsOfDegree(PZ4, 4);
    deltas := [Vector([MonomialCoefficient(d, m) : m in mons4]) : d in deltas];
    C`Dseq := deltas;
  else
    deltas := C`Dseq;
  end if;
  // naive height
  maxabs := Max([Abs(c) : c in Eltseq(pt)]);
  // number of digits for integral part of the height
  roughht10 := Ceiling(Log(10, Ceiling(Log(10, maxabs) + 1))) + 1;
  // naive height is computed together with height correction at infinity
//   htnaive := Log(RealField(Precision + 1 + roughht10)!maxabs);
//   vprintf JacHypHeight, 1: "\nnaive height = %o\n\n", ChangePrecision(htnaive, Precision);
  // compute first gcd = gcd(delta(x)) where x are the normalized coordinates
  ptR := ChangeUniverse(Eltseq(pt), Integers());
  ptR2 := evdelta(deltas, ptR);
  g0 := GCD([disc] cat ptR2); // note that gcd(delta(x)) always divides disc
  vprintf JacHypHeight, 2: "g0 = %o\n", g0;
  // normalize delta(x)
  x := [ExactQuotient(c, g0) : c in ptR2];
  // set up hashtable; it will map  q --> <B, M, m, x, [e_0, e_1, ..., e_m]>
  // where  q^{e_n}  is the q-part of the nth gcd.
  HT := AssociativeArray(Integers());
  // knowing g0 can lead to further splitting of disc
  newDPF := [Universe(DPF)| ];
  for entry in DPF do
    if entry[3] then
      // q = entry[1] is known to be prime
      vq := Valuation(g0, entry[1]);
      if vq gt 0 then
        // q is a bad prime for our point. Compute the relevant data and store in HT
        B := entry[2];
        B1 := entry[1] eq 2 and h eq 0 select B + 4 else B;
        M := Max(2, Floor(B1^2/3));
        m := Ilog2((B^3*M^2) div 3) div 2; // = floor(log_4 (...))
        HT[entry[1]] := <B, M, m, x, [vq]>;
      end if;
      Append(~newDPF, entry); // old entry is copied into new DPF
    else
      // try to split g0 with q = entry[1]
      seq, qs, gs := split(entry[1], g0);
      for i := 1 to #seq do
        if qs[i] gt 0 then
            if seq[i] lt PrimePowerCheckBound then
              // check if qs[i] is a prime power; if so, replace by q^e
              flag, q, e := IsPrimePower(seq[i]);
            else
              // for larger seq[i], IsPrimePower can be slow
              flag := false;
            end if;
          if not flag then
            q := seq[i];
            e := 1;
          end if;
          // update splitting of disc
          Append(~newDPF, <q, entry[2]*qs[i]*e, flag>);
          if gs[i] gt 0 then
            // q contains bad primes for our point
            B := entry[2]*qs[i]*e;
            B1 := flag select B else Floor(entry[2]*Log(TrialDivisionBound+1, q));
            M := Max(2, Floor(B1^2/3));
            m := Ilog2((B^3*M^2) div 3) div 2; // = floor(log_4 (...))
            HT[q] := <B, M, m, x, [gs[i]*e]>;
          end if;
        else
          // this will happen at most once; can replace g0 by this factor
          // (this will be the part of g0 coprime to entry[1])
          assert gs[i] eq 1;
          g0 := seq[i];
        end if;
      end for;
    end if;
  end for;
  // update stored DPF
  C`DiscriminantPartialFactorization := newDPF;
  DPF := newDPF;
  vprintf JacHypHeight, 3: "DPF = %o\n", DPF;
  if IsVerbose("JacHypHeight", 2) then
    printf "HT:\n";
    for q in Keys(HT) do
      printf "  %o --> <%o, %o, %o, _, %o>\n", q, HT[q,1], HT[q,2], HT[q,3], HT[q,5];
    end for;
  end if;
  // sequence of q's, for lookup purposes
  qseq := [e[1] : e in DPF];
  // now iterate
  m := 1;
  repeat
    vprintf JacHypHeight, 2: "iteration step %o\n", m;
    finished := true; // if not set to false in the loop body, leave
    for q in Keys(HT) do
      // do the stepping for each q
      HTentry := HT[q];
      if m le HTentry[3] then
        finished := false; // number of iterations not yet reached
        vprintf JacHypHeight, 3: "  computation at q = %o\n", q;
        n := HTentry[3] - m + 1; // precision needed for remaining steps
        // compute delta(x) modulo q^(B*n+1)
        R := Integers(q^(HTentry[1]*n + 1));
        // apply duplication over R and convert coordinates back to integers
        xR := ChangeUniverse(HTentry[4], R);
        dx := ChangeUniverse(evdelta(deltas, xR), Integers());
        // compute the new gcd (which is the q-part of the full gcd)
        g := GCD([q^HTentry[1]] cat dx);
        // normalize coordinates for the  next step
        xn := [ExactQuotient(c, g) : c in dx];
        // see if further splitting is possible
        seq, qs, gs := split(q, g);
        if qs ne [1] then // yes
          if IsVerbose("JacHypHeight", 3) and &+qs gt 1 then
            printf "    further splitting:\n    %o =", q;
            for i := 1 to #seq do
              if qs[i] gt 0 then
                printf " %o^%o", seq[i], qs[i];
              end if;
            end for;
            printf "\n";
          end if;
          // update DPF and qseq
          j := Position(qseq, q);
          entry := DPF[j];
          // remove current entries for q in DPF, qseq and HT
          Remove(~DPF, j);
          Remove(~qseq, j);
          Remove(~HT, q);
          for i := 1 to #seq do
            if qs[i] gt 0 then
              flag, p, e := IsPrimePower(seq[i]);
              if not flag then
                p := seq[i];
                e := 1;
              end if;
              // insert new data into DPF and qseq
              Insert(~DPF, j, <p, qs[i]*entry[2]*e, flag>);
              Insert(~qseq, j, p);
              // update HT
              B := entry[2]*qs[i]*e;
              B1 := flag select B else Floor(entry[2]*Log(TrialDivisionBound+1, p));
              M := Max(2, Floor(B1^2/3));
              m1 := gs[i] eq 0 select m else Ilog2((B^3*M^2) div 3) div 2; // if eps = 0, can stop
              HT[p] := <B, M, m1, xn, Append([qs[i]*e*a : a in HTentry[5]], gs[i]*e)>;
              vprintf JacHypHeight, 3: "    HT[%o] = <%o, %o, %o, _, %o>\n",
                                        p, B, M, m1, HT[seq[i],5];
            end if;
          end for;
          // update stored DPF
          C`DiscriminantPartialFactorization := DPF;
          vprintf JacHypHeight, 3: "DPF = %o\n", DPF;
        else
          m1 := gs[1] eq 0 select m else HTentry[3]; // stop iteration when eps = 0
          // extend list of gcd valuations
          HT[q] := <HTentry[1], HTentry[2], m1, xn, Append(HTentry[5], gs[1])>;
          vprintf JacHypHeight, 3: "    HT[%o] = <%o, %o, %o, _, %o>\n",
                                   q, HT[q,1], HT[q,2], HT[q,3], HT[q,5];
        end if; // qs ne [1]
      end if; // m le HTentry[3]
    end for;
    m +:= 1;
  until finished;
  // now sum up corrections at finite places
  htfin := 0;
  vprintf JacHypHeight, 2: "corrections at the finite places are\n";
  // muqseq will be a sequence of pairs <mu_q, q> such that
  // the correction term at finite places is  -sum_q mu_q*log(q)
  muqseq := [Parent(<1/2, 1>)|];
  for q in Keys(HT) do
    HTentry := HT[q];
    // compute lower and upper ends of interval containing mu_q
    mu0 := &+[Rationals()| 4^(-n)*HTentry[5][n] : n in [1..#HTentry[5]]];
    mu1 := mu0 + 1/HTentry[2]^2;
    // find simplest fraction between mu0 and mu1
    mu := SimplestFraction(mu0, mu1);
    assert Denominator(mu) le HTentry[2]; // safety check
    Append(~muqseq, <mu, q>);
    vprintf JacHypHeight, 2: "  %o --> %o log(%o)\n", q, mu, q;
  end for;
  if not IsEmpty(muqseq) then
    // the (relative) precision necessary for the log computation
    // to get absolute precision Precision
    precfin := Precision + 1 + Ceiling(Max([e[1]*Log(10, e[2]) : e in muqseq])) + roughht10;
    Rfin := RealField(precfin);
    for muq in muqseq do
      htfin +:= muq[1]*Log(Rfin!muq[2]);
    end for;
  end if;
  vprintf JacHypHeight, 1: "\ncorrection at finite places is %o\n\n", -htfin;
  // finally compute the correction at infinity
  // first determine the number of iteration steps and the initial precision
  vprintf JacHypHeight, 2: "computing correction at infinity\n";
  // retrieve/initialize eta (bound on |eps_infty|) and dprec
  log10 := Log(4, 10);
  if not assigned C`HCinf then
    eta := HCinfinity(f, deltas);
    dprec := 1.0/log10;
    C`HCinf := <eta, dprec>;
  else
    eta, dprec := Explode(C`HCinf);
  end if;
  vprintf JacHypHeight, 2: "  eta = %o\n", ChangePrecision(eta, 6);
  // bound for the number of steps necessary to get desired precision
  steps := Ceiling(Precision*log10 + Log(4, eta/3) + 1);
  vprintf JacHypHeight, 2: "  need %o iteration steps\n", steps;
  // we do the computation with two different precisions
  // if the result is the same, we keep it;
  // otherwise we repeat with increased precisions
  function infheight(prec)
    vprintf JacHypHeight, 2: "  using precision %o\n", prec;
    Rinf := RealField(prec);
    // now do the computation:
    // we avoid computing logarithms.
    // Instead we rescale by powers of 2, collect the shifts, and use the corresponding
    // multiple of log(2) in the end.
    // We start with the normalized integral coordinates; in this way, we include the naive height.
    x := ChangeUniverse(Eltseq(pt), Rinf);
    meseq := [<m, e> where m, e := MantissaExponent(c) : c in x];
    // find power 2^sh such that multiplication by 2^(-sh) brings max between 1 and 2
    shift := Max([Ilog2(Abs(me[1])) + me[2] : me in meseq | me[1] ne 0]);
    vprintf JacHypHeight, 3: "    shift = %o\n", shift;
    // normalize to get max(abs(x)) between 1 and 2
    x := [elt<Rinf | me[1], me[2]-shift> : me in meseq];
    for n := 0 to steps do
      dx := evdelta(deltas, x);
//       vprintf JacHypHeight, 3: "  dx = (%o, %o, %o, %o)\n",
//                                ChangePrecision(dx[1],5), ChangePrecision(dx[2],5),
//                                ChangePrecision(dx[3],5), ChangePrecision(dx[4],5);
      // extract mantissa and exponent of the coordinates
      meseq := [<m, e> where m, e := MantissaExponent(c) : c in dx];
      // find power 2^sh such that multiplication by 2^(-sh) brings max between 1 and 2
      sh := Max([Ilog2(Abs(me[1])) + me[2] : me in meseq | me[1] ne 0]);
      vprintf JacHypHeight, 3: "    shift = %o\n", sh;
      // update total shift
      shift := 4*shift + sh;
      if n lt steps then
        // renormalize coordinates
        x := [elt<Rinf | me[1], me[2]-sh> : me in meseq];
      end if;
    end for;
    // naive height + correction at infinity is (up to small error) shift/4^(steps+1)*Log(2)
    return shift;
  end function;
  // initial value with precision dprec*steps
  shift2 := infheight(Ceiling(steps*dprec));
  repeat
    dprec *:= 1.1;
    shift1 := shift2;
    shift2 := infheight(Ceiling(steps*dprec));
  until shift1 eq shift2;
  C`HCinf[2] := dprec / 1.1;
  R := RealField(Precision + roughht10);
  htinf := elt<R | shift1, -2*(steps+1)>*Log(elt<R | 1, 1>);
  vprintf JacHypHeight, 1: "\nnaive height with correction at infinity is %o\n", htinf;
  ht := ChangePrecision(htinf - htfin, Precision + roughht10);
  vprintf JacHypHeight, 1: "\nresult = %o\n", ht;
  return ht;
end intrinsic;

intrinsic HeightNew(pt::JacHypPt : Precision := MyPrec(RealField()), TrialDivisionBound := 1000) -> FldReElt
{ Compute the canonical height of the rational point pt on the Jacobian
  of a curve of genus 2 over the rationals. }
  return HeightNew(KummerSurface(Parent(pt))!pt
                    : Precision := Precision, TrialDivisionBound := TrialDivisionBound);
end intrinsic;

intrinsic HeightPairingNew(pt1::JacHypPt, pt2::JacHypPt : Precision  := MyPrec(RealField())) -> FldReElt
{ Compute the value of the Neron-Tate height pairing for two points on the Jacobian
  of a curve of genus 2. }
  return (HeightNew(pt1+pt2 : Precision := Precision) - HeightNew(pt1-pt2 : Precision := Precision))/4;
end intrinsic;

intrinsic HeightPairingMatrixNew(pts::[JacHypPt] : Precision := MyPrec(RealField())) -> AlgMatElt
{ Compute the height pairing matrix of the given sequence of points on the Jacobian
  of a curve of genus 2. }
  heights := IsEmpty(pts) select [RealField(Precision)| ]
                          else [HeightNew(pt : Precision := Precision) : pt in pts];
  return SymmetricMatrix(Universe(heights),
                         [j eq i select heights[i]
                                 else (HeightNew(pts[i]+pts[j] : Precision := Precision)
                                         - heights[i] - heights[j])/2
                           : j in [1..i], i in [1..#pts]]);
end intrinsic;

intrinsic ReducedBasisNew(pts::[JacHypPt] : Precision := MyPrec(RealField()), Rels := false)
  -> SeqEnum, AlgMatElt, SeqEnum
{ Given a sequence of points on the Jacobian of a genus 2 curve, compute an LLL-reduced basis
  (with respect to the height pairing) of the subgroup generated by the points modulo torsion.
  The second return value is the height pairing matrix of the basis, computed with the
  given precision. If Rels is set to true, the third return value
  is a sequence of sequences of integers such that the corresponding input point differs from
  the specified linear combination of the basis by a torsion point. }
  vprintf ReducedBasis, 1: "ReducedBasisNew: reduce sequence of %o points\n", #pts;
  // initialize
  J := Universe(pts);
  R := RealField(10);
  bas := [J| ];
  mat := Matrix(R, []);
  mati := mat; // inverse of mat
  if Rels then rels := [Parent([1])| ]; end if;
  height := func<pt | R!HeightNew(pt : Precision := 10)>;
  // now consider one point at a time and check if current lattice is enlarged
  for count := 1 to #pts do
    pt := pts[count];
    vprintf ReducedBasis, 2: "  looking at point no. %o...\n", count;
    // compute height
    hpt := height(pt);
    vprintf ReducedBasis, 3: "    height = %o\n", hpt;
    if hpt lt 0.0001 and Order(pt) gt 0 then
      // point is torsion
      vprintf ReducedBasis, 2: "    point is torsion\n";
      if Rels then Append(~rels, [Integers()| 0 : b in bas]); end if;
    else
      // compute height pairing with points in current basis
      hvec := Vector([R| (height(pt+bas[i]) - hpt - mat[i,i])/2 : i in [1..#bas]]);
      // project pt onto space generated by bas
      proj := hvec*mati;
      // subtract integral linear combination of basis to make point small
      cofs := [Round(c) : c in Eltseq(proj)];
      cvec := Vector(R, cofs);
      pt1 := pt - &+[J| cofs[i]*bas[i] : i in [1..#bas]];
      // height of pt1
      hpt1 := hpt + (cvec, cvec*mat - 2*hvec);
      if hpt1 lt 0.0001 and Order(pt1) gt 0 then
        // pt1 is torsion ==> pt in lattice generated by bas
        vprintf ReducedBasis, 2: "    point is %o in current lattice\n", cofs;
        if Rels then Append(~rels, cofs); end if;
      else
        // check if new point is independent
        hvec1 := hvec - cvec*mat;
        mat1 := Matrix([Append(Eltseq(mat[i]), hvec1[i]) : i in [1..#bas]]
                         cat [Append(Eltseq(hvec1), hpt1)]);
        // extend bas and rels corresponding to mat1
        bas1 := Append(bas, pt1);
        if Rels then rels1 := Append([Append(r, 0) : r in rels], Append([c : c in cofs], 1)); end if;
        eps := R!1e-9;
        matL := mat1;
        // testing the determinant below avoids a segfault later in ShortestVectors
        // when matL is deemed to be positive definite but has determinant zero
        // NOTE: in newer versions, IsPositiveDefinite gives an error when it
        //       cannot safely decide --> use a try/catch loop here!!!
        while true do
          flag := false;
          // TO DO: Check that error is the "correct" one!
          try flag := IsPositiveDefinite(matL) and Determinant(matL) gt 0; catch err; end try;
          if flag then break; end if;
          matL +:= eps*IdentityMatrix(R, #bas+1);
          eps *:= 2;
        end while;
        sv := ShortestVectors(LatticeWithGram(matL))[1];
        sseq := [Round(sv[i]) : i in [1..#bas+1]];
        if (Vector(sv)*mat1, Vector(sv)) lt 0.0001
             and Order(&+[J| sseq[i]*bas[i] : i in [1..#bas]] + sseq[#bas+1]*pt1) gt 0
        then
          vprintf ReducedBasis, 2: "    relation between current basis and point: %o\n", sseq;
          // found relation; determine generators of new lattice
          A := FreeAbelianGroup(#bas + 1);
          Q, qmap := quo<A | A!sseq>;
          gens := [Eltseq(A!g @@ qmap) : g in OrderedGenerators(Q)];
          // and representation of old generators by the new ones
          old := [Eltseq(qmap(a)) : a in OrderedGenerators(A)];
          // update bas etc.
          bas := [&+[g[i]*bas1[i] : i in [1..#bas1]] : g in gens];
          mat := gmat*mat1*Transpose(gmat) where gmat := Matrix(R, gens);
          mat := (mat + Transpose(mat))/2; // to be safe...
          if Rels then rels := [Eltseq(Vector(r)*omat) : r in rels1] where omat := Matrix(old); end if;
        else
          vprintf ReducedBasis, 2: "    point is independent from current basis\n";
          // points are independent: use extended bas, mat, rels
          bas := bas1;
          mat := mat1;
          if Rels then rels := rels1; end if;
        end if;
        // LLL reduce current basis
        mat, T := LLLGram(mat);
        // and update bas and rels
        bas := [J| &+[J| T[i,j]*bas[j] : j in [1..#bas]] : i in [1..#bas]];
        if Rels then rels := [Eltseq(Vector(r)*Ti) : r in rels] where Ti := T^-1; end if;
        mati := mat^-1;
      end if;
    end if;
    vprintf ReducedBasis, 1: "current rank is %o\n", #bas;
    vprintf ReducedBasis, 3: "current basis:\n%o\n", bas;
    vprintf ReducedBasis, 3: "current matrix:\n%o\n", mat;
    if Rels then vprintf ReducedBasis, 3: "current relations:\n%o\n", rels; end if;
  end for;
  if Rels then
    return bas, HeightPairingMatrixNew(bas : Precision := Precision), rels;
  else
    return bas, HeightPairingMatrixNew(bas : Precision := Precision);
  end if;
end intrinsic;

intrinsic ReducedBasisNew(pts::{@JacHypPt@} : Precision := MyPrec(RealField()), Rels := false)
  -> SeqEnum, AlgMatElt, SeqEnum
{ Given an index set of points on the Jacobian of a genus 2 curve, compute an LLL-reduced basis
  (with respect to the height pairing) of the subgroup generated by the points modulo torsion.
  The second return value is the height pairing matrix of the basis, computed with the
  given precision. If Rels is set to true, the third return value
  is a sequence of sequences of integers such that the corresponding input point differs from
  the specified linear combination of the basis by a torsion point. }
  return ReducedBasisNew(IndexedSetToSequence(pts) : Precision := Precision, Rels := Rels);
end intrinsic;

intrinsic ReducedBasisNew(pts::{JacHypPt} : Precision := MyPrec(RealField()))
  -> SeqEnum, AlgMatElt
{ Given a set of points on the Jacobian of a genus 2 curve, compute an LLL-reduced basis
  (with respect to the height pairing) of the subgroup generated by the points modulo torsion.
  The second return value is the height pairing matrix of the basis, computed with the
  given precision. }
  bas, mat := ReducedBasisNew(SetToSequence(pts) : Precision := Precision, Rels := false);
  return bas, mat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
// copied from package/Geometry/CrvG2/chabauty-MWS.m, using new height functions
// (can be removed in chabauty-MWS.m when new height functions are the default)
// --> check which parts of the code below are just copied!! (before removing...)
//////////////////////////////////////////////////////////////////////////////////

function MyKernel(mat, prec)
  // vprintf JacPtDivide, 3: "MyKernel: prec = %o, mat =\n%o\n", prec, mat;
  F := BaseRing(mat);
  p := UniformizingElement(F);
  nc := NumberOfColumns(mat);
  nr := NumberOfRows(mat);
  v := Min(prec, Min([Valuation(c) : c in Eltseq(mat)]));
  mat := Matrix([[mat[i,j]/p^v : j in [1..nc]] : i in [1..nr]]);
  assert forall{c : c in Eltseq(mat) | AbsolutePrecision(c) ge prec};
  Rp := pAdicRing(Integers()!p : Precision := prec);
  matR := ChangeRing(ChangeRing(mat, Integers(F)), Rp);
  bas := [ChangeRing(b, F) : b in Basis(Kernel(matR))];
  // vprintf JacPtDivide, 3: "MyKernel: bas =\n%o\n", bas;
  return bas;
end function;

intrinsic IsDivisibleByNew(P::JacHypPt, n::RngIntElt) -> BoolElt, JacHypPt
{Check if P (point on a genus 2 Jacobian over Q) is divisible by n. If yes,
 return a point Q with n*Q = P as second value.}
  // simple tests
  vprintf JacPtDivide, 1: "IsDivisibleBy(pt = %o, n = %o)\n", P, n;
  J := Parent(P);
  if P eq J!0 then return true, P; end if;
  if n eq 0 then return false, _; end if;
  // deal with negative n
  if n lt 0 then P := -P; n := -n; end if;
  if n eq 1 then return true, P; end if;
  // checks
  require BaseField(J) cmpeq Rationals(): "P must be on a Jacobian over Q.";
  C := Curve(J);
  require Genus(C) eq 2: "P must be on a genus 2 Jacobian.";
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve of P's parent must be of the form y^2 = f(x).";
  require IsIntegral(C):
          "The curve of P's parent must have integral coefficients.";
  // another special case
  if 2*P eq J!0 then
    vprintf JacPtDivide, 1: "Special case: 2*P = 0.\n";
    v := Valuation(n, 2);
    if v eq 0 then return true, P; end if;
    T, mT := TorsionSubgroup(J);
    vprintf JacPtDivide, 2: "Torsion subgroup has invariants %o\n", Invariants(T);
    // find element of T mapping to P
    T2 := Kernel(hom<T -> T | [2*t : t in OrderedGenerators(T)]>);
    for t in T2 do
      if mT(t) eq P then tP := t; break; end if;
    end for;
    m := hom<T -> T | [2^v*t : t in OrderedGenerators(T)]>;
    if tP in Image(m) then
      vprintf JacPtDivide, 1: "P is divisible by %o in torsion subgroup\n", 2^v;
      tQ := tP @@ m;
      return true, mT(tQ);
    else
      vprintf JacPtDivide, 1: "P is not divisible by %o in torsion subgroup\n", 2^v;
      return false, _;
    end if;
  end if;
  // pick a prime p such that 2*P is not zero mod p
  K := KummerSurface(J);
  twoPK := 2*K!P;
  a := GCD([Integers()|twoPK[i] : i in [1..3]]);
  assert a ne 0;
  disc := Integers()!Discriminant(f);
  p := 3;
  while IsDivisibleBy(disc, p) or IsDivisibleBy(a, p) or IsDivisibleBy(n, p) do
    p := NextPrime(p);
  end while;
  vprintf JacPtDivide, 1: "First prime p = %o\n", p;
  // find n-division points of P mod p
  Jp := BaseChange(J, Bang(Rationals(), GF(p)));
  G, mG := AbelianGroup(Jp);
  Pp := Jp!P;
  PG := Pp @@ mG;
  mult := hom<G -> G | [n*g : g in OrderedGenerators(G)]>;
  if PG notin Image(mult) then
    vprintf JacPtDivide, 1: "P is not divisible by %o mod p\n", n;
    return false, _;
  end if;
  QG := PG @@ mult;
  QGs := [QG + k : k in Kernel(mult)];
  if #QGs gt 1 then
    vprintf JacPtDivide, 1:
            "P is not uniquely divisible by %o in group mod p\n", n;
    // try to improve on number of points to check for lifting
    T, mT := TorsionSubgroup(J);
    nT := Kernel(hom<T -> T | [n*t : t in OrderedGenerators(T)]>);
    vprintf JacPtDivide, 2: "#J(Q)[%o] = %o\n", n, #nT;
    count := 1;
    p1 := NextPrime(p);
    while count lt 10 and #QGs gt #nT do
      while IsDivisibleBy(disc, p1) or IsDivisibleBy(a, p1)
              or IsDivisibleBy(n, p1) do
        p1 := NextPrime(p1);
      end while;
      vprintf JacPtDivide, 1: "Next prime p = %o\n", p1;
      Jp1 := BaseChange(J, Bang(Rationals(), GF(p1)));
      G1, mG1 := AbelianGroup(Jp1);
      Pp1 := Jp1!P;
      PG1 := Pp1 @@ mG1;
      mult1 := hom<G1 -> G1 | [n*g : g in OrderedGenerators(G1)]>;
      if PG1 notin Image(mult1) then
        vprintf JacPtDivide, 1: "P is not divisible by %o mod p\n", n;
        return false, _;
      end if;
      QG1 := PG1 @@ mult1;
      QGs1 := [QG1 + k : k in Kernel(mult1)];
      if #QGs1 lt #QGs then
        vprintf JacPtDivide, 2: "Current prime gives fewer division points\n";
        p := p1;
        Jp := Jp1;
        G := G1; mG := mG1;
        Pp := Pp1;
        PG := PG1;
        mult := mult1;
        QG := QG1;
        QGs := QGs1;
      end if;
      count +:= 1;
      pt := NextPrime(p1);
    end while;
    // reduce to representatives of cosets of nT
    nTp := Set(sub<G | [(Jp!mT(t)) @@ mG : t in Generators(nT)]>);;
    reps := {};
    rem := Set(QGs);
    while not IsEmpty(rem) do
      q := Rep(rem);
      Include(~reps, q);
      for t in nTp do
        Exclude(~rem, q+t);
      end for;
    end while;
    QGs := Setseq(reps);
    vprintf JacPtDivide, 1:
            "Need to check %o division points mod %o\n", #QGs, p;
  else // #QGs eq 1
    vprintf JacPtDivide, 1:
            "P is uniquely divisible by %o in group mod %o\n", n, p;
  end if;
  // Now QGs is a sequence of points Q in J(F_p) such that n*Q = P-bar
  // and such that if P is n-divisible, then one of them must lift to
  // an n-division point of P in J(Q).

  // Some preliminary computations.
  hP := HeightNew(P);
  vprintf JacPtDivide, 2: "\nCanonical height of P is %o\n", hP;
  hQ := hP/n^2; // canonical height of a potential Q
  vprintf JacPtDivide, 2: "Canonical height of P/%o would be %o\n", n, hQ;
  hc := HeightConstantNew(J : Fast);
  vprintf JacPtDivide, 2: "Height constant bound for J is %o\n", hc;
  bound := hQ + hc; // bound for naive height of Q
  Bound := Exp(bound);           // non-log height bound
  bound1 := Log(64.0) + 2*bound; // bound for p-adic precision
  pbound := Ceiling(bound1/Log(p)); // p-adic precision needed
  vprintf JacPtDivide, 2: "%o-adic precision needed is %o\n", p, pbound;
  F := pAdicField(p);
  KF := BaseExtend(K, F);
  Kp := KummerSurface(Jp);
  PKp := Kp!Pp;
  PK := K!P;
  jP := 1;
  while jP le 4 and PKp[jP] eq 0 do jP +:= 1; end while;
  // loop through the possible images of Q in J(F_p) (mod J(Q)[n])
  for QG in QGs do
    prec := 1;
    Qp := mG(QG);
    QpK := Kp!Qp;
    dkv := [ Evaluate(Kp`DEquation[i], Eltseq(QpK)) : i in [1..4] ];
    // vprintf JacPtDivide, 3: "QpK = %o, dkv = %o\n", QpK, dkv;
    jQ := 1;
    while jQ le 4 and QpK[jQ] eq 0 do jQ +:= 1; end while;
    iQ := 1;
    while iQ le 4 and dkv[iQ] eq 0 do iQ +:= 1; end while;
    assert iQ le 4;
    vprintf JacPtDivide, 1:
            "\nTrying to lift Q = %o...\n", QpK;
    QK:= KF![ (F!Integers()!a) + O(F!p) : a in Eltseq(QpK) ];
    L := Lattice(4, ChangeUniverse(Eltseq(QK), Integers())
                     cat [p,0,0,0, 0,p,0,0, 0,0,p,0, 0,0,0,p]);
    app := Eltseq(Basis(L)[1]);
    while prec lt pbound do
      vprintf JacPtDivide, 2: "Current precision is %o\n", prec;
      // next lift
      newprec := Min(2*prec, pbound);
      vprintf JacPtDivide, 2: "New precision is %o\n", newprec;
      F`DefaultPrecision := Max(F`DefaultPrecision, newprec);
      Onew := O(F!p^newprec);
      KF := BaseExtend(K, F);
      // lift point
      s := [ (F!Integers()!a) + Onew : a in Eltseq(QK) ];
      kv := Evaluate(KF`Equation, s);
      dkv := [ Evaluate(KF`DEquation[i], s) : i in [1..4] ];
      assert Valuation(dkv[iQ]) eq 0;
      s1 := s;
      s1[iQ] -:= kv/dkv[iQ];
      s1 := Eltseq(KF!s1);
      mat := Matrix([[dkv[k], k eq jQ select 1 else 0] : k in [1..4]]);
      vprintf JacPtDivide, 3:
              "matrix:\n%o\n", mat;
      matker := MyKernel(mat, prec);
      matker := [bs : b in matker | Min([Valuation(c) : c in bs]) eq 0
                                     where bs := Eltseq(b)];
      vprintf JacPtDivide, 3:
              "Kernel of matrix:\n%o\n", matker;
      assert #matker eq 2;
      assert Min([Min([AbsolutePrecision(c) : c in b]) : b in matker]) ge prec;
      s2 := KF![s1[i] + p^prec*matker[1][i] : i in [1..4]];
      s3 := KF![s1[i] + p^prec*matker[2][i] : i in [1..4]];
      s1 := KF!s1;
      vprintf JacPtDivide, 3:
              "Possible lifts:\n  %o\n  %o\n  %o\n", s1, s2, s3;
      // find correct lift so that n*Q = P
      ns1 := Eltseq(n*s1);
      ns2 := Eltseq(n*s2);
      ns3 := Eltseq(n*s3);
      assert Valuation(ns1[jP]) eq 0
               and Valuation(ns2[jP]) eq 0 and Valuation(ns3[jP]) eq 0;
      ns1 := Vector([a/ns1[jP] + Onew : a in ns1]);
      ns2 := Vector([a/ns2[jP] + Onew : a in ns2]);
      ns3 := Vector([a/ns3[jP] + Onew : a in ns3]);
      ns := Vector([a/es[jP] + Onew : a in es]) where es := Eltseq(KF!PK);
      vprintf JacPtDivide, 3: "Target (P on Kummer surface):\n  %o\n", ns;
      vprintf JacPtDivide, 3:
              "Approximations:\n  %o\n  %o\n  %o\n", ns1, ns2, ns3;
      ds1 := ns1 - ns;
      ds2 := ns2 - ns;
      ds3 := ns3 - ns;
      vprintf JacPtDivide, 3: "Errors:\n  %o\n  %o\n  %o\n", ds1, ds2, ds3;
      // write ds1 as linear combination of ds2 and ds3 (or similar)
      mat := Matrix([ds1, ds2, ds3]);
      matker := MyKernel(mat, newprec-prec);
      vprintf JacPtDivide, 3: "Kernel of corresponding matrix:\n%o\n", matker;
      matker := [b : b in matker | Min([Valuation(c) : c in Eltseq(b)]) eq 0];
      assert #matker eq 1;
      b := matker[1];
      s := &+Eltseq(b);
      assert Valuation(s) eq 0;
      b := [a/s : a in Eltseq(b)];
      v, i := Min([Valuation(c) : c in b]);
      if i eq 1 then
        QK := KF![s1[i] + b[2]*(s2[i]-s1[i]) + b[3]*(s3[i]-s1[i]) + Onew
                   : i in [1..4]];
      elif i eq 2 then
        QK := KF![s2[i] + b[1]*(s1[i]-s2[i]) + b[3]*(s3[i]-s2[i]) + Onew
                   : i in [1..4]];
      else
        QK := KF![s3[i] + b[1]*(s1[i]-s3[i]) + b[2]*(s2[i]-s3[i]) + Onew
                   : i in [1..4]];
      end if;
      vprintf JacPtDivide, 2: "New approximate lift:\n%o\n", QK;
      assert Min([AbsolutePrecision(c) : c in Eltseq(QK)]) ge newprec;
      qs := Vector([a/es[jP] : a in es]) where es := Eltseq(n*QK);
      vprintf JacPtDivide, 3: "approx. error n*Q - P:\n%o\n", qs-ns;
      assert forall{i : i in [1..4] | Valuation(qs[i]-ns[i]) ge newprec};
      // compute approximation
      q := p^newprec;
      L := Lattice(4, ChangeUniverse(Eltseq(QK), Integers())
                       cat [q,0,0,0, 0,q,0,0, 0,0,q,0, 0,0,0,q]);
      app1 := Eltseq(Basis(L)[1]);
      // check if already found
      if app eq app1 and IsPoint(K, app1) then
        QK := K!app1;
        if n*QK eq PK then break; end if; // finish the prec while loop
      end if;
      prec := newprec; app := app1;
    end while;
    // now prec = b. Check if found
    if IsPoint(K, app) then
      QK := K!app;
      if n*QK eq PK then
        QJ := {Q : Q in Points(J, QK) | n*Q eq P};
        if not IsEmpty(QJ) then
          vprintf JacPtDivide, 1: "\nFound rational point Q = %o\n\n", Rep(QJ);
          return true, Rep(QJ);
        end if;
      end if;
    end if;
    vprintf JacPtDivide, 1:
            "Q = %o does not lift to a %o-division point of P\n", QpK, n;
  end for;
  // nothing found
  return false, _;
end intrinsic;

function get_subspace(V, p, test)
  // V is an F_p-vector space or elementary abelian p-group,
  // test is a user program returning a flag and some additional information.
  // Returns a basis of the subspace V' of V
  //  consisting of elements satisfying the test,
  // together with information associated to them.
  // We assume that the subset of elements satisfying the test _is_ a subspace!
  curr := sub<V |>; // the currently known subspace of V'
  gens := [V | ];   // generators of curr
  reps := [];       // info associated to generators
  Vcurr, qmap := quo<V | curr>; // the quotient space V/curr
  S0 := { Vcurr | 0 };          // cosets we know are not in V', together with zero
  S1 := Set(Vcurr) diff S0;     // cosets that still have to be tested
  while not IsEmpty(S1) do
    // Choose some element in S1
    g := Rep(S1);
    gV := g @@ qmap; // a representative in V
    // check if it is in V'
    flag, divpt := test(gV);
    if flag then
      // can enlarge lower bound for V'
      Append(~gens, gV);
      Append(~reps, divpt);
      curr := sub<V | curr, gV>;
      Vcurr, qmap1 := quo<Vcurr | g>;
      qmap := qmap*qmap1;
      // update cosets we know are not in V' and elements remaining to be checked
      S0 := qmap1(S0);
      S1 := Set(Vcurr) diff S0;
    else
      // can enlarge known set of cosets not in V'
      Snew := { k*g : k in [1..p-1] };
      S0 join:= Snew;
      S1 diff:= Snew;
    end if;
  end while; // not IsEmpty(S1)
  return gens, reps;
end function;

function SaturateByDivision(bas, p)
  // Compute a set of generators of the p-saturation of bas
  //  (a sequence of points on a genus 2 Jacobian over Q)
  // by testing points whether they are divisible by p.
  J := Universe(bas);
  // This creates a test function returning a flag and (if it exists)
  //  a p-division point of the point represented by the vector vec.
  function maketest(gens)
    return func<vec | IsDivisibleByNew(&+[J | vec[i]*gens[i] : i in [1..#gens]])>;
  end function;

  // Find divisible subgroup, enlarge group, and repeat as long as there is change.
  V := KSpace(GF(p), #bas);
  repeat
    // find divisible subspace
    gens, reps := get_subspace(V, maketest(bas));
    if not IsEmpty(gens) then
      bas := ReducedBasisNew(bas cat reps);
    end if;
  until IsEmpty(gens);
  return bas;
end function;


intrinsic SaturationNew(bas::SeqEnum[JacHypPt], p::RngIntElt
                         : AuxPrimes := 3, Raw := false, RedPrimes := [])
                        -> SeqEnum, SeqEnum
{Saturate the subgroup of the Mordell-Weil group generated by bas
 at the prime p. Returns generators of the free part of the saturated group
 and the useful reduction primes.}
  J := Universe(bas);
  require IsPrime(p): "p must be a prime number.";
  // find a number (rank + AuxPrimes) of good primes q s.t. p|#J(F_q)
  require BaseField(J) cmpeq Rationals(): "P must be on a Jacobian over Q.";
  C := Curve(J);
  require Genus(C) eq 2: "P must be on a genus 2 Jacobian.";
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve of P's parent must be of the form y^2 = f(x).";
  require IsIntegral(C):
          "The curve of P's parent must have integral coefficients.";
  vprintf JacHypSaturation, 1: "Saturation: p = %o, on y^2 = %o\n", p, f;
  T, mT := TorsionSubgroup(J);
  if not Raw then
    bas := ReducedBasisNew(bas);
  end if;
  rank := #bas + #[i : i in Invariants(T) | IsDivisibleBy(i, p)];
  num := rank + AuxPrimes;
  disc := Integers()!Discriminant(Curve(J));
  q := 2;
  MW := AbelianGroup(Invariants(T) cat [0 : b in bas]);
  genMW := [mT(t) : t in OrderedGenerators(T)] cat bas;
  vprintf JacHypSaturation, 3:
          "Generators of known subgroup (torsion first):\n%o\n", genMW;
  mMW := map<MW -> J | x :-> &+[J | s[i]*genMW[i] : i in [1..#genMW]]
                        where s := Eltseq(x)>;
  MWp, qmap := quo<MW | [p*g : g in Generators(MW)]>;
  curr := MWp;
  // curr is the subgroup of MW/p*MW of potentially p-divisible elements
  count := 0;
  Gp := AbelianGroup([p]);
  remaining_qs := RedPrimes;
  RedPrimes := [Integers()|]; // collect the helpful primes
  while count lt num do
    repeat
      if IsEmpty(remaining_qs) then
        q := NextPrime(q);
        while IsDivisibleBy(disc, q) do q := NextPrime(q); end while;
      else
        q := remaining_qs[1]; Remove(~remaining_qs, 1);
        assert not IsDivisibleBy(disc, q);
      end if;
      Jq := BaseChange(J, Bang(Rationals(), GF(q)));
      h := #Jq;
    until IsDivisibleBy(h, p) and (IsDivisibleBy(#T, p) or Valuation(h, p) eq 1);
    vprintf JacHypSaturation, 2: "Found relevant prime q = %o\n", q;
    Append(~RedPrimes, q);
    // avoid discrete logarithms when easily possible
    if Valuation(h, p) eq 1 then
      // find a generator of the p-torsion in J(F_q)
      cofactor := ExactQuotient(h, p);
      repeat
        gen := cofactor*Random(Jq);
      until gen ne Jq!0;
      assert p*gen eq Jq!0;
      // set up lookup table
      multiples := [<Jq!0, Gp![0]>];
      pt := gen;
      for n := 1 to p-1 do
        Append(~multiples, <pt, Gp![n]>);
        pt +:= gen;
      end for;
      lookup := map<{e[1] : e in multiples} -> Gp | multiples>;
      // find discrete logs of generators of MW
      m := hom<MWp -> Gp | [lookup(cofactor*(Jq!b)) : b in bas]>;
      curr meet:= Kernel(m);
    else
      // use group structure, even though slow...
      Gq, mGq := AbelianGroup(Jq);
      Gqp, Gqmap := quo<Gq | [p*g : g in Generators(Gq)]>;
      m := hom<curr -> Gqp
              | [Gqmap((Jq!mMW((MWp!g) @@ qmap)) @@ mGq)
                  : g in OrderedGenerators(curr)]>;
      curr := Kernel(m);
    end if;
    if #curr eq 1 then
      // no potential p-divisible elements left
      vprintf JacHypSaturation, 1: "Group is saturated at p = %o\n", p;
      return bas, RedPrimes;
    else
      vprintf JacHypSaturation, 2: "Dimension of remaining space is %o\n",
                              Valuation(#curr, p);
    end if;
    count +:= 1;
  end while;
  // now check for elements of curr if they are p-divisible
  vprintf JacHypSaturation, 1: "Trying to divide remaining points...\n";
  function test(g)
    return IsDivisibleByNew(mMW((MWp!g) @@ qmap), p);
  end function;
  gens, new := get_subspace(curr, p, test);
  curr := sub< curr | gens >;
  if #curr eq 1 then
    // no potential p-divisible elements left
    vprintf JacHypSaturation, 1: "Group is saturated at p = %o\n", p;
    return bas, RedPrimes;
  end if;
  vprintf JacHypSaturation, 1: "Dimension of remaining space is %o\n",
                          Valuation(#curr, p);
  // Otherwise, extend bas and repeat
  // (could be made more efficient by also storing
  //  the mod q information computed above and re-using it)
  return SaturationNew(bas cat new, p : AuxPrimes := AuxPrimes, RedPrimes := RedPrimes);
end intrinsic;

SatEntry := recformat< p : RngIntElt,    // the prime at which we saturate
                       MWp : GrpAb,      // known group G mof p*G
                       qmap : Map,       // quotient map G -> MWp
                       curr : GrpAb,     // sungroup of MWp of elements potentially divisible by p
                       Gp : GrpAb,       // Z/pZ
                       count : RngIntElt // counts the reduction primes used so far for p
                     >;

intrinsic CheckSaturationAtPrimesNew(bas::SeqEnum[JacHypPt], primes::SeqEnum[RngIntElt]
                                      : AuxPrimes := 3, RedPrimes := [])
                                      -> BoolElt, SeqEnum, SeqEnum
{Check if the subgroup of the Mordell-Weil group generated by bas is saturated
 at all primes in primes. The second value is sequence of possibly non-saturated primes;
 the third value is a list of reduction primes that provided information.}
  J := Universe(bas);
  require BaseField(J) cmpeq Rationals(): "P must be on a Jacobian over Q.";
  C := Curve(J);
  require Genus(C) eq 2: "P must be on a genus 2 Jacobian.";
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve of P's parent must be of the form y^2 = f(x).";
  require IsIntegral(C):
          "The curve of P's parent must have integral coefficients.";
  vprintf JacHypSaturation, 1: "SaturationAtPrimes: primes = %o, bas =\n%o\n", primes, bas;
  T, mT := TorsionSubgroup(J);
  bas := ReducedBasisNew(bas);
  // deal with torsion primes and 2 separately
  torsion_primes := [p : p in PrimeDivisors(2*#T) | p in primes];
  rem_primes := [Integers()|];
  for p in torsion_primes do
    bas1 := SaturationNew(bas, p : AuxPrimes := AuxPrimes, Raw);
    if bas1 ne bas then Append(~rem_primes, p); end if; // note unsaturated prime
    Exclude(~primes, p);
  end for;
  for p in primes do
    require IsPrime(p): "The elements of primes must be prime numbers.";
  end for;
  // for the remaining primes, we have that G/pG = (Z/pZ)^#bas
  rank := #bas;
  num := rank + AuxPrimes;
  disc := Integers()!Discriminant(Curve(J));
  q := 2;
  MW := AbelianGroup(Invariants(T) cat [0 : b in bas]);
  genMW := [mT(t) : t in OrderedGenerators(T)] cat bas;
  vprintf JacHypSaturation, 2:
          "Generators of known subgroup (torsion first):\n%o\n", genMW;
  mMW := map<MW -> J | x :-> &+[J | s[i]*genMW[i] : i in [1..#genMW]]
                        where s := Eltseq(x)>;
  // now do everything in parallel for the primes in primes
  remaining_qs := RedPrimes;
  RedPrimes := {Integers()|}; // collect the helpful primes
  HT := AssociativeArray(Set(primes));
  for p in primes do
    MWp, qmap := quo<MW | [p*g : g in Generators(MW)]>;
    HT[p] := rec<SatEntry | p := p, MWp := MWp, qmap := qmap, curr := MWp,
                            count := 0, Gp := AbelianGroup([p])>;
  end for;
  primes0 := Set(primes); // primes still to be considered further
  while not IsEmpty(primes0) do
    // find next prime of good reduction or take next prime from given list
    if IsEmpty(remaining_qs) then
      q := NextPrime(q);
      while IsDivisibleBy(disc, q) do q := NextPrime(q); end while;
    else
      q := remaining_qs[1]; Remove(~remaining_qs, 1);
      assert not IsDivisibleBy(disc, q);
    end if;
    // find order of group mod q
    Jq := BaseChange(J, Bang(Rationals(), GF(q)));
    h := #Jq;
    for p in primes do
      // check if we get information on p-divisibility
      if Valuation(h, p) eq 1 then
        vprintf JacHypSaturation, 2: "Found relevant prime q = %o for p = %o\n", q, p;
        Include(~RedPrimes, q);
        MWp := HT[p]`MWp;
        Gp := HT[p]`Gp;
        curr := HT[p]`curr;
        count := HT[p]`count;
        // avoid discrete logarithms:
        // find a generator of the p-torsion in J(F_q)
        cofactor := ExactQuotient(h, p);
        repeat
          gen := cofactor*Random(Jq);
        until gen ne Jq!0;
        assert p*gen eq Jq!0;
        // set up lookup table
        multiples := [<Jq!0, Gp![0]>];
        pt := gen;
        for n := 1 to p-1 do
          Append(~multiples, <pt, Gp![n]>);
          pt +:= gen;
        end for;
        lookup := map<{e[1] : e in multiples} -> Gp | multiples>;
        // find discrete logs of generators of MW
        m := hom<MWp -> Gp | [lookup(cofactor*(Jq!b)) : b in bas]>;
        curr meet:= Kernel(m);
        if #curr eq 1 then
          // no potential p-divisible elements left
          vprintf JacHypSaturation, 1: "Group is saturated at p = %o (used reduction primes up to %o)\n", p, q;
          Exclude(~primes0, p);
          Exclude(~primes, p); // don't have to look at this prime any further
          vprintf JacHypSaturation, 1: "  %o primes remaining\n", #primes;
          Remove(~HT, p);
        else
          vprintf JacHypSaturation, 2: "Dimension of remaining space is %o\n",
                                  Valuation(#curr, p);
          count +:= 1;
          if count ge num then
            Exclude(~primes0, p); // don't wait further on this prime
          end if;
          // update data in HT
          HT[p]`curr := curr;
          HT[p]`count := count;
        end if;
      end if; // Valuation(h, p) eq 1
    end for;
  end while;
  rem_primes := Setseq(Set(rem_primes) join Keys(HT));
  return IsEmpty(rem_primes), rem_primes, Sort(Setseq(RedPrimes));
end intrinsic;

