// g2wrapper.m
//
// Some functions for genus 2 curves (and their Jacobians):
// * MordellWeilGroup
// * Genus2Information
//
// M. Stoll, started 2016-04-06

function check_jpoints()
  // need Magma version >= 2.21-12
  a, b, c := GetVersion();
  return a gt 2 or (a eq 2 and b gt 21) or (a eq 2 and b eq 21 and c ge 12);
//   return System("which j-points >& /dev/null") eq 0;
end function;

intrinsic MordellWeilGroupGenus2(J::JacHyp : SearchBounds := [5,10,20,50,100,300,1000],
                                             MaxBound := 1000, MaxIndex := 1000, Quiet := true)
                                  -> GrpAb, Map, BoolElt, BoolElt
{Given the Jacobian J of a genus 2 curve over the rationals, this attempts
 to compute the Mordell-Weil group J(Q). It returns an abstract abelian
 group G and a map from G to J(Q). The third value is a flag that indicates
 whether the result is proved to be correct. The fourth value is another flag
 that indicates whether the subgroup found could be shown to be of finite index,}
  // SearchBounds gives the successive height bounds for the point search on the Jacobian;
  // it can also be just a number
  if Type(SearchBounds) ne SeqEnum then SearchBounds := [SearchBounds]; end if;
  // MaxBound is the maximal bound used for point search when saturating
  MaxBound := Max(MaxBound, Max(SearchBounds));
  // MaxIndex is a bound for the largest prime at which to saturate
  jpflag := check_jpoints();

  // some checks
  require Dimension(J) eq 2: "J must be the Jacobian of a genus 2 curve.";
  require BaseField(J) cmpeq Rationals(): "J must be defined over the field of rational numbers.";
  if not Quiet then
    printf "\n"*"-"^72*"\n";
    printf "Mordell-Weil group of the Jacobian of\n%o\n", Curve(J);
    printf "-"^72*"\n\n";
    printf "jpflag = %o\n", jpflag;
  end if;

  // change to a model without linear terms in y if necessary
  C := Curve(J);
  f, h := HyperellipticPolynomials(C);
  if h ne 0 then
    C1 := SimplifiedModel(C);
    J1 := Jacobian(C1);
    changed := true;
  else
    C1 := C;
    J1 := J;
    changed := false;
  end if;
  // find torsion subgroup
  T, mT := TorsionSubgroup(J1);
  if not Quiet then printf "The torsion subgroup has invariants %o.\n", Invariants(T); end if;
  // compute upper bound on the rank
  if not Quiet then printf "Computing rank bound...\n"; end if;
  bound := RankBound(J1);
  if not Quiet then printf "Upper bound for the rank: %o\n\n", bound; end if;
  if bound gt 0 then
    // search for points on J
    if not Quiet then printf "Searching for points on J\n"; end if;
    for hb in SearchBounds do
      usedbound := hb;
      if not Quiet then printf "  up to multiplicative height %o...\n", hb; end if;
      points := jpflag select Points(J1 : Bound := hb, ReturnAll)
                       else Points(J1 : Bound := hb);
      if not Quiet then printf "Found %o point%o,", #points, #points eq 1 select "" else "s"; end if;
      bas, hmat := ReducedBasisNew(points);
      if not Quiet then printf " generating a subgroup of rank %o\n", #bas; end if;
      if #bas eq bound then
        // found enough points
        if not Quiet then printf " ==> rank is %o <==\n\n", bound; end if;
        break;
      end if;
    end for;
    finite_index := #bas eq bound;
    success := false; // will be set to true when saturation was successful
    if finite_index then
      // saturate
      hc := HeightConstantNew(J1 : Modified := jpflag);
        // for now use jpflag; if ReturnAll is implemented with Points(JacHyp), can always set to true
      if not Quiet then printf "Height difference bound is %o.\n", ChangePrecision(hc, 5); end if;
      // find covering radius if rank is small
      if #bas le 4 then
        L := LatticeWithGram(Matrix([[Round(2^10*hmat[i,j]) : j in [1..#bas]] : i in [1..#bas]]));
        cr := CoveringRadius(L)/2^10 + 1.0/2^9; // increase slightly to be on the safe side
        if not Quiet then printf "The MW lattice has (squared) covering radius %o.\n", ChangePrecision(cr, 5); end if;
        satbd := Floor(Exp(hc + cr));
        if satbd le usedbound then
          if not Quiet then printf "The group is already saturated.\n"; end if;
          success := true;
        elif satbd le MaxBound then
          // search for points again (should use "j-points -a" with new height constant)
          if not Quiet then printf "Search for points up to height %o to saturate...\n", satbd; end if;
          oldhmat := hmat;
          points := jpflag select Points(J1 : Bound := satbd, ReturnAll)
                           else Points(J1 : Bound := satbd);
          if not Quiet then printf "Found %o point%o.\n", #points, #points eq 1 select "" else "s"; end if;
          bas, hmat := ReducedBasisNew(points);
          if not Quiet then
            index := Round(Sqrt(Determinant(oldhmat)/Determinant(hmat)));
            if index gt 1 then printf "Saturation enlarges group by index %o\n", index; end if;
          end if;
          success := true;
        end if;
      end if; // #bas le 4
      if not success then
        // try to get good index bound
        if hc ge Log(MaxBound) then
          if not Quiet then printf "The height constant is too large: saturation not possible.\n"; end if;
        else
          if MaxBound gt usedbound then
            if not Quiet then printf "Search for points up to height %o to saturate...\n", MaxBound; end if;
            oldhmat := hmat;
            points := jpflag select Points(J1 : Bound := MaxBound, ReturnAll)
                             else Points(J1 : Bound := MaxBound);
            if not Quiet then printf "Found %o point%o.\n", #points, #points eq 1 select "" else "s"; end if;
            bas, hmat := ReducedBasisNew(points);
            if not Quiet then
              index := Round(Sqrt(Determinant(oldhmat)/Determinant(hmat)));
              if index gt 1 then printf "This leads to a larger group by index %o.\n", index; end if;
            end if;
          end if;
          L := LatticeWithGram(hmat);
          sm := SuccessiveMinima(L);
          B := Log(MaxBound) - hc; // bound for canonical height up to which we know all points
          if not Quiet then printf "We know all points up to canonical height %o.\n", ChangePrecision(B,5); end if;
          indexbound := Floor(Sqrt(Determinant(hmat)*HermiteConstant(#bas)/&*[Min(m,B) : m in sm]));
          if not Quiet then printf "We obtain an index bound of %o.\n\n", indexbound; end if;
          p := 2;
          while p le Min(indexbound, MaxIndex) do
            if not Quiet then printf "Saturating at p = %o...\n", p; end if;
            oldhmat := hmat;
            bas := SaturationNew(bas, p : Raw);
            hmat := HeightPairingMatrixNew(bas);
            if not Quiet then
              index := Round(Sqrt(Determinant(oldhmat)/Determinant(hmat)));
              if index gt 1 then printf "  --> we get a larger group by index %o.\n", index; end if;
            end if;
            p := NextPrime(p);
          end while;
          sucess := PreviousPrime(indexbound+1) le MaxIndex;
        end if;
      end if; // not success
    else
      if not Quiet then printf "We can only show that  %o <= rank <= %o.\n\n", #bas, bound; end if;
    end if; // success
  else
    // bound = 0, so finite group
    bas := [J1| ];
    finite_index := true;
    success := true;
  end if; // bound gt 0
  // set up abstract Mordell-Weil group
  MW := AbelianGroup(Invariants(T) cat [0 : b in bas]);
  gens := [mT(t) : t in OrderedGenerators(T)] cat bas;
  // and map
  if changed then
    // move back to original J
    gens := [Points(J, g[1], g[3])[1] : g in gens];
  end if;
  // set up map from J to the abstract MW group
  hpmati := HeightPairingMatrixNew(bas)^-1;
  // inverse of mT, by enumeration (T is small)
  mTinv := map<{mT(t) : t in T} -> T | [<mT(t), t> : t in T]>;
  function JtoMW(pt)
    // project to free part using height pairing
    vec := Vector([HeightPairingNew(pt, b) : b in bas])*hpmati;
    cofs := [Round(vec[i]) : i in [1..#bas]];
    pttors := pt - &+[cofs[i]*bas[i] : i in [1..#bas]];
    if Order(pttors) gt 0 then
      return MW!(Eltseq(mTinv(pttors)) cat cofs);
    elif HeightNew(pttors) lt 0.5*HeightNew(pt) then
      // repeat with new candidate (the first attempt might have failed
      // because of precision problems)
      mw := JtoMW(pttors);
      return mw + MW!(Eltseq(T!0) cat cofs);
    else
      error "JtoMW: failed to find preimage in MW";
    end if;
  end function;
  MWtoJ := map<MW -> J | a :-> &+[J| s[i]*gens[i] : i in [1..#s]] where s := Eltseq(a), pt :-> JtoMW(pt)>;
  if not Quiet then
    printf "\nThe group we found is";
    invs := Invariants(MW);
    if IsEmpty(invs) then
      printf " trivial.\n\n";
    else
      tors := [i : i in invs | i ne 0];
      rank := #invs - #tors;
      start := true;
      for i in tors do printf "%o Z/%oZ", start select "" else " x", i; start := false; end for;
      if rank eq 1 then
        printf "%o Z", start select "" else " x";
      elif rank gt 1 then
        printf "%o Z^%o", start select "" else " x", rank;
      end if;
      printf ".\n\n";
    end if;
    if success then
      printf "This could be shown to be the full Mordell-Weil group.\n\n";
    elif #bas lt bound then
      if IsOdd(bound - #bas) then
        printf "This group has too small rank, since the rank should be %o.\n\n", IsOdd(bound) select "odd" else "even";
      else
        printf "This group may have have too small rank.\n\n";
      end if;
    else
      printf "This group has finite index in the full Mordell-Weil group.\n\n";
    end if;
  end if;
  return MW, MWtoJ, success, finite_index;
end intrinsic;
