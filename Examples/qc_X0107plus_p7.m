// Compute the rational points on X0(107)+ using quadratic Chabauty for p=7
// + the Mordell-Weil sieve
//
// See §1.1 of GM. 
//
// This uses the Z=1 patch for the CG heights, then the X=1 patch for QC. 
//
// Requires the QCMod package, available from https://github.com/steffenmueller/QCMod

t0 := Cputime();
SetLogFile("qc_X0107plus.log");
load "qc_init_g2.m";
load "~/code/heights_above_p/Examples/good_reps.m";
load "qc_modular.m";
_<x> := PolynomialRing(Rationals());
 

f107 := x^6 + 2*x^5 + 5*x^4 + 2*x^3 - 2*x^2 - 4*x - 3;
X := HyperellipticCurve(f107); 

J := Jacobian(X);

N := 12;
f := HyperellipticPolynomials(X); 
gX := Genus(X);
ptsX := Points(X:Bound:=100);
"Small points: ", ptsX;


// Find primes for the quadratic Chabauty computation. In particular, check whether they 
// look promising for a combination of qc and the Mordell-Weil sieve
//qc_primes, groups , good_primes := find_qc_primes(X : mws_primes_bound := 10000, qc_primes_bound := 100, number_of_bad_disks := 0, inf_modp_allowed := true, ordinary := true, known_rat_pts := ptsX, printlevel :=1); 

// Compute generators for the Mordell-Weil group 
torsion_bas, torsion_orders, bas := generators_g2(J);
printf "The rank is %o.\n", #bas; // rank = 2
// This spares us the trouble of checking saturation in MW sieve computation.
bas[2] := -bas[2];

primes := [7]; 
p := primes[1];
exponents := [5]; // Comes from find_qc_primes

D_representatives, F_representatives, E_representatives, G_representatives,
     intersections, factors1, factors2 := 
         good_representatives(X, p, bas : N := N, multiple_bound := 20);




S0 := CuspidalSubspace(ModularSymbols(107, 2)); 
S := AtkinLehnerSubspace(S0, 107, 1);
assert hecke_operator_generates(S, p); // true for 7 and 11


// First compute local heights of representatives for generators of J(Q) tensor Q at p. 

fake_coeffs := [];

// Compute good generators and intersection data for Coleman-Gross heights

divisors := [* [* D_representatives[1,1], E_representatives[1,1] *],
               [* F_representatives[2,2], G_representatives[2,2] *] *];

splitting_indices := [[factors1[1,1],0], [0,factors2[2,2]]];

// Computed using sage

local_CG_hts_bas := [
 4*7 + 4*7^2 + 2*7^3 + 2*7^4 + 3*7^6 + 5*7^7 + 7^8 + 5*7^9 + 4*7^10 
, 4*7 + 3*7^2 + 5*7^3 + 7^4 + 7^5 + 2*7^6 + 7^7 + 7^8 + 7^9 + 3*7^10 
, 6*7^2 + 3*7^3 + 5*7^4 + 6*7^5 + 2*7^6 + 3*7^7];

ptsX := Points(X:Bound:=100);
"Small points: ", ptsX;
base_pt := [ptsX[3,1]/ptsX[3,3], ptsX[3,2]/ptsX[3,3]^(gX+1)]; 

//SetVerbose("JacHypHeight", 1);

data := coleman_data(y^2-f, p, N : useU :=false);
height_coeffs, reg := new_height_coefficients(divisors, Append(intersections[1], intersections[2,2]), [factors1, factors2], local_CG_hts_bas, data);

printf "\nStarting quadratic Chabauty for p = %o.\n", p;
time good_affine_rat_pts_xy, no_fake_pts, bad_affine_rat_pts_xy, data, fake_rat_pts, bad_Qppoints :=
     QCModAffine(y^2-f, p : printlevel := 1, unit_root_splitting,
          N := N, prec := 50, base_point := base_pt, 
              height_coeffs := height_coeffs, use_log_basis);

  // Here * good_affine_rat_pts_xy contains the found rational points in disks where the Frob lift is defined 
  //      * no_fake_pts is true iff the solutions are exactly the rational points
  //      * bad_affine_rat_pts_xy contains the found rational points in disks where the Frob lift isn't defined 
  //      * data is the Coleman data of X at p used in the qc computation
  //      * fake_rat_pts contains the p-adic solutions that don't look rational
  //      * bad_Qppoints contains the disks where Frob isn't defined
  //
  // Express the images of the solutions under Abel-Jacobi in terms of the generators mod p^N
  //
  fake_coeffs_mod_pN, rat_coeffs_mod_pN := coefficients_mod_pN(fake_rat_pts, good_affine_rat_pts_xy, divisors, base_pt, splitting_indices, data);
  // Check that the coefficients of the known rational points are correct.
  assert &and[&+[rat_coeffs_mod_pN[j,i] * bas[i] : i in [1..gX]] eq X!good_affine_rat_pts_xy[j] - X!base_pt : j in [1..#good_affine_rat_pts_xy]];
  Append(~fake_coeffs, [ fake_coeffs_mod_pN ]);

""; "Use the Mordell-Weil sieve to show that the additional solutions aren't rational.";

"generating cosets";
time qc_fake_coeffs_mod_M := coeffs_CRT(fake_coeffs, primes, exponents);
"number of cosets", #qc_fake_coeffs_mod_M;
qc_M := &*[primes[i]^exponents[i] : i in [1..#primes]];  // modulus

//mws_primes := sieving_primes(qc_M, good_primes, groups, 10); // compute sieving primes -- precomputed 131
mws_primes := [131];
printf "starting MW-sieve\n";
time done_fake := MWSieve(J, mws_primes, qc_M, bas cat torsion_bas, X!base_pt, qc_fake_coeffs_mod_M : known_rat_coeffs := rat_coeffs_mod_pN );
assert done_fake;
printf "No additional solutions are rational\n";



X, phi := Transformation(X, [0,1,1,0]);
"Now look at affine piece Z=1";
J := Jacobian(X);

f := HyperellipticPolynomials(X); 
ptsX := Points(X:Bound:=100);
"Small points: ", ptsX;
base_pt := [ptsX[3,1]/ptsX[3,3], ptsX[3,2]/ptsX[3,3]^(gX+1)]; 

function to_infty(L, g)
  M := [];
  for P in L do 
    assert P[1] ne 0;
    Append(~M, [1/P[1], P[2]/P[1]^(g+1)]);
  end for;
  return M;
end function;

divisors := [* [* to_infty(D_representatives[1,1], 2), to_infty(E_representatives[1,1], 2) *],
               [* to_infty(F_representatives[2,2], 2), to_infty(G_representatives[2,2], 2) *] *];

data := coleman_data(y^2-f, p, N : useU :=false);
height_coeffs, reg := new_height_coefficients(divisors, Append(intersections[1], intersections[2,2]), [factors1, factors2], local_CG_hts_bas, data);



printf "\nStarting quadratic Chabauty for p = %o.\n", p;
time good_affine_rat_pts_xy, no_fake_pts, bad_affine_rat_pts_xy, data, fake_rat_pts, bad_Qppoints :=
     QCModAffine(y^2-f, p : printlevel := 1, unit_root_splitting,
          N := N, prec := 50, base_point := base_pt, 
              height_coeffs := height_coeffs, use_log_basis);

"Done with QC";
  // Here * good_affine_rat_pts_xy contains the found rational points in disks where the Frob lift is defined 
  //      * no_fake_pts is true iff the solutions are exactly the rational points
  //      * bad_affine_rat_pts_xy contains the found rational points in disks where the Frob lift isn't defined 
  //      * data is the Coleman data of X at p used in the qc computation
  //      * fake_rat_pts contains the p-adic solutions that don't look rational
  //      * bad_Qppoints contains the disks where Frob isn't defined
  //
  // Express the images of the solutions under Abel-Jacobi in terms of the generators mod p^N
  //
  //
fake_coeffs := [];
data := coleman_data(y^2-f, p, 6 : useU :=false);
fake_coeffs_mod_pN, rat_coeffs_mod_pN := coefficients_mod_pN(fake_rat_pts, good_affine_rat_pts_xy, divisors, base_pt, splitting_indices, data);
// Check that the coefficients of the known rational points are correct.
//
bas := [Evaluate(phi, P) : P in bas];
assert &and[&+[rat_coeffs_mod_pN[j,i] * bas[i] : i in [1..gX]] eq X!good_affine_rat_pts_xy[j] - X!base_pt : j in [1..#good_affine_rat_pts_xy]];
Append(~fake_coeffs, [ fake_coeffs_mod_pN ]);

""; "Use the Mordell-Weil sieve to show that the additional solutions aren't rational.";

"generating cosets";
time qc_fake_coeffs_mod_M := coeffs_CRT(fake_coeffs, primes, exponents);
"number of cosets", #qc_fake_coeffs_mod_M;
qc_M := &*[primes[i]^exponents[i] : i in [1..#primes]];  // modulus

//mws_primes := sieving_primes(qc_M, good_primes, groups, 10); // compute sieving primes 
mws_primes := [131];
printf "starting MW-sieve\n";
time done_fake := MWSieve(J, mws_primes, qc_M, bas cat torsion_bas, X!base_pt, qc_fake_coeffs_mod_M : known_rat_coeffs := rat_coeffs_mod_pN );
assert done_fake;
printf "No additional solutions are rational\n";
printf "Hence the set of rational points on \n%o is precisely \n %o\n", X, ptsX;
t1 := Cputime();
printf "\nQC+MWS needed %o seconds \n", t1-t0;


