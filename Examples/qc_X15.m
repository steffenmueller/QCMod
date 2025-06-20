SetLogFile("qc_X15.log");
load "qc_init_g2.m";
load "qc_modular.m";
load "divisor_heights.m";
load "howe_zhu.m";
P<x> := PolynomialRing(Rationals());
 
g15 :=  x^3 + x + 1; ; 
h15 := x^6 - 13*x^4 - 38*x^3 + 6*x^2 + 22*x + 6;
 
C_15 := HyperellipticCurve(h15, g15);  
X_15, phi_15 := SimplifiedModel(C_15);

X := X_15;
J := Jacobian(X);
assert HasAbsolutelyIrreducibleJacobian(X, 1000 : printlevel := 0);
"The Jacobian is absolutely simple";

N := 12;
f := HyperellipticPolynomials(X); 
gX := Genus(X);
ptsX := Points(X:Bound:=100);
"Small points: ", ptsX;

// Find primes for the quadratic Chabauty computation. In particular, check whether they 
// look promising for a combination of qc and the Mordell-Weil sieve
//qc_primes, groups, good_primes := 
//             find_qc_primes(X : mws_primes_bound := 100000, qc_primes_bound := 120, number_of_bad_disks := 1, inf_modp_allowed := false, known_rat_pts := ptsX, printlevel :=1); 

// Compute generators for the Mordell-Weil group using Stoll's MordellWeilGroupGenus2
torsion_bas, torsion_orders, bas := generators_g2(J);
bas[2] := -bas[2];

primes := [71]; 
exponents := [3];
p := primes[1];

// First compute local heights of generators of J(Q) at p. 

fake_coeffs := [];
base_pt := [ptsX[1,1]/ptsX[1,3], -ptsX[1,2]/ptsX[1,3]^(gX+1)]; 



splitting_generators, divisors, intersections, splitting_indices, odd_divisors_Qp, odd_f_Qp := height_init_g2(X, p, bas: N := N, multiple_bound := 40); 

odd_f := ChangeRing(odd_f_Qp, Rationals());
odd_data := coleman_data(y^2-odd_f, p, 9 : useU :=false, heights);
odd_divisors := [* [*rationalize(D[1]), rationalize(D[2])*] : D in odd_divisors_Qp *];

odd_data_divisors :=  [
[  [<set_point(pair[1,i,1], pair[1,i,2], odd_data), 1> ,
  <set_point(pair[2,i,1], pair[2,i,2], odd_data), -1>] : i in [1..#pair]]
      : pair in odd_divisors];

// Need to manipulate the representatives to get disjoint support for 
// local height pairings.
// The following is specific to genus 2.
odd_data_divisors_inv := [
[ [<set_point(odd_divisors[1,1,i,1], -odd_divisors[1,1,i,2], odd_data), 1>, 
<set_point(odd_divisors[2,2,i,1], odd_divisors[2,2,i,2], odd_data), -1>] 
 : i in [1,2]  ],  
[ [<set_point(odd_divisors[2,1,i,1], -odd_divisors[2,1,i,2], odd_data), 1>, 
<set_point(odd_divisors[1,2,i,1], odd_divisors[1,2,i,2], odd_data), -1>] 
 : i in [1,2]  ]
];
odd_data`ordinary := true;
odd_data`cpm := -cup_product_matrix(odd_data`basis, odd_data`Q, 2, odd_data`r, odd_data`W0);
printf "Start computation of local height at %o between first pair of divisors\n", p;
time ht1, D1_data := local_height_divisors_p(odd_data_divisors[1], odd_data_divisors_inv[1],odd_data);
"Time for first height";
printf "Start computation of local height at %o between second pair of divisors\n", p;
time ht2 := local_height_divisors_p(odd_data_divisors[1], odd_data_divisors[2],odd_data :D1_data := D1_data);
"Time for second height";
printf "Start computation of local height at %o between third pair of divisors\n", p;
time ht3 := local_height_divisors_p(odd_data_divisors_inv[2], odd_data_divisors[2], odd_data);
"Time for third height";
local_CG_hts := [-ht1, ht2, -ht3];

N := 6;
/*
local_CG_hts := ChangeUniverse(
[
(5*71 + 20*71^2 + 39*71^3 + 41*71^4 + 6*71^6 + 66*71^7 + 56*71^8),
(43*71 + 35*71^2 + 57*71^3 + 42*71^4 + 35*71^5 + 31*71^6 + 17*71^7 + 47*71^8),
(52*71 + 68*71^2 + 16*71^3 + 15*71^4 + 36*71^5 + 30*71^6 + 70*71^7 + 71^8)
  ], pAdicField(p, N));
  */
N := 12;
"local heights", local_CG_hts;
data := coleman_data(y^2-f, p, N : useU :=false);
height_coeffs := height_coefficients(divisors, intersections, local_CG_hts, data);



printf "Starting quadratic Chabauty at p= %o.\n", p;
time good_affine_rat_pts_xy, no_fake_pts, bad_affine_rat_pts_xy, data, fake_rat_pts, bad_Qppoints :=
 QCModAffine(y^2-f, p : printlevel := 0,  unit_root_splitting := true,
N := N, prec := 30, base_point := base_pt, height_coeffs := height_coeffs, use_log_basis := true);

 // Here * good_affine_rat_pts_xy contains the found rational points in disks where the Frob lift is defined 
  //      * no_fake_pts is true iff the solutions are exactly the rational points
  //      * bad_affine_rat_pts_xy contains the found rational points in disks where the Frob lift isn't defined 
  //      * data is the Coleman data of X at p used in the qc computation
  //      * fake_rat_pts contains the p-adic solutions that don't look rational
  //      * bad_Qppoints contains the disks where Frob isn't defined
  //
  // Express the images of the solutions under Abel-Jacobi in terms of the generators mod p^N
  for i in [1..#fake_rat_pts] do
    fake_rat_pts[i] := [ChangePrecision(fake_rat_pts[i,j], 3) : j in [1..2]];
    // lower precision for speed and to avoid issues in Coleman integrals.
  end for;
  data := coleman_data(y^2-f, p, 6 : useU :=false);
  fake_coeffs_mod_pN, rat_coeffs_mod_pN := coefficients_mod_pN(fake_rat_pts, good_affine_rat_pts_xy, divisors, base_pt, splitting_indices, data); 
  // Check that the coefficients of the known rational points are correct.
  assert &and[&+[rat_coeffs_mod_pN[j,i] * bas[i] : i in [1..gX]] eq X!good_affine_rat_pts_xy[j] - X!base_pt : j in [1..#good_affine_rat_pts_xy]];
  Append(~fake_coeffs, [ fake_coeffs_mod_pN ]);

""; "Use the Mordell-Weil sieve to show that the additional solutions aren't rational.";

"generating cosets";
time qc_fake_coeffs_mod_M := coeffs_CRT(fake_coeffs, primes, exponents);
"number of cosets", #qc_fake_coeffs_mod_M;
qc_M := &*[primes[i]^exponents[i] : i in [1..#primes]];  // modulus


//mws_primes := sieving_primes(qc_M, good_primes, groups, 10); // compute sieving primes
mws_primes := [7,32,83,101,1399];
time done_fake := MWSieve(J, mws_primes, qc_M, bas cat torsion_bas, X!base_pt, qc_fake_coeffs_mod_M : known_rat_coeffs := rat_coeffs_mod_pN );
assert done_fake;
printf "No additional solutions are rational\n";
                                                       //


// Finally exclude points in bad disks and infinite. We checked above that none of these contain a known rational point.
bad_pts_p := [[Roots(ChangeRing(f,GF(p)))[1,1],0,1]] cat [Eltseq(P) : P in PointsAtInfinity(ChangeRing(X, GF(p)))];
modulus := Exponent(AbelianGroup(BaseChange(J, GF(p))));
coeffs_mod := prerun_mwsieve_g2r2(J, bas, base_pt, modulus, p, bad_pts_p);
"number of cosets", #coeffs_mod;
mws_primes_p := [31,109,8111];
printf "starting MW-sieve to exclude rational points in bad and infinite disks at p=%o\n", p;
time done_bad := MWSieve(J, mws_primes_p, modulus, bas cat torsion_bas, X!base_pt, coeffs_mod : special_p_points := [<p, bad_pts_p>], printlevel := 0 ); 

assert done_bad;
printf "There are no rational points in bad or infinite disks for p=%o", p;


