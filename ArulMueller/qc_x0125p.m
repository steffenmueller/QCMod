// Compute the rational points on X0(125)+ using quadratic Chabauty.
// Requires the package QCMod, available at https://github.com/steffenmueller/QCMod
// Due to Vishal Arul and Steffen Müller


load "qc_modular.m";
load "qc_init_g2.m";
_<x> := PolynomialRing(Rationals());

Y := SimplifiedModel(X0NQuotient(125, [125]));
// This has pot good reduction, use genus2reduction in sage
//
X, phi:= Transformation(SimplifiedModel(Y), [1,0,-3,1]);
f125 := HyperellipticPolynomials(X);
"Model for X0(125)+:", X;
ptsX := Points(X:Bound:=100);
"Small points: ", ptsX;

// Find good primes for QC
//qc_primes, quality, exponents, groups, good_primes := 
//        find_qc_primes(X : mws_primes_bound := 5000, qc_primes_bound := 120, number_of_bad_disks := 0, inf_modp_allowed := false, known_rat_pts := ptsX); 
p := 29;
// 29 looks promising for a QC+MWS computation, because
FactoredOrder(Jacobian(ChangeRing(X, GF(1399))));
assert not IsSquare(GF(p)!LeadingCoefficient(f125)); // no rational points in disk at
                                                     //infinity. That's why we chose the model X above.
assert IsZero(#Roots(ChangeRing(f125, GF(p)))); // no rational points in bad disks.
 
Q125 := y^2 - f125;
base_pt := [ -1/2, 1/8 ];
good_affine_rat_pts_xy, done, bad_affine_rat_pts_xy, data, fake_rat_pts, bad_Qppoints:= QCModAffine(Q125,p : N := 8,printlevel:=1, base_point := base_pt);

P1 := X![-1,1,2];
P2 := X![-1,-1,2]; 
Q1 := X![-1,1,3];
Q2 := X![-1,-1,3];
divisors := 
[* [*
    [
        [P1[1]/ P1[3], P1[2]/P1[3]^3]
    ],
    [
        [P2[1]/ P2[3], P2[2]/P2[3]^3]
    ]
*], [*
    [
        [Q1[1]/ Q1[3], Q1[2]/Q1[3]^3]
    ],
    [
        [Q2[1]/ Q2[3], Q2[2]/Q2[3]^3]
    ]
*] *];
our_bas := [P1-P2,Q1-Q2]; // these points are independent
A, psi, b1, b2 := MordellWeilGroupGenus2(Jacobian(Y));
basY := [psi(A.1), psi(A.2)];
assert b1 and b2; // This means that basY is really a set of generators for the full MW group.
assert #TorsionSubgroup(Jacobian(Y)) eq 1;
bas := [Evaluate(phi, P) : P in basY];
indices :=[ [1,2], [-1,0]];  // express our_bas in terms of generators
assert &and[our_bas[i] eq indices[i,1]*bas[1] +indices[i,2]*bas[2] : i in [1,2]];

// express images of fake (and actual) rational points under Abel-Jacobi in terms
// of bas, but using our_bas (since that's given by differences of rat'l points, hence
// better for Coleman integrals).
// The coefficients are correct modulo p^N.
fake_coeffs_mod_pN, rat_coeffs_mod_pN := coefficients_mod_pN(fake_rat_pts, good_affine_rat_pts_xy, divisors, base_pt, indices, data); 
// Now show that the fake cooeficients mod p^N don't come from actual rational points.
fake_coeffs := [[fake_coeffs_mod_pN]]; 
"generating residue classes";
primes := [p];
exponents := [1];
time fake_coeffs_mod_M := coeffs_CRT(fake_coeffs, primes, exponents);
"number of residue classes", #fake_coeffs_mod_M;
M := &*[primes[i]^exponents[i] : i in [1..#primes]];  // modulus
J := Jacobian(X);

"number of residue classes", #fake_coeffs_mod_M;
//mws_primes := sp_new(M, good_primes, groups, 15); // compute sieving primes
mws_primes := [1399];
"starting MW-sieve to exclude fake solutions";
time done_fake, bool_list := MWSieve(J, mws_primes, M, bas, X!base_pt, fake_coeffs_mod_M : known_rat_coeffs := rat_coeffs_mod_pN );

"done?", done_fake;

