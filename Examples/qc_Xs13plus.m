SetLogFile("qc_Xs13plus.log");
load "qc_modular.m";
load "howe_zhu.m";

// X_s(13)+ is isomorphic to X0(169)+ (and to X_ns(13)+)
level := 169;
printf "\n*** Compute the rational points on X0(%o)+ ***\n", level;

r, leading_taylor_coeffs := rank_J0Nplus(169); r;
leading_taylor_coeffs;
// We need T_p to be a generator.
S0 := CuspidalSubspace(ModularSymbols(169, 2)); 
S := AtkinLehnerSubspace(S0, 169, 1);
X := X0NQuotient(169, [169]); X;
// Need a monic model in y
X1 := AffinePatch(X, 1);
A2<y0, x0> := AmbientSpace(X1); Equation(X1);
//
Q := y^3 + y^2*x^2 + y^2*x + y^2 + y*x^3 + y*x - y + x^3 - 3*x^2 + x;
time success, Cpts, p, Q_inf := QCModQuartic(Q, S : N := 25, printlevel := 1);
assert success;
"Rational points on Xns(13)+", Cpts;


"
  For completeness, we include the quadratic Chabauty computation as
  described in the paper `Explicit Chabauty-Kim for the split Cartan
  curve of level 13`, using the prime p=17 and a hard-coded basis of 
  H^1. 
  We leave out the computation of the rational points
  in the bad disk, since this is somewhat harder to incorporate into
  our main function (see qc_C188.m for an examples where this is applied).
";


Q := y^4 + 5*x^4 - 6*x^2*y^2 + 6*x^3 + 26*x^2*y + 10*x*y^2 - 10*y^3 - 32*x^2 -40*x*y + 24*y^2 + 32*x - 16*y; 
// put in a basis omega[i]dx/z for H^1(Y) by hand:
r,Delta,s := auxpolys(Q);
lc := LeadingCoefficient(Delta);
omega := [Qxy|];
omega[1] := 1/lc;
omega[2] := x/lc;
omega[3] := y/lc;
omega[4] := (-160*x^4+736*x^3-16*x^2*y+436*x^2-440*x*y+68*y^2)/(3*lc);
omega[5] := (-80*x^3+132*x^2-40*x*y+68*y^2-96)/(3*lc);
omega[6] := (-48*x^2*y+84*x^2+216*x*y-12*y^2-160*x+272)/(3*lc);
omega[7] := x^2/lc;
omega[8] := x*y/lc;
omega[9] := y^2/lc;

basis0 := []; // first kind
for i := 1 to 3 do
  basis0[i] := Coefficients(reduce_mod_Q_exact(omega[i]*s,Q));
end for;

basis1 := []; // second kind
for i := 1 to 3 do
  basis1[i] := Coefficients(reduce_mod_Q_exact(omega[i+3]*s,Q));
end for;

basis2 := []; // basis for H^1(Y) over H^1(X)
for i := 1 to 3 do
  basis2[i] := Coefficients(reduce_mod_Q_exact(omega[i+6]*s,Q));
end for;

good_pts_first_patch, bool, bad_pts_first_patch, _, _, bad_disks_first_patch := 
          QCModAffine(Q, 17 : basis0 := basis0, basis1 := basis1,
                     basis2 := basis2, N := 20, prec := 25, base_point := [0,0], printlevel := 1);


"Good affine rational points on first patch:", good_pts_first_patch;

"";"Compute the rational points on second affine patch";
Q_inf := -16*x^3*y+32*x^3+24*x^2*y^2-40*x^2*y-32*x^2-10*x*y^3+10*x*y^2+26*x*y+6*x+y^4-6*y^2+5; // x^4*Evaluate(Q,[1/x,y/x])
r,Delta,s := auxpolys(Q_inf);
lc := LeadingCoefficient(Delta);

// put in a basis omega[i]dx/z for H^1(Y) by hand:

omega := [Qxy|];
omega[1] := -x/lc;
omega[2] := -1/lc;
omega[3] := -y/lc;
omega[4] := (768/5*x^2*y-448/5*x*y^2-1536/5*x^2+96*x*y+16*y^2+2272/15*x-1648/15*y+1712/15)/lc;
omega[5] := (128/7*x^2*y^2-5056/35*x^2*y+576/35*x*y^2+7552/35*x^2-816/7*x*y+136/7*y^2+10736/105*x-1072/15*y-184/105)/lc;
omega[6] := (-448/5*x^2*y+288/5*x*y^2+896/5*x^2-80*x*y-8*y^2-2272/15*x+96/5*y-1432/15)/lc; 
omega[7] := x^2/lc;
omega[8] := x*y/lc;
omega[9] := y^2/lc;

basis0 := []; // first kind
for i := 1 to 3 do
  basis0[i] := Coefficients(reduce_mod_Q_exact(omega[i]*s,Q_inf));
end for;

basis1 := []; // second kind
for i := 1 to 3 do
  basis1[i] := Coefficients(reduce_mod_Q_exact(omega[i+3]*s,Q_inf));
end for;

basis2 := []; // basis for H^1(Y) over H^1(X)
for i := 1 to 3 do
  basis2[i] := Coefficients(reduce_mod_Q_exact(omega[i+6]*s,Q_inf));
end for;

good_pts_second_patch, bool, bad_pts_second_patch, _, _, bad_disks_second_patch := 
          QCModAffine(Q_inf, 17 : basis0 := basis0, basis1 := basis1,
                     basis2 := basis2, N := 20, prec := 25, base_point := [0,-1], printlevel := 1);

"Good affine rational points on second patch:", good_pts_second_patch;
