SetLogFile("qc_XS4_13.log");
load "qc_modular.m";
//load "howe_zhu.m";

// We use the model of X_S4(13) found by Banwait-Cremona in `Tetrahedral elliptic curves
// and the local-global principle for isogenies`. Algebra & Number Theory, 8(5):1201–1229, 2014
Q_S4 := 4*x^3*y - x^3- 3*x^2*y^2 + 16*x^2*y+ 3*x^2+ 3*x*y^3 - 11*x*y^2+ 9*x*y+x+ 5*y^3+ y^2+ 2*y;
// We know that the Jacobian of X_S4(13) is isogenous to the Jacobian of X0(169)+, so
// the fact that the rank is 3 and that the Jacobian is absolutely simple follow from
// the analogous results in qc_Xs(13)plus.m

// Find a good affine covering. For this, we apply second_affine_patch twice.
p := 11; 
Q_inf := second_affine_patch(Q_S4, p : bd := 3);
Q := second_affine_patch(Q_inf, p : bd := 3);
good_pts_first_patch, bool1, bad_pts_first_patch, _, _, bad_disks_first_patch := 
                            QCModAffine(Q, p : N := 10, printlevel := 2);

good_pts_second_patch, bool2, bad_pts_second_patch, _, _, bad_disks_second_patch := 
                            QCModAffine(Q_inf, p : N := 10, printlevel := 2);
assert bool1 and bool2;

"Small points", Points(curve(Q): Bound:=100);
"Good affine points on first patch",
good_pts_first_patch;
"Good affine points on second patch",
good_pts_second_patch;


// Need to check that the Hecke operator at 11 generates. Are they in Banwait-Cremona?

//S0 := CuspidalSubspace(ModularSymbols(level, 2)); 
//S := AtkinLehnerSubspace(S0, level, 1);

/*
 * if we have the cuspforms, we might as well compute the rank and check abs simpl for
 * sanity
assert HasAbsolutelyIrreducibleJacobian(curve(Q_S4), 1000);
printf "\nJac(X_S4(13)) is absolutely simple.\n";
*/

//
