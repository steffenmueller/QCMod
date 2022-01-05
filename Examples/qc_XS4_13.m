SetLogFile("qc_XS4_13.log");
load "qc_modular.m";

// We use the model of X_S4(13) found by Banwait-Cremona in `Tetrahedral elliptic curves
// and the local-global principle for isogenies`. Algebra & Number Theory, 8(5):1201–1229, 2014
Q_S4 := 4*x^3*y - x^3- 3*x^2*y^2 + 16*x^2*y+ 3*x^2+ 3*x*y^3 - 11*x*y^2+ 9*x*y+x+ 5*y^3+ y^2+ 2*y;
// We know that the Jacobian of X_S4(13) is isogenous to the Jacobian of X0(169)+, so
// the fact that the rank is 3 and that the Jacobian is absolutely simple follow from
// the analogous results in qc_Xs13plus.m
//

// Find a good affine covering. For this, we apply second_affine_patch twice.
p := 11; 
Q := second_affine_patch(Q_S4, p );
Q_inf, A := second_affine_patch(Q, p );
good_pts1, bool1, bad_pts1, _, _, bad_disks_1 := 
                            QCModAffine(Q, p : N := 15, printlevel := 0);

good_pts2, bool2, bad_pts2, _, _, bad_disks_2 := 
                            QCModAffine(Q_inf, p : N:= 15, printlevel := 0);
assert bool1 and bool2;

"Good affine points on first patch",
good_pts1;
"Good affine points on second patch",
good_pts2;
C, Qxy := curve(Q);
P2 := Ambient(C);
X := P2.1; Y := P2.2; Z := P2.3;
C_inf := curve(Q_inf);
a,b,c,d := Explode(A);
C1 := Curve(P2, Evaluate(Equation(C), [a*X+Z+b*Y, Y, c*Z+X+d*Y]));
pi1 := map<C1 -> C | [a*X+Z+b*Y, Y, c*Z+X+d*Y]>;
lc := Rationals()!Coefficient(Equation(C1), Y, 4); 
pi2 := map<C_inf -> C1 | [X, Y/lc, Z]>;
pi := pi2*pi1;

Cpts := [C!P : P in good_pts1];
good_pts3 := [pi(C_inf!P) : P in good_pts2];
for P in good_pts3 do
  Include(~Cpts, P);
end for; 
small_pts := Points(C : Bound := 1000); 
assert #small_pts eq #Cpts;



