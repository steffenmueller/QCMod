// Compute the rational points on X0(N)+ for all composite N such that 
// * the genus of X0(N)+ is between 2 and 5
// * it was not already known from [1--4] below that there are no 
//   exceptional rational points.
// Due to Vishal Arul and Steffen Müller

// [1] Theorem 0.1 of MR0866046, F. Momose ``Rational points on the modular curves X_{0}^{+}(p^{r})'' 
// [2] Theorem 0.1 of MR0879929, F. Momose ``Rational points on the modular curves X_{0}^{+}(N)''
// [3] Proposition 2.11 of MR0879929, F. Momose ``Rational points on the modular curves X_{0}^{+}(N)''
// [4] Main Theorem of MR2660892, F. Momose and K. Arai ``Rational points on X_{0}^{+}(37M)''
//

/*
 * Genus 2 values of N are
 * [ 42, 46, 52, 57, 62, 67, 68, 69, 72, 73, 74, 77, 80, 87, 91, 98, 103, 107, 111, 121, 125, 143, 167, 191 ]
 *
 * [1] handles 121 
 * [2] handles 46, 57, 62, 68, 69, 77, 87, 121, 143 
 * [4] handles 74, 111
 * For good measure, we compute the rational points below:
   * 42, 46, 52, 62, 68, 69, 72, 80, 87, 98 have rank 0 
   * 57, 74, 77, 111, 121, 143 have rank 1
 * 91 is done in BBBM21 -> needs quadratic Chabauty plus the Mordell-Weil sieve
 * 125  needs quadratic Chabauty plus the Mordell-Weil sieve
 * Survey paper https://arxiv.org/abs/1910.12755 handles 67, 73, 103
 * BDMTV2 handles 107, 167, 191
 */
//L := [67,73,85,93,103,106,107,115,122,129,122,129,133,134,146,154,158,161,165,167,170,177,186,191,205,206,209,213,215,221,230,266,285,286,287,299,357,390];

"----------------------------------";
"Genus 2";
"----------------------------------";
L := [0] cat  [GenusX0NQuotient(N, [N]) : N in [2..10000]];

c := 2;
g2s := [i : i in [1..10000] | L[i] eq c];                                   
rank0s:=[];
rank1s:=[];
rank2s:=[];
for N in g2s do
  r := RankBound(Jacobian(X0NQuotient(N,[N]))); 
  assert r le 2;
  if r eq 0 then 
    Append(~rank0s, N);
  elif r eq 1 then 
    Append(~rank1s, N);
  else 
    Append(~rank2s, N);
  end if;
end for;
//ranksg2s := [<N,RankBound(Jacobian(X0NQuotient(N,[N])))> : N in g2s];
rank0s := [N : N in g2s |  RankBound(Jacobian(X0NQuotient(N,[N]))) eq 0];
pts_rank0s := [*<N, Chabauty0(Jacobian(SimplifiedModel(X0NQuotient(N,[N]))))> : N in rank0s*];
"Rational points on Rank 0 examples", pts_rank0s;
"----------------------------------";

pts_rank1s := [* *];
for j in [1..#rank1s] do 
  N := rank1s[j];
  //"N=", N;
  X := SimplifiedModel(X0NQuotient(N,[N]));
  J := Jacobian(X);
  l,u := RankBounds(J); 
  assert l eq u; // check if the exact rank is known
  ptsJ := Points(J:Bound:=100);
  i:=1;
  repeat 
    i+:=1;
  until Order(ptsJ[i]) eq 0;
  //"Use Point", ptsJ[i];
  rat_pts_N := Chabauty(ptsJ[i]);
  pts_rank1s[j] := <N, rat_pts_N>;
end for;
  
"Rational points on Rank 1 examples", pts_rank1s;
"----------------------------------";

"Rank 2 cases:",rank2s;
"----------------------------------";


/*
 * Genus 3 values of N are
 * [ 58, 60, 66, 76, 85, 86, 96, 97, 99, 100, 104, 109, 113, 127, 128, 139, 149, 151, 169, 179, 239 ]
 *
 * [1] handles 128
 * [2] handles 58, 66, 76, 85, 86, 99
 * [3] handles 104
 * The cursed curve paper handles 169 (isomorphic to X_{ns}(13))
 * See below for 60, 100, 96
 * BDMTV2 handles prime values 97, 109, 113, 127, 139, 149, 151, 179, 239
 *
 * That's all for genus 3, nothing is left.
 */
"----------------------------------";
"Genus 3";
"----------------------------------";
"N=60";
X060plus := X0NQuotient(60, [60]);  
// For hyperelliptic curves, magma has specific automorphism group code
// which won't be useful for us here, since it doesn't work with
// CurveQuotient.
C := Curve(Ambient(X060plus), Equation(X060plus)); 
aut_grp_C := AutomorphismGroup(C);
// Can't use full automorphism group, since the quotient is P^1.
auts1 := AutomorphismGroup(C, [aut_grp_C.2]);
Y, f1 := CurveQuotient(auts1);
"Genus of quotient", Genus(Y);
Z, f2 := SimplifiedModel(Y);
"rank bounds of quotient", RankBounds(Jacobian(Z));
pts_Z := Chabauty0(Jacobian(Z));
f := f1*f2;  
D := Pullback(f, &+[Place(Z!P) : P in pts_Z]);
"Points in the preimages of the rational points", [RepresentativePoint(P[1]) : P in Decomposition(D) | Degree(P[1]) eq 1]; // [ (3 : 56 : 1), (2 : 14 : 1), (2 : 13 : 1), (1 : 2 : 1), (1 : 1 : 0), (1 : 0 : 0) ]

"----------------------------------";
"N=96";
X096p := X0NQuotient(96, [96]);  
aut := iso<X096p->X096p| [- Y - Z, - X - Z, Z], [- Y - Z, - X - Z, Z]> where X is CR.1 where Y is CR.2 where Z is CR.3 where CR is (CoordinateRing(AmbientSpace(X096p)));
Y, f1 := CurveQuotient(AutomorphismGroup(X096p,[aut]));
"Genus of quotient", Genus(Y);
P := f1(X096p ! [1,0,0]);
E, f2 := EllipticCurve(Y,P);
"Conductor of quotient", Conductor(E);
Emin, f3 := MinimalModel(E);
"Rank of quotient", Rank(Emin);
T, phi := TorsionSubgroup(Emin);
S := [phi(Q) : Q in T];
"All rational points on minimal model of quotient", S;
f := f1*f2*f3; // quotient map to minimal model
D := Pullback(f, &+[Place(P) : P in S]);
"Points in the preimages of the rational points", [RepresentativePoint(P[1]) : P in Decomposition(D) | Degree(P[1]) eq 1]; // [ (0 : 0 : 1), (-1 : -1 : 1), (1 : 0 : 0), (0 : 1 : 0) ]

"----------------------------------";
"N=100";
X0100p := X0NQuotient(100, [100]);
auts := AutomorphismGroup(X0100p);
"Automorphism group", auts;
Y := CurveQuotient(auts);
Y, f1 := CurveQuotient(auts);
"Genus of quotient", Genus(Y);
"Small points on quotient", RationalPoints(Y : Bound := 10);
P := Y![0,1,0,0];
E, f2 := EllipticCurve(Y,P);
"Conductor of quotient", Conductor(E);
Emin, f3 := MinimalModel(E);
"Rank of quotient", Rank(Emin);
T, phi := TorsionSubgroup(Emin);
S := [phi(Q) : Q in T];
"All rational points on minimal model of quotient", S;
f := f1*f2*f3; // quotient map to minimal model
D := Pullback(f, &+[Place(P) : P in S]);
"Points in the preimages of the rational points", [RepresentativePoint(P[1]) : P in Decomposition(D) | Degree(P[1]) eq 1]; // [ (0 : 0 : 1), (1 : 0 : 0), (0 : 1 : 0), (-1 : 1 : 0) ]

"----------------------------------";
/*
 * Genus 4 values of N are
 * [ 70, 82, 84, 88, 90, 92, 93, 94, 108, 115, 116, 117, 129, 135, 137, 147, 155, 159, 161, 173, 199, 215, 251, 311 ]
 *
 * [2] handles 82, 88, 92, 93, 94, 115, 116, 129, 155, 159, 161, 215
 * [3] handles 70, 108, 135, 147
 * See below for 84, 90, 117 
 * AABCCKW handles prime levels 137, 173, 199, 251, 311
 *
 * That's all for genus 4, nothing is left.
 */
"----------------------------------";
"Genus 4";
"----------------------------------";

"N=84";
X084p := X0NQuotient(84, [84]);
auts := AutomorphismGroup(X084p);
"Automorphism group", auts;
// Can't use full automorphism group, since the quotient is P^1.
Y, f1 := CurveQuotient(AutomorphismGroup(X084p, [auts.1]));
"Genus of quotient", Genus(Y);
P := f1(X084p ! [1,0,0,0]);
E, f2 := EllipticCurve(Y,P);
"Conductor of quotient", Conductor(E);
Emin, f3 := MinimalModel(E);
"Rank of quotient", Rank(Emin);
T, phi := TorsionSubgroup(Emin);
S := [phi(Q) : Q in T];
"All rational points on minimal model of quotient", S;
f := f1*f2*f3; // quotient map to minimal model
D := Pullback(f, &+[Place(P) : P in S]);
"Points in the preimages of the rational points", [RepresentativePoint(P[1]) : P in Decomposition(D) | Degree(P[1]) eq 1]; // [ (1 : 0 : 1 : 0), (1 : 0 : 0 : 0), (1 : 0 : 0 : 1), (0 : 0 : 0 : 1), (0 : -1 : 0 : 1), (0 : -1 : 1 : 0), (0 : 0 : 1 : 0), (0 : 1 : 0 : 0) ]

"----------------------------------";
"N=90";
X090p := X0NQuotient(90, [90]);
auts := AutomorphismGroup(X090p);
"Automorphism group", auts;
// Can't use full automorphism group, since the quotient is P^1.
Y, f1 := CurveQuotient(AutomorphismGroup(X090p, [auts.1]));
"Genus of quotient", Genus(Y);
P := f1(X090p ! [1,0,0,0]);
E, f2 := EllipticCurve(Y,P);
"Conductor of quotient", Conductor(E);
Emin, f3 := MinimalModel(E);
"Rank of quotient", Rank(Emin);
T, phi := TorsionSubgroup(Emin);
S := [phi(Q) : Q in T];
"All rational points on minimal model of quotient", S;
f := f1*f2*f3; // quotient map to minimal model
D := Pullback(f, &+[Place(P) : P in S]);
"Points in the preimages of the rational points", [RepresentativePoint(P[1]) : P in Decomposition(D) | Degree(P[1]) eq 1]; // [ (0 : 0 : 0 : 1), (0 : 1 : 0 : 0), (1 : 0 : 0 : 0), (0 : -1 : 1 : 0) ]

"----------------------------------";
"N=117";
X0117p := X0NQuotient(117, [117]);
auts := AutomorphismGroup(X0117p);
"Automorphism group", auts;
Y, f1 := CurveQuotient(auts);
"Genus of quotient", Genus(Y);
Z, f2 := SimplifiedModel(Y);
"Small points on quotient", RationalPoints(Z:Bound:=10);
RankBounds(Jacobian(Z));
pts_Z := Chabauty0(Jacobian(Z));
f := f1*f2;  
D := Pullback(f, &+[Place(Z!P) : P in pts_Z]);
"Points in the preimages of the rational points", [RepresentativePoint(P[1]) : P in Decomposition(D) | Degree(P[1]) eq 1]; // [ (0 : 1 : 0 : 0), (0 : 1 : -1 : 1), (-1 : 0 : 1 : 0), (0 : 0 : 1 : 0) ]

"----------------------------------";
/*
 * Genus 5 values of N are
 * [ 78, 105, 106, 110, 112, 122, 123, 133, 134, 144, 145, 146, 157, 171, 175, 181, 185, 209, 227, 263 ]
 *
 * [2] handles 106, 110, 122, 123, 133, 134, 145, 146, 171, 209
 * [3] handles 78, 105, 175
 * [4] handles 185
 * See below for 112, 144
 * AABCCKW handles prime levels  157, 181, 227, 263
 *
 * That's all for genus 5, nothing is left.
 */

"----------------------------------";
"Genus 5";
"----------------------------------";

"N=112";
X0112p := X0NQuotient(112, [112]);
auts := AutomorphismGroup(X0112p);
"Automorphism group", auts;
Y, f1 := CurveQuotient(AutomorphismGroup(X0112p, [auts.2]));
"Genus of quotient", Genus(Y);
Z, f2 := SimplifiedModel(Y);
"Small points on quotient", RationalPoints(Z:Bound:=10);
RankBounds(Jacobian(Z));
pts_Z := Chabauty(Points(Jacobian(Z):Bound:=100)[4]);
f := f1*f2;  
D := Pullback(f, &+[Place(Z!P) : P in pts_Z]);
"Points in the preimages of the rational points", [RepresentativePoint(P[1]) : P in Decomposition(D) | Degree(P[1]) eq 1]; // [ (1 : -1 : 0 : -1 : 1), (-1 : -1 : 0 : -1 : 1), (0 : 0 : 1 : 0 : 0), (0 : 0 : 0 : 0 : 1), (1 : -1 : 0 : 1 : 1), (0 : 1 : 0 : 0 : 0) ]

"N=144";
X0144p := X0NQuotient(144, [144]);
auts := AutomorphismGroup(X0144p);
"Automorphism group", auts;
Y := CurveQuotient(auts);
Y, f1 := CurveQuotient(auts);
"Genus of quotient", Genus(Y);
"Small points on quotient", RationalPoints(Y : Bound := 10);
P := Y![0,0,0,1];
E, f2 := EllipticCurve(Y,P);
"Conductor of quotient", Conductor(E);
Emin, f3 := MinimalModel(E);
"Rank of quotient", Rank(Emin);
T, phi := TorsionSubgroup(Emin);
S := [phi(Q) : Q in T];
"All rational points on minimal model of quotient", S;
f := f1*f2*f3; // quotient map to minimal model
D := Pullback(f, &+[Place(P) : P in S]);
"Points in the preimages of the rational points", [RepresentativePoint(P[1]) : P in Decomposition(D) | Degree(P[1]) eq 1]; // [ (0 : 0 : 0 : 0 : 1), (0 : 0 : 1 : 0 : 1), (0 : 0 : 1 : 1 : 0), (0 : 0 : 0 : 1 : 0) ]
