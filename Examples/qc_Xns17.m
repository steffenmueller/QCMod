// Mercuri-Schoof model of Xns(17)+

P5<x1,x2,x3,x4,x5,x6> := ProjectiveSpace(Rationals(), 5);
q1:=-3*x1*x2+x1*x3+x1*x4+x1*x5+x2*x3+2*x2*x4+x2*x5-x2*x6-2*x3^2+2*x3*x4+2*x3*x5+x3*x6+x4*x5-x4*x6+x5^2-x5*x6;
q2:= x1*x2-2*x1*x3-2*x1*x4+x1*x6+x2*x5+2*x2*x6-x3*x4-2*x3*x5+x4^2-x4*x5+x4*x6-2*x5^2+x6^2;
q3:= 3*x1^2+3*x1*x2+x1*x3-x1*x4+x1*x6+x2*x3-x2*x4+x2*x5+2*x2*x6+ x3^2-x3*x4-x4^2-x4*x5-x4*x6+x5^2+2*x5*x6;
q4:= 2*x1^2+2*x1*x2-2*x1*x3+x1*x4-2*x1*x5+x1*x6-x2*x3-x2*x5+3*x2*x6-x3^2+3*x3*x4-3*x3*x5-x4^2-x4*x5+2*x5^2-x5*x6+x6^2;
q5:= x1*x2+5*x1*x3+2*x1*x4-x1*x5+x2^2+3*x2*x3+2*x2*x4-x2*x5-x3^2+2*x3*x4-3*x3*x5+x4^2+3*x4*x6-x5^2-2*x5*x6-x6^2;
q6:=-3*x1*x2+x1*x3-2*x1*x4+4*x1*x5-3*x1*x6-3*x2^2-2*x2*x3-5*x2*x4 +x2*x5-x2*x6+x3^2+x3*x4-3*x3*x5+x4^2-2*x4*x5-2*x4*x6+x5^2+3*x5*x6 -x6^2;
C := Curve(P5, [q1,q2,q3,q4,q5,q6]);

// Find a good model
P2<X,Y,Z> := ProjectiveSpace(Rationals(), 2);
phi := map<P5 -> P2 | [x1 + 2/3*x4 - 1/3*x5 + 1/3*x6, x2 + 4/3*x4 - 5/3*x5 - 1/3*x6, x3 - 2/3*x4 + 4/3*x5 + 2/3*x6]>;
phi2 :=map<P2 -> P2 | [X,Y-Z,Z]>;
D := phi2(phi(C));
_<x,y> := PolynomialRing(Rationals(), 2);
"First affine patch", Evaluate(Equation(D), [y,1,x]);
"Second affine patch", 5/188*Evaluate(Equation(D), [1,x,y]);


SetLogFile("qc_Xns17plus.log");
load "qc_modular.m";

Q1:= y^6 + (24/5*x + 12/5)*y^5 + (-99*x^2 - 543/5*x - 153/5)*y^4 + (-1472/5*x^3 - 2814/5*x^2 - 1719/5*x - 337/5)*y^3 + 
    (-1686/5*x^4 - 975*x^3 - 4761/5*x^2 - 1902/5*x - 263/5)*y^2 + (-108*x^5 - 2082/5*x^4 - 2952/5*x^3 - 375*x^2 - 107*x 
    - 56/5)*y + 188/5*x^6 + 534/5*x^5 + 567/5*x^4 + 284/5*x^3 + 14*x^2 + 7/5*x;
p:=31;
use_polys:=[
    x^3 + 4*x^2 - 13*x - 52,
    x^4 + 4*x^3 - 13*x^2 - 52*x,
    x^5 + 4*x^4 - 13*x^3 - 52*x^2
];
// a list [Pi] of polynomials such that [Pi(Tp)] span the subspace of End^0 (J) annihilating the one dimensional and two dimensional isogeny factors of Jns+(17).

a1,b1,c1,d1,e1:=QCModAffine(Q1,31:printlevel:=2,use_polys:=use_polys,number_of_correspondences:=2);

// the only bad disks are at infinity. we deal with these with the second model

Q2:=y^6 + (267/94*x - 135/47)*y^5 + (567/188*x^2 - 1041/94*x - 843/94)*y^4 + (71/47*x^3 - 738/47*x^2 - 4875/188*x - 368/47)*y^3 + (35/94*x^4 - 1875/188*x^3 - 4761/188*x^2 -
    1407/94*x - 495/188)*y^2 + (7/188*x^5 - 535/188*x^4 - 951/94*x^3 - 1719/188*x^2 - 543/188*x + 6/47)*y - 14/47*x^5 - 263/188*x^4 - 337/188*x^3 - 153/188*x^2 + 3/47*x + 
    5/188;

// the only bad disks of this model (at p=31) are at infinity, and the infinite F31-points of the two models do not intersect.

a2,b2,c2,d2,e2:=QCModAffine(Q2,31:printlevel:=2,use_polys:=use_polys,number_of_correspondences:=2);
