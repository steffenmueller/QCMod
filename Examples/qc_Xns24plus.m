SetLogFile("qc_Xns24plus.log");
// model from https://beta.lmfdb.org/ModularCurve/Q/24.96.3.iz.1/
// monic in y via swapping x and y
A2<x,y> := AffineSpace(Rationals(), 2);
Qlmfdb := x^4 - 2*x^3*y + 2*x^3 - x^2*y^2 - 2*x^2*y - x^2 + 2*x*y^3 - 2*x*y^2 + 2*x*y
- 2*x + 2*y^3*+ 2*y^2 + 2*y;
Q := y^4 - 2*y^3*x + 2*y^3 - y^2*x^2 - 2*y^2*x - y^2 + 2*y*x^3 - 2*y*x^2 + 2*y*x
- 2*y + 2*x^3+ 2*x^2 + 2*x;
Caff := Curve(A2, Q);
C := ProjectiveClosure(Caff);
//C2 := RegularModel(C, 2);
//C3 := RegularModel(C, 3);
load "qc_modular.m";
Q := y^4 - 2*y^3*x + 2*y^3 - y^2*x^2 - 2*y^2*x - y^2 + 2*y*x^3 - 2*y*x^2 + 2*y*x
- 2*y + 2*x^3+ 2*x^2 + 2*x;
QCModQuarticNoCheck(Q : p := 13, printlevel := 2, prec := 200);

