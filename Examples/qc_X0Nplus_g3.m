SetLogFile("qc_X0Nplus_g3.log");
load "qc_modular.m";
load "models_X0Nplus_g2g3.m";
load "howe_zhu.m";
// TODO: Which prime is used for 179 -- 7 or 17?

qc_data := [* *];
for i := 2 to #x0plus_quartics_list do
  Q := x0plus_quartics_list[i];
  level := levels_quartics_list[i];
  S0 := CuspidalSubspace(ModularSymbols(level, 2)); 
  S := AtkinLehnerSubspace(S0, level, 1);
  printf "\n*** Compute the rational points on  X0(%o)+ ***\n", level;
  assert HasAbsolutelyIrreducibleJacobian(curve(Q), 1000);
  printf "\nJ0(%o)+ is absolutely simple.", level;
  r,errors := rank_J0Nplus(level);
  assert Min([Abs(e) : e in errors]) gt 10^-2;  
  // leading coefficients of Taylor expansions should be sufficiently nonzero.
  printf "\nThe rank of J0(%o)+ is %o.", level, r;
  printf "\nStarting quadratic Chabauty for X0(%o)+.\n", level;
  time success, Cpts, p, Q_inf := QCModQuartic(Q, S : printlevel := 0, N := 20);
  assert success;
  printf "Finished quadratic Chabauty computation for X0(%o)+.\n", level;
  printf "Defining equation of first affine patch: \n%o.\n", Q;
  printf "Defining equation of second affine patch: \n%o.\n", Q_inf;
  printf "Rational points: \n%o\n", Cpts;
  printf "Prime used: %o\n\n", p;
  Append(~qc_data, <Q, Cpts, Q_inf, p>);
end for;


