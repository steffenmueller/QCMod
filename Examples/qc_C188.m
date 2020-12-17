SetLogFile("qc_C188.log");
_<x> := PolynomialRing(Rationals());
X :=  HyperellipticCurve( x^5 - x^4 + x^3 + x^2 - 2*x + 1);

load "coleman.m";
load "symplectic_basis.m";
load "hecke_correspondence.m";
load "hodge.m";
load "frobenius.m";
load "heights.m";
load "qc_init_g2.m";


p := 3;      // prime number p
rho := 2;
N := 20; prec :=50; basis0 := []; basis1 := []; basis2 := []; 
printlevel := 2; debug := false; base_point := 0;




Q:=y^2 -( x^5 - x^4 + x^3 + x^2 - 2*x + 1);

"Compute the rational points of the curve with affine model ",Q;
QQ := Rationals();
Qp := pAdicField(p,N);
r,Delta,s := auxpolys(Q);

Nend := Floor(N/2);  // Precision used for root finding in the end.
Qp_small   := pAdicField(p,Nend); 
S    := LaurentSeriesRing(Qp,prec);

Qptt := PowerSeriesRing(Qp_small);
Zp_small   := pAdicRing(p,Precision(Qp_small));
Zpt  := PolynomialRing(Zp_small);
Qpt  := PolynomialRing(Qp_small);

pl := printlevel;


// ==========================================================
// ===               2) SYMPLECTIC BASIS                  ===
// ==========================================================
if pl gt 0 then print "Computing a symplectic basis of H^1"; end if;
h1basis, g, r, W0 := h1_basis(Q,p,N);  
// Now h1basis is a basis of H^1 such that the first g elements span the regular
// differentials. Construct a symplectic basis by changing the last g elements of h1basis.
if pl gt 1 then print "Computing the cup product matrix"; end if;
cpm := cup_product_matrix(h1basis, Q, g, r, W0 : prec:=20);
coefficients := symplectic_basis(cpm); // Create coefficients of a symplectic basis in terms of h1basis
new_complementary_basis := [&+[coefficients[i,j]*h1basis[j] : j in [1..2*g]] : i in [1..g]];
sympl_basis := [h1basis[i] : i in [1..g]] cat new_complementary_basis;
if pl gt 2 then print "Symplectic basis of H^1", sympl_basis; end if;
basis0 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [1..g]]; // basis of regular differentials
basis1 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [g+1..2*g]];  // basis of complementary subspace
if pl gt 0 then printf "Computing Coleman data at p=%o.\n", p; end if;
data := coleman_data(Q,p,N : useU:=true,  basis0 := basis0, basis1 := basis1, basis2 := basis2);
data_hol := coleman_data(Q,p,N:useU:=false,basis0:=basis0,basis1:=basis1,basis2:=basis2);
if pl gt 1 then printf "Computed Coleman data at p=%o.\n", p; end if;
g   := data`g;  // genus
rho := g;       // Picard number, assumed equal to the genus

FF   := fun_field(data);
cup_prod_mat := cup_product_matrix(data`basis, Q, g, r, data`W0 : prec:=N);
// By construction, cup_prod_mat is a scalar multiple of the standard symplectic matrix.
// We want them to be equal.
standard_sympl_mat := ZeroMatrix(Rationals(),2*g,2*g);
for i in [1..g] do
  standard_sympl_mat[i,g+i] := 1; standard_sympl_mat[g+i,i] := -1;
end for;
if standard_sympl_mat ne cup_prod_mat then  
  error "The computed symplectic basis is not integral. Please try a different prime.";
end if;

// ==========================================================
// ===                    POINTS                       ===
// ==========================================================
bound := 1000;
Qpoints  := Q_points(data,bound); // small Q-rational points
Qppoints := Qp_points(data); // One Q_p-point for every residue disk.
Fp := FiniteField(p);

// Affine points where Frobenius lift isn't defined:
bad_Qppoints := [P : P in Qppoints | is_bad(P, data) and not P`inf];
bad_Qpoints := [P : P in Qpoints | is_bad(P, data) and not P`inf];
bad_Qpindices := [i : i in [1..#Qppoints] | is_bad(Qppoints[i], data) 
                                          and not Qppoints[i]`inf];

// Affine points where Frobenius lift is defined:
good_Qpoints := [P : P in Qpoints | not is_bad(P, data) and not P`inf];
good_Q_Qp_indices := [FindQpointQp(P,Qppoints) : P in good_Qpoints];
numberofpoints := #Qppoints;

// Find xy-coordinates of the small affine rational points as rational numbers.
// Use LLL for this.
good_coordinates := [xy_coordinates(P,data) : P in good_Qpoints];
good_affine_rat_pts_xy := [[lindepQp(P[1]), lindepQp(P[2])] : P in good_coordinates]; 
bad_coordinates := [xy_coordinates(P,data) : P in bad_Qpoints];
bad_affine_rat_pts_xy := [[lindepQp(P[1]), lindepQp(P[2])] : P in bad_coordinates]; 

if pl gt 1 then 
  print "\n Good affine rational points:", good_affine_rat_pts_xy;  
  print "\n Bad affine rational points:", bad_affine_rat_pts_xy;  
end if;

if IsZero(base_point) then  // No base point given, take the first possible one.
  global_base_point_index := 1;
  bQ := good_Qpoints[global_base_point_index]; // base point as Qpoint
  bQ_xy := good_affine_rat_pts_xy[global_base_point_index];  // xy-coordinates of base point
else 
  bQ := set_point(base_point[1], base_point[2], data); // base point given
  bQ_xy := base_point;
  global_base_point_index := Index(good_affine_rat_pts_xy, base_point);
end if;
local_base_point_index := FindQpointQp(bQ,Qppoints);       // Index of global base point in list of local points.

bpt   := CommonZeros([FF!x-bQ_xy[1], FF.1-bQ_xy[2]])[1]; // Base point as place on the function field
if pl gt 0 then printf "\n Using the base point %o.\n", bQ_xy; end if;
good_affine_rat_pts_xy_no_bpt := Remove(good_affine_rat_pts_xy, global_base_point_index); 

ks := Exclude(good_Q_Qp_indices, local_base_point_index);  // indices in Qppoints of good affine 
                                                           // rational points with base point removed
// compute Teichmueller representatives of good points
teichpoints := [**]; 
for i := 1 to numberofpoints do
  teichpoints[i] := is_bad(Qppoints[i],data) select 0  else teichmueller_pt(Qppoints[i],data);
end for;



// ==========================================================
// ===                 4) CORRESPONDENCES                 ===
// ==========================================================

if pl gt 0 then print "Computing correspondence";  end if;

// Construct correspondence using T_p
correspondences, Tq := hecke_corr(data,p,N:basis0:=basis0,basis1:=basis1,printlevel:=pl);

if pl gt 1 then printf "\nHecke operator at %o acting on H^1:\n%o\n", p, Tq; end if;

if pl gt 1 then
  printf "Hecke correspondences:\n%o\n\n", correspondences;
end if;


Tq_small := ExtractBlock(Tq,1,1,g,g);                // Hecke operator at q on H^0(X,Omega^1)
char_poly_Tq := CharacteristicPolynomial(Tq_small);  
Qp_ext := quo<PolynomialRing(Qp) | char_poly_Tq>;
Salpha := quo<PolynomialRing(S) | char_poly_Tq>;

eqsplit := eq_split(Tq);

// Test equivariance of splitting 
big_split := BlockMatrix(1,2,[eqsplit,ZeroMatrix(Rationals(),2*g,g)]);
check_equiv := ChangeRing((big_split*Transpose(Tq) - Transpose(Tq)*big_split), pAdicField(p, N-2));     
min_val_check_equiv := Min([Min([Valuation(check_equiv[i,j]) : j in [1..g]]): i in [1..2*g]]);
assert min_val_check_equiv ge Nend;

Z := correspondences[1];


// ==========================================================
// ===                     HODGE                       ===
// ==========================================================

if pl gt 0 then printf  "\nComputing Hodge filtration.\n"; end if;
eta,betafil,gammafil := hodge_data(data,Z,bpt); 
if pl gt 1 then 
  printf  "eta =  %o.\n", eta; 
  printf  "beta_fil  =  %o.\n", betafil; 
  printf  "gamma_fil =  %o.\n\n", gammafil; 
end if;

// ==========================================================
// ===                  FROBENIUS                      ===
// ==========================================================
 
b0 := teichmueller_pt(bQ,data); 
if pl gt 0 then printf  "Computing Frobenius structure.\n\n"; end if;
G := frob_struc(data,Z,eta,[QQ!(b0`x),QQ!(b0`b[2])/(Rationals()!W0[2,2])]); // matrix of Frobenius structure on A_Z(b)
G_list := [**]; // evaluations of G at Teichmuellers of all good points (0 if bad)
for i := 1 to numberofpoints do
  if is_bad(Qppoints[i],data) then
    G_list[i]:=0;
  else
    P  := teichpoints[i]; // P is the Teichmueller point in this disk
    pt := [IntegerRing()!c : c in xy_coordinates(P, data)]; // xy-coordinates of P
    G_list[i] := eval_mat_R(G,pt,r); 
  end if;
end for;

PhiAZb_to_b0 := parallel_transport(bQ,b0,Z,eta,data:prec:=prec);
for i := 1 to 2*g do
  PhiAZb_to_b0[2*g+2,i+1] := -PhiAZb_to_b0[2*g+2,i+1];
end for;

PhiAZb := [**]; // Frobenius on the phi-modules A_Z(b,P) (0 if P bad)
for i := 1 to numberofpoints do
  PhiAZb[i] := G_list[i] eq 0 select 0 else
    parallel_transport(teichpoints[i],Qppoints[i],Z,eta,data:prec:=prec)*PhiAZb_to_b0*frob_equiv_iso(G_list[i],data);
end for;

PhiAZb_to_z := [**]; // Frobenius on the phi-modules A_Z(b,z) for z in residue disk of P (0 if P bad)
for i := 1 to numberofpoints do
  PhiAZb_to_z[i] := G_list[i] eq 0 select 0 else
    parallel_transport_to_z(Qppoints[i],Z,eta,data:prec:=prec)*PhiAZb[i]; // Now from b0 to Qppoints[i].
end for;
 
gammafil_list := [* 0 : k in [1..numberofpoints] *]; // evaluations of gammafil at all good points (0 if bad)
gammafil_listb_to_z := [* 0 : k in [1..numberofpoints] *]; // evaluations of gammafil at local coordinates for all points 

if pl gt 2 then printf  "Computing expansions of the filtration-respecting function gamma_fil.\n\n"; end if;
for i := 1 to numberofpoints do
  if G_list[i] ne 0 then
    gammafil_listb_to_z[i] := expand_algebraic_function(Qppoints[i], gammafil, data, N, 200);
    gammafil_list[i] := evalf0(ChangeRing(gammafil,LaurentSeriesRing(BaseRing(gammafil))),Qppoints[i],data);
  end if;
end for;



// ==========================================================
// ===                  HEIGHTS                        ===
// ==========================================================
   

local_heights := [* *];    // local heights of auxiliary points. 
E1P := 0;
super_space := VectorSpace(Qp_small, g+1);
E1_E2_subspace := sub<super_space | [Zero(super_space)]>;
E1_E2_Ps := [* *]; // E1 tensor E2 of auxiliary points
E1_E2_P_vectors := [ ];  // E1 tensor E2 of auxiliary points and away coeffs


// We know that local heights away from p can only be trivial at 2. We also know
// that there is some c of the form rational*log(2) such that h_2(P) = c*f(P), where f(P) is 0,1 or 2
// depending on whether v_2(x(P)) is 0, <2 or >2. So we record f(P) for the known rational
// points (not the base point to avoid index problems).
factors_local_ht_at_2 := [0,2,2,2,2,2,2,0,0];

// Idea: We solve for a1, a2 and c such that
// h = a1*psi1 + a2*psi2, where psi1 and psi2 is the dual of the E1_tensor_E2-basis of
// suitable rational points.
// To do so, we compute h_p(P), E1(P) and E2(P) for sufficiently many known rational points (we need 3)
// and solve a linear system.
//



if IsZero(E1P) then  // Find a point with non-zero E1 to write down a basis of the Lie algebra.
  j := 1; // go through known rational points 
  repeat 
    loc_coord := - Qppoints[ks[j]]`x + good_affine_rat_pts_xy_no_bpt[j][1]; 
    // local coordinate of the jth known ratl pt
    PhiAZb_P := PhiAZb_to_z[ks[j]]; // Frobenius structure
    E1P := Vector(Qp,g,[Evaluate(PhiAZb_P[i+1,1], loc_coord) : i in [1..g]]);                    
  until not IsZero(E1P);
  if pl gt 1 then printf "Using point %o to generate the tangent space.\n", good_affine_rat_pts_xy_no_bpt[j]; end if;
  basisH0star := [];
  for i := 0 to g-1 do
    // basis for H^0(Omega^1)^* generated by powers of iota(Tq) acting on E1(P)
    Append(~basisH0star,Eltseq(E1P*(ChangeRing(Tq_small,Qp)^i))); 
  end for; 
end if; // IsZero(E1P)

// local_heights contains the list of local heights of auxiliary points
i := 1;
repeat 
  loc_coord := - Qppoints[ks[i]]`x + good_affine_rat_pts_xy_no_bpt[i][1];
  // local coordinate of the ith known ratl pt P
  E1_E2_series := E1_tensor_E2(PhiAZb_to_z[ks[i]],betafil,basisH0star,data,Salpha);
  Kt := Parent(E1_E2_series);
  E1_E2_P := Qp_ext![Evaluate(c, loc_coord) : c in Eltseq(E1_E2_series)];
  
  E1_E2_P_vector := Append(Eltseq(E1_E2_P), -factors_local_ht_at_2[i]);  // don't forget about height at 2
  new_E1_E2_subspace := E1_E2_subspace + sub<super_space | [super_space!Eltseq(E1_E2_P_vector)]>;
  if Dimension(new_E1_E2_subspace) gt Dimension(E1_E2_subspace) then
    //i, ks[i];
    E1_E2_subspace := new_E1_E2_subspace; 
    if pl gt 1 then printf "Using point %o to fit the height pairing.\n", good_affine_rat_pts_xy_no_bpt[i]; end if;
    local_ht_series := height(PhiAZb_to_z[ks[i]],betafil,gammafil_listb_to_z[ks[i]],eqsplit,data); // height as power series
    Append(~local_heights, Evaluate(local_ht_series, loc_coord)); // height of A_Z(b, P)
    Append(~E1_E2_P_vectors, E1_E2_P_vector);
  end if;
  i +:= 1;
until #local_heights eq g+1 or i gt #ks; 

local_height_list := [*0 : k in [1..numberofpoints]*];
E1_E2_list := [*0 : k in [1..numberofpoints]*];
for k := 1 to numberofpoints do
  if G_list[k] ne 0 then

    local_height_list[k] := height(PhiAZb_to_z[k],betafil,gammafil_listb_to_z[k],eqsplit,data);
    E1_E2_list[k] := E1_tensor_E2(PhiAZb_to_z[k],betafil,basisH0star,data,Salpha);

  end if;
end for;  // k := 1 to numberofpoints 
   

// Write the height pairing as a linear combination of the basis of symmetric bilinear
// pairings dual to the E1_E2-basis of the auxiliary points. Also solve for h2-constant c
E1_E2_Ps_matrix := Matrix(E1_E2_P_vectors);
local_heights_vector := Matrix(g+1,1,[ht : ht in local_heights]);
height_coeffs := Eltseq(E1_E2_Ps_matrix^(-1)*local_heights_vector);

c := height_coeffs[3];

away_contributions := [a*c : a in [0,1,2]];
// so the global height is of the form sum_i height_coeffs[i]*Psi[i], where 
// Psi[1],...,Psi[g] is the dual basis to E1_E2(P1),...,E1_E2(Pg)

F_list := [**];
for l := 1 to numberofpoints do
  if G_list[l] eq 0 then
    F_list[l] := 0;
  else
    // now find the locally analytic function that extends the global height.
    global_height := &+[height_coeffs[j]*Eltseq(E1_E2_list[l])[j] : j in [1..g]];
    F_list[l] := global_height - local_height_list[l];
  end if;

end for; // l := 1 to numberofpoints 


if pl gt 2 then
  printf "Power series expansions of the quadratic Chabauty functions in all good affine disks, capped at precision %o\n", 3;  
  for i := 1 to #F_list do
    if F_list[i] ne 0 then 
    printf "disk %o\n expansion: %o \n\n", [Fp!(Qppoints[i]`x), Fp!(Qppoints[i]`b[2])], ChangePrecision(F_list[i], 3);
    end if;
  end for;
end if; 
 

zero_list := [* *];
sol_list  := [* *];


// ==========================================================
// ===                    FIND ZEROES                     ===
// ==========================================================

for i := 1 to numberofpoints do
  sol_list[i] := []; 
  zero_list[i] := []; 
  if F_list[i] ne 0 then
    Pp := Qppoints[i];
    xt, yt := local_coord(Pp,prec,data);
    for contrib in away_contributions do
      // solve F_list[i] = contrib 
      f := Evaluate(Qptt!(F_list[i]-contrib),p*Qptt.1);
      val := Valuation(f);
      min_val := Min([Valuation(c) : c in Coefficients(f)]);
      f := p^(-min_val)*Qpt.1^val*(Qpt![Qp!c : c in Coefficients(f)]);
      zero_list[i] := my_roots_Zpt(Zpt!f);
      assert &and[z[2] gt 0 : z in zero_list[i]]; // Check that roots are simple.
      if not IsEmpty(zero_list[i]) then
        for j := 1 to #zero_list[i] do
          t := zero_list[i][j][1];
          Append(~sol_list[i], [Qp_small!Evaluate(c, p*t) : c in [xt, yt[2]]]);
        end for;
      end if;
    end for; // contrib in away_contributions
  end if; // F_list[i] ne 0
end for;  // i:=1 to numberofpoints


// ==========================================================
// ===                    SANITY CHECK                    ===
// ==========================================================


if pl gt 0 then printf "\nSanity check: Does the quadratic Chabauty function map the known good affine rational points into the appropriate set?.\n ", i; end if;
count := 0;
for j in [1..#good_Qpoints] do
  P := good_Qpoints[j]; 
  ind := FindQpointQp(P,Qppoints); 
  Pp := Qppoints[ind];
  xt, yt := local_coord(Pp,prec,data);
  vals := [];
  if ind gt 0 and (is_bad(Qppoints[ind],data) eq false) and (P`inf eq false) then		
    for contrib in away_contributions do
      Append(~vals,  Valuation(Qp_small!Evaluate(F_list[ind]-contrib,P`x - Pp`x))); 
    end for;
    // F_list[ind] = contrib for some away contribution contrib
    assert exists(v){ val : val in vals | val ge Nend/2};
    if pl gt 2 then  print good_affine_rat_pts_xy[j], "Valuation of the quadratic Chabauty function minus sum of contributions away from p", vals; end if;
  count := count+1;
  end if;
end for;
"Sanity check passed";


sols := &cat[L : L in sol_list | #L gt 0];
if pl gt 1 then printf "The quadratic Chabauty set in this affine patch is \n %o \n\n", sols; end if; 
if pl gt 2 then printf "The lists of zeroes is \n %o \n", zero_list; end if; 
fake_rat_pts := [* *];
for i := 1 to #sols do
  P := [lindepQp(sols[i,1]), lindepQp(sols[i,2])];
  if P notin good_affine_rat_pts_xy then
    Append(~fake_rat_pts, sols[i]); 
  end if;
end for;

fake_rat_pts_affine := fake_rat_pts;
good_rat_pts_affine := good_affine_rat_pts_xy;


" Now look at the affine patch Z=0 (actually we only care about the disk at infinity)."; 


X_inf, phi := Transformation(X, [0,1,1,0]);

pi := Inverse(phi);

f_inf := HyperellipticPolynomials(X_inf);
Q_inf := y^2;
for j:=0 to Degree(f_inf) do
  Q_inf -:= Coefficient(f_inf, j)*x^j; 
end for;

Q := Q_inf;
"Affine patch=",Q;
QQ := Rationals();
Qp := pAdicField(p,N);
r,Delta,s := auxpolys(Q);

Nend := Floor(N/2);  // Precision used for root finding in the end.
Qp_small   := pAdicField(p,Nend); 
S    := LaurentSeriesRing(Qp,prec);

Qptt := PowerSeriesRing(Qp_small);
Zp_small   := pAdicRing(p,Precision(Qp_small));
Zpt  := PolynomialRing(Zp_small);
Qpt  := PolynomialRing(Qp_small);

pl := printlevel;


// ==========================================================
// ===               2) SYMPLECTIC BASIS                  ===
// ==========================================================
if pl gt 0 then print "Computing a symplectic basis of H^1"; end if;
h1basis, g, r, W0 := h1_basis(Q,p,N);  
// Now h1basis is a basis of H^1 such that the first g elements span the regular
// differentials. Construct a symplectic basis by changing the last g elements of h1basis.
if pl gt 1 then print "Computing the cup product matrix"; end if;
cpm := cup_product_matrix(h1basis, Q, g, r, W0 : prec:=20);
coefficients := symplectic_basis(cpm); // Create coefficients of a symplectic basis in terms of h1basis
new_complementary_basis := [&+[coefficients[i,j]*h1basis[j] : j in [1..2*g]] : i in [1..g]];
sympl_basis := [h1basis[i] : i in [1..g]] cat new_complementary_basis;
if pl gt 2 then print "Symplectic basis of H^1", sympl_basis; end if;
basis0 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [1..g]]; // basis of regular differentials
basis1 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [g+1..2*g]];  // basis of complementary subspace
if pl gt 0 then printf "Computing Coleman data at p=%o.\n", p; end if;
data := coleman_data(Q,p,N : useU:=true,  basis0 := basis0, basis1 := basis1, basis2 := basis2);
if pl gt 1 then printf "Computed Coleman data at p=%o.\n", p; end if;
g   := data`g;  // genus
rho := g;       // Picard number, assumed equal to the genus

if pl gt 1 then printf "genus = %o.\n", g; end if;
if pl gt 1 then printf "Picard number = %o.\n", rho; end if;

FF   := fun_field(data);
if pl gt 1 then printf "The number of nice correspondences we're using is %o.\n", rho-1; end if;

cup_prod_mat := cup_product_matrix(data`basis, Q, g, r, data`W0 : prec:=N);
// By construction, cup_prod_mat is a scalar multiple of the standard symplectic matrix.
// We want them to be equal.
standard_sympl_mat := ZeroMatrix(Rationals(),2*g,2*g);
for i in [1..g] do
  standard_sympl_mat[i,g+i] := 1; standard_sympl_mat[g+i,i] := -1;
end for;
if standard_sympl_mat ne cup_prod_mat then  
  error "The computed symplectic basis is not integral. Please try a different prime.";
end if;

// ==========================================================
// ===                    POINTS                       ===
// ==========================================================
bound := 1000;
Qpoints  := Q_points(data,bound); // small Q-rational points
Qppoints := Qp_points(data); // One Q_p-point for every residue disk.
Fp := FiniteField(p);

// Affine points where Frobenius lift isn't defined:
bad_Qppoints := [P : P in Qppoints | is_bad(P, data) and not P`inf];
bad_Qpoints := [P : P in Qpoints | is_bad(P, data) and not P`inf];
bad_Qpindices := [i : i in [1..#Qppoints] | is_bad(Qppoints[i], data) 
                                          and not Qppoints[i]`inf];

good_Qpoints := [P : P in Qpoints | not is_bad(P, data) and not P`inf];
good_Q_Qp_indices := [FindQpointQp(P,Qppoints) : P in good_Qpoints];
// Affine points where Frobenius lift is defined:
good_Qpoints := [P : P in Qpoints | not is_bad(P, data) and not P`inf];
good_Q_Qp_indices := [FindQpointQp(P,Qppoints) : P in good_Qpoints];
numberofpoints := #Qppoints;

// Find xy-coordinates of the small affine rational points as rational numbers.
// Use LLL for this.
good_coordinates := [xy_coordinates(P,data) : P in good_Qpoints];
good_affine_rat_pts_xy := [[lindepQp(P[1]), lindepQp(P[2])] : P in good_coordinates]; 
bad_coordinates := [xy_coordinates(P,data) : P in bad_Qpoints];
bad_affine_rat_pts_xy := [[lindepQp(P[1]), lindepQp(P[2])] : P in bad_coordinates]; 

if pl gt 1 then 
  print "\n Good affine rational points on second patch:", good_affine_rat_pts_xy;  
  print "\n Bad affine rational points on second patch:", bad_affine_rat_pts_xy;  
end if;

if IsZero(base_point) then  // No base point given, take the first possible one.
  global_base_point_index := 1;
  bQ := good_Qpoints[global_base_point_index]; // base point as Qpoint
  bQ_xy := good_affine_rat_pts_xy[global_base_point_index];  // xy-coordinates of base point
else 
  bQ := set_point(base_point[1], base_point[2], data); // base point given
  bQ_xy := base_point;
  global_base_point_index := Index(good_affine_rat_pts_xy, base_point);
end if;
local_base_point_index := FindQpointQp(bQ,Qppoints);       // Index of global base point in list of local points.

bpt   := CommonZeros([FF!x-bQ_xy[1], FF.1-bQ_xy[2]])[1]; // Base point as place on the function field
if pl gt 0 then printf "\n Using the base point %o.\n", bQ_xy; end if;
good_affine_rat_pts_xy_no_bpt := Remove(good_affine_rat_pts_xy, global_base_point_index); 

ks := Exclude(good_Q_Qp_indices, local_base_point_index);  // indices in Qppoints of good affine 
                                                           // rational points with base point removed


// compute Teichmueller representatives of good points
teichpoints := [**]; 
for i := 1 to numberofpoints do
  teichpoints[i] := is_bad(Qppoints[i],data) select 0  else teichmueller_pt(Qppoints[i],data);
end for;



// ==========================================================
// ===                    CORRESPONDENCES                 ===
// ==========================================================

if pl gt 0 then print "Computing correspondence";  end if;

// Construct correspondence using T_p
correspondences, Tq := hecke_corr(data,p,N:basis0:=basis0,basis1:=basis1,printlevel:=pl);

if pl gt 1 then printf "\nHecke operator at %o acting on H^1:\n%o\n", p, Tq; end if;

if pl gt 1 then
  printf "Hecke correspondences:\n%o", correspondences;
end if;


Tq_small := ExtractBlock(Tq,1,1,g,g);                // Hecke operator at q on H^0(X,Omega^1)
char_poly_Tq := CharacteristicPolynomial(Tq_small);  
Qp_ext := quo<PolynomialRing(Qp) | char_poly_Tq>;
Salpha := quo<PolynomialRing(S) | char_poly_Tq>;


eqsplit := eq_split(Tq);

// Test equivariance of splitting 
big_split := BlockMatrix(1,2,[eqsplit,ZeroMatrix(Rationals(),2*g,g)]);
check_equiv := ChangeRing((big_split*Transpose(Tq) - Transpose(Tq)*big_split), pAdicField(p, N-2));     
min_val_check_equiv := Min([Min([Valuation(check_equiv[i,j]) : j in [1..g]]): i in [1..2*g]]);
assert min_val_check_equiv ge Nend/2;

Z := correspondences[1];

// ==========================================================
// ===                     HODGE                       ===
// ==========================================================

if pl gt 0 then printf  "\nComputing Hodge filtration.\n"; end if;
eta,betafil,gammafil := hodge_data(data,Z,bpt); 
if pl gt 1 then 
  printf  "eta =  %o.\n", eta; 
  printf  "beta_fil  =  %o.\n", betafil; 
  printf  "gamma_fil =  %o.\n\n", gammafil; 
end if;

// ==========================================================
// ===                  FROBENIUS                      ===
// ==========================================================
 
b0 := teichmueller_pt(bQ,data); 
if pl gt 0 then printf  "Computing Frobenius structure.\n\n"; end if;
G := frob_struc(data,Z,eta,[QQ!(b0`x),QQ!(b0`b[2])/(Rationals()!W0[2,2])]); // matrix of Frobenius structure on A_Z(b)
G_list := [**]; // evaluations of G at Teichmuellers of all good points (0 if bad)
for i := 1 to numberofpoints do
  if is_bad(Qppoints[i],data) then
    G_list[i]:=0;
  else
    P  := teichpoints[i]; // P is the Teichmueller point in this disk
    pt := [IntegerRing()!c : c in xy_coordinates(P, data)]; // xy-coordinates of P
    G_list[i] := eval_mat_R(G,pt,r); 
  end if;
end for;

PhiAZb_to_b0 := parallel_transport(bQ,b0,Z,eta,data:prec:=prec);
for i := 1 to 2*g do
  PhiAZb_to_b0[2*g+2,i+1] := -PhiAZb_to_b0[2*g+2,i+1];
end for;

PhiAZb := [**]; // Frobenius on the phi-modules A_Z(b,P) (0 if P bad)
for i := 1 to numberofpoints do
  PhiAZb[i] := G_list[i] eq 0 select 0 else
    parallel_transport(teichpoints[i],Qppoints[i],Z,eta,data:prec:=prec)*PhiAZb_to_b0*frob_equiv_iso(G_list[i],data);
end for;

PhiAZb_to_z := [**]; // Frobenius on the phi-modules A_Z(b,z) for z in residue disk of P (0 if P bad)
for i := 1 to numberofpoints do
  PhiAZb_to_z[i] := G_list[i] eq 0 select 0 else
    parallel_transport_to_z(Qppoints[i],Z,eta,data:prec:=prec)*PhiAZb[i]; // Now from b0 to Qppoints[i].
end for;
 
gammafil_list := [* 0 : k in [1..numberofpoints] *]; // evaluations of gammafil at all good points (0 if bad)
gammafil_listb_to_z := [* 0 : k in [1..numberofpoints] *]; // evaluations of gammafil at local coordinates for all points 

if pl gt 2 then printf  "Computing expansions of the filtration-respecting function gamma_fil.\n\n"; end if;
for i := 1 to numberofpoints do
  gammafil_listb_to_z[i] := expand_algebraic_function(Qppoints[i], gammafil, data, N, 200);
  if G_list[i] ne 0 then
    gammafil_list[i] := evalf0(ChangeRing(gammafil,LaurentSeriesRing(BaseRing(gammafil))),Qppoints[i],data);
  end if;
end for;



// ==========================================================
// ===                     HEIGHTS                        ===
// ==========================================================
   

local_heights := [* *];    // local heights of auxiliary points. 
E1P := 0;
super_space := VectorSpace(Qp_small, g+1);
E1_E2_subspace := sub<super_space | [Zero(super_space)]>;
E1_E2_Ps := [* *]; // E1 tensor E2 of auxiliary points
E1_E2_P_vectors := [ ];  // E1 tensor E2 of auxiliary points and away coeffs
factors_local_ht_at_2 := [0,2,2,0,0,2,2];


if IsZero(E1P) then  // Find a point with non-zero E1 to write down a basis of the Lie algebra.
  j := 1; // go through known rational points 
  repeat 
    loc_coord := - Qppoints[ks[j]]`x + good_affine_rat_pts_xy_no_bpt[j][1]; 
    // local coordinate of the jth known ratl pt
    PhiAZb_P := PhiAZb_to_z[ks[j]]; // Frobenius structure
    E1P := Vector(Qp,g,[Evaluate(PhiAZb_P[i+1,1], loc_coord) : i in [1..g]]);                    
  until not IsZero(E1P);
  if pl gt 1 then printf "Using point %o to generate the tangent space.\n", good_affine_rat_pts_xy_no_bpt[j]; end if;
  basisH0star := [];
  for i := 0 to g-1 do
    // basis for H^0(Omega^1)^* generated by powers of iota(Tq) acting on E1(P)
    Append(~basisH0star,Eltseq(E1P*(ChangeRing(Tq_small,Qp)^i))); 
  end for; 
end if; // IsZero(E1P)

// local_heights contains the list of local heights of auxiliary points
i := 1;
repeat 
  loc_coord := - Qppoints[ks[i]]`x + good_affine_rat_pts_xy_no_bpt[i][1];
  // local coordinate of the ith known ratl pt P
  E1_E2_series := E1_tensor_E2(PhiAZb_to_z[ks[i]],betafil,basisH0star,data,Salpha);
  Kt := Parent(E1_E2_series);
  E1_E2_P := Qp_ext![Evaluate(c, loc_coord) : c in Eltseq(E1_E2_series)];
  
  E1_E2_P_vector := Append(Eltseq(E1_E2_P), -factors_local_ht_at_2[i]); 
  new_E1_E2_subspace := E1_E2_subspace + sub<super_space | [super_space!Eltseq(E1_E2_P_vector)]>;
  if Dimension(new_E1_E2_subspace) gt Dimension(E1_E2_subspace) then
    E1_E2_subspace := new_E1_E2_subspace; 
    if pl gt 1 then printf "Using point %o to fit the height pairing.\n", good_affine_rat_pts_xy_no_bpt[i]; end if;
    local_ht_series := height(PhiAZb_to_z[ks[i]],betafil,gammafil_listb_to_z[ks[i]],eqsplit,data); // height as power series
    Append(~local_heights, Evaluate(local_ht_series, loc_coord)); // height of A_Z(b, P)
    Append(~E1_E2_P_vectors, E1_E2_P_vector);
  end if;
  i +:= 1;
until #local_heights eq g+1 or i gt #ks; 

local_height_list := [*0 : k in [1..numberofpoints]*];
E1_E2_list := [*0 : k in [1..numberofpoints]*];
for k := 1 to numberofpoints do
  if G_list[k] ne 0 then

    local_height_list[k] := height(PhiAZb_to_z[k],betafil,gammafil_listb_to_z[k],eqsplit,data);
    E1_E2_list[k] := E1_tensor_E2(PhiAZb_to_z[k],betafil,basisH0star,data,Salpha);

  end if;
end for;  // k := 1 to numberofpoints 
   

// Write the height pairing as a linear combination of the basis of symmetric bilinear
// pairings dual to the E1_E2-basis of the auxiliary points. 
E1_E2_Ps_matrix := Matrix(E1_E2_P_vectors);
local_heights_vector := Matrix(g+1,1,[ht : ht in local_heights]);
height_coeffs := Eltseq(E1_E2_Ps_matrix^(-1)*local_heights_vector);

c := height_coeffs[3];

away_contributions := [a*c : a in [0,1,2]];

// so the global height is of the form sum_i height_coeffs[i]*Psi[i], where 
// Psi[1],...,Psi[g] is the dual basis to E1_E2(P1),...,E1_E2(Pg)

F_list := [**];
for l := 1 to numberofpoints do
  if G_list[l] eq 0 then
    F_list[l] := 0;
  else
    // now find the locally analytic function that extends the global height.
    global_height := &+[height_coeffs[j]*Eltseq(E1_E2_list[l])[j] : j in [1..g]];
    F_list[l] := global_height - local_height_list[l];
  end if;

end for; // l := 1 to numberofpoints 

"To deal with the Weierstrass disk, we change the base point and use Coleman integration.";
data2 := coleman_data(Q,p,N:useU:=false,basis0:=basis0,basis1:=basis1,basis2:=basis2);
// recompute coleman data, but restrict to H^1(X) (as opposed to H^1(U))
k := 3;
P0 := Qppoints[k]; // This is the bad point (0,0) 
assert is_bad(P0, data) and not P0`inf;
time singleints := coleman_integrals_on_basis(bQ,P0,data2:e:=100);
correctionfactor := IdentityMatrix(Qp,2*g+2);
for i:=1 to 2*g do
  correctionfactor[2*g+2,i+1] := -2*Eltseq(ChangeRing(singleints,Qp)*ChangeRing(Z,Qp))[i];
end for;

PhiAZb := PhiAZb[local_base_point_index];
PhiAZP0 := PhiAZb*correctionfactor;
PhiAZP0_to_z := parallel_transport_to_z(P0,Z,eta,data:prec:=prec)*PhiAZP0;
local_height_list[k] := height(PhiAZP0_to_z,betafil,gammafil_listb_to_z[k] - Evaluate(gammafil_listb_to_z[k],0),eqsplit,data);
E1_E2_list[k] := E1_tensor_E2(PhiAZP0_to_z,betafil,basisH0star,data,Salpha);
global_height := &+[height_coeffs[j]*Eltseq(E1_E2_list[k])[j] : j in [1..g]];
F_list[k] := global_height - local_height_list[k];




if pl gt 2 then
  printf "Power series expansions of the quadratic Chabauty functions in all affine disks, capped at precision %o\n", 3;  
  for i := 1 to #F_list do
    if F_list[i] ne 0 then 
    printf "disk %o\n expansion: %o \n\n", [Fp!(Qppoints[i]`x), Fp!(Qppoints[i]`b[2])], ChangePrecision(F_list[i], 3);
    end if;
  end for;
end if; 
 

zero_list := [* *];
sol_list  := [* *];


// ==========================================================
// ===                 FIND ZEROES                     ===
// ==========================================================

for i := 1 to numberofpoints do
  sol_list[i] := []; 
  zero_list[i] := []; 
  if F_list[i] ne 0 then
    Pp := Qppoints[i];
    xt, yt := local_coord(Pp,prec,data);
    for contrib in away_contributions do
      // solve F_list[i] = contrib 
      f := Evaluate(Qptt!(F_list[i]-contrib),p*Qptt.1);
      val := Valuation(f);
      min_val := Min([Valuation(c) : c in Coefficients(f)]);
      f := p^(-min_val)*Qpt.1^val*(Qpt![Qp!c : c in Coefficients(f)]);
      zero_list[i] := my_roots_Zpt(Zpt!f);
      assert &and[z[2] gt 0 : z in zero_list[i]]; // Check that roots are simple.
      if not IsEmpty(zero_list[i]) then
        for j := 1 to #zero_list[i] do
          t := zero_list[i][j][1];
          Append(~sol_list[i], [Qp_small!Evaluate(c, p*t) : c in [xt, yt[2]]]);
        end for;
      end if;
    end for; // contrib in away_contributions
  end if; // F_list[i] ne 0
end for;  // i:=1 to numberofpoints


// ==========================================================
// ===                 SANITY CHECK                    ===
// ==========================================================


if pl gt 0 then printf "\nSanity check: Does the quadratic Chabauty function map the known good affine rational points into the appropriate set?.\n ", i; end if;
count := 0;
for j in [1..#good_Qpoints] do
  P := good_Qpoints[j]; 
  ind := FindQpointQp(P,Qppoints); 
  Pp := Qppoints[ind];
  xt, yt := local_coord(Pp,prec,data);
  vals := [];
  if ind gt 0 and (is_bad(Qppoints[ind],data) eq false) and (P`inf eq false) then		
    for contrib in away_contributions do
      Append(~vals,  Valuation(Qp_small!Evaluate(F_list[ind]-contrib,P`x - Pp`x))); 
    end for;
    // F_list[ind] = contrib for some away contribution contrib
    assert exists(v){ val : val in vals | val ge Nend/2};
    if pl gt 2 then  print good_affine_rat_pts_xy[j], "Valuation of the quadratic Chabauty function minus sum of contributions away from p", vals; end if;
  count := count+1;
  end if;
end for;

"Sanity check passed";

if pl gt 0 then printf "\nSanity check: Does the quadratic Chabauty function map the bad affine rational point into the appropriate set?.\n ", i; end if;
P := Qpoints[7];
assert is_bad(P, data);
ind := 3;
Pp := Qppoints[ind];
//assert Pp eq P0;
xt, yt := local_coord(Pp,prec,data);
vals := [];
for contrib in away_contributions do
  Append(~vals,  Valuation(Qp_small!Evaluate(F_list[ind]-contrib,P`x - Pp`x))); 
end for;
// F_list[ind] = contrib for some away contribution contrib
assert exists(v){ val : val in vals | val ge Nend/2};
if pl gt 2 then  print [0,0], "Valuation of the quadratic Chabauty function minus sum of contributions away from p", vals; end if;

"Sanity check passed";


//

sols := &cat[L : L in sol_list | #L gt 0];
if pl gt 1 then printf "The quadratic Chabauty set in the second affine patch is \n %o \n\n", sols; end if; 
if pl gt 2 then printf "The lists of zeroes is \n %o \n", zero_list; end if; 
fake_rat_pts := [* *];
for i := 1 to #sols do
  P := [lindepQp(sols[i,1]), lindepQp(sols[i,2])];
  if P notin good_affine_rat_pts_xy cat bad_affine_rat_pts_xy then
    Append(~fake_rat_pts, sols[i]); 
  end if;
end for;
fake_rat_pts_inf := fake_rat_pts;



"Sanity check: Do the additional solutions on the affine patches correspond to each other?";
K := Universe(fake_rat_pts_affine[1]);
X_p := ChangeRing(X, K);
X_inf_p, phi_p := Transformation(X_p, [0,1,1,0]);
fake1 := [ X_p![P[1],P[2]] : P in fake_rat_pts_affine];
fake2 := [ X_inf_p![P[1],P[2]] : P in fake_rat_pts_inf];
fake1_transformed := [phi_p(P) : P in fake1];
for P in [P : P in fake1_transformed | Valuation(P[1]) ge 0] do // points not mapped to infinity
  assert &or[Valuation(Q[1] - P[1]) ge Floor(N/2)-1 and Valuation(Q[2] - P[2]) ge Floor(N/2)-2 : Q in fake2];
end for;
"Sanity check passed";

// return only those points in fake2 that are not already in fake1.
psi_p := Inverse(phi_p);
fake2_new := [psi_p(P) : P in fake2 | Valuation(psi_p(P)[1]) lt 0];
all_fake_rat_pts := [[P[1],P[2]] : P in fake1 cat fake2_new];

Xpts := [X!P : P in good_rat_pts_affine];
good_pts3 := [pi(X_inf!P) : P in good_affine_rat_pts_xy cat bad_affine_rat_pts_xy];
for P in good_pts3 do
  Include(~Xpts, P);
end for; 
small_pts := Points(X : Bound := 1000); // check we're not missing any small points
assert &and[P in Xpts : P in small_pts];

"";
"Run the Mordell-Weil sieve to show there are no additional rational points in affine disks.";
base_pt := [1,1];
J := Jacobian(X);
torsion_bas, torsion_orders, bas := generators(J);
assert #bas eq 2; // rank = 2
divisors := [* [* [[1,1]],[[0,1]]*],    [* [[1,-1]], [[4,29]] *]*];
P1:=X![1,1]-X![0,1];
P2 := X![1,-1]-X![4,29];
splitting_generators := [P1,P2];
"Use independent points", splitting_generators;
splitting_indices := [[-2,-1], [6,1]];
fake_coeffs_mod_pN, rat_coeffs_mod_pN := coefficients_mod_pN(all_fake_rat_pts, good_rat_pts_affine, divisors, base_pt, splitting_indices, data_hol); 
fake_coeffs := [* *];
Append(~fake_coeffs, [ fake_coeffs_mod_pN ]);

mws_primes := [43];

M := 3^4;
fake_coeffs_mod_M := coeffs_CRT(fake_coeffs, [3], [4]);
"number of residue classes", #fake_coeffs_mod_M;

"Start the Mordell-Weil sieve";
time done_fake := MWSieve(J, mws_primes, M, bas cat torsion_bas, X!base_pt, fake_coeffs_mod_M : known_rat_coeffs := rat_coeffs_mod_pN );
"done with the Mordell-Weil sieve?", done_fake;
"For sieving used the prime(s)", mws_primes;
